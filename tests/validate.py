#!/usr/bin/env python3
import pathlib, subprocess, random, sys, tempfile, hashlib
ROOT=pathlib.Path(__file__).resolve().parents[1]
IMPORTER=ROOT/'importer/target/debug/asm-to-lean'

def generate(path, namespace='Imported'):
    # This is only a subprocess adapter. Parsing and code generation are entirely Rust.
    with tempfile.TemporaryDirectory() as tmp:
        output=pathlib.Path(tmp)/'Generated.lean'
        result=subprocess.run([str(IMPORTER),str(path),str(output),namespace],capture_output=True,text=True)
        if result.returncode:
            raise ValueError(result.stderr.strip())
        return output.read_text()

def call(*args): return subprocess.check_output(args,cwd=ROOT,text=True).strip()
def main():
    for name,ns in [('sum_bytes','Imported'),('beyond','Beyond'),('omit','Omit')]:
        path=ROOT/f'fixtures/{name}.s'
        expected=generate(path,ns)
        assert expected==generate(path,ns)==(ROOT/f'Verification/{ns}.lean').read_text()
        assert hashlib.sha256(path.read_bytes()).hexdigest() in expected
    with tempfile.TemporaryDirectory() as tmp:
        tmp=pathlib.Path(tmp)
        objects=[]
        for name in ['sum_bytes','beyond','omit']:
            # The fixture bytes are concatenated unchanged; this is the fixed native wrapper.
            wrapper=tmp/f'{name}.s'
            wrapper.write_bytes(b'.intel_syntax noprefix\n.text\n'+(ROOT/f'fixtures/{name}.s').read_bytes()+b'\n.section .note.GNU-stack,"",@progbits\n')
            obj=tmp/f'{name}.o'; call('gcc','-c',str(wrapper),'-o',str(obj)); objects.append(str(obj))
        native=tmp/'native'
        call('gcc','-O2','-Wall','-Wextra','-Werror','tests/native.c','tests/ret_probe.s',*objects,'-o',str(native))
        print(call(str(native)))
        assert call('.lake/build/bin/probe','ret','512','0','0')=='8'
        base=(ROOT/'fixtures/sum_bytes.s').read_text()
        bad=[
            base.replace('ret','syscall'), base.replace('ret','call loop'),
            base.replace('ret','jmp rax'), base.replace('ret','ret 8'),
            base.replace('loop:', 'done:'), base.replace('jz done','jz missing'),
            base+'.globl other\nother:\nret\n', '.include "other.s"\n'+base,
            '.macro foo\n.endm\n'+base, '.if 1\n'+base+'.endif\n',
            base.replace('add rax, rdx','add eax, edx'),
            base.replace('[rdi]','[rdi+1]'), base.replace('ret','ret; nop'),
            base.replace('ret','nop'), base.replace('ret','.byte 0xc3'),
            base.replace('jz done','jz trailing')+'trailing:\n', '',
        ]
        for i,source in enumerate(bad):
            f=tmp/f'reject{i}.s'; f.write_text(source)
            try: generate(f)
            except ValueError: pass
            else: raise AssertionError(('Rust accepted',source))
            results=[subprocess.run([str(ROOT/'.lake/build/bin/parser'),str(f)],capture_output=True,text=True) for _ in range(2)]
            assert all(r.returncode==1 for r in results),(source,results)
            assert results[0].stdout==results[1].stdout
        assert call('.lake/build/bin/parser','fixtures/sum_bytes.s')=='accepted'
        # Check Rust's Lean-string escaping with actual kernel certificates.
        source_variants=[
            '.globl tiny\ntiny:\n\txor eax,eax # café \"quoted\" \\ path\nret\n',
            '.globl tiny\r\ntiny:\r\n xor eax, eax\r\nret # control: \x01\r\n',
        ]
        for index,source in enumerate(source_variants):
            f=tmp/f'escaped{index}.s'; f.write_bytes(source.encode('utf-8'))
            generated=generate(f,'Escaped')
            artifact=tmp/'Escaped.lean'; artifact.write_text(generated)
            call('lake','env','lean',str(artifact))
            assert hashlib.sha256(f.read_bytes()).hexdigest() in generated
        for padding in [0,1,15,31,32,55,56,63,64,65,127,128]:
            f=tmp/'hash.s'; f.write_bytes(b'.globl tiny\ntiny:\nret #'+b'x'*padding)
            assert hashlib.sha256(f.read_bytes()).hexdigest() in generate(f)
        f=tmp/'invalid.s'; f.write_bytes(b'\xff')
        try: generate(f)
        except ValueError as e: assert 'invalid UTF-8' in str(e)
        else: raise AssertionError('Rust accepted invalid UTF-8')
        print('Rust emission: UTF-8/escaping/CRLF kernel certificates and hash boundary cases passed')
        # A wrong generated instruction cannot retain the parsing certificate.
        tampered=tmp/'Tampered.lean'
        certified=generate(ROOT/'fixtures/sum_bytes.s','Tampered').replace(
            'import Verification.Parser','import Verification.Imported').replace(
            'by decide +kernel','by exact Imported.certificate')
        tampered.write_text(certified)
        call('lake','env','lean',str(tampered))
        tampered.write_text(certified.replace('⟨.jz 8,','⟨.jz 7,'))
        result=subprocess.run(['lake','env','lean',str(tampered)],cwd=ROOT,capture_output=True,text=True)
        assert result.returncode!=0 and 'Type mismatch' in result.stdout,result
        print(f'rejection: {len(bad)} cases in both parsers, stable diagnostics; tampered certificate rejected')
        probe=tmp/'probe'
        call('gcc','-O2','-Wall','-Wextra','-Werror','tests/probe.c','-o',str(probe))
        rng=random.Random(20261105)
        values=[0,1,255,256,2**32-1,2**32,2**63,2**64-1]+[rng.getrandbits(64) for _ in range(12)]
        count=0
        for op in ['xor','test','movzx','add','inc','dec','jz','jnz']:
            for i,a in enumerate(values):
                for z in [0,1]:
                    b=values[-i-1]
                    args=[op,str(a),str(b),str(z)]
                    model=call('.lake/build/bin/probe',*args)
                    actual=call(str(probe),*args)
                    assert model==actual,(args,model,actual)
                    count+=1
        print(f'instruction differential: {count} cases passed (plus native return probe)')
    print('deterministic generation and source hashes: passed')
if __name__=='__main__': main()
