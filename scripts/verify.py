#!/usr/bin/env python3
"""Regenerate, kernel-check, audit dependencies, and run native validation."""
import json, pathlib, platform, subprocess, sys, tempfile, re
root=pathlib.Path(__file__).resolve().parents[1]
def run(*args): subprocess.run(args,cwd=root,check=True)
lock=json.loads((root/'tools.lock.json').read_text())
assert platform.machine()=='x86_64' and sys.platform=='linux', 'native validation requires x86_64 Linux'
assert platform.python_version()==lock['python'], 'Python version differs from tools.lock.json'
assert subprocess.check_output(['gcc','-dumpfullversion'],text=True).strip()==lock['gcc']
assert subprocess.check_output(['as','--version'],text=True).splitlines()[0].endswith(lock['assembler'])
for tool in ['rustc','cargo']:
    assert subprocess.check_output([tool,'--version'],text=True).split()[1] == lock[tool], f'{tool} version differs from tools.lock.json'
run('cargo','test','--manifest-path','importer/Cargo.toml','--locked','--offline')
run('cargo','build','--manifest-path','importer/Cargo.toml','--locked','--offline')
for name,ns in [('sum_bytes','Imported'),('beyond','Beyond'),('omit','Omit')]:
    run(str(root/'importer/target/debug/asm-to-lean'), str(root/f'fixtures/{name}.s'), str(root/f'Verification/{ns}.lean'), ns)
for path in [root/'Verification.lean', *(root/'Verification').glob('*.lean')]:
    # Reject proof bypasses even in otherwise unreachable declarations.
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',path.read_text()),path
run('lake','build','Verification','probe','parser')
with tempfile.TemporaryDirectory() as tmp:
    audit=pathlib.Path(tmp)/'Audit.lean'
    names=['Imported.certificate','sum_bytes_correct','all_accesses_safe','empty_reads_only_stack','callee_saved','run_memory','never_faults','stays_returned','run_registers64','example_preconditions','beyond_counterexample','omission_counterexample']
    audit.write_text('import Verification\n'+'\n'.join('#print axioms Verification.'+n for n in names))
    output=subprocess.check_output(['lake','env','lean',str(audit)],cwd=root,text=True)
    for deps in re.findall(r'depends on axioms: \[([^]]*)\]',output):
        assert set(filter(None,(d.strip() for d in deps.split(',')))) <= {'propext','Quot.sound','Classical.choice'}
    assert len(re.findall(r'depends on axioms:',output)) == len(names)
    print(output,end='',flush=True)
run(sys.executable,'tests/validate.py')
