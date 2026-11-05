.globl omit
omit:
    xor eax, eax
    dec rsi
    test rsi, rsi
    jz done
loop:
    movzx edx, BYTE PTR [rdi]
    add rax, rdx
    inc rdi
    dec rsi
    jnz loop
done:
    ret
