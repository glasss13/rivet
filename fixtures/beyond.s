.globl beyond
beyond:
    xor eax, eax
    test rsi, rsi
loop:
    movzx edx, BYTE PTR [rdi]
    add rax, rdx
    inc rdi
    dec rsi
    jnz loop
done:
    ret
