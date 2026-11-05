.globl sum_bytes
sum_bytes:
    xor eax, eax
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
