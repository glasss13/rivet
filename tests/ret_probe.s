.intel_syntax noprefix
.text
.globl ret_probe
ret_probe:
    lea rdx, [rip + .Lresume]
    push rdx
    mov rax, rsp
    ret
.Lresume:
    sub rax, rsp
    neg rax
    ret
.section .note.GNU-stack,"",@progbits
