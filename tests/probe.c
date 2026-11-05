#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
  if(argc!=5) return 2;
  const char *op=argv[1];
  uint64_t a=strtoull(argv[2],0,10), b=strtoull(argv[3],0,10), pc=6;
  unsigned z=atoi(argv[4]); unsigned char f=0, byte=(unsigned char)b;
  if(!strcmp(op,"xor")) __asm__ volatile("xor %%eax,%%eax; setz %1" : "+a"(a),"=qm"(f) :: "cc");
  else if(!strcmp(op,"test")) __asm__ volatile("test %%rsi,%%rsi; setz %0" : "=qm"(f) : "S"(a) : "cc");
  else if(!strcmp(op,"movzx")) __asm__ volatile("cmp $1,%2; movzbl (%%rdi),%%edx; setz %1" : "=d"(a),"=qm"(f) : "r"(z),"D"(&byte) : "cc");
  else if(!strcmp(op,"add")) __asm__ volatile("add %%rdx,%%rax; setz %1" : "+a"(a),"=qm"(f) : "d"(b) : "cc");
  else if(!strcmp(op,"inc")) __asm__ volatile("inc %%rdi; setz %1" : "+D"(a),"=qm"(f) :: "cc");
  else if(!strcmp(op,"dec")) __asm__ volatile("dec %%rsi; setz %1" : "+S"(a),"=qm"(f) :: "cc");
  else if(!strcmp(op,"jz")) __asm__ volatile("cmp $1,%2; jz 1f; mov $6,%0; jmp 2f; 1: mov $17,%0; 2: setz %1" : "=r"(pc),"=qm"(f) : "r"(z) : "cc");
  else if(!strcmp(op,"jnz")) __asm__ volatile("cmp $1,%2; jnz 1f; mov $6,%0; jmp 2f; 1: mov $17,%0; 2: setz %1" : "=r"(pc),"=qm"(f) : "r"(z) : "cc");
  else return 2;
  printf("%llu %u %llu\n",(unsigned long long)a,f,(unsigned long long)pc);
}
