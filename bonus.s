.data
    n: .word 11
.text
.globl __start


jal x0, __start
#----------------------------------------------------Do not modify above text----------------------------------------------------
FUNCTION:
# Todo: Define your own function
# We store the input n in register a0, and you should store your result in register a1
addi sp, sp, -8
sw x1, 4(sp)
sw a0, 0(sp)
#Test a0 >= or < 10
addi t1, x0, 10
bge a0, t1, BE10
addi a0, a0, -1
addi t3, x0, 1
#need to solve x1
auipc x1, 0
addi x1, x1, 40
bge a0,  t3, FUNCTION#Test if a0>=1
addi a1, x0, 7
jalr x0, 0(x1)
BE10:#bigger than or equal 10
add t2, x0, a0#a0
add a0, t2, a0#2*a0
add a0, t2, a0#3*a0
srai a0, a0, 2
jal x1, FUNCTION
L1:
slli a1, a1, 1
lw a0, 0(sp)
lw x1, 4(sp)
addi sp, sp, 8
addi a3, x0, 10
bge a0, a3, L2
jalr x0, 0(x1)
L2:
addi t4, x0, 7
mul a2, a0, t4
srai a2, a2, 3
add a1, a1, a2
addi a1, a1, -137
jalr x0, 0(x1)



#----------------------------------------------------Do not modify below text----------------------------------------------------
__start:
    la   t0, n
    lw   a0, 0(t0)
    jal  x1, FUNCTION
    la   t0, n
    sw   a1, 4(t0)
    li a7, 10
    ecall
