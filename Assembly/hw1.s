.data
    n: .word 7
    
.text
.globl __start

FUNCTION:
    # Todo: Define your own function in HW1
    

# Do NOT modify this part!!!
__start:
    la   t0, n
    lw   x10, 0(t0)
    jal  x1,FUNCTION
    la   t0, n
    sw   x10, 4(t0)
    addi a0,x0,10
    ecall