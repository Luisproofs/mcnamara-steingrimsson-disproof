"""Exact finite part and rational bounds for the full one-parameter family."""
from fractions import Fraction
from verify_permutation import add, mul, good, chunks, interval, template


def kernel(ks):
    v = [1]
    for k in ks:
        jump = [0,0]+[1]*k
        v = mul(v, add([0]*(k+1)+[1,1], jump))
    return v, good(chunks(ks))


def evaluate(p, x):
    value = 0
    for a in reversed(p):
        value = value*x + a
    return value


def moments(p):
    mass = sum(p)
    mean = Fraction(sum(j*a for j,a in enumerate(p)),mass)
    variance = sum(a*(j-mean)**2 for j,a in enumerate(p))/mass
    return mass, mean, variance


def main():
    u, v = template(3,1)
    vu, gu = kernel(u)
    vv, gv = kernel(v)
    A, B = mul(vu,gv), mul(gu,vv)
    assert moments(A) == (8192,Fraction(231,8),Fraction(1399,64))
    assert moments(B) == (8192,Fraction(67,2),Fraction(13,4))
    for q, x, bound in ((A,Fraction(11,10),2),(B,Fraction(4,5),4)):
        radius = x+x*x
        assert radius>1 and radius/(radius-1)<bound
        assert evaluate(q,x) < Fraction(9,10)*8192*x**31
    assert 6*(4*80+2)*9**80 < 10**80
    print('Exact means, variances, rational tilts, and the L=80 tail comparison passed.')

    # The only division is by x+x^2-1, with constant coefficient -1.
    # Multiply each macro power by its fixed small kernel once per step.
    kernels = [A,B,gu,gv,mul(gu,gv)]
    powers = [[1] for _ in kernels]
    for L in range(1,80):
        powers = [mul(k,p) for k,p in zip(kernels,powers)]
        a,b,u_power,v_power,both = powers
        radius=[0,1,1]
        divisor=[-1,1,1]
        positive=mul(radius,add(a,b))
        subtract=add(add(u_power,v_power),mul(divisor,add(u_power,both)))
        numerator=add(positive,[-c for c in subtract])
        h=[]
        previous=older=0
        for n in numerator:
            current=previous+older-n
            h.append(current)
            older,previous=previous,current
        assert len(h)==40*L+3 and h[-2:]==[0,0]
        del h[-2:]
        assert min(h)==0 and h[15*L]==h[-1]==1
        if L<=4:
            assert h==interval(*template(3,L))
        if L<4:
            peak=h.index(max(h))
            assert h[:peak+1]==sorted(h[:peak+1]) and h[peak:]==sorted(h[peak:],reverse=True)
        else:
            assert h[29*L]>h[31*L]<h[33*L], L
    print('L=1,2,3 are unimodal. Lengths 29L, 31L, 33L certify every L from 4 through 79.')


if __name__=='__main__':
    main()
