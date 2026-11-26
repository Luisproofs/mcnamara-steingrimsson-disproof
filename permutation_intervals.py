"""Rank coefficients of intervals of layered permutations in classical pattern order."""
from functools import cache
from itertools import product
from math import prod
from random import Random


def ranks(lower,upper):
    # Each distinct layer sequence has one leftmost greedy embedding.
    width=(prod(x+1 for x in upper).bit_length()+7)//8
    bit=8*width
    radix=1<<bit
    m=len(lower)
    # Group positive next letters by their first possible matching position.
    moves=[]
    for i in range(len(upper)+1):
        groups=[]
        prev=0
        for j in range(i,len(upper)):
            v=upper[j]
            if v>prev:
                groups.append((j+1,prev+1,v))
                prev=v
        moves.append(groups)
    @cache
    def shifts(a,b):
        return ((radix**(b-a+1)-1)//(radix-1)) << (bit*a)
    @cache
    def suffix(i,k):
        result=int(k==m)
        for j,a,b in moves[i]:
            if k==m:
                result+=shifts(a,b)*suffix(j,k)
            else:
                v=lower[k]
                if a<v:
                    result+=shifts(a,min(b,v-1))*suffix(j,k)
                if b>=v:
                    result+=shifts(max(a,v),b)*suffix(j,k+1)
        return result
    data=suffix(0,0).to_bytes(width*(sum(upper)+1),'little')
    return [int.from_bytes(data[i:i+width],'little') for i in range(0,len(data),width)]


def search():
    rng=Random(20261125)
    count=0
    for _ in range(10000):
        length=rng.randint(3,25)
        palette=rng.sample(range(1,18),rng.randint(2,4))
        top=tuple(rng.choice(palette) for _ in range(length))
        if _%2:
            sub=top[:rng.randint(1,length-1)]
            top=tuple(sub)+top+tuple(sub)
        bottom=tuple(rng.choice((v,v,1,rng.randint(1,v))) for v in top if rng.randrange(5)<3)
        y=ranks(bottom,top)
        fallen=False
        for j in range(1,len(y)):
            if y[j]<y[j-1]:
                fallen=True
            if fallen and y[j]>y[j-1]:
                print('COUNTEREXAMPLE',bottom,top,y,flush=True)
                return
        count+=1
    print('Layered permutation intervals checked',count)
if __name__=='__main__':
    search()
