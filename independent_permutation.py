"""Enumerate by canonical direct-sum factors and greedy transitions on individual runs.

No interval inclusion-exclusion, chunk-polynomial recurrence, or polynomial package.
"""
from collections import Counter
from itertools import combinations, product
from bisect import bisect_left


def side_counts(word):
    """Count states (greedy end position, number of runs, length) of run words."""
    r = len(word)
    transitions = {}
    for start in range(r+1):
        for size in range(1, max(word)+1):
            finish = next((i+1 for i in range(start,r) if word[i] >= size), None)
            if finish is not None:
                transitions[start,size] = finish
    states = [Counter() for _ in range(r+1)]
    states[0][0,0] = 1
    # nontrivial indecomposable factors, split by whether they contain D_r
    short, full = Counter(), Counter()
    for start, by_size in enumerate(states):
        for (layers, length), number in by_size.items():
            if layers == r:
                full[length] += number
            elif layers >= 2:
                short[length] += number
            for size in range(1,max(word)+1):
                finish = transitions.get((start,size))
                if finish is not None:
                    states[finish][layers+1,length+size] += number
    return short, full


def canonical_counts(u,v):
    """Disjoint factor types, each counted exactly once."""
    r=len(u)
    assert len(v) == r >= 2
    us,uf=side_counts(u)
    vs,vf=side_counts(v)
    counts=Counter()
    # A single nontrivial factor visible on at least one side. Count words
    # one part at a time, tracking which of the two full embeddings still fits.
    singles=Counter({(0,True,True):1})
    for a,b in zip(u,v):
        after=Counter()
        for (n,left,right), number in singles.items():
            for t in range(1,max(a,b)+1):
                fits_left, fits_right = left and t<=a, right and t<=b
                if fits_left or fits_right:
                    after[n+t,fits_left,fits_right] += number
        singles=after
    for (n,_,_), number in singles.items():
        counts[n] += number
    # One nontrivial factor with singleton factors on one side.
    for full, bound in [(uf,max(v)),(vf,max(u))]:
        for n,number in full.items():
            for singleton_count in range(1,bound+1):
                counts[n+singleton_count] += number
    # Two nontrivial factors. Each must come entirely from its respective side.
    for left,right in [(uf,vs),(us,vf),(uf,vf)]:
        for m,a in left.items():
            for n,b in right.items():
                counts[m+n] += a*b
    return tuple(counts[n] for n in range(sum(u)+sum(v)+1))


def skew_runs(word):
    remaining=sum(word)
    out=[]
    for a in word:
        remaining -= a
        out.extend(range(remaining+1,remaining+a+1))
    return tuple(out)


def make_top(u,v):
    return skew_runs(u)+tuple(sum(u)+i for i in skew_runs(v))


def standardize(entries):
    order={v:i+1 for i,v in enumerate(sorted(entries))}
    return tuple(order[v] for v in entries)


def longest_decrease(entries):
    ends=[]
    for x in entries:
        k=bisect_left(ends,-x)
        if k == len(ends):
            ends.append(-x)
        else:
            ends[k] = -x
    return len(ends)


def literal_interval(u,v):
    """Only for small tops. Enumerate subsequences of the actual permutation."""
    top=make_top(u,v)
    values=[]
    for k in range(len(top)+1):
        pats={standardize(sub) for sub in combinations(top,k) if longest_decrease(sub)>=len(u)}
        values.append(len(pats))
    return tuple(values)


def main():
    from verify_permutation import chunks, template, interval, short_example
    checked=0
    for r,alphabet in [(2,(1,2,3)),(3,(1,2))]:
        for u in product(alphabet,repeat=r):
            for v in product(alphabet,repeat=r):
                assert literal_interval(u,v) == canonical_counts(u,v), (u,v)
                checked+=1
    print('Canonical classes vs literal subsequences:',checked,'small intervals')
    u,v,short = short_example()
    assert canonical_counts(u,v)==tuple(short)
    from verify_by_deletion import TOP
    assert make_top(u,v)==TOP
    print('Length-50 witness matches all 33 ranks and literal one-line top.')
    c,d=template(3,4)
    u=(1,)*14+(2,)
    v=(1,1,2)*3+(2,)*6
    u,v=u*4,v*4
    assert (u,v)==(chunks(c),chunks(d))
    canonical=canonical_counts(u,v)
    assert canonical==tuple(interval(c,d))
    assert canonical[121:124]==(318760232883761,314759367160492,318217445359443)
    assert sorted(make_top(u,v))==list(range(1,161))
    assert longest_decrease(make_top(u,v))==60
    print('Witness top length 160; longest decreasing subsequence 60')
    import json
    from pathlib import Path
    cert=json.loads(Path(__file__).with_name('permutation-certificate.json').read_text())
    for record in cert:
        a,b=record['left_capacities'],record['right_capacities']
        r=len(a)
        assert record['bottom']==list(range(r,0,-1))
        assert record['top']==list(make_top(a,b))
        assert record['rank_sizes']==list(canonical_counts(a,b)[r:])
        assert record['total']==sum(record['rank_sizes'])
    print('Both complete one-line endpoint pairs and rank certificates agree.')
    print('All 101 rank sizes agree; interval cardinality', sum(canonical))
    print('Ranks 61, 62, 63:', *canonical[121:124])


if __name__=='__main__':
    main()
