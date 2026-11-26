"""Exact rank tests under endpoint deletions of the 38-point witness."""
from functools import cache
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from permutation_intervals import ranks

U = (1,) * 7 + (2,) + (1,) * 6
V = (2,) + (2, 1) * 7
BASE = 1 << 48  # No coefficient exceeds the number of subsets of the 38-point top.

@cache
def words(host):
    result = {()}
    for k in host:
        result |= {w + (a,) for w in result for a in range(1, k + 1)}
    return result

@cache
def poly(s, host):
    return sum(c * BASE**k for k, c in enumerate(ranks(s, host)))

def fits(s, host):
    pos = 0
    for a in host:
        if pos < len(s) and s[pos] <= a:
            pos += 1
    return pos == len(s)

def cut_one(host):
    for j, k in enumerate(host):
        yield host[:j] + ((k-1,) if k > 1 else ()) + host[j+1:]

def is_unimodal(h):
    prev = 0
    falling = False
    while h:
        h, a = divmod(h, BASE)
        if falling and a > prev:
            return False
        falling |= a < prev
        prev = a
    return True

def inspect(u, v, s, common):
    # For a bottom containing a descent, a good skew-layered factor is directly indecomposable.
    gu, gv = poly(s, u), poly(s, v)
    intersection = sum(BASE**sum(w) for w in common if fits(s, w))
    h = gu * poly((), v) + (poly((), u) - gu)*gv - intersection
    return h, is_unimodal(h)

def initial_segment(k):
    return sum(BASE**j for j in range(k+1))

def principal(u, v, common):
    # A single-side pattern is increasing or is directly indecomposable with a descent.
    a, b = max(u), max(v)
    du = poly((), u) - initial_segment(a)
    dv = poly((), v) - initial_segment(b)
    both = sum(BASE**sum(w) for w in common if len(w) > 1)
    return (initial_segment(a+b) + du*dv + du*initial_segment(b)
            + initial_segment(a)*dv - both)

if __name__ == '__main__':
    tops = {(U, V)}
    # Each bottom with at least two runs contains a descent.
    bottoms = sorted(w for w in words(U) if len(w) >= 2)
    for deleted in range(3):
        tested = 0
        for u, v in sorted(tops):
            common = [w for w in words(u) if fits(w, v)]
            full = principal(u, v, common)
            # Avoiding 1 leaves just the empty pattern. Avoiding 12 leaves the
            # decreasing patterns, one per length up to the longest decreasing subsequence.
            for s, avoided in [((1,), 1), ((2,), initial_segment(max(len(u), len(v))))]:
                tested += 1
                if not is_unimodal(full - avoided):
                    print('valley', sum(u)+sum(v), sum(s), s, u, v, flush=True)
            for s in bottoms:
                if not fits(s, u) and not fits(s, v):
                    continue
                tested += 1
                h, good = inspect(u, v, s, common)
                if not good:
                    print('valley', sum(u)+sum(v), sum(s), s, u, v, flush=True)
        print('deleted', deleted, 'tops', len(tops), 'comparable intervals', tested, flush=True)
        if deleted < 2:
            tops = ({(a, v) for u, v in tops for a in cut_one(u)} |
                    {(u, b) for u, v in tops for b in cut_one(v)})
