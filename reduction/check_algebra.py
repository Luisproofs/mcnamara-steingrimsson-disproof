"""Coefficient arithmetic in the two-page proof. Polynomials are lists in ascending degree."""
from math import comb

def product(f, g):
    h = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            h[i+j] += a*b
    return h

def add(f, g):
    return [(f[i] if i < len(f) else 0) + (g[i] if i < len(g) else 0)
            for i in range(max(len(f), len(g)))]

def verify():
    fu = add([1]*15, [0, 0] + product([1]*8, [1]*7))
    assert fu[15] == 1
    proper = fu[:15]
    # First F_(1), then prepend six copies of (1,2) and two copies of (2).
    fv = [1, 1]
    for _ in range(6):
        fv = add([1, 1], product([0, 0, 2, 1], fv))
    for _ in range(2):
        fv = add([1], product([0, 1, 1], fv))
    right_good = product([comb(6, k) for k in range(7)], [1, 5, 1])
    proper_left = product(proper, right_good)
    rows = [(r, fv[r], proper_left[r], fv[r]+proper_left[r]) for r in (14, 15, 16)]
    assert [t[-1] for t in rows] == [3662, 3659, 3685]
    return rows

if __name__ == '__main__':
    print('rank  full-left  proper-left  total')
    for r in verify():
        print(*r)
