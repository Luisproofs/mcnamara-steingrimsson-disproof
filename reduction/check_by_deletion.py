"""Verify the interval directly from its one-line endpoints, using only Python's standard library."""
from bisect import bisect_left

BOTTOM = (15,14,13,12,11,10,9,7,8,6,5,4,3,2,1)
TOP = BOTTOM + (37,38,35,36,34,32,33,31,29,30,28,26,27,25,23,24,22,20,21,19,17,18,16)
EXPECTED = (1,13,61,175,365,628,968,1377,1827,2294,2763,3196,
            3516,3660,3662,3659,3685,3441,2622,1473,565,136,18,1)

def insert_tail(tails, value):
    pos = bisect_left(tails, value)
    if pos == len(tails):
        tails.append(value)
    else:
        tails[pos] = value

def contains_bottom(w):
    # An occurrence is a decreasing seven, an ascent, and a decreasing six,
    # with all seven larger and all six smaller than both entries of the ascent.
    n = len(w)
    prefix = [-1] * n
    tails = []
    for i, a in enumerate(w):
        if len(tails) >= 7:
            prefix[i] = -tails[6]  # largest last value of a preceding decreasing seven
        insert_tail(tails, -a)
    tails.clear()
    for j in range(n-1, 6, -1):
        b = w[j]
        if len(tails) >= 6:
            threshold = tails[5]  # smallest first value of a subsequent decreasing six
            if any(threshold < w[i] < b < prefix[i] for i in range(7, j)):
                return True
        insert_tail(tails, b)
    return False

def enumerate_interval():
    bottom = bytes(x-1 for x in BOTTOM)
    top = bytes(x-1 for x in TOP)
    assert sorted(top) == list(range(len(top)))
    assert contains_bottom(bottom)
    tables = [bytes(j - (j > a) for j in range(256)) for a in range(len(top))]
    layer = {top}
    sizes = [1]
    for _ in range(len(top)-len(bottom)):
        candidates = {(p[:i]+p[i+1:]).translate(tables[a])
                      for p in layer for i, a in enumerate(p)}
        layer = {p for p in candidates if contains_bottom(p)}
        sizes.append(len(layer))
    assert layer == {bottom}
    return tuple(reversed(sizes))

if __name__ == '__main__':
    sizes = enumerate_interval()
    assert sizes == EXPECTED
    print('Relative ranks 0 through 23:', *sizes)
    print('Total:', sum(sizes))
