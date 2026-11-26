"""Direct enumeration of the length-50 interval from the one-line permutation.

No run decomposition or rank formula. A level is a set of ordinary permutations.
"""
from bisect import bisect_left

TOP = (
    19,18,17,16,15,14,13,12,10,11,9,8,7,6,5,4,3,2,1,
    49,50,47,48,45,46,43,44,42,40,41,39,37,38,36,34,35,33,
    31,32,30,28,29,26,27,24,25,22,23,20,21,
)
BOTTOM_LENGTH = 18
# Upon deleting v, all remaining entries greater than v decrease by one.
STANDARDIZE = [bytes(j-(j>v) for j in range(256)) for v in range(len(TOP))]


def contains_bottom(word):
    # Patience sorting on negated entries calculates the longest decreasing length.
    ends = []
    for a in word:
        j = bisect_left(ends, -a)
        if j == len(ends):
            ends.append(-a)
            if len(ends) == BOTTOM_LENGTH:
                return True
        else:
            ends[j] = -a
    return False


def count_ranks():
    assert sorted(TOP) == list(range(1,len(TOP)+1))
    top = bytes(v-1 for v in TOP)
    assert contains_bottom(top)
    level = {top}
    high_to_low = [1]
    for length in range(len(top)-1,BOTTOM_LENGTH-1,-1):
        children = set()
        for word in level:
            for j,v in enumerate(word):
                shorter = (word[:j]+word[j+1:]).translate(STANDARDIZE[v])
                children.add(shorter)
        level = {word for word in children if contains_bottom(word)}
        high_to_low.append(len(level))
    assert level == {bytes(reversed(range(BOTTOM_LENGTH)))}
    return list(reversed(high_to_low))


if __name__=='__main__':
    ranks = count_ranks()
    assert ranks[19:22] == [78468,78022,78544]
    assert sum(ranks)==1125373
    import json
    from pathlib import Path
    cert=json.loads(Path(__file__).with_name('permutation-certificate.json').read_text())[0]
    assert list(TOP)==cert['top'] and ranks==cert['rank_sizes']
    print('Length-50 top. All ranks by literal deletion:', ranks)
    print('Total distinct interval permutations:',sum(ranks))
