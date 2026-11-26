# A counterexample with endpoints of lengths 15 and 38

[Two-page research note (PDF)](note.pdf) · [Editable, printable note (HTML)](note.html) · [Endpoints and full rank sequence](literal-results.txt)

The new top is an actual pattern of the length-50 top. In the old left summand retain runs 1–7, 9, and 10–15, with their original capacities. In the old right summand retain runs 1–15, trimming them to the word `2 (2 1)^7`. This deletes four entries on the left and eight on the right. The new bottom is the entire 15-point left summand. It has a single ascent. The original 18-point bottom was decreasing.

The new interval contains 40,106 permutations. Its rank sizes at levels 14, 15 and 16 are 3,662, 3,659 and 3,685. The algebraic proof and the checks here pertain to the length-38 top. The earlier Lean project certifies the length-50 top.

## Reproduction

From the project root, using Python 3 with its standard library, run

```sh
python3 reduction/check_algebra.py
python3 reduction/check_by_deletion.py
python3 reduction/verify_smaller.py
python3 reduction/neighborhood.py
```

The first check multiplies the ordinary integer polynomials in the note. The second starts with the literal top, deletes each possible entry, standardizes, and deduplicates. It retains a permutation exactly when it has an ascent flanked by a decreasing seven above it and a decreasing six below it. Every pattern containing the bottom can be reached along such a chain by keeping one occurrence and deleting unused entries. The third check independently builds the sets of patterns on each side and counts distinct direct sums meeting the lower bound. The two literal enumerations agree at every rank.

## Local minimality

For the top, take every permutation obtained by deleting zero, one or two entries and standardizing. For the bottom, allow **any nonempty pattern of the new bottom**, including itself. Test all comparable pairs. The exact enumeration produced the following results.

| Top entries deleted | Distinct tops | Intervals tested | Nonunimodal |
|---:|---:|---:|---:|
| 0 | 1 | 70 | 1 |
| 1 | 18 | 1,260 | 0 |
| 2 | 148 | 10,346 | 0 |

The sole exception is the displayed witness. This gives local minimality under these deletions. The search leaves open both the globally shortest top and whether this same top admits a shorter bottom outside the tested set.

For a top with capacity words A and B, let F count all patterns on a side and G count those containing the chosen bottom. Subscripts indicate the side. For a bottom with a descent in this search, every occurrence fits in one summand, since the bottom is directly indecomposable. Every side pattern containing it is also directly indecomposable. A pair counted by the left-good class has its left side determined by the first direct factor, and a right-good pair is determined analogously. A decomposable permutation in both classes has exactly two direct factors: in its left-good representation the suffix contains a descent in the last factor, so it is a skew-layered permutation with a descent and hence directly indecomposable. Thus its two factors must both be good. The indecomposable permutations in the overlap are exactly the common good single-side patterns. The absolute rank polynomial is therefore

```
G_A F_B + (F_A − G_A) G_B − (common good single-side polynomial).
```

The computation obtains F and G from the existing greedy word enumerator in `permutation_intervals.py`. For bottoms 1 and 12 it uses the entire principal downset and subtracts respectively the empty pattern or all decreasing patterns. To enumerate that downset, classify each side as increasing (including empty) or directly indecomposable with a descent. Two increasing sides give precisely the increasing patterns up to the sum of their maximum lengths. In the other three cases the factors with descents are recoverable from the direct factorization; the only duplicates are common single-side patterns with a descent. The program uses radix 2^48 for polynomial evaluation, which exceeds even the number of subsets of the 38-point top.

## Search record

The original shrinking routine checked single capacity reductions and paired run deletions of the original words. The subsequent searches varied side lengths, run alignments and capacities, tried a distinguished ascent in the bottom, and explored direct and skew sums with different blocks. Lengths 43 and 42 occurred along the way. The length-38 construction was found by `tagged.py`, which lets the marked double occupy any eligible slot. Allowing one more run on the right than on the left permits many short right patterns while restricting the location of that double in patterns containing the bottom. The opposing changes in these two contributions give the three-rank valley.

The other search scripts and their results are retained here as exploratory records. Some use rank cutoffs, canonical representatives or seeded sampling. The local minimality table uses the separate full-rank enumeration in `neighborhood.py`.
