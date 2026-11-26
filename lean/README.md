# Lean certificate for the McNamara–Steingrímsson counterexample

Lean 4.36.0 verifies that the classical permutation-pattern interval with decreasing bottom of length 18 and the specified top of length 50 has the following rank sizes.

| Relative rank | Length | Distinct permutations |
|---:|---:|---:|
| 19 | 37 | 78,468 |
| 20 | 38 | 78,022 |
| 21 | 39 | 78,544 |

The two public theorems are `PatternInterval.consecutive_rank_sizes` and `PatternInterval.disproof`. The latter proves the negation of Conjecture 9.4. The paper defines its poset on permutations of positive length in §1 and states weak rank-unimodality in §9.4. The Lean statement follows both conventions. [Formal theorems](PatternInterval.lean) · [Conjecture and definitions](PatternInterval/Order.lean) · [Original paper](https://arxiv.org/pdf/1305.5569)

## Verify

From this directory, with the pinned toolchain installed, run

```sh
lake --wfail build
lake env lean Audit.lean
```

The project uses the libraries shipped with Lean and has zero external Lake packages. The build checks the numerical equalities by kernel reduction. The audit prints both theorem types and rejects axiom dependencies outside the three standard Lean axioms. In the verified build, both theorems depend on `propext`, `Classical.choice`, and `Quot.sound`.

For a second kernel check, the following commands export the two theorems and their transitive dependencies, then replay them in an initially empty kernel environment.

```sh
proof_export=$(mktemp)
lake env leanexport PatternInterval -- PatternInterval.consecutive_rank_sizes PatternInterval.disproof > "$proof_export" &&
  lake env leanchecker --from-export "$proof_export"
rm -f "$proof_export"
```

The replay returned `Lean default kernel accepts the solution`.

## How the proof connects the counts to the poset

1. An ordinary permutation is a list containing each integer from zero through its length minus one exactly once. The top is written out literally and translated from the paper's one-based notation. A pattern occurs when some subsequence has the same strict comparison at every pair of positions. [Definitions](PatternInterval/Order.lean) · [Endpoints](PatternInterval/Witness.lean)
2. The proof records those comparisons in a triangular table. Restricting the table by a mask corresponds to selecting a subsequence. A mask splits across a direct or skew sum. Each summand of the witness is a skew sum of increasing runs of length one or two, so its subpatterns correspond to words of admissible run sizes. [Block restrictions](PatternInterval/Blocks.lean) · [Run characterization](PatternInterval/Runs.lean)
3. A decreasing subsequence lies on one side of a direct sum and uses at most one entry per run. At the target ranks, each admissible pair of run words uniquely determines an interval element and can be recovered from it. The number of greater entries to the right of a position is at most one in the right summand. In the left summand it is at least the entire selected right length, which is at least two at all three ranks. This distinguishes the two sides even when a pattern has many embeddings. [Encoding and injectivity](PatternInterval/Encoding.lean)
4. A greedy enumeration produces each admissible word once. A histogram records how many such words have a given number of runs and entries. Lean proves that the histogram agrees with the duplicate-free enumeration for every weighting function, then evaluates the exact rank counts. [Enumeration](PatternInterval/Language.lean) · [Counting](PatternInterval/Counting.lean)
5. Reading a comparison table reconstructs the unique standardized one-line permutation. Lean transfers the cardinalities to ordinary permutations in the interval. The drop at rank 19 forces a putative peak to be at most 19, while the rise from rank 20 to rank 21 then contradicts unimodality. [Standardization](PatternInterval/Standardize.lean) · [Final contradiction](PatternInterval.lean)

This project formalizes the finite disproof. The periodic infinite-family theorem is treated in the [research manuscript](../permutation-disproof.md).
