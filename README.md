# Nonunimodal intervals in the classical permutation pattern poset

An AI-assisted research project presenting counterexamples to McNamara–Steingrímsson, Conjecture 9.4 in [On the topology of the permutation pattern poset (2015)](https://arxiv.org/abs/1305.5569).

## Results

* **Lean-verified witness:** bottom length 18, top length 50. Relative ranks 19, 20 and 21 contain 78,468, 78,022 and 78,544 distinct permutations, respectively. The strict valley contradicts weak rank-unimodality.
* **Smaller witness:** bottom length 15, top length 38. Relative ranks 14, 15 and 16 contain 3,662, 3,659 and 3,685 distinct permutations, respectively. The smaller witness has a conventional algebraic proof and computational checks, not a Lean formalization. No global minimality claim is made.
* The research manuscript also gives a proposed infinite-family theorem; this theorem is not Lean-formalized.

## Read the mathematics

- [Two-page note on the smaller witness](reduction/note.pdf)
- [Full research manuscript](permutation-disproof.md) (its original Lean plan predates the completed certificate below)
- [Original witness and complete rank sequences](permutation-certificate.json)
- [Smaller witness endpoints and complete rank sequence](reduction/literal-results.txt)

## Reproduce

Python 3, standard library only, from the repository root:

```sh
python3 verify_permutation.py
python3 independent_permutation.py
python3 verify_by_deletion.py
python3 verify_family.py
python3 reduction/check_algebra.py
python3 reduction/check_by_deletion.py
```

For the original finite witness, use the pinned Lean 4.36.0 toolchain:

```sh
cd lean
lake --wfail build
lake env lean Audit.lean
```

The [recorded build and axiom audit](lean-audit.txt) reports success, with theorems `PatternInterval.consecutive_rank_sizes` and `PatternInterval.disproof` depending only on `propext`, `Classical.choice`, and `Quot.sound`. See [Lean documentation](lean/README.md) for the proof structure and replay instructions.

## Research status

The finite Lean certificate applies to the length-50 witness only. The work has not undergone external peer review. The literature search reported in the manuscript found no earlier disproof as of November 25, 2026; priority remains provisional. AI (Astra/Codex) was used for discovery, mathematical reasoning, computation, and formalization. Review the manuscript and add accurate human attribution before public release.
