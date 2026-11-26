# Small Counterexamples to the McNamara–Steingrímsson Conjecture

An AI-assisted investigation of Conjecture 9.4 from [On the topology of the permutation pattern poset (2015)](https://arxiv.org/abs/1305.5569).

## Main result

The conjecture that every interval in the classical permutation pattern poset is rank-unimodal is false.

An explicit counterexample with bottom permutation length 18 and top permutation length 50 has three consecutive rank sizes:

**78,468 > 78,022 < 78,544**

A smaller counterexample with bottom length 15 and top length 38 gives:

**3,662 > 3,659 < 3,685**

The manuscript also establishes an infinite family of counterexamples with exponentially deep rank valleys.

## Formal verification

The length-50 counterexample is fully verified in Lean 4.36.0.

- No `sorry` or `admit`.
- No nonstandard axioms.
- No external Lean dependencies.
- Successful independent kernel replay.

Both formal theorems depend exclusively on `propext`, `Classical.choice`, and `Quot.sound`.

[Lean source](lean/) | [Verification audit](lean-audit.txt)

## Mathematical proofs

- [Full research manuscript](permutation-disproof.md)
- [Two-page proof of the smaller counterexample](reduction/note.pdf)
- [Explicit permutations and rank certificates](permutation-certificate.json)
- [Smaller counterexample endpoints and rank sequence](reduction/literal-results.txt)

## Reproduce the formal verification

From the repository root:

```sh
cd lean
lake --wfail build
lake env lean Audit.lean
```

## Independent construction and attribution

A disproof by aadrianvv was published on November 25, 2026, using a top permutation of length 109,118.

This project presents an alternative construction with a Lean-verified counterexample of length 50, a smaller counterexample of length 38, and an infinite family with exponentially deep rank valleys.

- [Disproof by aadrianvv](https://github.com/1337isnot1337/solved-conjectures/pull/651)
- [Mathematical proof and endpoint lengths](https://github.com/1337isnot1337/solved-conjectures/blob/main/results/mcnamara-steingrimsson-rank-unimodality/PROOF.md)
- [Associated Lean formalization](https://github.com/1337isnot1337/solved-conjectures/issues/658)

## Authorship

Research directed by Luis Gonzalez, using Astra 6.2 through OpenAI Codex for mathematical discovery, proof development, computational verification, and Lean 4 formalization.

Contact: [@100xluis on X](https://x.com/100xluis).

## Research status

The length-50 counterexample is machine-verified. The smaller counterexample and infinite-family theorem have conventional mathematical proofs and computational verification but are not yet Lean-formalized.

No claim of priority for the original disproof or global minimality of the counterexamples is made. The work has not undergone external peer review.
