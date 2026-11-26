# Nonunimodal intervals in the classical permutation pattern poset

## The conjecture and the counterexample

Peter R. W. McNamara and Einar Steingrímsson, *On the topology of the permutation pattern poset*, Journal of Combinatorial Theory, Series A **134** (2015), 1–35, state Conjecture 9.4 as follows.

> Every interval $[\sigma,\tau]$ in $\mathcal P$ is rank-unimodal.

Here containment means that a subsequence of the larger permutation has the relative order of the smaller. Each distinct permutation counts once. Intervals are closed, and the rank of $\pi$ in this interval is $|\pi|-|\sigma|$. The authors checked every interval with top length at most eight. [Original paper, §9.4](https://www.linux.bucknell.edu/~pm040/Papers/topology-perm-poset.pdf) · [Journal record](https://arxiv.org/abs/1305.5569)

For a word $u=(u_1,\ldots,u_r)$ of positive integers, write $P(u)$ for the permutation consisting of consecutive increasing runs of those lengths, with every value in each run larger than every value in later runs. For example, $P(1,2,1)=4231$. Write $\alpha\oplus\beta$ for concatenation after adding $|\alpha|$ to each entry of $\beta$. Write $D_r=r,r-1,\ldots,1$. In a capacity word, powers denote repetition by concatenation.

**Theorem 1.** A counterexample with top length 50 is
$$
u=(1^8,2,1^9),\qquad v=(2^4,(1,2)^5,2^4),\qquad
[\sigma,\tau]=[D_{18},\ P(u)\oplus P(v)].
$$

| Rank | Permutation length | Distinct permutations |
|---:|---:|---:|
| 19 | 37 | 78,468 |
| 20 | 38 | 78,022 |
| 21 | 39 | 78,544 |

The middle rank is strictly smaller than each neighbor. In a weakly unimodal sequence, a strict decrease forces all subsequent steps to be weak decreases. Thus the table disproves Conjecture 9.4. Both words have 18 runs. The two summands have lengths 19 and 31. Selecting one entry from every left run gives an occurrence of the bottom.

For a second counterexample, set $U=(1^{14},2)$ and $V=((1,1,2)^3,2^6)$. Take $\sigma=D_{60}$ and $\tau=P(U^4)\oplus P(V^4)$. The permutations of lengths 121, 122, and 123 number 318,760,232,883,761, then 314,759,367,160,492, then 318,217,445,359,443. These are interval ranks 61, 62, and 63. Each of $U,V$ has 15 entries. Their entries sum to 16 and 24 respectively, giving a top of length 160.

All the permutations in these intervals are separable. The top is built by direct and skew sums from singletons, and restricting such an expression to a subsequence gives another such expression after deleting empty factors. Moreover an increasing subsequence uses at most one run of each summand, with at most two entries per run. Every permutation in every displayed interval therefore avoids the increasing pattern 12345.

## Counting patterns without counting embeddings

Let $F_u(x)$ enumerate all distinct patterns in $P(u)$ by absolute length, including the empty permutation. Each pattern is uniquely $P(w)$ where $w$ is a word of positive selected run sizes. Its possible embeddings select an increasing sequence of run indices with capacities at least the corresponding sizes. This characterization follows because entries selected within a run increase and each change of retained run is a descent. The empty word gives the empty pattern.

The longest decreasing subsequence of $P(w)$ has length equal to the number of runs. Thus for a host of $r$ runs, its patterns containing $D_r$ must use every run. Call these patterns full. With $p_a=x+\cdots+x^a$, their enumerator is
$$
G_u(x)=\prod_{i=1}^r p_{u_i}(x).
$$
For $r\ge2$, each full pattern is directly indecomposable. Indeed the first entry exceeds the last, so no proper cut separates a prefix of smaller values from a suffix of larger values. More generally, every pattern of a side is empty, increasing, or directly indecomposable with at least two runs. A nonempty permutation has a unique list of directly indecomposable factors. Its proper factor boundaries are exactly the positions $j$ whose first $j$ values form the set $\{1,\ldots,j\}$.

**Lemma 2.** For any two positive words $u,v$ with the same number $r\ge2$ of runs, the absolute-length enumerator $H$ of the interval $[D_r,P(u)\oplus P(v)]$ is
$$
H=G_uF_v+F_uG_v-G_uG_v-G_{\min(u,v)}.\tag{1}
$$
Here the minimum is coordinatewise.

*Proof.* Every subsequence of the top splits as $\alpha\oplus\beta$ with $\alpha$ available on the left and $\beta$ on the right, either possibly empty. A decreasing subsequence lies on one side. The interval is the union of the class with a full left pattern and the class with a full right pattern.

In the left class, the first direct factor recovers the full left pattern, so each pair counted by $G_uF_v$ yields a distinct permutation. The analogous last-factor argument gives $F_uG_v$. An indecomposable member of their intersection occurs in both sides and is full in both. Its run sizes are bounded by their coordinatewise minimum, giving $G_{\min(u,v)}$. A decomposable member of the intersection has a full first factor and a full last factor. In a left-full representation the remaining suffix is a pattern in the right side. That suffix contains a descent in its last factor, so it is itself directly indecomposable by the preceding classification. Thus there are exactly two factors. Conversely every pair of full factors from the respective sides belongs to the intersection. This yields $G_uG_v$ and proves (1). $\square$

## An exact coefficient calculation

Write $W_k=(1^k,2)$ for $k\ge0$ and define
$$
d_k=\sum_{j=0}^k x^j,\qquad g_k=x^{k+1}(1+x),\qquad
v_k=g_k+\sum_{j=0}^{k-1}x^{j+2}.
$$
An empty sum is zero. A suffix $T$ is any word over $\{1,2\}$. Then
$$
F_{W_kT}=d_k+v_k F_T,\qquad G_{W_kT}=g_kG_T,\qquad F_{\varnothing}=G_{\varnothing}=1.\tag{2}
$$
For the first identity, embed each run word greedily at its earliest eligible positions. This succeeds for every embeddable word because moving any matched part earlier leaves all later positions available. A word that stops within the initial $k$ units is $1^j$, $0\le j\le k$. A word reaching the terminal capacity 2 consumes either $k$ units followed by a part 1 or 2, or $j<k$ units followed by a part 2. These disjoint choices have weights $d_k$, $g_k$, and $v_k-g_k$, respectively, with arbitrary continuation in $T$ in the latter two cases. The second identity is the full-run product.

For the length-50 witness in Theorem 1, put $T_k(f)=d_k+v_kf$. Its left side has only one run of capacity 2. A word containing a part 2 is uniquely $1^i,2,1^j$ with $0\le i\le8$, $0\le j\le9$. The other words consist of at most 18 units. Consequently
$$
F_u=d_{18}+x^2 d_8 d_9,\quad
F_v=(T_0^4\circ T_1^5\circ T_0^4)(1),\quad
G_u=x^{18}(1+x),\quad G_v=x^{18}(1+x)^{13}.
$$
At each of the three target lengths the split into two sides can be checked directly. An increasing contribution on either side supplies at most two entries, giving a total length at most $31+2=33$. Both contributions must therefore have a descent. Each is directly indecomposable, so the two-factor split is unique. A decreasing subsequence of length 18 occurs precisely when at least one factor uses all 18 runs on its side. Counting pairs with either factor full and subtracting pairs with both full gives the three product columns below. In (1), the ninth capacity of $v$ is 1, so $G_{\min(u,v)}=x^{18}$ also confirms that the one-factor intersection contributes zero here. The coefficient table can also be reproduced using the identity $(1-x-x^2)F_v=1-(x+x^2)x^{18}(1+x)^8(2+x)^5$, obtained by iterating (2). In particular its coefficients at degrees 18 through 21 are $4181,6733,10546,15327$.

| Absolute length | $[x^j]G_u F_v$ | $[x^j]F_u G_v$ | $[x^j]G_u G_v$ | Interval count |
|---:|---:|---:|---:|---:|
| 37 | 10,914 | 67,568 | 14 | 78,468 |
| 38 | 17,279 | 60,834 | 91 | 78,022 |
| 39 | 25,873 | 53,035 | 364 | 78,544 |

The last column is the sum of the first two coefficient columns less the third. This finishes the finite proof. It can also be checked by direct enumeration of all 1,125,373 interval elements from the actual one-line top permutation.

For the witness $u=U^4$, $v=V^4$, the exact polynomial instructions are
$$
F_u=T_{14}^{\,4}(1),\qquad
F_v=(T_2^{\,3}\circ T_0^{\,6})^{4}(1),\qquad
G_u=x^{60}(1+x)^4,\qquad G_v=x^{60}(1+x)^{36}.
$$
Powers of operators mean composition. Since $u\le v$ coordinatewise, the last term of (1) is $G_u$, of degree 64. Multiplying the given polynomials gives the following intermediate coefficients.

| Absolute length | $[x^j]G_uF_v$ | $[x^j]F_uG_v$ | $[x^j]G_uG_v$ | $[x^j]G_u$ |
|---:|---:|---:|---:|---:|
| 121 | 27,376,555,262,826 | 291,383,677,620,975 | 40 | 0 |
| 122 | 43,594,598,718,406 | 271,164,768,442,866 | 780 | 0 |
| 123 | 68,567,174,077,032 | 249,650,271,292,291 | 9,880 | 0 |

Column addition and subtraction as in (1) gives the three reported ranks of the length-160 example. The binomial entries in the fourth column also follow immediately from $G_uG_v=x^{120}(1+x)^{40}$.

## Why the construction works for infinitely many lengths

**Theorem 3.** For every integer $L\ge4$, the interval
$$
[D_{15L},\ P(U^L)\oplus P(V^L)]
$$
fails rank-unimodality. As $L$ grows, the size of the rank at absolute length $31L$ is exponentially small relative to some rank on each side of it. For $L=1,2,3$ the rank sequence is unimodal.

*Proof.* For a fixed word $W$ built from chunks $W_k$, write $g(W)$ and $v(W)$ for the products of their $g_k$ and $v_k$. Composing (2) across $W$ gives $F_{WT}=d(W)+v(W)F_T$ with $d(W)$ a nonnegative polynomial. Consequently
$$
F_{W^L}=v(W)^L+d(W)\sum_{i=0}^{L-1}v(W)^i,\qquad G_{W^L}=g(W)^L.
$$
Coefficientwise, $F_{W^L}$ dominates $v(W)^L$. Define $A=v(U)g(V)$ and $B=g(U)v(V)$. By the injections in Lemma 2 the interval polynomial $H_L$ coefficientwise dominates each of $A^L$ and $B^L$. It is bounded above coefficientwise by $F_{U^L}G_{V^L}+G_{U^L}F_{V^L}$.

For a nonzero polynomial $Q$ with nonnegative coefficients, let $m(Q)=Q'(1)/Q(1)$. This is the expected degree when coefficient mass is normalized at 1, and means add under multiplication. Each $g_k(1)=2$, $v_k(1)=k+2$, and
$$
m(g_k)=k+\tfrac32,\qquad m(g_k)-m(v_k)=\frac{k^2}{2(k+2)}.
$$
For $k>0$ the extra $k$ terms in $v_k$ have average degree $(k+3)/2$, giving the identity. The $k=0$ equality follows directly. For our two words, $g(U)(1)=2$, $g(V)(1)=2^9$, $v(U)(1)=16$ and $v(V)(1)=4^3 2^6$. Hence
$$
A(1)=B(1)=S=8192,\quad
m(g(U)g(V))=35,\quad m(A)=35-49/8=231/8,\quad m(B)=35-3/2=67/2.
$$

For explicit uniform bounds, put $R=x+x^2$. The identity $v_k-1=(R-1)d_k$, including $k=0$, telescopes (2) to
$$
(R-1)F_{W^L}=R\,v(W)^L-1.
$$
At a positive $x$ with $R(x)>1$, this gives $F_{W^L}(x)\le R(x)v(W)(x)^L/(R(x)-1)$. For a polynomial with nonnegative coefficients, its coefficient at degree $31L$ is at most its value at $x$ divided by $x^{31L}$. Apply this to the two injective classes separately with the following rational substitutions. Each bound follows by substituting the given $g_k$ and $v_k$ and clearing positive denominators.

| Class | $Q$ | $x$ | Upper bound for $R/(R-1)$ | Upper bound for $Q(x)/(8192 x^{31})$ |
|---|---|---:|---:|---:|
| $F_{U^L}G_{V^L}$ | $A$ | $11/10$ | $2$ | $9/10$ |
| $G_{U^L}F_{V^L}$ | $B$ | $4/5$ | $4$ | $9/10$ |

Hence $[x^{31L}]H_L\le6 S^L(9/10)^L$.

For $Q=A,B$, normalizing $Q^L$ at 1 gives the distribution of a sum of $L$ independent degrees drawn from $Q$. Using $Q''(1)/S+m(Q)-m(Q)^2$, the one-step variances for $A$ and $B$ are respectively $1399/64$ and $13/4$, both below 22. For $L\ge80$, Chebyshev's inequality puts more than half of each distribution within distance $L$ of its own mean $L m(Q)$, since the probability outside is at most $22/L$. The window for $A$ lies wholly below $31L$ and that for $B$ wholly above. Each has at most $2L+1$ integer degrees. Consequently $H_L$ has, on each side, a coefficient at least $S^L/(4L+2)$. This exceeds the central upper bound for every $L\ge80$. Indeed $6(4\cdot80+2)9^{80}<10^{80}$, and $(4L+2)(9/10)^L$ decreases for $L\ge80$. The ratio of the central count to each of these larger counts is at most $6(4L+2)(9/10)^L$.

For completeness the finite range can be checked by an integer recurrence. Write $a=g(U)$, $b=g(V)$. The coordinatewise comparison $U\le V$ gives
$$
(R-1)H_L
=R(A^L+B^L)-a^L-b^L-(R-1)((ab)^L+a^L).\tag{3}
$$
Start the five powers on the right at 1 and multiply by their respective fixed polynomials at each step. If $n_j$ is the coefficient on the right and $h_j=[x^j]H_L$, set $h_{-2}=h_{-1}=0$ and use $h_j=h_{j-1}+h_{j-2}-n_j$. Exact evaluation gives $h_{29L}>h_{31L}<h_{33L}$ for every $4\le L\le79$ and unimodality for $L=1,2,3$. The short verifier `verify_family.py` checks every one of these inequalities and the rational estimates above. This finishes the proof. $\square$

The decreasing bottom must live entirely on one side of a direct sum. Using every run on that side changes the distribution of typical lengths. The long stretch of unit capacities in $U$ makes that change larger than the three short stretches in $V$. The two classes have the same exponential growth in total size but concentrate at different lengths. The gap can therefore become arbitrarily pronounced even within separable permutations, with a decreasing bottom and at most two entries in each increasing run of either summand.

## Literature and priority audit

McNamara presented the conjecture at FPSAC 2014. The journal version states it as Conjecture 9.4. Vincent Vatter's 2026 open-problem survey again attributes the assertion to both authors as Conjecture 2.2. The survey distinguishes the principal-downset assertion (2.1) and the layered principal-downset assertion (2.6). Our bottom has positive length greater than one, so these principal cases remain separate questions. [Author's FPSAC slides](https://www.linux.bucknell.edu/~pm040/MySlides/fpsac14.pdf) · [Original article](https://doi.org/10.1016/j.jcta.2015.02.009) · [Vatter, §2 and updates](https://arxiv.org/pdf/2602.16355)

Elizalde and McNamara proved rank-unimodality in the consecutive pattern order, where an occurrence must occupy consecutive positions. Tyler B. Hughes's November 2026 work addresses Question 9.5 on the Sperner property in the classical order. Its displayed finite witness has rank sizes $1,3,7,7,1$, which are unimodal. The separate results clarify why rank sizes must be checked for ordinary, arbitrary-position subsequences. [Elizalde and McNamara](https://arxiv.org/abs/1508.05963) · [Hughes's result and rank table](https://mathdiscoveries.org/results/pattern-poset-not-sperner)

Searches through 25 November 2026 used the authors' names, both conjecture numbers, classical pattern intervals, nonunimodal rank sequences, separable permutations, generalized subword order, principal ideals, and indexed preprint and public research repositories. The benchmark repository yielded no matching published result. The available MathDB entry displayed zero solutions. The strongest evidence for prior open status is the recent specialist survey. I found no earlier disproof or theorem implying this counterexample. Indexing delays, private work and unpublished work limit the priority assessment. This work has received no external peer review. [MathDB problem record](https://mathdb.com/p/373198/mcnamara-steingrimsson-interval-rank-unimodality-conjecture) · [Benchmark catalogue](https://github.com/1337isnot1337/solved-conjectures) · [Vatter's survey](https://arxiv.org/abs/2602.16355)

## Independent verification and Lean 4 plan

Run the following in this directory using Python 3 with its standard library.

```sh
python3 verify_permutation.py
python3 independent_permutation.py
python3 verify_by_deletion.py
python3 verify_family.py
```

The first verifier computes (1) using the chunk recurrence. The second counts canonical direct factors by disjoint cases. A side's individual words are counted by greedy transitions on individual capacities, recording length and number of used runs. A permutation with one nontrivial direct factor alone is counted by a two-flag automaton tracking which full-side embeddings remain possible. Other permutations have a full factor with a nonempty increasing word on the opposite side, or two nontrivial factors with at least one full. The latter split into three disjoint combinations of full and non-full factors. This computation independently reproduces every rank of the stated interval. The second program also enumerates all subsequences of the actual top permutations and standardizes them for 145 small analogous intervals. For the length-50 witness, the third program begins at the literal top and repeatedly deletes a single entry, standardizes, deduplicates, and retains permutations containing the decreasing bottom. Every member occurs in this enumeration because its chosen occurrence can be kept while the other entries are deleted in any order. This verifies all 33 ranks using ordinary permutations throughout. The fourth program verifies the effective family theorem. The JSON certificate gives both endpoint pairs in one-line notation and both complete rank sequences.

For Lean 4, the finite counterexample suffices. The following order keeps the analytic family optional.

1. Represent each endpoint as a permutation of a finite ordinal and each occurrence by a strictly increasing index embedding preserving pairwise value comparisons. Define rank counts as cardinalities of distinct permutations of the given length.
2. Define the skew sum of increasing runs. Prove the characterization of containment by capacity-word embeddings, via the descents at run boundaries. Prove that containing $D_r$ in a side with $r$ runs forces all its runs to be used.
3. Prove uniqueness of direct factorization by prefix cuts, then formalize the two injective classes and their intersection in Lemma 2. Counting by length gives (1), which can equally be stated as an additive identity of natural-number polynomials.
4. Prove (2) by the first greedy match of the terminal capacity 2. Instantiate the finite words and evaluate the three coefficients by kernel-reduced arithmetic on coefficient lists. Close the conjecture's negation with the three-rank strict-valley lemma. The length-50 witness requires just three coefficient evaluations and two strict comparisons. The definitions and structural lemmas also apply to the length-160 witness.
5. Theorem 3 can be formalized separately using finite probability distributions, variance additivity, Chebyshev’s inequality, and rational evaluation of nonnegative polynomials. The classical finite disproof is already complete before this step.
