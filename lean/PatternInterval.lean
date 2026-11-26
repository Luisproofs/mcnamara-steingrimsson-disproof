import PatternInterval.Witness
import PatternInterval.Standardize

namespace PatternInterval

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem counts :
    count leftCaps rightCaps 18 37 = 78468 ∧
    count leftCaps rightCaps 18 38 = 78022 ∧
    count leftCaps rightCaps 18 39 = 78544 := by decide +kernel

/-- Cardinalities of three consecutive levels of the actual classical interval. -/
private theorem shape_rank_sizes :
    HasCard (Level (shape bottom) (shape top) 19) 78468 ∧
    HasCard (Level (shape bottom) (shape top) 20) 78022 ∧
    HasCard (Level (shape bottom) (shape top) 21) 78544 := by
  rw [bottom_shape,top_shape,← counts.1,← counts.2.1,← counts.2.2]
  exact ⟨level_card _ _ 18 19 (by decide), level_card _ _ 18 20 (by decide),
    level_card _ _ 18 21 (by decide)⟩

/-- Exact cardinalities, counting distinct ordinary one-line permutations. -/
theorem consecutive_rank_sizes :
    HasCard (RankLevel bottom top 19) 78468 ∧
    HasCard (RankLevel bottom top 20) 78022 ∧
    HasCard (RankLevel bottom top 21) 78544 :=
  ⟨card_one_line top_perm shape_rank_sizes.1,
   card_one_line top_perm shape_rank_sizes.2.1,
   card_one_line top_perm shape_rank_sizes.2.2⟩

/-- Negation of the published universal rank-unimodality conjecture. -/
theorem disproof : ¬ IntervalRankUnimodality := by
  intro conjecture
  obtain ⟨f,hf,peak,hp,hinc,hdec⟩ :=
    conjecture bottom top ⟨by decide, bottom_perm⟩ ⟨by decide, top_perm⟩
      ((occurs_shape_iff ..).1 endpoints_comparable)
  have a := card_unique (hf 19 (by decide)) consecutive_rank_sizes.1
  have b := card_unique (hf 20 (by decide)) consecutive_rank_sizes.2.1
  have c := card_unique (hf 21 (by decide)) consecutive_rank_sizes.2.2
  by_cases h : 19 < peak
  · have step := hinc 19 h
    change f 19 ≤ f 20 at step
    omega
  · have step := hdec 20 (by omega) (by decide)
    change f 21 ≤ f 20 at step
    omega

end PatternInterval
