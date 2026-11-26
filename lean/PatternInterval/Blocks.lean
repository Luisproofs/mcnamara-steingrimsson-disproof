import PatternInterval.Order

namespace PatternInterval

/-- Every left position compares to every right position with the same sign. -/
def join (c : Bool) : Shape → Shape → Shape
  | [], b => b
  | r :: rs, b => (r ++ List.replicate b.length c) :: join c rs b

@[simp] theorem join_length (c : Bool) (a b : Shape) :
    (join c a b).length = a.length + b.length := by
  induction a <;> simp [join, *, Nat.succ_add]

@[simp] theorem join_nil (c : Bool) (a : Shape) : join c a [] = a := by
  induction a <;> simp [join, *]

theorem tri_join (c : Bool) {a b : Shape} (ha : Tri a) (hb : Tri b) :
    Tri (join c a b) := by
  induction a with
  | nil => exact hb
  | cons r rs ih =>
    exact ⟨by simp [ha.1], ih ha.2⟩

theorem restrict_length {m : List Bool} {a : Shape} (h : m.length = a.length) :
    (restrict m a).length = m.count true := by
  induction m generalizing a with
  | nil => simp [restrict]
  | cons b bs ih =>
    cases a with
    | nil => simp at h
    | cons r rs => cases b <;> simp_all [restrict]

theorem pick_append {α : Type} {m : List Bool} {xs : List α} (n : List Bool) (ys : List α)
    (h : m.length = xs.length) : pick (m++n) (xs++ys) = pick m xs ++ pick n ys := by
  induction m generalizing xs with
  | nil => cases xs <;> simp_all [pick]
  | cons b bs ih => cases xs <;> cases b <;> simp_all [pick]

theorem pick_const {m : List Bool} {n : Nat} (c : Bool) (h : m.length = n) :
    pick m (List.replicate n c) = List.replicate (m.count true) c := by
  subst n
  induction m with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [List.replicate_succ, pick, ih]

theorem restrict_join (c : Bool) {a b : Shape} {m n : List Bool}
    (ha : Tri a) (hm : m.length = a.length) (hn : n.length = b.length) :
    restrict (m++n) (join c a b) = join c (restrict m a) (restrict n b) := by
  induction a generalizing m with
  | nil => cases m <;> simp_all [join,restrict]
  | cons r rs ih =>
    cases m with
    | nil => simp at hm
    | cons bit bs =>
      have hs : bs.length = rs.length := by simpa using hm
      have hr : bs.length = r.length := hs.trans ha.1.symm
      cases bit
      · exact ih ha.2 hs
      · simp only [List.cons_append, join, restrict, ite_true]
        rw [pick_append _ _ hr,pick_const _ hn,restrict_length hn,ih ha.2 hs]

theorem occurs_join (c : Bool) (p a b : Shape) (ha : Tri a) :
    Occurs p (join c a b) ↔
    ∃ l r, Occurs l a ∧ Occurs r b ∧ p = join c l r := by
  constructor
  · rintro ⟨m,hm,rfl⟩
    rw [join_length] at hm
    have hl : (m.take a.length).length = a.length := by simp [hm]
    have hr : (m.drop a.length).length = b.length := by simp [hm]
    refine ⟨_,_,⟨_,hl,rfl⟩,⟨_,hr,rfl⟩,?_⟩
    rw [← restrict_join c ha hl hr,List.take_append_drop]
  · rintro ⟨_,_,⟨m,hm,rfl⟩,⟨n,hn,rfl⟩,rfl⟩
    exact ⟨m++n,by simp [hm,hn],restrict_join c ha hm hn⟩

end PatternInterval
