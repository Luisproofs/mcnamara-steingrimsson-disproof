import Std

namespace PatternInterval

/-- One row per position, recording its strict comparison with each later value. -/
abbrev Shape := List (List Bool)

def shape : List Nat → Shape
  | [] => []
  | x :: xs => xs.map (fun y => decide (x < y)) :: shape xs

@[simp] theorem length_shape (xs : List Nat) : (shape xs).length = xs.length := by
  induction xs <;> simp [shape, *]

def pick {α : Type} : List Bool → List α → List α
  | b :: bs, a :: as => if b then a :: pick bs as else pick bs as
  | _, _ => []

def restrict : List Bool → Shape → Shape
  | b :: bs, r :: rs =>
    if b then pick bs r :: restrict bs rs else restrict bs rs
  | _, _ => []

def Occurs (p t : Shape) : Prop :=
  ∃ m : List Bool, m.length = t.length ∧ restrict m t = p

def Tri : Shape → Prop
  | [] => True
  | r :: rs => r.length = rs.length ∧ Tri rs

@[simp] theorem tri_shape (xs : List Nat) : Tri (shape xs) := by
  induction xs <;> simp [shape, Tri, *]

theorem pick_map {α β : Type} (f : α → β) (m : List Bool) (xs : List α) :
    pick m (xs.map f) = (pick m xs).map f := by
  induction m generalizing xs with
  | nil => simp [pick]
  | cons b bs ih => cases xs <;> cases b <;> simp [pick, ih]

theorem restrict_shape (m : List Bool) (xs : List Nat) :
    restrict m (shape xs) = shape (pick m xs) := by
  induction m generalizing xs with
  | nil => rfl
  | cons b bs ih => cases xs <;> cases b <;> simp [shape, pick, restrict, ih, pick_map]

theorem pick_sublist {α : Type} (m : List Bool) (ys : List α) :
    (pick m ys).Sublist ys := by
  induction m generalizing ys with
  | nil => exact List.nil_sublist _
  | cons b bs ih =>
    cases ys with
    | nil => exact .slnil
    | cons y ys => cases b
                   · exact (ih ys).cons _
                   · exact (ih ys).cons_cons _

theorem mask_of_sublist {α : Type} {xs ys : List α} (h : xs.Sublist ys) :
    ∃ m : List Bool, m.length = ys.length ∧ pick m ys = xs := by
  induction h with
  | slnil => exact ⟨[],rfl,rfl⟩
  | cons a _ ih =>
    obtain ⟨m,hl,hm⟩ := ih
    exact ⟨false :: m, by simp [hl], hm⟩
  | cons_cons a _ ih =>
    obtain ⟨m,hl,hm⟩ := ih
    exact ⟨true :: m, by simp [hl], by simp [pick, hm]⟩

/-- Classical containment is subsequence selection preserving all pairwise comparisons. -/
theorem occurs_shape_iff (p : Shape) (xs : List Nat) :
    Occurs p (shape xs) ↔ ∃ ys, ys.Sublist xs ∧ shape ys = p := by
  constructor
  · rintro ⟨m, _, hm⟩
    exact ⟨_, pick_sublist m xs, (restrict_shape m xs).symm.trans hm⟩
  · rintro ⟨ys, hs, rfl⟩
    obtain ⟨m, hl, hm⟩ := mask_of_sublist hs
    exact ⟨m, by simpa using hl, by rw [restrict_shape, hm]⟩

/-- Zero-based one-line permutations of arbitrary finite length. -/
def IsPermutation (xs : List Nat) : Prop := xs.Perm (List.range xs.length)

/-- Extensional cardinality of a finite collection; each member occurs once. -/
def HasCard {α : Type} (P : α → Prop) (n : Nat) : Prop :=
  ∃ xs : List α, xs.Nodup ∧ (∀ x, x ∈ xs ↔ P x) ∧ xs.length = n

theorem card_unique {α : Type} {P : α → Prop} {i j : Nat}
    (h : HasCard P i) (k : HasCard P j) : i = j := by
  obtain ⟨xs, hx, hp, rfl⟩ := h
  obtain ⟨ys, hy, hq, rfl⟩ := k
  exact ((List.perm_ext_iff_of_nodup hx hy).2 (fun x => (hp x).trans (hq x).symm)).length_eq

def Level (lo hi : Shape) (rank : Nat) (p : Shape) : Prop :=
  Occurs lo p ∧ Occurs p hi ∧ p.length = lo.length + rank

def Unimodal (f : Nat → Nat) (height : Nat) : Prop :=
  ∃ peak ≤ height,
    (∀ i, i < peak → f i ≤ f (i+1)) ∧
    (∀ i, peak ≤ i → i < height → f (i+1) ≤ f i)

/-- Some subsequence of the host has precisely the pairwise order of the pattern. -/
def PatternLE (a b : List Nat) : Prop :=
  ∃ s, s.Sublist b ∧ shape s = shape a

/-- Distinct standardized one-line permutations in a closed interval at relative rank i. -/
def RankLevel (a b : List Nat) (i : Nat) (p : List Nat) : Prop :=
  IsPermutation p ∧ PatternLE a p ∧ PatternLE p b ∧ p.length = a.length + i

/-- The authors take the union of the symmetric groups of strictly positive degree. -/
def InPatternPoset (xs : List Nat) : Prop := 0 < xs.length ∧ IsPermutation xs

/-- McNamara and Steingrímsson, JCTA 134 (2015), Conjecture 9.4. -/
def IntervalRankUnimodality : Prop :=
  ∀ a b : List Nat, InPatternPoset a → InPatternPoset b → PatternLE a b →
    ∃ f : Nat → Nat,
      (∀ i, i ≤ b.length - a.length → HasCard (RankLevel a b i) (f i)) ∧
      Unimodal f (b.length - a.length)

end PatternInterval
