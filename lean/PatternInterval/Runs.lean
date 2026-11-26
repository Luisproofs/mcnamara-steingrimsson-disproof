import PatternInterval.Blocks

namespace PatternInterval

abbrev Word := List Bool

/-- A false letter is a singleton increasing run and a true letter an increasing pair. -/
def block : Bool → Shape
  | false => [[]]
  | true => [[true],[]]

def allowed (b a : Bool) : Prop := b = false ∨ a = true

def side : Word → Shape
  | [] => []
  | a :: as => join false (block a) (side as)

def size (b : Bool) : Nat := if b then 2 else 1

def weight : Word → Nat
  | [] => 0
  | a :: as => size a + weight as

@[simp] theorem block_length (a : Bool) : (block a).length = size a := by cases a <;> rfl
@[simp] theorem side_length (w : Word) : (side w).length = weight w := by
  induction w <;> simp [side,weight, *]

theorem tri_block (a : Bool) : Tri (block a) := by cases a <;> simp [block, Tri]
theorem tri_side (w : Word) : Tri (side w) := by
  induction w with
  | nil => trivial
  | cons a _ ih => exact tri_join _ (tri_block a) ih

def Fits (w : Word) : Word → Prop
  | [] => w = []
  | a :: as => Fits w as ∨ ∃ b v, w = b :: v ∧ allowed b a ∧ Fits v as

theorem fits_nil (u : Word) : Fits [] u := by
  induction u with
  | nil => rfl
  | cons _ _ ih => exact Or.inl ih

theorem fits_length {w u : Word} (h : Fits w u) : w.length ≤ u.length := by
  induction u generalizing w with
  | nil => change w=[] at h; simp [h]
  | cons a as ih =>
    rcases h with h | ⟨b,v,rfl,_,h⟩
    · exact Nat.le_succ_of_le (ih h)
    · exact Nat.succ_le_succ (ih h)

theorem fits_weight {w u : Word} (h : Fits w u) : weight w ≤ weight u := by
  induction u generalizing w with
  | nil => change w=[] at h; simp [h,weight]
  | cons a as ih =>
    rcases h with h | ⟨b,v,rfl,hab,h⟩
    · exact Nat.le_add_left_of_le (ih h)
    · have hs : size b ≤ size a := by cases a <;> cases b <;> simp_all [size,allowed]
      exact Nat.add_le_add hs (ih h)

private def masks : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (masks n).map (false :: ·) ++ (masks n).map (true :: ·)

private theorem mem_masks (m : List Bool) (n : Nat) : m ∈ masks n ↔ m.length = n := by
  induction n generalizing m with
  | zero => simp [masks]
  | succ n ih => cases m with
    | nil => simp [masks]
    | cons a as => cases a <;> simp [masks,ih]

private theorem occurs_mem (p t : Shape) :
    Occurs p t ↔ p ∈ (masks t.length).map (fun m => restrict m t) := by
  simp [Occurs,mem_masks]

theorem occurs_block (p : Shape) (a : Bool) :
    Occurs p (block a) ↔ p = [] ∨ ∃ b, allowed b a ∧ p = block b := by
  rw [occurs_mem]
  cases a <;> simp [masks,block,restrict,pick,allowed,Bool.exists_bool]

theorem occurs_empty (p : Shape) : Occurs p [] ↔ p = [] := by
  simp [occurs_mem,masks,restrict]

theorem occurs_side (p : Shape) (u : Word) :
    Occurs p (side u) ↔ ∃ w, Fits w u ∧ p = side w := by
  induction u generalizing p with
  | nil => simp [side,occurs_empty,Fits]
  | cons a as ih =>
    rw [side,occurs_join _ _ _ _ (tri_block a)]
    constructor
    · rintro ⟨l,r,hl,hr,rfl⟩
      obtain ⟨v,hv,rfl⟩ := (ih _).1 hr
      rcases (occurs_block _ _).1 hl with rfl | ⟨b,hab,rfl⟩
      · exact ⟨v,Or.inl hv,rfl⟩
      · exact ⟨b::v,Or.inr ⟨_,_,rfl,hab,hv⟩,rfl⟩
    · rintro ⟨w,hw,rfl⟩
      rcases hw with h | ⟨b,v,rfl,hab,hv⟩
      · exact ⟨[],_,(occurs_block _ _).2 (Or.inl rfl),(ih _).2 ⟨_,h,rfl⟩,rfl⟩
      · exact ⟨_,_,(occurs_block _ _).2 (Or.inr ⟨b,hab,rfl⟩),(ih _).2 ⟨_,hv,rfl⟩,rfl⟩

def pairShape (l r : Word) := join true (side l) (side r)

theorem occurs_pair (p : Shape) (u v : Word) : Occurs p (pairShape u v) ↔
    ∃ l r, Fits l u ∧ Fits r v ∧ p = pairShape l r := by
  rw [pairShape,occurs_join _ _ _ _ (tri_side u)]
  constructor
  · rintro ⟨s,t,hs,ht,rfl⟩
    obtain ⟨l,hl,rfl⟩ := (occurs_side _ _).1 hs
    obtain ⟨r,hr,rfl⟩ := (occurs_side _ _).1 ht
    exact ⟨_,_,hl,hr,rfl⟩
  · rintro ⟨l,r,hl,hr,rfl⟩
    exact ⟨_,_,(occurs_side _ _).2 ⟨_,hl,rfl⟩,(occurs_side _ _).2 ⟨_,hr,rfl⟩,rfl⟩

end PatternInterval
