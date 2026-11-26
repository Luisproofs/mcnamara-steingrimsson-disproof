import PatternInterval.Runs

namespace PatternInterval

/-- Number of larger entries to the right at each position. -/
def digits (p : Shape) := p.map (List.count true)

theorem digits_join (c : Bool) (s t : Shape) : digits (join c s t) =
    (digits s).map (fun d => d + (if c then t.length else 0)) ++ digits t := by
  induction s with
  | nil => rfl
  | cons row rs ih =>
    cases c <;> simp [join,digits,List.count_replicate] at ih ⊢ <;> exact ih

def letters : Word → List Nat
  | [] => []
  | false :: w => 0 :: letters w
  | true :: w => 1 :: 0 :: letters w

theorem digits_side (w : Word) : digits (side w) = letters w := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [side,digits_join,ih]; cases a <;> rfl

theorem letters_inj {u v : Word} (h : letters u = letters v) : u = v := by
  induction u generalizing v with
  | nil => cases v with
    | nil => rfl
    | cons b v => cases b <;> simp [letters] at h
  | cons a u ih =>
    cases v with
    | nil => cases a <;> simp [letters] at h
    | cons b v => cases a <;> cases b <;> simp [letters] at h ⊢ <;> exact ih h

theorem side_inj {u v : Word} (h : side u = side v) : u = v :=
  letters_inj ((digits_side u).symm.trans ((congrArg digits h).trans (digits_side v)))

@[simp] theorem small_letters (w : Word) : (letters w).filter (· ≤ 1) = letters w := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [letters,ih]

theorem no_small (xs : List Nat) (n : Nat) (hn : 2 ≤ n) :
    (xs.map (· + n)).filter (· ≤ 1) = [] := by
  induction xs with
  | nil => rfl
  | cons d ds ih =>
    have h : ¬d+n ≤ 1 := by omega
    simp [h,ih]

theorem digits_pair (l r : Word) : digits (pairShape l r) =
    (letters l).map (· + weight r) ++ letters r := by
  simp [pairShape,digits_join,digits_side]

theorem pair_inj {l r a b : Word} (hr : 2 ≤ weight r) (hb : 2 ≤ weight b)
    (h : pairShape l r = pairShape a b) : (l,r) = (a,b) := by
  have e := congrArg digits h
  simp only [digits_pair] at e
  have f := congrArg (List.filter (fun n : Nat => decide (n ≤ 1))) e
  simp [no_small _ _ hr,no_small _ _ hb] at f
  obtain rfl := letters_inj f
  have g := List.append_cancel_right e
  have hh := (List.map_inj_right (f := (· + weight r)) (by intros; omega)).mp g
  rw [letters_inj hh]

def down (k : Nat) := side (List.replicate k false)

theorem letters_down (k : Nat) :
    letters (List.replicate k false) = List.replicate k 0 := by
  induction k <;> simp [List.replicate_succ,letters, *]

theorem fits_down (n : Nat) (w : Word) :
    Fits (List.replicate n false) w ↔ n ≤ w.length := by
  constructor
  · intro h; simpa using fits_length h
  · induction w generalizing n with
    | nil => intro h; have : n=0 := by simpa using h
             subst n; rfl
    | cons a w ih =>
      cases n with
      | zero => intro; exact fits_nil _
      | succ n =>
        intro h
        exact Or.inr ⟨false,_,List.replicate_succ,Or.inl rfl,ih _ (by simpa using h)⟩

theorem down_cannot_cross (n : Nat) {l r : Word} (h : down n = pairShape l r) :
    l = [] ∨ r = [] := by
  cases l with
  | nil => exact Or.inl rfl
  | cons a l =>
    cases r with
    | nil => exact Or.inr rfl
    | cons b r =>
      have e := congrArg (fun s => (digits s).head?) h
      change (digits (side (List.replicate n false))).head? = _ at e
      rw [digits_side,letters_down] at e
      cases n <;> cases a <;> cases b <;>
        simp [digits_pair,letters,weight,size,List.replicate_succ] at e <;> omega

theorem down_occurs_pair (n : Nat) (u v : Word) :
    Occurs (down n) (pairShape u v) ↔ n ≤ u.length ∨ n ≤ v.length := by
  rw [occurs_pair]
  constructor
  · rintro ⟨l,r,hl,hr,h⟩
    rcases down_cannot_cross n h with rfl | rfl
    · have eq : List.replicate n false = r := side_inj h
      exact Or.inr ((fits_down n v).1 (eq ▸ hr))
    · simp [pairShape,side,down] at h
      have eq := side_inj h
      exact Or.inl ((fits_down n u).1 (eq ▸ hl))
  · rintro (h|h)
    · exact ⟨_,[],(fits_down _ _).2 h,fits_nil _,by simp [down,pairShape,side]⟩
    · exact ⟨[],_,fits_nil _,(fits_down _ _).2 h,rfl⟩

end PatternInterval
