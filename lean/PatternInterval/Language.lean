import PatternInterval.Encoding

namespace PatternInterval

theorem fits_tail {b : Bool} {w u : Word} (h : Fits (b :: w) u) : Fits w u := by
  induction u with
  | nil => contradiction
  | cons a as ih =>
    rcases h with h | ⟨_,_,e,_,hv⟩
    · exact Or.inl (ih h)
    · cases e; exact Or.inl hv

theorem fits_cons (b a : Bool) (w as : Word) :
    Fits (b::w) (a::as) ↔ if b && !a then Fits (b::w) as else Fits w as := by
  cases b <;> cases a <;> simp [Fits,allowed] <;>
    exact fun h => fits_tail h

/-- All accepted words, together with the tails of those beginning with a double.
Each next letter uses its earliest available run. -/
def lang : Word → List Word × List Word
  | [] => ([[]], [])
  | a :: as =>
    let (all, old) := lang as
    let doubles := if a then all else old
    ([] :: (all.map (false :: ·) ++ doubles.map (true :: ·)), doubles)

theorem mem_lang (as : Word) :
    (∀ w, w ∈ (lang as).1 ↔ Fits w as) ∧
    (∀ w, w ∈ (lang as).2 ↔ Fits (true :: w) as) := by
  induction as with
  | nil => simp [lang,Fits]
  | cons a as ih =>
    constructor
    · intro w
      cases w with
      | nil => simp [lang,fits_nil]
      | cons b w => rw [fits_cons]; cases a <;> cases b <;> simp [lang,ih.1,ih.2]
    · intro w
      rw [fits_cons]
      cases a <;> simp [lang,ih.1,ih.2]

theorem nodup_map_on {α β : Type} (xs : List α) (f : α → β) (hx : xs.Nodup)
    (hi : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hx
    refine List.nodup_cons.mpr ⟨?_,ih ht (fun x h y k => hi x (by simp [h]) y (by simp [k]))⟩
    rintro h
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp h
    exact hn ((hi b (by simp [hb]) a (by simp) eq) ▸ hb)

theorem nodup_lang (as : Word) : (lang as).1.Nodup ∧ (lang as).2.Nodup := by
  induction as with
  | nil => simp [lang]
  | cons a as ih =>
    let y := if a then (lang as).1 else (lang as).2
    have hy : y.Nodup := by cases a <;> simp [y,ih.1,ih.2]
    have inject (b : Bool) (ws : List Word) (h : ws.Nodup) :
        (ws.map (b :: ·)).Nodup := nodup_map_on _ _ h (by simp)
    refine ⟨List.nodup_cons.mpr ⟨by simp,List.nodup_append.mpr ⟨inject _ _ ih.1,
      inject _ _ hy,?_⟩⟩,hy⟩
    simp

def pairs {α β : Type} (xs : List α) (ys : List β) :=
  xs.flatMap (fun a => ys.map (a,·))

@[simp] theorem mem_pairs {α β : Type} (p : α × β) (xs : List α) (ys : List β) :
    p ∈ pairs xs ys ↔ p.1 ∈ xs ∧ p.2 ∈ ys := by
  cases p
  simp [pairs]

theorem nodup_pairs {α β : Type} {xs : List α} {ys : List β}
    (hx : xs.Nodup) (hy : ys.Nodup) : (pairs xs ys).Nodup := by
  induction xs with
  | nil => simp [pairs]
  | cons a as ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hx
    change ((ys.map (a,·)) ++ pairs as ys).Nodup
    refine List.nodup_append.mpr ⟨nodup_map_on _ _ hy (by simp),ih ht,?_⟩
    simp
    grind

end PatternInterval
