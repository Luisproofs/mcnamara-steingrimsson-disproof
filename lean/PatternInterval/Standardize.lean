import PatternInterval.Language

namespace PatternInterval

/-- Reconstruct each entry's zero-based rank from comparisons to the other entries. -/
def readShape : Shape → List Nat
  | [] => []
  | row :: rs => row.count false ::
    List.zipWith (fun (b : Bool) (k : Nat) => k + (if b then 1 else 0)) row (readShape rs)

def smaller (xs : List Nat) (x : Nat) := xs.countP (fun y => decide (y < x))

theorem read_shape {xs : List Nat} (hx : xs.Nodup) :
    readShape (shape xs) = xs.map (smaller xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨hne,hn⟩ := List.nodup_cons.mp hx
    simp only [shape,readShape,List.map_cons,ih hn,List.zipWith_map,List.zipWith_self,List.cons.injEq]
    constructor
    · simp only [smaller,List.countP_cons,Nat.lt_irrefl,decide_false,
        List.count_eq_countP,List.countP_map]
      apply List.countP_congr
      intro y hy
      have ne : y ≠ x := by rintro rfl; exact hne hy
      simp
      omega
    · apply List.map_congr_left
      intro y _
      simp [smaller,List.countP_cons]

theorem smaller_mono (xs : List Nat) {x y : Nat} (h : x ≤ y) :
    smaller xs x ≤ smaller xs y := by
  apply List.countP_mono_left
  intro z _ hz
  exact decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true hz) h)

theorem smaller_strict {xs : List Nat} {x y : Nat} (hx : x ∈ xs) (h : x < y) :
    smaller xs x < smaller xs y := by
  obtain ⟨as,bs,rfl⟩ := List.append_of_mem hx
  have ha := smaller_mono as (Nat.le_of_lt h)
  have hb := smaller_mono bs (Nat.le_of_lt h)
  simp [smaller,List.countP_append,h] at *
  omega

theorem smaller_iff {xs : List Nat} {x y : Nat} (hx : x ∈ xs) :
    smaller xs x < smaller xs y ↔ x < y := by
  constructor
  · intro h
    by_cases hxy : x < y
    · exact hxy
    · have := smaller_mono xs (Nat.le_of_not_gt hxy)
      omega
  · exact smaller_strict hx

theorem smaller_bound {xs : List Nat} {x : Nat} (hx : x ∈ xs) : smaller xs x < xs.length := by
  have h : smaller xs x ≤ xs.length := List.countP_le_length
  have ne : smaller xs x ≠ xs.length := by
    intro e
    have := List.countP_eq_length.mp e x hx
    simp at this
  omega

theorem shape_map_on (f : Nat → Nat) (xs : List Nat)
    (hf : ∀ x ∈ xs, ∀ y ∈ xs, f x < f y ↔ x < y) : shape (xs.map f) = shape xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,shape,List.map_map,List.cons.injEq]
    constructor
    · apply List.map_congr_left
      intro y hy
      simp [hf x (by simp) y (by simp [hy])]
    · exact ih (fun a ha b hb => hf a (by simp [ha]) b (by simp [hb]))

theorem standard_perm {xs : List Nat} (hx : xs.Nodup) :
    IsPermutation (xs.map (smaller xs)) := by
  let ys := xs.map (smaller xs)
  have len : ys.length = xs.length := List.length_map _
  have hn : ys.Nodup := nodup_map_on _ _ hx (by
    intro x hx' y hy' eq
    have a := smaller_iff (y:=y) hx'
    have b := smaller_iff (y:=x) hy'
    omega)
  have sub : ys ⊆ List.range ys.length := by
    intro y hy
    obtain ⟨x,hm,rfl⟩ := List.mem_map.mp hy
    exact List.mem_range.mpr (len.symm ▸ smaller_bound hm)
  refine (List.perm_ext_iff_of_nodup hn List.nodup_range).2 (fun x => ⟨fun hx => sub hx, ?_⟩)
  intro hm
  by_cases he : x ∈ ys
  · exact he
  · have hnod : (x::ys).Nodup := List.nodup_cons.mpr ⟨he,hn⟩
    have hsub : x::ys ⊆ List.range ys.length := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hm
      · exact sub hy
    have := hnod.length_le_of_subset hsub
    simp at this
    omega

theorem smaller_range (n x : Nat) : smaller (List.range n) x = min n x := by
  induction n with
  | zero => simp [smaller]
  | succ n ih =>
    simp only [List.range_succ,smaller,List.countP_append,List.countP_cons,List.countP_nil,
      Nat.zero_add,decide_eq_true_eq] at ih ⊢
    split <;> omega

theorem read_perm {xs : List Nat} (hx : IsPermutation xs) : readShape (shape xs) = xs := by
  rw [read_shape (hx.nodup_iff.mpr List.nodup_range)]
  conv => rhs; rw [← List.map_id xs]
  apply List.map_congr_left
  intro x hm
  have h := List.mem_range.mp (hx.subset hm)
  exact (hx.countP_eq _).trans ((smaller_range _ _).trans (Nat.min_eq_right (Nat.le_of_lt h)))

theorem realize {b : List Nat} (hb : IsPermutation b) {p : Shape} (h : Occurs p (shape b)) :
    IsPermutation (readShape p) ∧ shape (readShape p) = p := by
  obtain ⟨ys,hs,rfl⟩ := (occurs_shape_iff _ _).1 h
  have hn := hs.nodup (hb.nodup_iff.mpr List.nodup_range)
  rw [read_shape hn]
  exact ⟨standard_perm hn,shape_map_on _ _ (fun _ hx _ _ => smaller_iff hx)⟩

theorem card_one_line {a b : List Nat} (hb : IsPermutation b) {i n : Nat}
    (h : HasCard (Level (shape a) (shape b) i) n) : HasCard (RankLevel a b i) n := by
  obtain ⟨ls,hd,hm,hl⟩ := h
  have valid (x : Shape) (hx : x ∈ ls) := realize hb ((hm x).1 hx).2.1
  refine ⟨ls.map readShape,nodup_map_on _ _ hd ?_,?_,by simpa using hl⟩
  · intro x hx y hy eq
    exact (valid x hx).2.symm.trans ((congrArg shape eq).trans (valid y hy).2)
  · intro w
    constructor
    · intro hw
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hw
      obtain ⟨hp,he⟩ := valid x hx
      obtain ⟨low,high,len⟩ := (hm x).1 hx
      rw [← he] at low high len
      exact ⟨hp,(occurs_shape_iff ..).1 low,(occurs_shape_iff ..).1 high,by simpa using len⟩
    · rintro ⟨hp,low,high,len⟩
      exact List.mem_map.mpr ⟨shape w,(hm _).2 ⟨(occurs_shape_iff ..).2 low,
        (occurs_shape_iff ..).2 high,by simpa using len⟩,read_perm hp⟩

end PatternInterval
