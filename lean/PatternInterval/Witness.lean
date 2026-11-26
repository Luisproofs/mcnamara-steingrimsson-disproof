import PatternInterval.Counting

namespace PatternInterval

@[simp] theorem down_length (n : Nat) : (down n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [down,side_length] at ih ⊢
    simp [List.replicate_succ,weight,ih,size,Nat.add_comm]

@[simp] theorem pair_length (u v : Word) : (pairShape u v).length = weight u + weight v := by
  simp [pairShape]

/-- At these levels at least two entries come from the right, so the pair
encoding is uniquely recoverable from the actual comparison triangle. -/
theorem level_card (u v : Word) (d i : Nat) (h : weight u + 2 ≤ d + i) :
    HasCard (Level (down d) (pairShape u v) i) (count u v d (d+i)) := by
  let xs := choices u v d (d+i)
  let render (x : Word × Word) := pairShape x.1 x.2
  have rightBound (x : Word × Word) (hx : x ∈ xs) : 2 ≤ weight x.2 := by
    obtain ⟨hl,_,_,hs⟩ := (choices_mem ..).1 hx
    have hw := fits_weight hl
    omega
  refine ⟨xs.map render,nodup_map_on _ _ (choices_nodup ..) ?_,?_,?_⟩
  · intro a ha b hb eq
    exact pair_inj (rightBound _ ha) (rightBound _ hb) eq
  · intro p
    constructor
    · rintro hmem
      obtain ⟨⟨a,b⟩,hw,rfl⟩ := List.mem_map.mp hmem
      obtain ⟨ha,hb,hd,hn⟩ := (choices_mem ..).1 hw
      exact ⟨(down_occurs_pair ..).2 hd, (occurs_pair ..).2 ⟨_,_,ha,hb,rfl⟩,
        by simpa [render] using hn⟩
    · rintro ⟨hb,ht,hn⟩
      obtain ⟨a,b,ha,hb',rfl⟩ := (occurs_pair ..).1 ht
      refine List.mem_map.mpr ⟨(a,b),(choices_mem ..).2 ⟨ha,hb',(down_occurs_pair ..).1 hb,?_⟩,rfl⟩
      simpa using hn
  · simpa [xs] using choices_length u v d (d+i)

def leftCaps : Word := List.replicate 8 false ++ [true] ++ List.replicate 9 false

def rightCaps : Word := List.replicate 4 true ++
  (List.replicate 5 [false,true]).flatten ++ List.replicate 4 true

def bottom : List Nat := (List.range 18).reverse

/-- The original one-line witness, translated to zero-based values. -/
def top : List Nat := [19,18,17,16,15,14,13,12,10,11,9,8,7,6,5,4,3,2,1,
  49,50,47,48,45,46,43,44,42,40,41,39,37,38,36,34,35,33,31,32,30,28,29,
  26,27,24,25,22,23,20,21].map (· - 1)

theorem bottom_perm : IsPermutation bottom := List.reverse_perm _
theorem top_perm : IsPermutation top := by
  unfold IsPermutation
  decide

theorem bottom_shape : shape bottom = down 18 := by decide
theorem top_shape : shape top = pairShape leftCaps rightCaps := by decide

theorem endpoints_comparable : Occurs (shape bottom) (shape top) := by
  rw [bottom_shape,top_shape,down_occurs_pair]
  exact Or.inl (by decide)

end PatternInterval
