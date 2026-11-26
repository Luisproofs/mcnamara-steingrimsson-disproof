import PatternInterval.Language

namespace PatternInterval

/-- A bin records (number of runs, number of entries) and a multiplicity. -/
abbrev Key := Nat × Nat
abbrev Bin := Key × Nat
abbrev Table := List Bin

def stat (w : Word) : Key := (w.length,weight w)
def shift (a : Bool) (k : Key) : Key := (k.1+1,size a + k.2)

def total {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a::as => f a + total f as

theorem total_append {α : Type} (f : α → Nat) (xs ys : List α) :
    total f (xs++ys) = total f xs + total f ys := by
  induction xs <;> simp [total, *, Nat.add_assoc]

theorem total_map {α β : Type} (f : β → Nat) (g : α → β) (xs : List α) :
    total f (xs.map g) = total (fun x => f (g x)) xs := by
  induction xs <;> simp [total, *]

def mass (t : Table) (f : Key → Nat) := total (fun (p : Bin) => p.2 * f p.1) t

def addBin (p : Bin) : Table → Table
  | [] => [p]
  | q::qs => if p.1 = q.1 then (p.1,p.2+q.2)::qs else q :: addBin p qs

def merge (xs ys : Table) := xs.foldr addBin ys

theorem mass_addBin (p : Bin) (ys : Table) (f : Key → Nat) :
    mass (addBin p ys) f = p.2 * f p.1 + mass ys f := by
  induction ys with
  | nil => simp [addBin,mass,total]
  | cons q qs ih =>
    by_cases h : p.1=q.1
    · simp [addBin,h,mass,total,Nat.add_mul,Nat.add_assoc]
    · simp [addBin,h,mass,total] at ih ⊢
      omega

theorem mass_merge (xs ys : Table) (f : Key → Nat) :
    mass (merge xs ys) f = mass xs f + mass ys f := by
  induction xs with
  | nil => simp [merge,mass,total]
  | cons p ps ih =>
    change mass (addBin p (merge ps ys)) f = _
    rw [mass_addBin, ih]
    simp [mass,total,Nat.add_assoc]

def lifted (b : Bool) (t : Table) : Table := t.map (fun (k,m) => (shift b k,m))

theorem mass_lifted (b : Bool) (t : Table) (f : Key → Nat) :
    mass (lifted b t) f = mass t (fun k => f (shift b k)) := by
  simp [mass,lifted,total_map]

def histogram : Word → Table × Table
  | [] => ([((0,0),1)], [])
  | a::as =>
    let (all,old) := histogram as
    let doubles := if a then all else old
    (((0,0),1) :: merge (lifted false all) (lifted true doubles), doubles)

theorem histogram_correct (u : Word) :
    (∀ f, total (fun w => f (stat w)) (lang u).1 = mass (histogram u).1 f) ∧
    (∀ f, total (fun w => f (stat w)) (lang u).2 = mass (histogram u).2 f) := by
  induction u with
  | nil => simp [histogram,lang,mass,total,stat,weight]
  | cons a as ih =>
    have first (b : Bool) (ws : List Word) (f : Key → Nat) :
        total (fun w => f (stat w)) (ws.map (b :: ·)) =
        total (fun w => f (shift b (stat w))) ws := total_map _ _ _
    have consMass (t : Table) (f : Key → Nat) :
        mass (((0,0),1)::t) f = f (0,0) + mass t f := by simp [mass,total]
    cases a <;> constructor <;> intro f <;>
      simp only [lang,histogram,Bool.false_eq_true,ite_false,ite_true,total,
        total_append,first,consMass,mass_merge,mass_lifted,ih.1,ih.2] <;>
      simp only [ih.1 (fun k => f (shift false k)),ih.1 (fun k => f (shift true k)),
        ih.2 (fun k => f (shift true k))] <;> rfl

def accepts (d n : Nat) (a b : Key) : Bool :=
  decide ((d ≤ a.1 ∨ d ≤ b.1) ∧ a.2 + b.2 = n)

def choices (u v : Word) (d n : Nat) : List (Word × Word) :=
  (pairs (lang u).1 (lang v).1).filter (fun (l,r) => accepts d n (stat l) (stat r))

theorem choices_mem (u v : Word) (d n : Nat) (p : Word × Word) :
    p ∈ choices u v d n ↔ Fits p.1 u ∧ Fits p.2 v ∧
      (d ≤ p.1.length ∨ d ≤ p.2.length) ∧ weight p.1 + weight p.2 = n := by
  cases p
  simp [choices,accepts,stat,(mem_lang u).1,(mem_lang v).1,and_assoc]
  intros; exact decide_eq_true_iff

theorem choices_nodup (u v : Word) (d n : Nat) : (choices u v d n).Nodup :=
  (nodup_pairs (nodup_lang u).1 (nodup_lang v).1).filter _

theorem length_filter_total {α : Type} (q : α → Bool) (xs : List α) :
    (xs.filter q).length = total (fun x => if q x then 1 else 0) xs := by
  induction xs with
  | nil => rfl
  | cons a as ih => cases h : q a <;> simp [h,total,ih,Nat.add_comm]

theorem total_pairs {α β : Type} (f : α × β → Nat) (xs : List α) (ys : List β) :
    total f (pairs xs ys) = total (fun a => total (fun b => f (a,b)) ys) xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    change total f ((ys.map (a,·)) ++ pairs as ys) = _
    rw [total_append,total_map,ih]; rfl

def count (u v : Word) (d n : Nat) := mass (histogram u).1 (fun a =>
  mass (histogram v).1 (fun b => if accepts d n a b then 1 else 0))

theorem choices_length (u v : Word) (d n : Nat) :
    (choices u v d n).length = count u v d n := by
  unfold choices count
  rw [length_filter_total,total_pairs]
  let indicator (a b : Key) : Nat := if accepts d n a b then 1 else 0
  change total (fun w => total (fun z => indicator (stat w) (stat z)) _) _ = _
  have inn (w : Word) := (histogram_correct v).1 (indicator (stat w))
  simp only [inn]
  exact (histogram_correct u).1 (fun a => mass (histogram v).1 (indicator a))

end PatternInterval
