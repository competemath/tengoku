import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kernel-reducible arithmetic primitives

Several of the primitives the executable pipeline is built from are defined in
core or in Mathlib by well-founded recursion (`Nat.sqrt`, `List.mergeSort`) or
through rational arithmetic (`Int.floor` of a quotient).  Those definitions run
perfectly well in compiled code, but the *kernel* cannot reduce them, so no
`decide`-style proof can evaluate them.

This file supplies kernel-reducible replacements together with the theorems
identifying them with the originals:

* `natSqrtK` / `isqrtK`  — a binary-search integer square root, proved equal to
  `Nat.sqrt` / `Int.sqrt`;
* `insertB` / `isortB`   — insertion sort for a `Bool`-valued comparison, with
  its permutation and sortedness lemmas, and
  `List.mergeSort_eq_isortB`, which identifies it with `List.mergeSort` on any
  list whose elements are pairwise antisymmetric;
* `Finset.sort_eq_of_sorted_lt` — a `Finset.sort` elimination lemma;
* `Int.floor_intCast_div` / `Int.ceil_intCast_div` — the floor and ceiling of a
  quotient of integers as integer division.

Nothing here is specific to the manuscript; it is generic infrastructure.
-/

namespace TunnellMap

/-! ## A kernel-reducible integer square root -/

/-- Binary search for `⌊√n⌋`.  The invariant maintained by the recursion is
`lo * lo ≤ n < hi * hi`; `fuel` bounds `hi - lo`.-/
def sqrtBSAux (n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then lo
      else
        let mid := (lo + hi) / 2
        if mid * mid ≤ n then sqrtBSAux n fuel mid hi else sqrtBSAux n fuel lo mid

/-- A kernel-reducible integer square root on `ℕ`.-/
def natSqrtK (n : ℕ) : ℕ := sqrtBSAux n (n + 1) 0 (n + 1)

/--
@isnad1 id=and.4h4v.s7.7ac2356ce954 from=translated src=- shape=9f721f5f vocab=4c9bbf4d
-/
theorem sqrtBSAux_spec (n : ℕ) :
    ∀ fuel lo hi, lo < hi → hi ≤ lo + 1 + fuel → lo * lo ≤ n → n < hi * hi →
      (sqrtBSAux n fuel lo hi) * (sqrtBSAux n fuel lo hi) ≤ n ∧
        n < (sqrtBSAux n fuel lo hi + 1) * (sqrtBSAux n fuel lo hi + 1) := by
  intro fuel
  induction fuel with
  | zero =>
      intro lo hi hlt hle hlo hhi
      have hhieq : hi = lo + 1 := by omega
      subst hhieq
      exact ⟨hlo, hhi⟩
  | succ fuel ih =>
      intro lo hi hlt hle hlo hhi
      rw [sqrtBSAux]
      by_cases hstop : hi ≤ lo + 1
      · rw [ite_eq_left hstop]
        have hhieq : hi = lo + 1 := by omega
        subst hhieq
        exact ⟨hlo, hhi⟩
      · rw [ite_eq_right hstop]
        simp only []
        set mid := (lo + hi) / 2 with hmid
        have hmid₁ : lo < mid := by omega
        have hmid₂ : mid < hi := by omega
        by_cases hm : mid * mid ≤ n
        · rw [ite_eq_left hm]
          exact ih mid hi hmid₂ (by omega) hm hhi
        · rw [ite_eq_right hm]
          exact ih lo mid hmid₁ (by omega) hlo (by omega)

/--
@isnad1 id=and.0h1v.s5.0c063d7c917b from=translated src=- shape=9e47c25e vocab=6d4d9165
-/
theorem natSqrtK_spec (n : ℕ) :
    natSqrtK n * natSqrtK n ≤ n ∧ n < (natSqrtK n + 1) * (natSqrtK n + 1) := by
  refine sqrtBSAux_spec n (n + 1) 0 (n + 1) (by omega) (by omega) (by omega) ?_
  nlinarith

/-- The binary-search square root is `Nat.sqrt`.
@isnad1 id=eq.0h1v.s3.63a3abcaa281 from=translated src=- shape=0fc427d2 vocab=c2c8aa53
-/
theorem natSqrtK_eq (n : ℕ) : natSqrtK n = Nat.sqrt n := by
  obtain ⟨h₁, h₂⟩ := natSqrtK_spec n
  have hle : natSqrtK n ≤ Nat.sqrt n := Nat.le_sqrt.mpr h₁
  have hlt : Nat.sqrt n < natSqrtK n + 1 := Nat.sqrt_lt.mpr h₂
  omega

/-- A kernel-reducible integer square root on `ℤ`.-/
def isqrtK (z : ℤ) : ℤ := (natSqrtK z.toNat : ℤ)

/--
@isnad1 id=eq.0h1v.s3.c1d1a32e544b from=translated src=- shape=0fc427d2 vocab=7c149d43
-/
@[simp] theorem isqrtK_eq (z : ℤ) : isqrtK z = Int.sqrt z := by
  rw [isqrtK, natSqrtK_eq, Int.sqrt]

/-! ## Floor and ceiling of an integer quotient -/

/--
@isnad1 id=eq.1h2v.s5.96e8c7d67efe from=translated src=- shape=329fbc89 vocab=8da1367c
-/
theorem floor_intCast_div_intCast (a b : ℤ) (hb : 0 ≤ b) :
    ⌊((a : ℚ) / (b : ℚ))⌋ = a / b := by
  rw [Int.floor_div_cast_of_nonneg hb, Int.floor_intCast]

/--
@isnad1 id=eq.1h2v.s5.9e0b96bb69d3 from=translated src=- shape=00036e6e vocab=ebbe6e87
-/
theorem ceil_intCast_div_intCast (a b : ℤ) (hb : 0 ≤ b) :
    ⌈((a : ℚ) / (b : ℚ))⌉ = -((-a) / b) := by
  have h : ((a : ℚ) / (b : ℚ)) = -(((-a : ℤ) : ℚ) / (b : ℚ)) := by push_cast; ring
  rw [h, Int.ceil_neg, floor_intCast_div_intCast _ _ hb]

/-! ## Insertion sort for a `Bool`-valued comparison -/

variable {α : Type*}

/-- Insert `a` into a list, before the first element it compares `le` to.-/
def insertB (le : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: l => if le a b then a :: b :: l else b :: insertB le a l

/-- Insertion sort for a `Bool`-valued comparison.  Unlike `List.mergeSort`
this is structurally recursive, hence reducible by the kernel.-/
def isortB (le : α → α → Bool) : List α → List α
  | [] => []
  | a :: l => insertB le a (isortB le l)

/--
@isnad1 id=perm.0h4v.s4.c2fdbee8d42e from=translated src=- shape=2957a096 vocab=a3c60aa2
-/
theorem insertB_perm (le : α → α → Bool) (a : α) (l : List α) :
    (insertB le a l).Perm (a :: l) := by
  induction l with
  | nil => simp [insertB]
  | cons b l ih =>
      by_cases h : le a b
      · simp [insertB, h]
      · simp only [insertB, h, Bool.false_eq_true, ite_false]
        exact ((ih.cons b).trans (List.Perm.swap a b l))

/--
@isnad1 id=perm.0h3v.s4.4ee2cd28c88a from=translated src=- shape=56a1e743 vocab=e41af6ac
-/
theorem isortB_perm (le : α → α → Bool) (l : List α) : (isortB le l).Perm l := by
  induction l with
  | nil => simp [isortB]
  | cons a l ih => exact (insertB_perm le a (isortB le l)).trans (ih.cons a)

/--
@isnad1 id=pairwise.3h4v.s6.f7b91e40c7e0 from=translated src=- shape=5f2ef21f vocab=241274da
-/
theorem insertB_sorted (le : α → α → Bool)
    (htotal : ∀ a b, le a b = true ∨ le b a = true)
    (htrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (a : α) {l : List α} (hl : l.Pairwise fun x y => le x y = true) :
    (insertB le a l).Pairwise fun x y => le x y = true := by
  induction l with
  | nil => simp [insertB]
  | cons b l ih =>
      rw [List.pairwise_cons] at hl
      by_cases h : le a b
      · simp only [insertB, h, ite_true]
        refine List.Pairwise.cons ?_ (List.pairwise_cons.mpr hl)
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact h
        · exact htrans _ _ _ h (hl.1 y hy)
      · have hba : le b a = true := (htotal a b).resolve_left (by simpa using h)
        simp only [insertB, h, Bool.false_eq_true, ite_false]
        refine List.Pairwise.cons ?_ (ih hl.2)
        intro y hy
        rcases List.mem_cons.mp ((insertB_perm le a l).mem_iff.mp hy) with rfl | hy'
        · exact hba
        · exact hl.1 y hy'

/--
@isnad1 id=pairwise.2h3v.s6.acf735305342 from=translated src=- shape=5bb598a5 vocab=8f494274
-/
theorem isortB_sorted (le : α → α → Bool)
    (htotal : ∀ a b, le a b = true ∨ le b a = true)
    (htrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (l : List α) : (isortB le l).Pairwise fun x y => le x y = true := by
  induction l with
  | nil => simp [isortB]
  | cons a l ih => exact insertB_sorted le htotal htrans a ih

/-- `List.mergeSort` and `isortB` agree on any list whose elements are
pairwise antisymmetric for the comparison.
@isnad1 id=eq.3h3v.s6.88505d9df347 from=translated src=- shape=99f841d8 vocab=da8dc14b
-/
theorem mergeSort_eq_isortB (le : α → α → Bool)
    (htotal : ∀ a b, le a b = true ∨ le b a = true)
    (htrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    {l : List α}
    (hanti : ∀ a ∈ l, ∀ b ∈ l, le a b = true → le b a = true → a = b) :
    l.mergeSort le = isortB le l := by
  have hperm₁ : (l.mergeSort le).Perm l := List.mergeSort_perm _ _
  have hperm₂ : (isortB le l).Perm l := isortB_perm le l
  refine List.Perm.eq_of_pairwise (le := fun x y => le x y = true) ?_ ?_ ?_
    (hperm₁.trans hperm₂.symm)
  · intro a b ha hb hab hba
    exact hanti a (hperm₁.mem_iff.mp ha) b (hperm₂.mem_iff.mp hb) hab hba
  · exact List.pairwise_mergeSort (fun {a b c} => htrans a b c)
      (fun a b => by simpa using htotal a b) l
  · exact isortB_sorted le htotal htrans l

/-! ## Eliminating `Finset.sort` -/

/-- A strictly increasing list whose members are exactly the members of a
finite set *is* the sorted list of that set.
@isnad1 id=eq.2h3v.s6.9ea28c61c105 from=translated src=- shape=e6440115 vocab=cba801fd
-/
theorem Finset.sort_eq_of_sorted_lt {β : Type*} [LinearOrder β] (s : Finset β)
    (l : List β) (hs : l.Pairwise (· < ·)) (hmem : ∀ x, x ∈ l ↔ x ∈ s) :
    s.sort (· ≤ ·) = l := by
  have hnd : l.Nodup := hs.imp (fun h => ne_of_lt h)
  have hperm : (s.sort (· ≤ ·)).Perm l :=
    (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) hnd).mpr fun x => by
      rw [Finset.mem_sort, hmem]
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => le_antisymm hab hba)
    (Finset.pairwise_sort _ _) (hs.imp (fun h => le_of_lt h)) hperm

end TunnellMap
