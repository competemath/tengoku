/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov
-/
module

public import Tengoku.Seed.Algebra.Order.Ring.Nat
public import Tengoku.Seed.Algebra.Ring.Regular
public import Tengoku.Seed.Data.Finset.Image
public import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Defs
public import Tengoku.Arklib.ArkLib.ToMathlib.List.Basic
public import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
public import Tengoku.Seed.Data.PNat.Notation
public import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  # Definitions and lemmas related to `Finset`.
-/

@[expose] public section
namespace Tengoku.Arklib end Tengoku.Arklib open Tengoku.Arklib 
def _root_.Tengoku.Arklib.erase_odd (s : Finset ℕ) : Finset ℕ := s.filter Even
def _root_.Tengoku.Arklib.erase_even (s : Finset ℕ) : Finset ℕ := s.filter Odd

/--
@isnad1 id=eq.0h0v.s3.d538f381d400 from=translated src=- shape=f2c814de vocab=9ca716c2
-/
@[simp]
lemma _root_.Tengoku.Arklib.erase_odd_empty :
    erase_odd ∅ = ∅ := rfl

/--
@isnad1 id=eq.0h1v.s3.52790242a61d from=translated src=- shape=ba0e3ce9 vocab=8e2e84bc
-/
lemma _root_.Tengoku.Arklib.erase_odd_def {s : Finset ℕ} :
    erase_odd s = s.filter Even := rfl

/--
@isnad1 id=eq.0h0v.s3.3ced3380bab6 from=translated src=- shape=f2c814de vocab=eb292b94
-/
@[simp]
lemma _root_.Tengoku.Arklib.erase_even_empty :
    erase_even ∅ = ∅ := rfl

/--
@isnad1 id=eq.0h1v.s3.6bfb185d5631 from=translated src=- shape=ba0e3ce9 vocab=3d3f1085
-/
lemma _root_.Tengoku.Arklib.erase_even_def {s : Finset ℕ} :
    erase_even s = s.filter Odd := rfl

def _root_.Tengoku.Arklib.shift_left (s : Finset ℕ) : Finset ℕ :=
  s.filterMap
    (fun n => match n with
      | 0 => .none
      | n + 1 => .some n
      )
    (by aesop)

/--
@isnad1 id=eq.0h0v.s3.99ce206d43c6 from=translated src=- shape=f2c814de vocab=5c40cffe
-/
@[simp]
lemma _root_.Tengoku.Arklib.shift_left_empty :
    shift_left ∅ = ∅ := rfl

/--
@isnad1 id=eq.0h1v.s4.ed4b8372af45 from=translated src=- shape=fc99221f vocab=c92eefe5
-/
lemma _root_.Tengoku.Arklib.shift_left_def {s : Finset ℕ} :
    shift_left s = s.filterMap
    (fun n => match n with
      | 0 => .none
      | n + 1 => .some n
      )
    (by aesop) := rfl

/-- The embedding of natural numbers given by multiplication by two.-/
def _root_.Tengoku.Arklib.mulByTwoEmbedding : ℕ ↪ ℕ :=
  ⟨fun n => 2 * n, by
    intro a b
    simp⟩

/--
@isnad1 id=eq.0h1v.s4.09ca9053cb90 from=translated src=- shape=331357e5 vocab=376dc929
-/
@[simp]
lemma _root_.Tengoku.Arklib.mulByTwoEmbedding_apply (n : ℕ) : mulByTwoEmbedding n = 2 * n := rfl

def _root_.Tengoku.Arklib.mul_by_2 (s : Finset ℕ) : Finset ℕ :=
  s.map mulByTwoEmbedding

/--
@isnad1 id=eq.0h0v.s3.87dae08dcbff from=translated src=- shape=f2c814de vocab=a9d2b203
-/
@[simp]
lemma _root_.Tengoku.Arklib.mul_by_empty :
    mul_by_2 ∅ = ∅ := rfl

/--
@isnad1 id=eq.0h1v.s3.c5b2e723b6f2 from=translated src=- shape=1bdde0d6 vocab=5a38944a
-/
lemma _root_.Tengoku.Arklib.mul_by_2_def {s : Finset ℕ} :
    mul_by_2 s = s.map mulByTwoEmbedding := rfl

def _root_.Tengoku.Arklib.divide_by_2 (s : Finset ℕ) : Finset ℕ :=
  (erase_odd s).image (fun n => n / 2)

/--
@isnad1 id=eq.0h0v.s3.3722a4c028ca from=translated src=- shape=f2c814de vocab=7b452b43
-/
@[simp]
lemma _root_.Tengoku.Arklib.divide_by_2_empty :
    divide_by_2 ∅ = ∅ := rfl

/--
@isnad1 id=eq.0h1v.s4.fb177a9703e7 from=translated src=- shape=d3e18be3 vocab=0812ee53
-/
lemma _root_.Tengoku.Arklib.divide_by_2_def {s : Finset ℕ} :
    divide_by_2 s = (erase_odd s).image (fun n => n / 2) := rfl

/--
@isnad1 id=iff.0h2v.s5.abd7b15f0b90 from=translated src=- shape=2bb26db8 vocab=63f84635
-/
@[simp]
theorem _root_.Tengoku.Arklib.erase_odd_mem
    {s : Finset ℕ}
  {n : ℕ} : n ∈ (erase_odd s) ↔ Even n ∧ n ∈ s := by aesop (add simp erase_odd)

/--
@isnad1 id=iff.0h2v.s5.cb2061f24361 from=translated src=- shape=2bb26db8 vocab=d17f590d
-/
@[simp]
theorem _root_.Tengoku.Arklib.erase_even_mem
    {s : Finset ℕ}
  {n : ℕ} : n ∈ (erase_even s) ↔ Odd n ∧ n ∈ s := by aesop (add simp erase_even)

/--
@isnad1 id=iff.0h2v.s5.91c1b252c27a from=translated src=- shape=1f9fb7fe vocab=b4fb0bd1
-/
@[simp]
theorem _root_.Tengoku.Arklib.mul_by_2_mem {s : Finset ℕ} {d : ℕ} :
    d ∈ mul_by_2 s ↔ Even d ∧ (d / 2) ∈ s := by
  aesop (add simp [mul_by_2, mulByTwoEmbedding_apply, Nat.even_iff], safe (by omega))

/--
@isnad1 id=iff.0h2v.s5.cd4874ab0597 from=translated src=- shape=d3805c96 vocab=565d71d2
-/
@[simp]
theorem _root_.Tengoku.Arklib.divide_by_2_mem {s : Finset ℕ} {d : ℕ} :
    d ∈ divide_by_2 s ↔ 2 * d ∈ s := by
  simp only [divide_by_2, Finset.mem_image, erase_odd_mem]
  exact ⟨
    fun _ ↦ by aesop (add simp [Nat.even_iff, Nat.mul_div_cancel', Nat.dvd_iff_mod_eq_zero]),
    fun _ ↦ ⟨2 * d, by aesop⟩
  ⟩

/--
@isnad1 id=iff.0h2v.s5.ed0f1de28a69 from=translated src=- shape=4b3de587 vocab=2489031a
-/
@[simp]
theorem _root_.Tengoku.Arklib.shift_left_mem {s : Finset ℕ} {d : ℕ} : d ∈ shift_left s ↔ (d + 1) ∈ s := by
  aesop (add simp shift_left) (add safe (by existsi d + 1))

@[simp]
def _root_.Tengoku.Arklib.finRangeTo (k : ℕ) (i : ℕ) : Finset (Fin k) :=
  (List.take i (List.finRange k)).toFinset

/--
@isnad1 id=eq.0h3v.s7.8c0ac1f68035 from=translated src=- shape=83b42a46 vocab=0dc49063
-/
@[simp]
lemma _root_.Tengoku.Arklib.sum_finRangeTo_add_one {n} {i : Fin (n + 1)} {f : Fin (n + 1) → ℕ} :
    ∑ j' ∈ finRangeTo (n + 1) (i + 1), f j' = (∑ j' ∈ finRangeTo (n + 1) i, f j') + f i := by
  unfold finRangeTo
  suffices ∑ x ∈ insert i (List.take i (List.finRange (n + 1))).toFinset, f x =
           ∑ x ∈ (List.take i (List.finRange (n + 1))).toFinset, f x + f i by
    simpa [List.take_add]
  have : i ∉ (List.take i (List.finRange (n + 1))).toFinset := by
    aesop (add simp List.mem_iff_getElem) (add safe (by grind [cases Fin]))
  simp +arith [Finset.sum_insert this]

/--
@isnad1 id=le.1h4v.s7.5e3e293f054f from=translated src=- shape=fa7eb5b0 vocab=7599594b
-/
lemma _root_.Tengoku.Arklib.sum_finRangeTo_le_sub_of_le {n k : ℕ} {s : Fin (k + 1) → ℕ+} {i : Fin (k + 1)}
    (k_le_n : ∑ j', (s j' : ℕ) ≤ n) :
  ∑ j' ∈ finRangeTo (k + 1) i, (s j' : ℕ) ≤ n - (s i : ℕ) := by
    apply Nat.le_sub_of_add_le
    rw [←sum_finRangeTo_add_one]
    transitivity
    · exact Finset.sum_le_univ_sum_of_nonneg (by simp)
    · exact k_le_n
-- Tengoku: root names of this library moved to Tengoku.Arklib so they do not collide with other libraries (generated)
