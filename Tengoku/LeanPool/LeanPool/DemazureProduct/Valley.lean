/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import Tengoku

/-!
# Valleys

A *valley* is a function `f : ℤ → ℤ` tending to positive infinity on both sides. This
terminology is not used in
[An extended Demazure product](https://arxiv.org/abs/2206.14227); it is introduced here in order
to package some elementary arguments that are needed about such functions. In particular, we need
to keep track of the set where the minimum value is achieved, and some facts about how this set
changes when the valley is modified in simple ways.
-/

@[expose] public section

namespace LeanPool.DemazureProduct

/-- A function on `ℤ` whose sublevel sets are finite. This is the abstraction
used to talk about minima and rightmost minimizers.
-/
structure Valley where
  /-- The integer-valued function. -/
  f : ℤ → ℤ
  /-- Every sublevel set is finite. -/
  rises : ∀ m : ℤ, {n : ℤ | f n ≤ m}.Finite

instance : CoeFun Valley (fun _ => ℤ → ℤ) :=
  ⟨Valley.f⟩

namespace Valley
variable (v : Valley)

/-! ### Minima and rightmost minimizers

This namespace develops the basic API for working with a `Valley`: its minimum
value, the rightmost index where that minimum is attained, and behavior under
vertical shifts. -/

/-- The finite sublevel set `{n | v n ≤ m}`. -/
noncomputable def floor (m : ℤ) : Finset ℤ := Set.Finite.toFinset (v.rises m)

/--
@isnad1 id=iff.0h3v.s4.38d4d630b0a4 from=translated src=- shape=a8c06c53 vocab=53a60500
-/
@[simp] lemma mem_floor (m n : ℤ) : n ∈ v.floor m ↔ v.f n ≤ m := by
  simp only [floor, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/--
@isnad1 id=nonempty.0h2v.s4.45393fefa06e from=translated src=- shape=e33067c8 vocab=04385271
-/
lemma floor_image_nonempty (n : ℤ) : (Finset.image v.f <| v.floor (v.f n)).Nonempty := by
  refine ⟨v.f n, ?_⟩
  exact Finset.mem_image.mpr ⟨n, by simp, rfl⟩

/-- The minimum value of a valley. -/
noncomputable def min : ℤ := Finset.min' (Finset.image v.f (v.floor (v.f 0)))
  (v.floor_image_nonempty 0)

/--
@isnad1 id=ex.0h1v.s5.198b8b82c230 from=translated src=- shape=f027e45b vocab=58135146
-/
lemma min_mem : ∃ a ∈ {n | v.f n ≤ v.f 0}, v.f a = v.min := by
  simpa [min, Finset.mem_image] using
    Finset.min'_mem (Finset.image v.f (v.floor (v.f 0))) (v.floor_image_nonempty 0)

/--
@isnad1 id=le.0h2v.s3.0c0f45ba7ae4 from=translated src=- shape=7c82f523 vocab=feaea2c0
-/
lemma min_spec : ∀ n : ℤ, v.f n ≥ v.min := by
  intro n
  by_cases h : v.f n > v.f 0
  · rcases v.min_mem with ⟨m, hm⟩
    have := le_trans (hm.1) (le_of_lt h)
    rwa [hm.2] at this
  have mem_floor : n ∈ v.floor (v.f 0) := by
    simpa using le_of_not_gt h
  have mem_image_floor : v.f n ∈ Finset.image v.f (v.floor (v.f 0)) :=
    Finset.mem_image.mpr ⟨n, mem_floor, rfl⟩
  exact Finset.min'_le (Finset.image v.f (v.floor (v.f 0))) (v.f n) mem_image_floor

/--
@isnad1 id=nonempty.0h1v.s3.281c6b7f025a from=translated src=- shape=96d2610a vocab=7994f154
-/
lemma argmin_set_nonempty : (v.floor v.min).Nonempty := by
  rcases v.min_mem with ⟨m, -, hm⟩
  exact ⟨m, by simp only [mem_floor, hm, le_refl]⟩

/-- The largest index at which the minimum of the valley is attained. -/
noncomputable def M : ℤ := Finset.max' (v.floor v.min) v.argmin_set_nonempty

/--
@isnad1 id=eq.0h1v.s3.778bc2e48e9a from=translated src=- shape=aa9ebf7c vocab=054e7f19
-/
lemma f_M : v.f v.M = v.min := by
  have ge : v.f v.M ≥ v.min := v.min_spec v.M
  have le : v.f v.M ≤ v.min := by
    have : v.M ∈ v.floor v.min := Finset.max'_mem (v.floor v.min) v.argmin_set_nonempty
    simpa using this
  exact le_antisymm le ge

/--
@isnad1 id=and.0h2v.s5.4042cc01f0c4 from=translated src=- shape=41feb417 vocab=162c6c72
-/
lemma M_spec : ∀ n : ℤ, v.f n ≥ v.f v.M ∧ (n > v.M → v.f n > v.f v.M) := by
  intro n
  constructor
  · have := v.min_spec n
    rwa [v.f_M]
  · intro n_gt_vM
    contrapose! n_gt_vM with fn_le_fM
    have : n ∈ v.floor v.min := by
      simpa [v.f_M] using fn_le_fM
    simpa [M] using Finset.le_max' (v.floor v.min) n this

/-- Shift every value of a valley downward by the constant `k`. -/
def shiftDown (k : ℤ) : Valley where
  f := fun n => v.f n - k
  rises := by
    intro m
    have : {n : ℤ | v.f n - k ≤ m} = {n : ℤ | v.f n ≤ m + k} := by
      simp_all
    rw [this]
    apply v.rises

/-- Shifting a valley downward does not change its rightmost minimizer.
@isnad1 id=eq.0h2v.s3.a23297199681 from=translated src=- shape=393de0b8 vocab=595f22c3
-/
lemma shift_down_M (k : ℤ) : (v.shiftDown k).M = v.M := by
  let v' := v.shiftDown k
  suffices v.M = v'.M by rw [this]
  have ge : v.f v'.M ≥ v.f v.M := (v.M_spec v'.M).1
  have le : v'.f v'.M ≤ v'.f v.M := by
    exact ((v.shiftDown k).M_spec v.M).1
  have f_eq : v.f v.M = v.f v'.M := by
    subst v'
    unfold Valley.shiftDown at le ge ⊢
    simp only [tsub_le_iff_right, sub_add_cancel] at le
    omega
  have f'_eq : v'.f v.M = v'.f v'.M := by
    subst v'
    unfold Valley.shiftDown at le ge ⊢
    simp only [tsub_le_iff_right, sub_add_cancel, sub_left_inj] at le ⊢
    omega
  have M_le_M' : v.M ≤ v'.M := by
    have := (v'.M_spec v.M).2
    simp_all
  have M'_le_M : v'.M ≤ v.M := by
    have := (v.M_spec v'.M).2
    simp_all
  exact le_antisymm M_le_M' M'_le_M

/-- Shifting a valley downward subtracts `k` from its minimum value.
@isnad1 id=eq.0h2v.s4.c70dc95a4a2f from=translated src=- shape=42db545a vocab=d93468d6
-/
lemma shift_down_min (k : ℤ) : (v.shiftDown k).min = v.min - k := by
  let v' := v.shiftDown k
  rw [← v'.f_M, ← v.f_M, v.shift_down_M k]
  subst v'
  unfold Valley.shiftDown
  simp

end Valley

end LeanPool.DemazureProduct
