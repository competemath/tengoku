/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic

/-!
# Inverse of the tanh function

In this file we define an inverse of tanh as a function from ℝ to (-1, 1).

## Main definitions

- `Real.artanh`: An inverse function of `Real.tanh` as a function from ℝ to (-1, 1).

- `Real.tanhPartialEquiv`: `Real.tanh` and `Real.artanh` bundled as a `PartialEquiv`
  from ℝ to (-1, 1).

## Main Results

- `Real.tanh_artanh`, `Real.artanh_tanh`: tanh and artanh are inverse in the appropriate domains.

- `Real.tanh_bijOn`, `Real.tanh_injective`, `Real.tanh_surjOn`: `Real.tanh` is
  bijective, injective and surjective as a function from ℝ to (-1, 1)

- `Real.artanh_bijOn`, `Real.artanh_injOn`, `Real.artanh_surjOn`: `Real.artanh` is bijective,
  injective and surjective as a function from (-1, 1) to ℝ

## Tags

artanh, arctanh, argtanh, atanh
-/

@[expose] public section


noncomputable section

open Function Set

open scoped Topology

namespace Real

variable {x y : ℝ}

/-- `artanh` is defined using a logarithm, `artanh x = log √((1 + x) / (1 - x))`. -/
@[pp_nodot]
def artanh (x : ℝ) :=
  log √((1 + x) / (1 - x))

/--
@isnad1 id=eq.1h1v.s6.b1a7d78ba97d from=seed src=0 shape=f0501aca vocab=fed9b6fa
-/
theorem artanh_eq_half_log {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    artanh x = 1 / 2 * log ((1 + x) / (1 - x)) := by
  rw [artanh, log_sqrt <| div_nonneg (by grind) (by grind), one_div_mul_eq_div]

/--
@isnad1 id=eq.1h1v.s6.741b6d0ff01c from=seed src=0 shape=728349fc vocab=7838b2ba
-/
theorem exp_artanh {x : ℝ} (hx : x ∈ Ioo (-1) 1) : exp (artanh x) = √((1 + x) / (1 - x)) :=
  exp_log <| sqrt_pos_of_pos <| div_pos (by grind) (by grind)

/--
@isnad1 id=eq.0h0v.s3.191e2724d881 from=seed src=0 shape=3c26ae4f vocab=ada5747a
-/
@[simp]
theorem artanh_zero : artanh 0 = 0 := by simp [artanh]

/--
@isnad1 id=eq.1h1v.s6.aeb5f28040fc from=seed src=0 shape=fb1927f6 vocab=cbebb268
-/
theorem sinh_artanh {x : ℝ} (hx : x ∈ Ioo (-1) 1) : sinh (artanh x) = x / √(1 - x ^ 2) := by
  have : 0 < √((1 + x) / (1 - x)) := sqrt_pos_of_pos <| div_pos (by grind) (by grind)
  rw [← one_pow, sq_sub_sq 1 x, sqrt_mul]
    <;> grind [artanh, sinh_eq, exp_neg, exp_log, sqrt_div]

/--
@isnad1 id=eq.1h1v.s6.b7e0f068c07d from=seed src=0 shape=02abf707 vocab=e2487638
-/
theorem cosh_artanh {x : ℝ} (hx : x ∈ Ioo (-1) 1) : cosh (artanh x) = 1 / √(1 - x ^ 2) := by
  have : 0 < √((1 + x) / (1 - x)) := sqrt_pos_of_pos <| div_pos (by grind) (by grind)
  rw [← one_pow, sq_sub_sq 1 x, sqrt_mul]
    <;> grind [artanh, cosh_eq, exp_neg, exp_log, sqrt_div]

/-- `artanh` is the right inverse of `tanh` over (-1, 1).
@isnad1 id=eq.1h1v.s5.1c3854988ea5 from=seed src=0 shape=be6d127b vocab=0b83b138
-/
theorem tanh_artanh {x : ℝ} (hx : x ∈ Ioo (-1) 1) : tanh (artanh x) = x := by
  have := sq_sub_sq 1 x
  grind [tanh_eq_sinh_div_cosh, sinh_artanh, cosh_artanh, sqrt_ne_zero', mul_pos]

/-- `artanh` is the left inverse of `tanh`.
@isnad1 id=eq.0h1v.s3.abf3c2f9da5a from=seed src=0 shape=47dcad53 vocab=c6611f4f
-/
theorem artanh_tanh (x : ℝ) : artanh (tanh x) = x := by
  have h : 0 < (1 + tanh x) / (1 - tanh x) :=
    div_pos (by grind [neg_one_lt_tanh]) (by grind [tanh_lt_one])
  rw [artanh, ← exp_eq_exp, exp_log (sqrt_pos_of_pos h),
    ← sq_eq_sq₀ (le_of_lt <| sqrt_pos_of_pos h) (exp_nonneg x),
    sq_sqrt (le_of_lt h), tanh_eq, exp_neg]
  field

/--
@isnad1 id=strictmo.0h0v.s5.ae85c8a5176e from=seed src=0 shape=7581beee vocab=c905c532
-/
theorem strictMonoOn_one_add_div_one_sub :
    StrictMonoOn (fun (x : ℝ) => (1 + x) / (1 - x)) (Ioo (-1) 1) := by
  intro x hx y hy h
  field_simp [show 0 < 1 - x by grind, show 0 < 1 - y by grind]
  grind

/--
@isnad1 id=strictmo.0h0v.s4.580fbc6bd240 from=seed src=0 shape=c86032c6 vocab=ed2d5697
-/
theorem strictMonoOn_artanh : StrictMonoOn artanh (Ioo (-1) 1) := by
  apply strictMonoOn_log.comp ?_ fun x hx ↦ sqrt_pos_of_pos <| div_pos (by grind) (by grind)
  apply strictMonoOn_sqrt.comp strictMonoOn_one_add_div_one_sub
    fun x hx ↦ show 0 ≤ (1 + x) / (1 - x) by exact div_nonneg (by grind) (by grind)

/--
@isnad1 id=iff.2h2v.s6.5bef74920d83 from=seed src=0 shape=fd40a26d vocab=7b37dadd
-/
theorem artanh_le_artanh_iff {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1) :
    artanh x ≤ artanh y ↔ x ≤ y :=
  strictMonoOn_artanh.le_iff_le hx hy

/--
@isnad1 id=iff.2h2v.s6.4c59c50b5519 from=seed src=0 shape=fd40a26d vocab=b34298b5
-/
theorem artanh_lt_artanh_iff {x y : ℝ} (hx : x ∈ Ioo (-1) 1) (hy : y ∈ Ioo (-1) 1) :
    artanh x < artanh y ↔ x < y :=
  strictMonoOn_artanh.lt_iff_lt hx hy

/--
@isnad1 id=le.3h2v.s5.46de35df6d0f from=seed src=0 shape=f1ee5026 vocab=4847cb5f
-/
theorem artanh_le_artanh {x y : ℝ} (hx : -1 < x) (hy : y < 1) (hxy : x ≤ y) :
    artanh x ≤ artanh y :=
  (artanh_le_artanh_iff (by grind) (by grind)).mpr hxy

/--
@isnad1 id=lt.3h2v.s5.7eecae55914b from=seed src=0 shape=43aeadd0 vocab=a0c05955
-/
theorem artanh_lt_artanh {x y : ℝ} (hx : -1 < x) (hy : y < 1) (hxy : x < y) :
    artanh x < artanh y :=
  (artanh_lt_artanh_iff (by grind) (by grind)).mpr hxy

/--
@isnad1 id=iff.0h1v.s5.1ab1084074a5 from=seed src=0 shape=e20e8b31 vocab=4ba92322
-/
theorem artanh_eq_zero_iff {x : ℝ} : artanh x = 0 ↔ x ≤ -1 ∨ x = 0 ∨ 1 ≤ x := by
  grind [artanh, log_eq_zero, div_nonpos_iff]

/--
@isnad1 id=lt.1h1v.s5.43ef9a104c7a from=seed src=0 shape=fca5627a vocab=16ff3bd6
-/
theorem artanh_pos {x : ℝ} (hx : x ∈ Ioo 0 1) : 0 < artanh x := by
  rw [← artanh_zero, artanh_lt_artanh_iff (by grind) (by grind)]
  exact hx.1

/--
@isnad1 id=lt.1h1v.s5.ebf3b71dccf1 from=seed src=0 shape=d671cc6b vocab=b34298b5
-/
theorem artanh_neg {x : ℝ} (hx : x ∈ Ioo (-1) 0) : artanh x < 0 := by
  rw [← artanh_zero, artanh_lt_artanh_iff (by grind) (by grind)]
  exact hx.2

/--
@isnad1 id=le.1h1v.s4.57594daad2e0 from=seed src=0 shape=35bd48ee vocab=62341790
-/
theorem artanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ artanh x := by
  by_cases x < 1
  case pos =>
    rw [← artanh_zero, artanh_le_artanh_iff (by grind) (by grind)]
    exact hx
  case neg => grind [artanh_eq_zero_iff]

/--
@isnad1 id=le.1h1v.s4.d8f660a51414 from=seed src=0 shape=5aedd577 vocab=62341790
-/
theorem artanh_nonpos {x : ℝ} (hx : x ≤ 0) : artanh x ≤ 0 := by
  by_cases -1 < x
  case pos =>
    rw [← artanh_zero, artanh_le_artanh_iff (by grind) (by grind)]
    exact hx
  case neg => grind [artanh_eq_zero_iff]

/-- `Real.tanh` as a `PartialEquiv`. -/
def tanhPartialEquiv : PartialEquiv ℝ ℝ where
  toFun := tanh
  invFun := artanh
  source := univ
  target := Ioo (-1) 1
  map_source' r _ := mem_Ioo.mpr ⟨neg_one_lt_tanh r, tanh_lt_one r⟩
  map_target' _ _ := trivial
  left_inv' r _ := artanh_tanh r
  right_inv' _ hr := tanh_artanh hr

/--
@isnad1 id=bijon.0h0v.s4.a60fe2df7cbb from=seed src=0 shape=6fcd010e vocab=7cf745fa
-/
theorem tanh_bijOn : BijOn tanh univ (Ioo (-1) 1) := tanhPartialEquiv.bijOn

/--
@isnad1 id=injectiv.0h0v.s2.b693a7b29f2c from=seed src=0 shape=e3d48bcb vocab=0bb01ce7
-/
theorem tanh_injective : Injective tanh := fun _ _ ↦ tanhPartialEquiv.injOn trivial trivial

/--
@isnad1 id=surjon.0h0v.s4.30b3536c5e26 from=seed src=0 shape=6fcd010e vocab=c1e5ea7d
-/
theorem tanh_surjOn : SurjOn tanh univ (Ioo (-1) 1) := tanhPartialEquiv.surjOn

/--
@isnad1 id=bijon.0h0v.s4.3fa08614e02e from=seed src=0 shape=8ec0d87f vocab=27ec1f84
-/
theorem artanh_bijOn : BijOn artanh (Ioo (-1) 1) univ := tanhPartialEquiv.symm.bijOn

/--
@isnad1 id=injon.0h0v.s4.fea3bf123b2a from=seed src=0 shape=c86032c6 vocab=620109d0
-/
theorem artanh_injOn : InjOn artanh (Ioo (-1) 1) := tanhPartialEquiv.symm.injOn

/--
@isnad1 id=surjon.0h0v.s4.1c6130d372e2 from=seed src=0 shape=8ec0d87f vocab=2c8aff0e
-/
theorem artanh_surjOn : SurjOn artanh (Ioo (-1) 1) univ := tanhPartialEquiv.symm.surjOn

end Real
