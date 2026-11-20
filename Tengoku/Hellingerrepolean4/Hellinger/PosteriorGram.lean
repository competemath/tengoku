import Tengoku.Hellingerrepolean4.Hellinger.PosteriorState
import Tengoku.Hellingerrepolean4.Hellinger.FourierRigidity
import Tengoku.Hellingerrepolean4.Hellinger.TraceEquality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms posterior_strict_bounds` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms plus_norm_sq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms minus_norm_sq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms plus_neighbor_inner` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms minus_neighbor_inner` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms posterior_abs_constant_of_component_gram` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms noise_second_moment_of_abs_constant_and_objective_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bsc_posterior_abs_constant_of_lifting_equality` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms signed_dictator_of_lifting_and_objective_equality` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Actual posterior components and neighboring Gram identities

All vectors are constructed from the finite BSC kernel and the Boolean output.
Strict posterior bounds and edge inner products are derived directly.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Matrix

namespace Hellinger.PosteriorGram

open Hellinger.Fourier Hellinger.PosteriorState

def plusVector {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (K : UniformChannel Ω)
    (y : Ω) : Ω → ℝ :=
  fun x => if f x = 1 then posteriorVector K y x else 0

def minusVector {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (K : UniformChannel Ω)
    (y : Ω) : Ω → ℝ :=
  fun x => if f x = 1 then 0 else posteriorVector K y x

/--
@isnad1 id=and.2h2v.s6.5387ecb59334 from=translated src=- shape=6f3ca58d vocab=5051cb37
-/
theorem boolean_has_both_signs {Ω : Type*} (f : Ω → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hnonconstant : ∃ x z, f x ≠ f z) :
    (∃ x, f x = 1) ∧ ∃ x, f x = -1 := by
  obtain ⟨x, z, hxz⟩ := hnonconstant
  rcases hf x with hx | hx <;> rcases hf z with hz | hz
  · exact False.elim (hxz (hx.trans hz.symm))
  · exact ⟨⟨z, hz⟩, ⟨x, hx⟩⟩
  · exact ⟨⟨x, hx⟩, ⟨z, hz⟩⟩
  · exact False.elim (hxz (hx.trans hz.symm))

/--
@isnad1 id=lt.2h3v.s5.1582fa3f541a from=translated src=- shape=81ee41dc vocab=1bc0532a
-/
theorem bsc_weight_pos (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1)
    (y x : Bool) : 0 < (bsc ρ hρ).weight y x := by
  change 0 < if y = x then (1 + ρ) / 2 else (1 - ρ) / 2
  split_ifs <;> linarith [hρ.1]

/--
@isnad1 id=lt.2h4v.s6.abf9025340ae from=translated src=- shape=d21c94ed vocab=18d16b7c
-/
theorem cube_weight_pos (n : ℕ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hρlt : ρ < 1) (y x : Cube n) : 0 < (cubeBSC n ρ hρ).weight y x := by
  change 0 < ∏ i : Fin n, (bsc ρ hρ).weight (y i) (x i)
  exact Finset.prod_pos (fun i _ => bsc_weight_pos ρ hρ hρlt (y i) (x i))

/--
@isnad1 id=and.3h4v.s6.49e5be64225f from=translated src=- shape=7e973576 vocab=93039190
-/
theorem apply_strict_bounds {Ω : Type*} [Fintype Ω]
    (K : UniformChannel Ω) (hK : ∀ y x, 0 < K.weight y x) (f : Ω → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hnonconstant : ∃ x z, f x ≠ f z) (y : Ω) :
    -1 < K.apply f y ∧ K.apply f y < 1 := by
  obtain ⟨⟨xp, hxp⟩, ⟨xm, hxm⟩⟩ := boolean_has_both_signs f hf hnonconstant
  have hb (x : Ω) : -1 ≤ f x ∧ f x ≤ 1 := by
    rcases hf x with h | h <;> norm_num [h]
  constructor
  · calc
      -1 = ∑ x, K.weight y x * (-1) := by rw [← Finset.sum_mul, K.row_sum]; ring
      _ < K.apply f y := by
        apply Finset.sum_lt_sum
        · intro x hx
          exact mul_le_mul_of_nonneg_left (hb x).1 (hK y x).le
        · refine ⟨xp, Finset.mem_univ _, ?_⟩
          rw [hxp]
          linarith [hK y xp]
  · calc
      K.apply f y < ∑ x, K.weight y x * 1 := by
        apply Finset.sum_lt_sum
        · intro x hx
          exact mul_le_mul_of_nonneg_left (hb x).2 (hK y x).le
        · refine ⟨xm, Finset.mem_univ _, ?_⟩
          rw [hxm]
          linarith [hK y xm]
      _ = 1 := by simp only [mul_one, K.row_sum]

/--
@isnad1 id=and.4h4v.s7.007c6d989727 from=translated src=- shape=186075de vocab=ff5a4015
-/
theorem posterior_strict_bounds {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hnonconstant : ∃ x z, f x ≠ f z)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1) (y : Cube n) :
    -1 < (cubeBSC n ρ hρ).apply f y ∧ (cubeBSC n ρ hρ).apply f y < 1 :=
  apply_strict_bounds (cubeBSC n ρ hρ) (cube_weight_pos n ρ hρ hρlt)
    f hf hnonconstant y

/--
@isnad1 id=eq.1h4v.s6.710f9ae09991 from=translated src=- shape=6864d9a0 vocab=67024ffc
-/
theorem plus_norm_sq {Ω : Type*} [Fintype Ω] (f : Ω → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (K : UniformChannel Ω) (y : Ω) :
    plusVector f K y ⬝ᵥ plusVector f K y = (1 + K.apply f y) / 2 := by
  have he (x : Ω) : plusVector f K y x * plusVector f K y x =
      (K.weight y x + K.weight y x * f x) / 2 := by
    rcases hf x with h | h
    · norm_num [plusVector, h]
    · simp only [plusVector, h, ite_true, posteriorVector, Real.mul_self_sqrt (K.nonneg y x)]
      ring
  unfold dotProduct
  simp only [he]
  rw [← Finset.sum_div, Finset.sum_add_distrib, K.row_sum]
  rfl

/--
@isnad1 id=eq.1h4v.s6.8d4f9f69925c from=translated src=- shape=6864d9a0 vocab=f607a8c6
-/
theorem minus_norm_sq {Ω : Type*} [Fintype Ω] (f : Ω → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (K : UniformChannel Ω) (y : Ω) :
    minusVector f K y ⬝ᵥ minusVector f K y = (1 - K.apply f y) / 2 := by
  have he (x : Ω) : minusVector f K y x * minusVector f K y x =
      (K.weight y x - K.weight y x * f x) / 2 := by
    rcases hf x with h | h
    · norm_num [minusVector, h, posteriorVector, Real.mul_self_sqrt (K.nonneg y x)]
    · simp only [minusVector, h, ite_true]
      ring
  unfold dotProduct
  simp only [he]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, K.row_sum]
  rfl

/--
@isnad1 id=eq.0h5v.s5.b7dc1b6211bb from=translated src=- shape=90222d58 vocab=d26c0560
-/
theorem component_orthogonal {Ω : Type*} [Fintype Ω]
    (f : Ω → ℝ) (K : UniformChannel Ω) (y z : Ω) :
    plusVector f K y ⬝ᵥ minusVector f K z = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  by_cases h : f x = 1 <;> simp [plusVector, minusVector, h]

/--
@isnad1 id=eq.1h3v.s5.201c25ac4f02 from=translated src=- shape=99a252b0 vocab=fe56347f
-/
theorem bsc_flip_sum (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (y x : Bool) :
    (bsc ρ hρ).weight y x + (bsc ρ hρ).weight (!y) x = 1 := by
  cases y <;> cases x <;> simp [bsc] <;> ring

/--
@isnad1 id=eq.1h3v.s6.25a49333eae9 from=translated src=- shape=76c4c61d vocab=3d190bbb
-/
theorem bsc_flip_sqrt_product (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (y x : Bool) :
    Real.sqrt ((bsc ρ hρ).weight y x) *
      Real.sqrt ((bsc ρ hρ).weight (!y) x) = root ρ / 2 := by
  cases y <;> cases x <;> simpa [bsc, mul_comm] using bsc_sqrt_cross ρ hρ

/--
@isnad1 id=eq.1h5v.s6.0af936920921 from=translated src=- shape=dd57e88d vocab=e68cde46
-/
theorem cube_weight_split {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (y x : Cube n) (i : Fin n) :
    (cubeBSC n ρ hρ).weight y x =
      (bsc ρ hρ).weight (y i) (x i) *
        ∏ j ∈ Finset.univ.erase i, (bsc ρ hρ).weight (y j) (x j) := by
  exact (Finset.mul_prod_erase Finset.univ
    (fun j => (bsc ρ hρ).weight (y j) (x j)) (Finset.mem_univ i)).symm

/--
@isnad1 id=eq.1h5v.s7.f100d910ec78 from=translated src=- shape=f3aa1bd7 vocab=04a49798
-/
theorem cube_weight_neighbor_sum {n : ℕ} (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (y x : Cube n) (i : Fin n) :
    (cubeBSC n ρ hρ).weight y x +
      (cubeBSC n ρ hρ).weight (Function.update y i (!(y i))) x =
        ∏ j ∈ Finset.univ.erase i, (bsc ρ hρ).weight (y j) (x j) := by
  rw [cube_weight_split ρ hρ y x i,
    cube_weight_split ρ hρ (Function.update y i (!(y i))) x i]
  simp only [Function.update_self]
  have he :
      (∏ j ∈ Finset.univ.erase i,
        (bsc ρ hρ).weight ((Function.update y i (!(y i))) j) (x j)) =
      ∏ j ∈ Finset.univ.erase i, (bsc ρ hρ).weight (y j) (x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he, ← add_mul, bsc_flip_sum, one_mul]

/-- The pointwise neighboring posterior-vector identity, before restricting
to either Boolean output fiber.
@isnad1 id=eq.1h5v.s7.9cd1c42b89bb from=translated src=- shape=793c46a8 vocab=48ec6a03
-/
theorem posterior_neighbor_product {n : ℕ} (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (y x : Cube n) (i : Fin n) :
    posteriorVector (cubeBSC n ρ hρ) y x *
      posteriorVector (cubeBSC n ρ hρ) (Function.update y i (!(y i))) x =
      root ρ / 2 * ((cubeBSC n ρ hρ).weight y x +
        (cubeBSC n ρ hρ).weight (Function.update y i (!(y i))) x) := by
  rw [cube_weight_neighbor_sum]
  simp only [cube_posterior_product, ← Finset.prod_mul_distrib]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => Real.sqrt ((bsc ρ hρ).weight (y j) (x j)) *
      Real.sqrt ((bsc ρ hρ).weight ((Function.update y i (!(y i))) j) (x j)))
    (Finset.mem_univ i)]
  simp only [Function.update_self, bsc_flip_sqrt_product]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1,
    Real.mul_self_sqrt ((bsc ρ hρ).nonneg (y j) (x j))]

/-- The positive-output posterior component has the manuscript's exact
neighboring inner product.
@isnad1 id=eq.2h5v.s8.a00610d91065 from=translated src=- shape=21226355 vocab=cfea2adb
-/
theorem plus_neighbor_inner {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (y : Cube n) (i : Fin n) :
    plusVector f (cubeBSC n ρ hρ) y ⬝ᵥ
      plusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) =
      root ρ / 2 * (1 + ((cubeBSC n ρ hρ).apply f y +
        (cubeBSC n ρ hρ).apply f (Function.update y i (!(y i)))) / 2) := by
  have he (x : Cube n) :
      plusVector f (cubeBSC n ρ hρ) y x *
        plusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) x =
      root ρ / 2 *
        (plusVector f (cubeBSC n ρ hρ) y x * plusVector f (cubeBSC n ρ hρ) y x +
          plusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) x *
            plusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) x) := by
    by_cases h : f x = 1
    · simp only [plusVector, h, ite_true]
      rw [posterior_neighbor_product]
      simp only [posteriorVector, Real.mul_self_sqrt ((cubeBSC n ρ hρ).nonneg _ _)]
    · simp [plusVector, h]
  unfold dotProduct
  simp only [he, ← Finset.mul_sum, Finset.sum_add_distrib]
  change root ρ / 2 * (plusVector f (cubeBSC n ρ hρ) y ⬝ᵥ
      plusVector f (cubeBSC n ρ hρ) y +
      plusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) ⬝ᵥ
        plusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i)))) = _
  rw [plus_norm_sq f hf, plus_norm_sq f hf]
  ring

/--
@isnad1 id=eq.2h5v.s8.f501895dc1fb from=translated src=- shape=5a1ba5dd vocab=ed4accfa
-/
theorem minus_neighbor_inner {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (y : Cube n) (i : Fin n) :
    minusVector f (cubeBSC n ρ hρ) y ⬝ᵥ
      minusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) =
      root ρ / 2 * (1 - ((cubeBSC n ρ hρ).apply f y +
        (cubeBSC n ρ hρ).apply f (Function.update y i (!(y i)))) / 2) := by
  have he (x : Cube n) :
      minusVector f (cubeBSC n ρ hρ) y x *
        minusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) x =
      root ρ / 2 *
        (minusVector f (cubeBSC n ρ hρ) y x * minusVector f (cubeBSC n ρ hρ) y x +
          minusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) x *
            minusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) x) := by
    by_cases h : f x = 1
    · simp [minusVector, h]
    · simp only [minusVector, h, ite_false]
      rw [posterior_neighbor_product]
      simp only [posteriorVector, Real.mul_self_sqrt ((cubeBSC n ρ hρ).nonneg _ _)]
  unfold dotProduct
  simp only [he, ← Finset.mul_sum, Finset.sum_add_distrib]
  change root ρ / 2 * (minusVector f (cubeBSC n ρ hρ) y ⬝ᵥ
      minusVector f (cubeBSC n ρ hρ) y +
      minusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i))) ⬝ᵥ
        minusVector f (cubeBSC n ρ hρ) (Function.update y i (!(y i)))) = _
  rw [minus_norm_sq f hf, minus_norm_sq f hf]
  ring

/--
@isnad1 id=eq.1h2v.s6.4251108e13b0 from=translated src=- shape=9f5cb864 vocab=613f93bf
-/
theorem sqrt_half_product (a b : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (a / 2) * Real.sqrt (b / 2) = Real.sqrt (a * b) / 2 := by
  rw [← Real.sqrt_mul (div_nonneg ha (by norm_num))]
  rw [show a / 2 * (b / 2) = (a * b) / 4 by ring]
  rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

/--
@isnad1 id=eq.1h4v.s6.1ed5fda14851 from=translated src=- shape=79e3e599 vocab=35d228e8
-/
theorem root_eq_two_component_norms {Ω : Type*} [Fintype Ω]
    (f : Ω → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) (K : UniformChannel Ω) (y : Ω) :
    root (K.apply f y) =
      2 * Real.sqrt (plusVector f K y ⬝ᵥ plusVector f K y) *
        Real.sqrt (minusVector f K y ⬝ᵥ minusVector f K y) := by
  have hb := K.apply_mem_Icc f (fun x => by
    rcases hf x with h | h <;> norm_num [h]) y
  rw [plus_norm_sq f hf, minus_norm_sq f hf, mul_assoc, sqrt_half_product _ _
    (by linarith [hb.1])]
  rw [show (1 + K.apply f y) * (1 - K.apply f y) = 1 - K.apply f y ^ 2 by ring]
  unfold root
  ring

/--
@isnad1 id=eq.1h4v.s7.8965c33cdf65 from=translated src=- shape=dadac24b vocab=5cbfa96a
-/
theorem pureDifference_components {Ω : Type*} [Fintype Ω]
    (f : Ω → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) (K : UniformChannel Ω) (y : Ω) :
    MatrixLifting.pureDifference (posteriorVector K y)
      (reflectedVector f (posteriorVector K y)) =
      (2 : ℝ) • (Matrix.vecMulVec (plusVector f K y) (minusVector f K y) +
        Matrix.vecMulVec (minusVector f K y) (plusVector f K y)) := by
  ext x z
  rcases hf x with hx | hx <;> rcases hf z with hz | hz <;>
    norm_num [MatrixLifting.pureDifference, reflectedVector, plusVector, minusVector,
      Matrix.vecMulVec_apply, hx, hz] <;> ring

/--
@isnad1 id=eq.1h3v.s8.906ac442bf34 from=translated src=- shape=c259e6fb vocab=a9f0e4a4
-/
theorem average_component_cross {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (f : Ω → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) (K : UniformChannel Ω) :
    averageProjection K - reflection f * averageProjection K * reflection f =
      (2 : ℝ) • ∑ y, (Fintype.card Ω : ℝ)⁻¹ •
        (Matrix.vecMulVec (plusVector f K y) (minusVector f K y) +
          Matrix.vecMulVec (minusVector f K y) (plusVector f K y)) := by
  rw [average_difference]
  simp only [pureDifference_components f hf, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  exact smul_comm _ _ _

/--
@isnad1 id=eq.1h3v.s7.5b59f569aa0a from=translated src=- shape=1ad135a8 vocab=f86f83e2
-/
theorem weighted_component_roots {Ω : Type*} [Fintype Ω]
    (f : Ω → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) (K : UniformChannel Ω) :
    (2 : ℝ) * ∑ y, (Fintype.card Ω : ℝ)⁻¹ *
        Real.sqrt (plusVector f K y ⬝ᵥ plusVector f K y) *
        Real.sqrt (minusVector f K y ⬝ᵥ minusVector f K y) =
      mean (fun y => root (K.apply f y)) := by
  unfold mean
  simp only [root_eq_two_component_norms f hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- Equality in actual posterior lifting gives precisely the cross-ensemble
trace equality required by the abstract equality theorem.
@isnad1 id=eq.2h3v.s8.af53d19164d5 from=translated src=- shape=cc25d37f vocab=be44fc74
-/
theorem cross_equality_of_lifting_equality {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (f : Ω → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) (K : UniformChannel Ω)
    (heq : TraceNorm.traceNorm
      (averageProjection K - reflection f * averageProjection K * reflection f) / 2 =
        mean (fun y => root (K.apply f y))) :
    TraceNorm.traceNorm
      (∑ y, (Fintype.card Ω : ℝ)⁻¹ •
        (Matrix.vecMulVec (plusVector f K y) (minusVector f K y) +
          Matrix.vecMulVec (minusVector f K y) (plusVector f K y))) =
      2 * ∑ y, (Fintype.card Ω : ℝ)⁻¹ *
        Real.sqrt (plusVector f K y ⬝ᵥ plusVector f K y) *
        Real.sqrt (minusVector f K y ⬝ᵥ minusVector f K y) := by
  rw [average_component_cross f hf, TraceNorm.traceNorm_smul] at heq
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at heq
  rw [weighted_component_roots f hf]
  linarith

/--
@isnad1 id=and.4h4v.s7.a2c88c1d1249 from=translated src=- shape=c8fbb959 vocab=c5b28983
-/
theorem component_norms_pos {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hnonconstant : ∃ x z, f x ≠ f z)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1) (y : Cube n) :
    0 < plusVector f (cubeBSC n ρ hρ) y ⬝ᵥ plusVector f (cubeBSC n ρ hρ) y ∧
      0 < minusVector f (cubeBSC n ρ hρ) y ⬝ᵥ minusVector f (cubeBSC n ρ hρ) y := by
  rw [plus_norm_sq f hf, minus_norm_sq f hf]
  have h := posterior_strict_bounds f hf hnonconstant ρ hρ hρlt y
  constructor <;> linarith

/--
@isnad1 id=eq.4h3v.s9.8a69345d16f9 from=translated src=- shape=763a9359 vocab=d1258b30
-/
theorem normalized_gram_of_component_equality (p q c : ℝ)
    (hp : -1 < p ∧ p < 1) (hq : -1 < q ∧ q < 1) (hc : 0 < c)
    (h :
      (c / 2 * (1 + (p + q) / 2)) /
          (Real.sqrt ((1 + p) / 2) * Real.sqrt ((1 + q) / 2)) =
        (c / 2 * (1 - (p + q) / 2)) /
          (Real.sqrt ((1 - p) / 2) * Real.sqrt ((1 - q) / 2))) :
    (1 + (p + q) / 2) / Real.sqrt ((1 + p) * (1 + q)) =
      (1 - (p + q) / 2) / Real.sqrt ((1 - p) * (1 - q)) := by
  have hplus : Real.sqrt ((1 + p) * (1 + q)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos (by linarith [hp.1]) (by linarith [hq.1])))
  have hminus : Real.sqrt ((1 - p) * (1 - q)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos (by linarith [hp.2]) (by linarith [hq.2])))
  rw [sqrt_half_product _ _ (by linarith [hp.1]),
    sqrt_half_product _ _ (by linarith [hp.2])] at h
  have hleft :
      (c / 2 * (1 + (p + q) / 2)) / (Real.sqrt ((1 + p) * (1 + q)) / 2) =
      c * ((1 + (p + q) / 2) / Real.sqrt ((1 + p) * (1 + q))) := by
    field_simp
  have hright :
      (c / 2 * (1 - (p + q) / 2)) / (Real.sqrt ((1 - p) * (1 - q)) / 2) =
      c * ((1 - (p + q) / 2) / Real.sqrt ((1 - p) * (1 - q))) := by
    field_simp
  rw [hleft, hright] at h
  exact mul_left_cancel₀ (ne_of_gt hc) h

/-- The actual posterior has constant absolute value once equality of its
normalized positive/negative component Gram matrices has been established.
The equality-of-Gram premise is discharged by the abstract trace-equality module.
@isnad1 id=eq.5h5v.s9.33b3e4b5dc2f from=translated src=- shape=3852324d vocab=844ad20b
-/
theorem posterior_abs_constant_of_component_gram {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hnonconstant : ∃ x z, f x ≠ f z)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1)
    (hgram : ∀ y z : Cube n,
      (plusVector f (cubeBSC n ρ hρ) y ⬝ᵥ plusVector f (cubeBSC n ρ hρ) z) /
        (Real.sqrt (plusVector f (cubeBSC n ρ hρ) y ⬝ᵥ plusVector f (cubeBSC n ρ hρ) y) *
          Real.sqrt (plusVector f (cubeBSC n ρ hρ) z ⬝ᵥ plusVector f (cubeBSC n ρ hρ) z)) =
      (minusVector f (cubeBSC n ρ hρ) y ⬝ᵥ minusVector f (cubeBSC n ρ hρ) z) /
        (Real.sqrt (minusVector f (cubeBSC n ρ hρ) y ⬝ᵥ minusVector f (cubeBSC n ρ hρ) y) *
          Real.sqrt (minusVector f (cubeBSC n ρ hρ) z ⬝ᵥ minusVector f (cubeBSC n ρ hρ) z))) :
    ∀ y z, |(cubeBSC n ρ hρ).apply f y| = |(cubeBSC n ρ hρ).apply f z| := by
  have hb := posterior_strict_bounds f hf hnonconstant ρ hρ hρlt
  apply Rigidity.abs_constant_of_normalized_edge_gram ((cubeBSC n ρ hρ).apply f) hb
  intro y i
  have hg := hgram y (Function.update y i (!(y i)))
  rw [plus_neighbor_inner f hf, minus_neighbor_inner f hf] at hg
  simp only [plus_norm_sq f hf, minus_norm_sq f hf] at hg
  have hc : 0 < root ρ := by
    unfold root
    apply Real.sqrt_pos.2
    nlinarith [hρ.1]
  have hh := normalized_gram_of_component_equality _ _ _ (hb y) (hb _) hc hg
  simpa only [add_comm, mul_comm] using hh

/--
@isnad1 id=ex.2h2v.s6.8f074c15b2e5 from=translated src=- shape=4b9d5e95 vocab=b92d6217
-/
theorem balanced_boolean_nonconstant {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hm : mean f = 0) :
    ∃ x z, f x ≠ f z := by
  by_contra! h
  let x₀ : Cube n := fun _ => false
  have hc : f = fun _ => f x₀ := funext (fun x => h x x₀)
  have hmean : mean f = f x₀ := calc
    mean f = mean (fun _ : Cube n => f x₀) := congrArg mean hc
    _ = f x₀ := mean_const _
  have hz : f x₀ = 0 := hmean.symm.trans hm
  rcases hf x₀ with hs | hs <;> linarith

/-- Once the actual posterior has constant absolute value, equality in the
Hellinger objective forces its actual second moment to be rho squared.
@isnad1 id=eq.5h3v.s8.4998b513f814 from=translated src=- shape=c6d0e653 vocab=88ecee5b
-/
theorem noise_second_moment_of_abs_constant_and_objective_eq {n : ℕ}
    (f : Cube n → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) (hm : mean f = 0)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (habs : ∀ y z, |(cubeBSC n ρ hρ).apply f y| = |(cubeBSC n ρ hρ).apply f z|)
    (hobj : objective ((cubeBSC n ρ hρ).apply f) = 1 - root ρ) :
    mean (fun x => ((cubeBSC n ρ hρ).apply f x) ^ 2) = ρ ^ 2 := by
  let x₀ : Cube n := fun _ => false
  have hsq (x : Cube n) :
      (cubeBSC n ρ hρ).apply f x ^ 2 = (cubeBSC n ρ hρ).apply f x₀ ^ 2 := by
    have h := congrArg (fun r : ℝ => r ^ 2) (habs x x₀)
    rw [_root_.sq_abs ((cubeBSC n ρ hρ).apply f x),
      _root_.sq_abs ((cubeBSC n ρ hρ).apply f x₀)] at h
    exact h
  have hroot (x : Cube n) :
      root ((cubeBSC n ρ hρ).apply f x) = root ((cubeBSC n ρ hρ).apply f x₀) := by
    unfold root
    rw [hsq x]
  have hmroot :
      mean (fun x => root ((cubeBSC n ρ hρ).apply f x)) =
        root ((cubeBSC n ρ hρ).apply f x₀) := by
    simp only [hroot, mean_const]
  unfold objective at hobj
  rw [UniformChannel.mean_apply, hm, hmroot] at hobj
  have hr0 : root (0 : ℝ) = 1 := by norm_num [root]
  rw [hr0] at hobj
  have hr : root ((cubeBSC n ρ hρ).apply f x₀) = root ρ := by linarith
  have hb := (cubeBSC n ρ hρ).apply_mem_Icc f
    (fun x => by rcases hf x with h | h <;> norm_num [h]) x₀
  have hp : 0 ≤ 1 - (cubeBSC n ρ hρ).apply f x₀ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (show 0 ≤ 1 + (cubeBSC n ρ hρ).apply f x₀ by linarith [hb.1])]
  have hρsq : 0 ≤ 1 - ρ ^ 2 := by nlinarith [hρ.1, hρ.2]
  have hp2 : root ((cubeBSC n ρ hρ).apply f x₀) ^ 2 =
      1 - (cubeBSC n ρ hρ).apply f x₀ ^ 2 := Real.sq_sqrt hp
  have hρ2 : root ρ ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt hρsq
  rw [hr] at hp2
  have heq : (cubeBSC n ρ hρ).apply f x₀ ^ 2 = ρ ^ 2 := by linarith
  simp only [hsq, heq, mean_const]

/-- Equality in actual BSC lifting forces constant absolute posterior.
The trace-equality theorem constructs the common contraction and proves the
Gram identity; no contraction or Gram condition is an input here.
@isnad1 id=eq.5h5v.s9.9bb52045198d from=translated src=- shape=b321127f vocab=70275a6f
-/
theorem posterior_abs_constant_of_lifting_equality {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hnonconstant : ∃ x z, f x ≠ f z)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1)
    (heq : TraceNorm.traceNorm
      (averageProjection (cubeBSC n ρ hρ) -
        reflection f * averageProjection (cubeBSC n ρ hρ) * reflection f) / 2 =
        mean (fun y => root ((cubeBSC n ρ hρ).apply f y))) :
    ∀ y z, |(cubeBSC n ρ hρ).apply f y| = |(cubeBSC n ρ hρ).apply f z| := by
  apply posterior_abs_constant_of_component_gram f hf hnonconstant ρ hρ hρlt
  have hnorm := component_norms_pos f hf hnonconstant ρ hρ hρlt
  have hcross := cross_equality_of_lifting_equality f hf (cubeBSC n ρ hρ) heq
  intro y z
  exact TraceEquality.weighted_cross_trace_equality_gram
    (fun _ : Cube n => (Fintype.card (Cube n) : ℝ)⁻¹)
    (plusVector f (cubeBSC n ρ hρ)) (minusVector f (cubeBSC n ρ hρ))
    (fun _ => by positivity) (fun y => (hnorm y).1) (fun y => (hnorm y).2)
    hcross y z

/--
@isnad1 id=eq.5h5v.s8.4365e43111a8 from=translated src=- shape=5ab1973d vocab=3864f693
-/
theorem bsc_posterior_abs_constant_of_lifting_equality {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hnonconstant : ∃ x z, f x ≠ f z)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1)
    (heq : TraceNorm.traceNorm
      (ProductState.state n (root ρ) -
        reflection f * ProductState.state n (root ρ) * reflection f) / 2 =
        mean (fun y => root ((cubeBSC n ρ hρ).apply f y))) :
    ∀ y z, |(cubeBSC n ρ hρ).apply f y| = |(cubeBSC n ρ hρ).apply f z| := by
  apply posterior_abs_constant_of_lifting_equality f hf hnonconstant ρ hρ hρlt
  simpa only [cube_averageProjection] using heq

/-- The actual lifting and Hellinger equalities imply the full Boolean
signed-dictator classification. Every Fourier and Gram step is discharged.
@isnad1 id=ex.7h3v.s9.4ed695e4c917 from=translated src=- shape=1bef508d vocab=3371f0d9
-/
theorem signed_dictator_of_lifting_and_objective_equality {n : ℕ} (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hm : mean f = 0)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (hlift : TraceNorm.traceNorm
      (ProductState.state n (root ρ) -
        reflection f * ProductState.state n (root ρ) * reflection f) / 2 =
        mean (fun y => root ((cubeBSC n ρ hρ).apply f y)))
    (hobj : objective ((cubeBSC n ρ hρ).apply f) = 1 - root ρ) :
    ∃ i : Fin n, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
      ∀ x, f x = a * boolSign (x i) := by
  have habs := bsc_posterior_abs_constant_of_lifting_equality f hf
    (balanced_boolean_nonconstant f hf hm) ρ hρ hρlt hlift
  exact Fourier.signed_dictator_of_noise_equality f hf hm ρ hρ hρpos hρlt
    (noise_second_moment_of_abs_constant_and_objective_eq f hf hm ρ hρ habs hobj)

/-- A signed dictator that reverses sign under a specified input translation
must use a coordinate in that translation's actual support.
@isnad1 id=mem.3h5v.s6.10d0283105bb from=translated src=- shape=9d731410 vocab=eb9f96f1
-/
theorem signed_dictator_coordinate_in_support {n : ℕ} (f : Cube n → ℝ)
    (i : Fin n) (a : ℝ) (ha : a = 1 ∨ a = -1)
    (hform : ∀ x, f x = a * boolSign (x i)) (v : Cube n)
    (hv : ∀ x, f (translate v x) = -f x) : i ∈ support v := by
  have h := hv (fun _ => false)
  rw [hform, hform] at h
  cases hvi : v i
  · simp [translate, hvi, boolSign] at h
    rcases ha with ha | ha <;> linarith
  · simp [support, hvi]

end Hellinger.PosteriorGram
