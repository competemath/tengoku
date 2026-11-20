import Tengoku.Hellingerrepolean4.Hellinger.SpinState
import Tengoku.Hellingerrepolean4.Hellinger.FourierProducts
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The explicit three-qubit reflection from the manuscript. Its trace
distance is computed from the concrete product state, and its failure of
Boolean multiplication structure is certified by two equal-XOR entries. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators MatrixOrder
open Matrix

namespace Hellinger.ReflectionCounterexample
open ProductState TraceNorm

/--
@isnad1 id=eq.0h2v.s6.d973be0f2678 from=translated src=- shape=f65cdd33 vocab=d5e91992
-/
theorem abs_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) :
    CFC.abs (Matrix.diagonal d) = Matrix.diagonal (fun i => |d i|) := by
  apply CFC.sqrt_unique
  · simp only [Matrix.diagonal_mul_diagonal, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, star_trivial]
    congr 1
    funext i
    exact abs_mul_abs_self (d i)
  · exact (Matrix.posSemidef_diagonal_iff.mpr (fun i => abs_nonneg (d i))).nonneg

/--
@isnad1 id=eq.0h2v.s5.7564bfd8de30 from=translated src=- shape=f6691694 vocab=9cef3a71
-/
theorem traceNorm_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) :
    traceNorm (Matrix.diagonal d) = ∑ i, |d i| := by
  rw [traceNorm, abs_diagonal, Matrix.trace_diagonal]

/--
@isnad1 id=eq.0h4v.s4.cf829b8e60e0 from=translated src=- shape=b7bdf0e7 vocab=fd0d1bcb
-/
theorem multiplication_xor (n : ℕ) (f : Cube n → ℝ) (s t : Cube n) :
    ParityBlocks.transformedReflection n f s t = Fourier.walsh f (Fourier.translate s t) := by
  simp only [ParityBlocks.transformedReflection, Unitary.conjStarAlgAut_apply,
    hadamardUnitary_coe, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, hadamard_transpose]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, ProductState.hadamard]
  calc
    (∑ x, (normalization n * Fourier.phase x s * f x) *
        (normalization n * Fourier.phase t x)) =
      normalization n ^ 2 * ∑ x, f x * Fourier.phase (Fourier.translate s t) x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [Fourier.phase_symm x s, ← FourierProducts.phase_product]
        ring
    _ = _ := by
      unfold Fourier.walsh mean
      rw [Fourier.cube_card]
      push_cast
      have hnorm := normalization_square n
      have hne : (2 : ℝ) ^ n ≠ 0 := by positivity
      have hn : normalization n ^ 2 = ((2 : ℝ) ^ n)⁻¹ := by
        rw [← one_div]
        apply (eq_div_iff hne).mpr
        exact hnorm
      rw [hn]

def threeBitsEquiv : Cube 3 ≃ Bool × Bool × Bool where
  toFun x := ⟨x 0, x 1, x 2⟩
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a, b, c⟩; rfl

/--
@isnad1 id=eq.0h2v.s7.17f1360c5c2b from=translated src=- shape=93fcb5f6 vocab=89ae159f
-/
theorem sum_three_bits {R : Type*} [AddCommMonoid R] (F : Cube 3 → R) :
    (∑ x, F x) = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, F ![a, b, c] := by
  rw [← threeBitsEquiv.symm.sum_comp F]
  simp [Fintype.sum_prod_type, threeBitsEquiv]

def pairSwap (x : Cube 3) : Cube 3 :=
  match x 0, x 1, x 2 with
  | false, false, false => ![false, false, true]
  | false, false, true => ![false, false, false]
  | false, true, false => ![true, false, false]
  | true, false, false => ![false, true, false]
  | false, true, true => ![true, true, true]
  | true, true, true => ![false, true, true]
  | true, false, true => ![true, true, false]
  | true, true, false => ![true, false, true]

/--
@isnad1 id=eq.0h3v.s5.c9cbed38dc1b from=translated src=- shape=d950ae09 vocab=2c47fde2
-/
@[simp] theorem vec3_last (a b c : Bool) : (![a, b, c] : Cube 3) 2 = c := rfl

/--
@isnad1 id=involuti.0h0v.s3.3339eb4bdbf6 from=translated src=- shape=06f63001 vocab=8097d9f4
-/
theorem pairSwap_involutive : Function.Involutive pairSwap := by
  unfold Function.Involutive
  decide

def pairing : Equiv.Perm (Cube 3) :=
  ⟨pairSwap, pairSwap, pairSwap_involutive, pairSwap_involutive⟩

/--
@isnad1 id=eq.0h1v.s6.997d363bc17a from=translated src=- shape=bf96346e vocab=759ee5a5
-/
@[simp] theorem pairing_apply (x : Cube 3) : pairing x = pairSwap x := rfl

/--
@isnad1 id=eq.0h3v.s6.88ccd0787409 from=translated src=- shape=696fc90a vocab=8d36a4fb
-/
theorem degree_three (a b c : Bool) :
    Fourier.degree ![a, b, c] =
      (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> decide

/--
@isnad1 id=ne.0h1v.s6.0aae480616d5 from=translated src=- shape=20edd117 vocab=3368b109
-/
theorem pairing_nofixed (x : Cube 3) : pairing x ≠ x := by
  have h : ∀ x : Cube 3, pairSwap x ≠ x := by decide
  exact h x

def fourierReflection : Matrix (Cube 3) (Cube 3) ℝ := pairing.permMatrix ℝ

/--
@isnad1 id=eq.0h0v.s4.474aaaae92a0 from=translated src=- shape=ed66abb5 vocab=da196db7
-/
theorem pairing_inv : pairing⁻¹ = pairing := rfl

/--
@isnad1 id=ishermit.0h0v.s5.f155f5c645f4 from=translated src=- shape=d3a93718 vocab=14a13cd3
-/
theorem fourierReflection_isHermitian : fourierReflection.IsHermitian := by
  simp [Matrix.IsHermitian, fourierReflection, pairing_inv]

/--
@isnad1 id=eq.0h0v.s7.a83ecdd629b6 from=translated src=- shape=af6c9ceb vocab=f4dd1084
-/
theorem fourierReflection_squared : fourierReflection * fourierReflection = 1 := by
  rw [fourierReflection, ← Matrix.permMatrix_mul]
  have h : pairing * pairing = 1 := by
    apply Equiv.ext
    intro x
    exact pairSwap_involutive x
  rw [h, Matrix.permMatrix_one]

/--
@isnad1 id=eq.0h2v.s7.28049fe2a0c0 from=translated src=- shape=947a7d83 vocab=cb91644b
-/
theorem fourierReflection_entry (x y : Cube 3) :
    fourierReflection x y = if pairing x = y then 1 else 0 := by
  simp [fourierReflection, Equiv.toPEquiv_apply]
  rfl

/--
@isnad1 id=eq.0h1v.s4.1cc47a970344 from=translated src=- shape=6e4c2516 vocab=ad04690c
-/
theorem fourierReflection_diagonal (x : Cube 3) : fourierReflection x x = 0 := by
  rw [fourierReflection_entry, ite_eq_right (pairing_nofixed x)]

/--
@isnad1 id=eq.0h1v.s8.b460be5c0f78 from=translated src=- shape=c383169e vocab=e69c01bc
-/
theorem conjugate_diagonal (d : Cube 3 → ℝ) :
    fourierReflection * Matrix.diagonal d * fourierReflection =
      Matrix.diagonal (fun x => d (pairing x)) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  ext x
  simp only [← Matrix.mulVec_mulVec, fourierReflection, Matrix.permMatrix_mulVec,
    Function.comp_apply, Matrix.mulVec_diagonal]
  change d (pairSwap x) * v (pairSwap (pairSwap x)) = d (pairSwap x) * v x
  rw [pairSwap_involutive]

/--
@isnad1 id=eq.1h1v.s9.421f9dad51e4 from=translated src=- shape=15d6c682 vocab=10692c49
-/
theorem fourier_trace_distance (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    traceNorm (Matrix.diagonal (eigenvalue 3 c) -
      fourierReflection * Matrix.diagonal (eigenvalue 3 c) * fourierReflection) / 2 =
        c * (1 + c ^ 2) / 2 := by
  rw [conjugate_diagonal, Matrix.diagonal_sub, traceNorm_diagonal, sum_three_bits]
  norm_num [Fintype.sum_bool, eigenvalue, degree_three, pairSwap, Matrix.cons_val]
  have h₁ : 0 ≤ ((1 + c) / 2) ^ 3 - ((1 + c) / 2) ^ 2 * ((1 - c) / 2) := by
    nlinarith [mul_nonneg hc.1 (sq_nonneg ((1 + c) / 2))]
  have h₂ : 0 ≤ (1 + c) / 2 * ((1 - c) / 2) ^ 2 - ((1 - c) / 2) ^ 3 := by
    nlinarith [mul_nonneg hc.1 (sq_nonneg ((1 - c) / 2))]
  rw [abs_sub_comm (((1 - c) / 2) ^ 3),
    abs_sub_comm (((1 + c) / 2) ^ 2 * ((1 - c) / 2)),
    abs_of_nonneg h₁, abs_of_nonneg h₂]
  ring

def reflection : Matrix (Cube 3) (Cube 3) ℝ :=
  Unitary.conjStarAlgAut ℝ _ (hadamardUnitary 3) fourierReflection

/--
@isnad1 id=eq.0h2v.s14.f54395c04650 from=translated src=- shape=97152108 vocab=01e66624
-/
theorem hadamard_conjugate_involution (n : ℕ) (A : Matrix (Cube n) (Cube n) ℝ) :
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n)
      (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) A) = A := by
  simp only [Unitary.conjStarAlgAut_apply, hadamardUnitary_coe,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    hadamard_transpose]
  simp only [← Matrix.mul_assoc, hadamard_squared, Matrix.one_mul]
  rw [Matrix.mul_assoc, hadamard_squared, Matrix.mul_one]

/--
@isnad1 id=ishermit.0h0v.s5.70650f64bbc5 from=translated src=- shape=d3a93718 vocab=8e69f19d
-/
theorem reflection_isHermitian : reflection.IsHermitian := by
  change star reflection = reflection
  rw [reflection, ← map_star]
  congr 1
  exact fourierReflection_isHermitian

/--
@isnad1 id=eq.0h0v.s7.a34238e5fab0 from=translated src=- shape=af6c9ceb vocab=9722b19a
-/
theorem reflection_squared : reflection * reflection = 1 := by
  rw [reflection, ← map_mul, fourierReflection_squared, map_one]

/--
@isnad1 id=eq.0h1v.s14.40e2c0c117ce from=translated src=- shape=e1d29759 vocab=fa9f95c8
-/
theorem reflection_fourier_diagonal (x : Cube 3) :
    (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary 3) reflection) x x = 0 := by
  rw [reflection, hadamard_conjugate_involution, fourierReflection_diagonal]

/--
@isnad1 id=eq.1h1v.s8.36720b1a7f6e from=translated src=- shape=657efce3 vocab=59e6640c
-/
theorem reflection_trace_distance (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    traceNorm (state 3 c - reflection * state 3 c * reflection) / 2 =
      c * (1 + c ^ 2) / 2 := by
  rw [← traceNorm_conjugate (hadamardUnitary 3)]
  rw [map_sub, map_mul, map_mul, ParityBlocks.transformed_state,
    reflection, hadamard_conjugate_involution]
  exact fourier_trace_distance c hc

/--
@isnad1 id=ne.0h1v.s5.bb9b11aae680 from=translated src=- shape=e9b1c854 vocab=2c36e396
-/
theorem fourierReflection_not_multiplication (f : Cube 3 → ℝ) :
    fourierReflection ≠ ParityBlocks.transformedReflection 3 f := by
  intro h
  have h₁ := congrArg (fun M : Matrix (Cube 3) (Cube 3) ℝ =>
    M ![false, false, false] ![false, false, true]) h
  have h₂ := congrArg (fun M : Matrix (Cube 3) (Cube 3) ℝ =>
    M ![false, true, false] ![false, true, true]) h
  rw [fourierReflection_entry, multiplication_xor] at h₁ h₂
  have hs : Fourier.translate ![false, false, false] ![false, false, true] =
      Fourier.translate ![false, true, false] ![false, true, true] := by decide
  rw [hs] at h₁
  norm_num [pairSwap, Matrix.cons_val, show
    (![true, false, false] : Cube 3) ≠ ![false, true, true] from by decide] at h₁ h₂
  linarith

/--
@isnad1 id=ne.0h1v.s6.f8e28a460691 from=translated src=- shape=8dcf7c28 vocab=574eede1
-/
theorem reflection_not_multiplication (f : Cube 3 → ℝ) :
    reflection ≠ Matrix.diagonal f := by
  intro h
  have hh := congrArg (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary 3)) h
  rw [reflection, hadamard_conjugate_involution] at hh
  exact fourierReflection_not_multiplication f hh

/--
@isnad1 id=ex.1h1v.s14.6a5a6ada6363 from=translated src=- shape=6b04e8a7 vocab=07048917
-/
theorem reflection_counterexample (c : ℝ) (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ P : Matrix (Cube 3) (Cube 3) ℝ,
      P.IsHermitian ∧ P * P = 1 ∧
      (∀ x, (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary 3) P) x x = 0) ∧
      traceNorm (state 3 c - P * state 3 c * P) / 2 = c * (1 + c ^ 2) / 2 ∧
      c * (1 + c ^ 2) / 2 < c ∧ (∀ f : Cube 3 → ℝ, P ≠ Matrix.diagonal f) := by
  refine ⟨reflection, reflection_isHermitian, reflection_squared,
    reflection_fourier_diagonal, reflection_trace_distance c ⟨hc.1.le, hc.2.le⟩,
    ?_, reflection_not_multiplication⟩
  have hs : c ^ 2 < 1 := by nlinarith [mul_lt_mul_of_pos_left hc.2 hc.1, hc.2]
  nlinarith [mul_pos hc.1 (sub_pos.mpr hs)]

end Hellinger.ReflectionCounterexample
