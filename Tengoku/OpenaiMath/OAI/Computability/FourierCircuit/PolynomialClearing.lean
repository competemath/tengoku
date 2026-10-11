import Tengoku.OpenaiMath.OAI.Computability.FourierCircuit.BoundaryActiveCircuit

namespace OAI

section
namespace ExactFourier
open TensorAxis CoefficientTime
open scoped Kronecker
namespace Boundary
variable {α : Type} [Fintype α] [DecidableEq α]

end Boundary
end ExactFourier

end

section
/-! Exact finite Taylor change of coefficient basis. -/
namespace ExactFourier.Taylor
open Polynomial
open scoped BigOperators Kronecker

noncomputable def matrix (t : ℕ) (s : ℂ) : Matrix (Fin t) (Fin t) ℂ :=
  fun a b => (taylor s (X^b.val : Polynomial ℂ)).coeff a.val

@[simp] theorem matrix_zero (t : ℕ) : matrix t 0=1 := by
  ext i j
  simp only [matrix,taylor_zero,coeff_X_pow,Matrix.one_apply]
  simp [Fin.ext_iff]

theorem taylor_modulus (t : ℕ) (s : ℂ) :
    taylor s ((X-C s)^t : Polynomial ℂ)=X^t := by simp

variable {α : Type} [Fintype α] [DecidableEq α]

noncomputable def translate (s : ℂ) (G : Matrix α α (Polynomial ℂ)) : Matrix α α (Polynomial ℂ) :=
  G.map (taylor s)

end ExactFourier.Taylor

end

section
namespace ExactFourier.Taylor
open Polynomial CoefficientTime
open scoped Kronecker

noncomputable def kernel (s : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun j => s^j/(j.factorial:ℂ))

@[simp] theorem kernel_constant (s : ℂ) : PowerSeries.constantCoeff (kernel s)=1 := by
  simp [kernel]

variable {α : Type} [Fintype α] [DecidableEq α]

end ExactFourier.Taylor

end

section
namespace ExactFourier.CellPoly
open Polynomial
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def feedback (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (s : ℂ) : Matrix α α ℂ :=
  M+s•(C*(1-s•D)⁻¹*B)

@[simp] theorem eval_Z
    {β : Type} [Fintype β] [DecidableEq β] (D : Matrix β β ℂ) (s : ℂ) :
    (Z D).map (evalRingHom s)=1-s•D := by
  rw [Z,Matrix.map_sub _ (map_sub (evalRingHom s)),map_smul,
    Matrix.map_one _ (map_zero (evalRingHom s)) (map_one (evalRingHom s))]
  simp only [coe_evalRingHom,eval_X]
  congr 2
  ext i j
  exact eval_C

@[simp] theorem eval_a (D : Matrix β β ℂ) (s : ℂ) : (a D).eval s=(1-s•D).det := by
  change evalRingHom s ((Z D).det)=_
  rw [RingHom.map_det,RingHom.mapMatrix_apply,eval_Z]

@[simp] theorem eval_R (D : Matrix β β ℂ) (s : ℂ) :
    (R D).map (evalRingHom s)=(1-s•D).adjugate := by
  change (evalRingHom s).mapMatrix (Z D).adjugate=_
  rw [RingHom.map_adjugate,RingHom.mapMatrix_apply,eval_Z]

theorem adjugate_eq_det_smul_inv (A : Matrix β β ℂ) (hA : IsUnit A) :
    A.adjugate=A.det•A⁻¹ := by
  have h := congrArg (fun Q : Matrix β β ℂ => Q*A⁻¹) (Matrix.adjugate_mul A)
  rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),mul_one,
    Matrix.smul_mul,one_mul] at h
  exact h

theorem eval_F
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (s : ℂ)
    (hD : IsUnit (1-s•D)) :
    (F M C B D).map (evalRingHom s)=(a D).eval s • feedback M C B D s := by
  rw [F,Matrix.map_add _ (map_add (evalRingHom s)),map_smul,map_smul,
    Matrix.map_mul,Matrix.map_mul,eval_R]
  have hconst {ι κ : Type} (X : Matrix ι κ ℂ) : (X.map Polynomial.C).map (evalRingHom s)=X := by ext i j; simp
  rw [hconst,hconst,hconst,adjugate_eq_det_smul_inv _ hD]
  simp only [coe_evalRingHom,eval_X,eval_a,feedback,smul_add,Matrix.mul_smul,Matrix.smul_mul]
  congr 1
  exact smul_comm _ _ _

end ExactFourier.CellPoly

end

section
/-! The real limit used by the boundary comparison argument. Only the fixed real
prices are compared; no continuity of a price functional is used. -/
namespace ExactFourier
open Filter Topology

noncomputable def boundaryError (m : ℕ) : ℝ :=
  Real.log (2*((m:ℝ)+2)^8)/((m:ℝ)+1) +
    ((m:ℝ)+2)^6/(((m:ℝ)+2)^8*((m:ℝ)+1))

theorem boundaryError_tendsto : Tendsto boundaryError atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun m : ℕ => (m:ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hi1 : Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h1
  have hi2 : Tendsto (fun m : ℕ => 1/((m:ℝ)+2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h2
  have hl : Tendsto (fun m : ℕ => Real.log ((m:ℝ)+2)/((m:ℝ)+2)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp h2
  have ha := (hi1.const_mul (Real.log 2)).add
    ((hl.mul ((tendsto_const_nhds (x := (1:ℝ))).add hi1)).const_mul 8)
  have hb := ha.add ((hi2.pow 2).mul hi1)
  simp only [mul_zero,zero_mul,add_zero] at hb
  convert hb using 1
  funext m
  have hn1 : (m:ℝ)+1 ≠ 0 := by positivity
  have hn2 : (m:ℝ)+2 ≠ 0 := by positivity
  dsimp [boundaryError]
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (pow_ne_zero _ hn2),Real.log_pow]
  field_simp
  ring

theorem fixed_price_of_boundary (x y C : ℝ)
    (h : ∀ k t : ℕ, 0 < k → 0 < t →
      (t:ℝ)*k*(x-y) ≤ C*((t:ℝ)*Real.log (2*t)+(k+1:ℝ)^6)) : x ≤ y := by
  have he (m : ℕ) : x-y ≤ C*boundaryError m := by
    have hh := h (m+1) ((m+2)^8) (by omega) (by positivity)
    push_cast at hh
    have ht : 0 < ((m:ℝ)+2)^8*((m:ℝ)+1) := by positivity
    have hh' : x-y ≤ (C*(((m:ℝ)+2)^8*Real.log (2*((m:ℝ)+2)^8)+((m:ℝ)+2)^6)) / (((m:ℝ)+2)^8*((m:ℝ)+1)) :=
      (le_div_iff₀ ht).mpr (by nlinarith only [hh])
    convert hh' using 1 ; dsimp [boundaryError] ; field_simp
  have hh := ge_of_tendsto (boundaryError_tendsto.const_mul C) (Filter.Eventually.of_forall he)
  have : x-y ≤ 0 := by simpa using hh
  linarith

end ExactFourier

end

section
/-! The literal feedback law; the state block D is not assumed invertible.
The limiting inequalities compare fixed matrix prices, never their continuity. -/
namespace ExactFourier.MatrixPrice
open TensorAxis CoefficientTime Polynomial
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

end ExactFourier.MatrixPrice

end

end OAI
