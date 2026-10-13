import Tengoku.Degiorgi.DeGiorgi.Foundations

/-!
# Chapter 03: Coefficients

This chapter defines the elliptic coefficient structures used throughout the
development.

It uses a unified coefficient structure with measurable coefficients, lower
ellipticity on `a` and `a⁻¹`, and derived mixed and upper bounds recorded as
theorems rather than primitive fields.
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace DeGiorgi

/-- The ambient Euclidean space used by the elliptic regularity development. -/
abbrev AmbientSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Matrix action on the ambient Euclidean space. -/
def matMulE {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (ξ : AmbientSpace d) : AmbientSpace d :=
  WithLp.toLp 2 (Matrix.mulVec M ξ.ofLp)

/--
@isnad1 id=eq.0h3v.s6.e75b3cc00786 from=translated src=- shape=47073bc3 vocab=c0996c88
-/
@[simp] theorem matMulE_ofLp {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (ξ : AmbientSpace d) :
    (matMulE M ξ).ofLp = Matrix.mulVec M ξ.ofLp :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.e1cc757f89dd from=translated src=- shape=624f6d5c vocab=c0996c88
-/
@[simp] theorem matMulE_apply {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (ξ : AmbientSpace d) (i : Fin d) :
    matMulE M ξ i = Matrix.mulVec M ξ.ofLp i :=
  rfl

/-- Unified nonsymmetric elliptic coefficient field for the elliptic regularity
development.

It is designed to serve both:

- the variational / weak-solution branch, which needs measurability;
- the De Giorgi / Moser branch, which uses coercivity of `a⁻¹` to derive mixed
  and upper bounds.

The upper bounds are intentionally not primitive fields in this structure. -/
structure EllipticCoeff (d : ℕ) [NeZero d] (Ω : Set (AmbientSpace d)) where
  /-- Matrix-valued coefficient field. -/
  a : AmbientSpace d → Matrix (Fin d) (Fin d) ℝ
  /-- Lower ellipticity constant. -/
  lam : ℝ
  /-- Upper ellipticity constant. -/
  Λ : ℝ
  /-- Componentwise measurability of the coefficient field. -/
  measurable_comp : ∀ i j, Measurable (fun x => a x i j)
  /-- Positivity of the lower ellipticity constant. -/
  hlam : 0 < lam
  /-- Comparison of lower and upper ellipticity scales. -/
  hΛ : lam ≤ Λ
  /-- Coercivity on `a`, stated almost everywhere on `Ω`. -/
  coercive : ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
    lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE (a x) ξ⟫_ℝ
  /-- Coercivity on `a⁻¹`, stated almost everywhere on `Ω`. -/
  coercive_inv : ∀ᵐ x ∂(MeasureTheory.volume.restrict Ω), ∀ ξ : AmbientSpace d,
    Λ⁻¹ * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE ((a x)⁻¹) ξ⟫_ℝ

/-- The ellipticity ratio governing scale-invariant estimates. -/
def ellipticityRatio {d : ℕ} [NeZero d] {Ω : Set (AmbientSpace d)}
    (A : EllipticCoeff d Ω) : ℝ :=
  A.Λ / A.lam

/-- Optional normalized view of the unified coefficient structure. -/
abbrev NormalizedEllipticCoeff (d : ℕ) [NeZero d] (Ω : Set (AmbientSpace d)) :=
  {A : EllipticCoeff d Ω // A.lam = 1}

namespace EllipticCoeff

variable {d : ℕ} [NeZero d] {Ω : Set (AmbientSpace d)} (A : EllipticCoeff d Ω)

/--
@isnad1 id=eq.0h3v.s5.74e966199afc from=translated src=- shape=cdd96964 vocab=056affd5
-/
@[simp] theorem ellipticityRatio_def :
    ellipticityRatio A = A.Λ / A.lam := rfl

/--
@isnad1 id=le.0h3v.s5.140ce25fe463 from=translated src=- shape=cb420898 vocab=225bd0ab
-/
theorem lam_nonneg : 0 ≤ A.lam :=
  le_of_lt A.hlam

/--
@isnad1 id=lt.0h3v.s5.5ac874d45d97 from=translated src=- shape=cb420898 vocab=39b7f690
-/
theorem Λ_pos : 0 < A.Λ :=
  lt_of_lt_of_le A.hlam A.hΛ

/--
@isnad1 id=lt.0h3v.s5.aefcce4da387 from=translated src=- shape=cb420898 vocab=114ddb26
-/
theorem ellipticityRatio_pos : 0 < ellipticityRatio A := by
  dsimp [ellipticityRatio]
  exact div_pos A.Λ_pos A.hlam

/--
@isnad1 id=le.0h3v.s5.7b9d4d9969b6 from=translated src=- shape=cb420898 vocab=24c2b886
-/
theorem ellipticityRatio_nonneg : 0 ≤ ellipticityRatio A :=
  (A.ellipticityRatio_pos).le

/--
@isnad1 id=le.0h3v.s5.50c457065130 from=translated src=- shape=cb420898 vocab=24c2b886
-/
theorem one_le_ellipticityRatio : 1 ≤ ellipticityRatio A := by
  simpa [ellipticityRatio] using (one_le_div A.hlam).2 A.hΛ

end EllipticCoeff

namespace NormalizedEllipticCoeff

variable {d : ℕ} [NeZero d] {Ω : Set (AmbientSpace d)}
  (A : NormalizedEllipticCoeff d Ω)

/--
@isnad1 id=eq.0h3v.s5.0d02223d42ee from=translated src=- shape=bf73bb67 vocab=a95faa0f
-/
@[simp] theorem lam_eq_one : A.1.lam = 1 :=
  A.2

/--
@isnad1 id=eq.0h3v.s6.b50be5c7b341 from=translated src=- shape=d2cf5207 vocab=562b6229
-/
@[simp] theorem ellipticityRatio_eq_Λ :
    ellipticityRatio A.1 = A.1.Λ := by
  simp [ellipticityRatio]

end NormalizedEllipticCoeff

end DeGiorgi
