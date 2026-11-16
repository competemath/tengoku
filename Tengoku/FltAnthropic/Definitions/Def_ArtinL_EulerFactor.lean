import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_EllipticCurve_FrobeniusTrace
import Tengoku.FltAnthropic.Definitions.Def_Deformations_MatrixRepresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open Polynomial
open scoped MatrixGroups

namespace ArtinL

def charpolyRev {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (T : W →ₗ[K] W) : K[X] :=
  (LinearMap.toMatrix (Module.finBasis K W) (Module.finBasis K W) T).charpolyRev

section charpolyRev

variable {K W W' : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  [AddCommGroup W'] [Module K W'] [FiniteDimensional K W']

/--
@isnad1 id=eq.0h3v.s6.8560a15cca8e from=translated src=- shape=34d460b0 vocab=ae26a8f2
-/
theorem charpolyRev_eq_reverse_charpoly (T : W →ₗ[K] W) :
    charpolyRev T = (LinearMap.charpoly T).reverse := by
  rw [charpolyRev, ← Matrix.reverse_charpoly, LinearMap.charpoly_toMatrix]

/--
@isnad1 id=eq.0h5v.s9.bb3fac01d644 from=translated src=- shape=80e978b1 vocab=01f84d1b
-/
theorem charpolyRev_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K W)
    (T : W →ₗ[K] W) : (LinearMap.toMatrix b b T).charpolyRev = charpolyRev T := by
  rw [charpolyRev_eq_reverse_charpoly, ← Matrix.reverse_charpoly, LinearMap.charpoly_toMatrix]

/--
@isnad1 id=eq.0h3v.s6.9a57a0708fe9 from=translated src=- shape=733d8905 vocab=6049c972
-/
@[simp] theorem coeff_charpolyRev_zero (T : W →ₗ[K] W) : (charpolyRev T).coeff 0 = 1 := by
  rw [charpolyRev, coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

/--
@isnad1 id=eq.0h3v.s9.8c21565fd60a from=translated src=- shape=8853ede0 vocab=ed65387a
-/
@[simp] theorem coeff_charpolyRev_one (T : W →ₗ[K] W) :
    (charpolyRev T).coeff 1 = -LinearMap.trace K W T := by
  rw [charpolyRev, Matrix.coeff_charpolyRev_eq_neg_trace,
    LinearMap.trace_eq_matrix_trace K (Module.finBasis K W)]

/--
@isnad1 id=le.0h3v.s6.305a51cc22e9 from=translated src=- shape=563a0dd3 vocab=84f98e7a
-/
theorem natDegree_charpolyRev_le (T : W →ₗ[K] W) :
    (charpolyRev T).natDegree ≤ Module.finrank K W := by
  rw [charpolyRev_eq_reverse_charpoly]
  exact (reverse_natDegree_le _).trans (LinearMap.charpoly_natDegree T).le

/--
@isnad1 id=eq.0h5v.s9.d2fb0489af7d from=translated src=- shape=80846095 vocab=ef6b577c
-/
theorem charpolyRev_conj (e : W ≃ₗ[K] W') (T : W →ₗ[K] W) :
    charpolyRev (e.conj T) = charpolyRev T := by
  rw [charpolyRev_eq_reverse_charpoly, charpolyRev_eq_reverse_charpoly, LinearEquiv.charpoly_conj]

/--
@isnad1 id=ne.0h3v.s6.eda6f049d462 from=translated src=- shape=e84e9dc8 vocab=0c28290d
-/
theorem charpolyRev_ne_zero (T : W →ₗ[K] W) : charpolyRev T ≠ 0 := fun h => by
  simpa [h] using coeff_charpolyRev_zero T

/--
@isnad1 id=eq.0h3v.s6.02e1d3cd0e84 from=translated src=- shape=cd66156f vocab=81c4ea24
-/
theorem charpolyRev_mulVecLin {m : ℕ} (A : Matrix (Fin m) (Fin m) K) :
    charpolyRev (Matrix.mulVecLin A) = A.charpolyRev := by
  rw [← charpolyRev_toMatrix (Pi.basisFun K (Fin m)), ← Matrix.toLin'_apply',
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

end charpolyRev

variable {n : ℕ}

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def invariantsUnder (ρ : Γℚ →* GL (Fin n) ℂ) (H : Subgroup Γℚ) : Submodule ℂ (Fin n → ℂ) :=
  Representation.invariants ((Deformation.matrixRepresentation ρ).comp H.subtype)

abbrev inertiaInvariants (ρ : Γℚ →* GL (Fin n) ℂ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) : Submodule ℂ (Fin n → ℂ) :=
  invariantsUnder ρ (A.inertiaSubgroupIn ℚ)

open scoped Classical in

def eulerFactorAt (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (σ : Γℚ) : ℂ[X] :=
  if h : ∀ v ∈ inertiaInvariants ρ A,
      Deformation.matrixRepresentation ρ σ v ∈ inertiaInvariants ρ A then
    charpolyRev ((Deformation.matrixRepresentation ρ σ).restrict h)
  else 1

open scoped Classical in

def eulerFactor (ρ : Γℚ →* GL (Fin n) ℂ) (p : ℕ) : ℂ[X] :=
  if h : ∃ A : ValuationSubring (AlgebraicClosure ℚ), ∃ σ : Γℚ,
      A.LiesOverPrime p ∧ A.IsFrobeniusAt σ p then
    eulerFactorAt ρ h.choose h.choose_spec.choose
  else 1

def coeffPrimePow (ρ : Γℚ →* GL (Fin n) ℂ) (p k : ℕ) : ℂ :=
  PowerSeries.coeff k ((eulerFactor ρ p : PowerSeries ℂ)⁻¹)

def coeff (ρ : Γℚ →* GL (Fin n) ℂ) (m : ℕ) : ℂ :=
  if m = 0 then 0 else m.factorization.prod fun p k => coeffPrimePow ρ p k

def LSeries (ρ : Γℚ →* GL (Fin n) ℂ) (s : ℂ) : ℂ :=
  _root_.LSeries (coeff ρ) s

/--
@isnad1 id=eq.0h2v.s8.d9fc74c8db1a from=translated src=- shape=ee518122 vocab=907369bd
-/
@[simp] theorem coeff_zero (ρ : Γℚ →* GL (Fin n) ℂ) : coeff ρ 0 = 0 := by
  simp [coeff]

/--
@isnad1 id=eq.0h2v.s8.6fc671f81891 from=translated src=- shape=ee518122 vocab=907369bd
-/
@[simp] theorem coeff_one (ρ : Γℚ →* GL (Fin n) ℂ) : coeff ρ 1 = 1 := by
  simp [coeff]

/--
@isnad1 id=eq.0h4v.s8.3a2d96ee9db9 from=translated src=- shape=4ebe6023 vocab=b0625a6c
-/
@[simp] theorem coeff_eulerFactorAt_zero (ρ : Γℚ →* GL (Fin n) ℂ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : Γℚ) : (eulerFactorAt ρ A σ).coeff 0 = 1 := by
  unfold eulerFactorAt
  split_ifs <;> simp

/--
@isnad1 id=eq.0h3v.s8.b094e8895d58 from=translated src=- shape=3d072491 vocab=473c3852
-/
@[simp] theorem coeff_eulerFactor_zero (ρ : Γℚ →* GL (Fin n) ℂ) (p : ℕ) :
    (eulerFactor ρ p).coeff 0 = 1 := by
  unfold eulerFactor
  split_ifs <;> simp

end ArtinL

end
