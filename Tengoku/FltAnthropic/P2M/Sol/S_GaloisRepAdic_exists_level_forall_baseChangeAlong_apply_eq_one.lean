import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_exists_level_forall_baseChangeAlong_apply_eq_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_exists_level_forall_baseChangeAlong_apply_eq_one

set_option autoImplicit false

/--
@isnad1 id=ex.0h3v.s11.879d14ec58e2 from=translated src=- shape=6d0e7a87 vocab=195a80c7
-/
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (K : ℕ) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ {B : Type} [CommRing B] [IsLocalRing B] (f : A →+* B) (hf : IsLocalHom f),
        (∀ a ∈ IsLocalRing.maximalIdeal A ^ K, f a = 0) →
        ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, s x = x) →
          (ρ.baseChangeAlong f hf).ρ s = 1 := by
  obtain ⟨L, hL, h1⟩ := ρ.isAdicContinuous K
  refine ⟨L, hL, fun {B} _ _ f hf hK s hs => ?_⟩
  letI : Algebra A B := f.toAlgebra
  have hkill : ∀ x ∈ (IsLocalRing.maximalIdeal A ^ K) • (⊤ : Submodule A ρ.V), ∀ b : B,
      TensorProduct.tmul A b x = (0 : TensorProduct A B ρ.V) := by
    intro x hx b
    refine Submodule.smul_induction_on
      (p := fun x => TensorProduct.tmul A b x = (0 : TensorProduct A B ρ.V)) hx ?_ ?_
    · intro a ha w _
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
        RingHom.algebraMap_toAlgebra, hK a ha, zero_mul, TensorProduct.zero_tmul]
    · intro x y hx hy
      rw [TensorProduct.tmul_add, hx, hy, add_zero]
  refine LinearMap.ext fun w => ?_
  show (ρ.ρ s).baseChange B w = w
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | tmul b v =>
    rw [LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub]
    exact hkill _ (h1 s hs v) b
  | add x y hx hy => rw [map_add, hx, hy]
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
