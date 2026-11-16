import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_faithfulSMul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_faithfulSMul

/--
@isnad1 id=isintegr.0h2v.s5.e05adb1c0b10 from=translated src=- shape=ef068099 vocab=4dbce9f8
-/
theorem solution
    (A F : Type*) [CommRing A] [IsDomain A] [Field F] [Algebra A F] [FaithfulSMul A F]
    [IsIntegrallyClosedIn A F] : IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  have hinj : Function.Injective (algebraMap A F) := FaithfulSMul.algebraMap_injective A F
  let φ : FractionRing A →ₐ[A] F :=
    { IsFractionRing.lift hinj with
      commutes' := fun a => by simp [IsFractionRing.lift_algebraMap] }
  have hφ : ∀ y, φ y = IsFractionRing.lift hinj y := fun _ => rfl
  have hx' : IsIntegral A (φ x) := hx.map φ
  obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hx'
  refine ⟨a, ?_⟩
  apply (IsFractionRing.lift hinj : FractionRing A →+* F).injective
  rw [IsFractionRing.lift_algebraMap, ← hφ]
  exact ha
