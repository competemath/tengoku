import Tengoku.FltAnthropic.Definitions.Def_SwdAlgebra
import Tengoku.FltAnthropic.Definitions.Def_CuspForm_ModPForms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModPForms_thetaPS_not_mem_of_sub_smul_mem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModPForms_thetaPS_not_mem_of_sub_smul_mem

set_option autoImplicit false

/--
@isnad1 id=not.4h5v.s10.f2c2bb3fa986 from=translated src=- shape=ce06f8a8 vocab=843fed21
-/
theorem solution (p : ℕ) (F : Type) [Field F] [CharP F p]
    (M : ℤ → Submodule F (PowerSeries F)) (k : ℤ) (hpk : ¬ (p : ℤ) ∣ k) (φ : PowerSeries F)
    (hserre : (12 : F) • ModPForms.thetaPS φ - (k : F) • (SwdAlgebra.qP F * φ) ∈ M (k + 2))
    (hkatz : SwdAlgebra.qP F * φ ∈ M (k + 2) → φ ∈ M (k - ((p : ℤ) - 1)))
    (hlow : φ ∉ M (k - ((p : ℤ) - 1))) :
    ModPForms.thetaPS φ ∉ M (k + 2) := by
  intro hθ
  apply hlow
  apply hkatz
  have hk : ((k : ℤ) : F) ≠ 0 := by
    rw [Ne, CharP.intCast_eq_zero_iff F p]
    exact hpk
  have h1 : (k : F) • (SwdAlgebra.qP F * φ) ∈ M (k + 2) := by
    have := (M (k + 2)).sub_mem ((M (k + 2)).smul_mem (12 : F) hθ) hserre
    rwa [sub_sub_cancel] at this
  have h2 := (M (k + 2)).smul_mem ((k : F)⁻¹) h1
  rwa [smul_smul, inv_mul_cancel₀ hk, one_smul] at h2
