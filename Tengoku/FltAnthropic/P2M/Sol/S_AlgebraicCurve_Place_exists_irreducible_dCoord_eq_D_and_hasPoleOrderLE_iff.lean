import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_LogDeRhamH1

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_exists_irreducible_dCoord_eq_D_and_hasPoleOrderLE_iff

set_option autoImplicit false
open KaehlerDifferential

/--
@isnad1 id=ex.0h3v.s9.06ffb6a98ea9 from=translated src=- shape=f94bd64b vocab=828a9bdb
-/
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) :
    ∃ π : v.toValuationSubring, Irreducible π ∧
      v.dCoord = KaehlerDifferential.D K F (π : F) ∧
      (∀ (n : ℕ) (ω : Ω[F⁄K]), v.HasPoleOrderLE n ω ↔
        ∃ f : F, (π : F) ^ n * f ∈ v.toValuationSubring ∧ ω = f • v.dCoord) ∧
      (∀ (n : ℕ) (g : F), v.FnPoleOrderLE n g ↔ (π : F) ^ n * g ∈ v.toValuationSubring) ∧
      (∀ (ω : Ω[F⁄K]) (a : K), v.HasLogResidue ω a ↔
        ∃ f : F, ω = f • v.dCoord ∧ v.HasValue ((π : F) * f) a) := by
  exact ⟨_, (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec, rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩
