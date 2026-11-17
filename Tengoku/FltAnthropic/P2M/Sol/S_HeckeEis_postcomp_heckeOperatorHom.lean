import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_postcomp_heckeOperatorHom.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_postcomp_heckeOperatorHom

open CongruenceSubgroup Subgroup

/--
@isnad1 id=eq.0h6v.s16.56690a1a16c2 from=translated src=- shape=e6bc3762 vocab=fef0d9af
-/
theorem solution (N ℓ : ℕ) [NeZero ℓ] {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (f : A →+ B) (φ : Additive ↥(Gamma0 N) →+ A) :
    f.comp (HeckeEis.heckeOperatorHom N ℓ A φ) =
      HeckeEis.heckeOperatorHom N ℓ B (f.comp φ) := by
  ext g
  letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  exact map_sum f _ _
