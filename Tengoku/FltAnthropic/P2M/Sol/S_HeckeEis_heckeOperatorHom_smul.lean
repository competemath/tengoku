import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_heckeOperatorHom_smul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_heckeOperatorHom_smul

open CongruenceSubgroup Subgroup

/--
@isnad1 id=eq.0h6v.s16.8cf64df6875a from=translated src=- shape=ac39427a vocab=a8fc7985
-/
theorem solution (N ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]
    {R : Type*} [Monoid R] [DistribMulAction R A] (r : R)
    (φ : Additive ↥(Gamma0 N) →+ A) :
    HeckeEis.heckeOperatorHom N ℓ A (r • φ) =
      r • HeckeEis.heckeOperatorHom N ℓ A φ := by
  ext g
  letI := (HeckeEis.heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  show (∑ q : ↥(Gamma0 N) ⧸ HeckeEis.heckeUpper N ℓ, (r • φ) _) =
    r • (∑ q : ↥(Gamma0 N) ⧸ HeckeEis.heckeUpper N ℓ, φ _)
  simp only [AddMonoidHom.smul_apply]
  exact Finset.smul_sum.symm
