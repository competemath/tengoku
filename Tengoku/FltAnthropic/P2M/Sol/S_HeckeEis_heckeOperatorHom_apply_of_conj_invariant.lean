import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.FltAnthropic.Theorems.Thm_HeckeEis_coresHom_resHom_apply

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_heckeOperatorHom_apply_of_conj_invariant.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_heckeOperatorHom_apply_of_conj_invariant

open CongruenceSubgroup Subgroup

theorem solution (N ℓ : ℕ) [NeZero ℓ] {A : Type*}
    [AddCommGroup A] (φ : Additive ↥(Gamma0 N) →+ A)
    (hφ : ∀ γ : ↥(HeckeEis.heckeUpper N ℓ),
      φ (Additive.ofMul ((HeckeEis.heckeConj N ℓ) γ)) = φ (Additive.ofMul ↑γ))
    (g : Additive ↥(Gamma0 N)) :
    HeckeEis.heckeOperatorHom N ℓ A φ g = (HeckeEis.heckeUpper N ℓ).index • φ g := by
  have hpb : HeckeEis.pullbackHom (HeckeEis.heckeConj N ℓ) φ =
      HeckeEis.resHom (HeckeEis.heckeUpper N ℓ) φ := by
    ext γ
    exact hφ γ
  show HeckeEis.coresHom (HeckeEis.heckeUpper N ℓ)
    (HeckeEis.pullbackHom (HeckeEis.heckeConj N ℓ) φ) g = _
  rw [hpb]
  exact HeckeEis.coresHom_resHom_apply (HeckeEis.heckeUpper N ℓ) φ g.toMul
