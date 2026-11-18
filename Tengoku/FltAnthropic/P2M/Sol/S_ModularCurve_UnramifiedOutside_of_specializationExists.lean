import Tengoku.FltAnthropic.Definitions.Def_HeckeGalois_EichlerShimura

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_UnramifiedOutside_of_specializationExists.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_UnramifiedOutside_of_specializationExists

open ModularCurve

/--
@isnad1 id=unramifi.1h5v.s8.e6d64c435643 from=translated src=- shape=0d3e7f3f vocab=ff2ce1a0
-/
theorem solution {K L : Type*} [Field K] [Field L] [Algebra K L] (N p : ℕ) (J : Type*)
    [AddCommGroup J] [Module ModularCurve.HeckeAlg J] [DistribMulAction (L ≃ₐ[K] L) J]
    [SMulCommClass (L ≃ₐ[K] L) ModularCurve.HeckeAlg J]
    (h : ModularCurve.SpecializationExists (K := K) (L := L) N p J) :
    ModularCurve.UnramifiedOutside (K := K) (L := L) N p J := by
  intro ℓ hℓ hℓN A hA σ hσ x hx
  obtain ⟨J', _, _, sp, F, hsp, -⟩ := h ℓ hℓ hℓN A hA
  have hker : sp (σ • x - x) = 0 := by
    rw [map_sub, hsp.inertia_comm σ hσ x, sub_self]
  have htor : ∃ n : ℕ, p ^ n • (σ • x - x) = 0 := by
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    rw [smul_sub, hn, smul_comm, hn, smul_zero, sub_zero]
  exact sub_eq_zero.mp (hsp.injective_torsion _ htor hker)
