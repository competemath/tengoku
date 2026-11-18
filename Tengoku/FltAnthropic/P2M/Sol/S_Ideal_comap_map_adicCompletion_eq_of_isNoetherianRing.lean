import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_comap_map_adicCompletion_eq_of_isNoetherianRing.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ideal_comap_map_adicCompletion_eq_of_isNoetherianRing

set_option autoImplicit false

/--
@isnad1 id=faithful.0h1v.s6.85028dee5ad7 from=translated src=- shape=d7071ce9 vocab=eca1334a
-/
theorem Ws34.faithfullyFlat_adicCompletion_maximalIdeal (S : Type*) [CommRing S] [IsNoetherianRing S]
    [IsLocalRing S] : Module.FaithfullyFlat S (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
  rw [Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top]
  refine ⟨inferInstance, fun I hI => ?_⟩
  by_contra hne
  have hle : I ≤ IsLocalRing.maximalIdeal S := IsLocalRing.le_maximalIdeal hne

  have h1 : (IsLocalRing.maximalIdeal S • (⊤ : Submodule S (AdicCompletion (IsLocalRing.maximalIdeal S) S))) ≤
      LinearMap.ker (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) 1).toLinearMap := by
    rw [Submodule.smul_le]
    intro r hr x _
    rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [pow_one]; exact hr), zero_mul]
  have htop : (⊤ : Submodule S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) ≤
      LinearMap.ker (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) 1).toLinearMap := by
    rw [← hI]
    exact (Submodule.smul_mono hle le_rfl).trans h1
  have h0 : (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) 1) 1 = 0 := htop Submodule.mem_top
  rw [map_one] at h0
  have hne1 : (IsLocalRing.maximalIdeal S ^ 1 : Ideal S) ≠ ⊤ := by
    rw [pow_one]; exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  exact (Ideal.Quotient.zero_ne_one_iff.mpr hne1) h0.symm

/--
@isnad1 id=eq.0h2v.s9.0c2beee20e0e from=translated src=- shape=ee2cda4e vocab=03932625
-/
theorem solution
    {S : Type*} [CommRing S] [IsNoetherianRing S] [IsLocalRing S] (𝔞 : Ideal S) :
    (𝔞.map (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S))).comap
        (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) = 𝔞 := by
  haveI := Ws34.faithfullyFlat_adicCompletion_maximalIdeal S
  exact Ideal.comap_map_eq_self_of_faithfullyFlat 𝔞
