import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_FaithfullyFlat_of_forall_isMaximal_exists_ringHom_field.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_FaithfullyFlat_of_forall_isMaximal_exists_ringHom_field

set_option autoImplicit false

universe u v w

namespace KatzDescFF

/--
@isnad1 id=faithful.1h2v.s8.bb3dd9481aba from=translated src=- shape=834caae4 vocab=c3866444
-/
theorem faithfullyFlat_of_exists_ringHom_field' {B : Type u} {S : Type v} [CommRing B]
    [CommRing S] [Algebra B S] [Module.Flat B S]
    (h : ∀ m : Ideal B, m.IsMaximal →
      ∃ (K : Type w) (_ : Field K) (ψ : S →+* K), m ≤ RingHom.ker (ψ.comp (algebraMap B S))) :
    Module.FaithfullyFlat B S := by
  rw [Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top]
  refine ⟨inferInstance, fun I hI => ?_⟩
  by_contra hne
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
  obtain ⟨K, _, ψ, hker⟩ := h m hm
  have h1 : (1 : S) ∈ Ideal.map (algebraMap B S) m := by
    have hle : I • (⊤ : Submodule B S) ≤ m • ⊤ := Submodule.smul_mono_left hIm
    rw [hI, top_le_iff, Ideal.smul_top_eq_map] at hle
    have h := (hle ▸ Submodule.mem_top : (1 : S) ∈ (Ideal.map (algebraMap B S) m).restrictScalars B)
    exact h
  have h2 : ψ 1 ∈ Ideal.map ψ (Ideal.map (algebraMap B S) m) := Ideal.mem_map_of_mem ψ h1
  rw [Ideal.map_map, map_one] at h2
  have h3 : Ideal.map (ψ.comp (algebraMap B S)) m = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker]; exact hker
  rw [h3] at h2
  exact one_ne_zero ((Submodule.mem_bot K).mp h2)

end KatzDescFF

/--
@isnad1 id=faithful.1h2v.s8.bb3dd9481aba from=translated src=- shape=834caae4 vocab=c3866444
-/
theorem solution
    {B : Type u} {S : Type v} [CommRing B] [CommRing S] [Algebra B S] [Module.Flat B S]
    (h : ∀ m : Ideal B, m.IsMaximal →
      ∃ (K : Type w) (_ : Field K) (ψ : S →+* K), m ≤ RingHom.ker (ψ.comp (algebraMap B S))) :
    Module.FaithfullyFlat B S :=
  KatzDescFF.faithfullyFlat_of_exists_ringHom_field' h
