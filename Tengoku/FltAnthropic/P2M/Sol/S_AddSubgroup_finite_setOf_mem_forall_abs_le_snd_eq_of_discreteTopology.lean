import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AddSubgroup_finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AddSubgroup_finite_setOf_mem_forall_abs_le_snd_eq_of_discreteTopology

set_option autoImplicit false

/--
@isnad1 id=finite.0h5v.s9.9e2452d89855 from=translated src=- shape=8f40ab8b vocab=15f76a73
-/
theorem solution
    {r c : ℕ} (Λ : AddSubgroup ((Fin r → ℝ) × (Fin c → ℤ))) [DiscreteTopology Λ] (R : ℝ) (k₀ : Fin c → ℤ) :
    {γ : (Fin r → ℝ) × (Fin c → ℤ) | γ ∈ Λ ∧ (∀ i, |γ.1 i| ≤ R) ∧ γ.2 = k₀}.Finite := by
  have hcl : IsClosed (Λ : Set ((Fin r → ℝ) × (Fin c → ℤ))) := AddSubgroup.isClosed_of_discrete
  have hbox : IsCompact ({x : Fin r → ℝ | ∀ i, |x i| ≤ R} ×ˢ ({k₀} : Set (Fin c → ℤ))) := by
    refine IsCompact.prod ?_ isCompact_singleton
    have : {x : Fin r → ℝ | ∀ i, |x i| ≤ R} = Set.pi Set.univ fun _ => Set.Icc (-R) R := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const, abs_le]
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hK : IsCompact ((Λ : Set ((Fin r → ℝ) × (Fin c → ℤ))) ∩
      ({x : Fin r → ℝ | ∀ i, |x i| ≤ R} ×ˢ ({k₀} : Set (Fin c → ℤ)))) := hbox.inter_left hcl
  have hfin : ((Λ : Set ((Fin r → ℝ) × (Fin c → ℤ))) ∩
      ({x : Fin r → ℝ | ∀ i, |x i| ≤ R} ×ˢ ({k₀} : Set (Fin c → ℤ)))).Finite := by
    refine hK.finite ?_
    have : IsDiscrete (Λ : Set ((Fin r → ℝ) × (Fin c → ℤ))) :=
      isDiscrete_iff_discreteTopology.2 ‹DiscreteTopology Λ›
    exact this.mono Set.inter_subset_left
  refine hfin.subset ?_
  rintro γ ⟨hγ, hx, hk⟩
  exact ⟨hγ, hx, hk⟩
