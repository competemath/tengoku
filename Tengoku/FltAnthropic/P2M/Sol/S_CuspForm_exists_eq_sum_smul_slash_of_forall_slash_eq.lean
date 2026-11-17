import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspForm_exists_eq_sum_smul_slash_of_forall_slash_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CuspForm_exists_eq_sum_smul_slash_of_forall_slash_eq

set_option autoImplicit false

open scoped ModularForm MatrixGroups Manifold
open UpperHalfPlane OnePoint Matrix.SpecialLinearGroup

namespace SolRD4Aux

/--
@isnad1 id=iscusp.1h2v.s10.3bf7bcf5f962 from=translated src=- shape=4132f655 vocab=c7ad38b1
-/
lemma isCusp_SL2Z_map_smul {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) (β : GL (Fin 2) ℚ) :
    IsCusp (β.map (Rat.castHom ℝ) • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  refine ⟨β • c₀, ?_⟩
  have h := OnePoint.map_smul (Rat.castHom ℝ) β c₀
  simpa only [Rat.coe_castHom] using h

/--
@isnad1 id=iscusp.1h2v.s8.fe9f1b6d705a from=translated src=- shape=6aba3374 vocab=8561e515
-/
lemma isCusp_SL2Z_of_isCusp_map {Γ : Subgroup SL(2, ℤ)} {c : OnePoint ℝ}
    (hc : IsCusp c (Subgroup.map (mapGL ℝ) Γ)) : IsCusp c 𝒮ℒ :=
  hc.mono (Subgroup.map_le_range _ _)

/--
@isnad1 id=iszeroat.1h4v.s10.ce221390583e from=translated src=- shape=60819f50 vocab=d7848058
-/
lemma isZeroAt_slash_map {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (β : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) :
    c.IsZeroAt ((⇑g) ∣[(2 : ℤ)] β.map (Rat.castHom ℝ)) 2 := by
  rw [← OnePoint.IsZeroAt.smul_iff]
  apply CuspFormClass.zero_at_cusps g
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  exact isCusp_SL2Z_map_smul hc β

/--
@isnad1 id=iszeroat.1h5v.s6.11b6872fb169 from=translated src=- shape=603a234b vocab=88e485f1
-/
lemma isZeroAt_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → UpperHalfPlane → ℂ)
    {x : OnePoint ℝ} (hf : ∀ i ∈ s, x.IsZeroAt (f i) 2) :
    x.IsZeroAt (∑ i ∈ s, c i • f i) 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro γ _
    simp
    exact Filter.zero_zeroAtFilter _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine OnePoint.IsZeroAt.add ?_ (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    intro γ hγ
    rw [ModularForm.smul_slash]
    exact (hf a (Finset.mem_insert_self a s) γ hγ).smul _

/--
@isnad1 id=mdiffere.1h4v.s8.ab4896b12f78 from=translated src=- shape=4d285e86 vocab=b8584ffa
-/
lemma mdifferentiable_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → UpperHalfPlane → ℂ)
    (hf : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f i)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => (simp; exact mdifferentiable_const)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact ((hf a (Finset.mem_insert_self a s)).const_smul _).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end SolRD4Aux

open SolRD4Aux in
open _root_.CuspForm _root_.ModularForm.CuspForm in
/--
@isnad1 id=ex.2h7v.s11.8c2a3941466a from=translated src=- shape=7314d936 vocab=50a64e8b
-/
theorem solution
    {M N : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    {ι : Type} [Fintype ι] (c : ι → ℂ) (β : ι → GL (Fin 2) ℚ)
    (F : UpperHalfPlane → ℂ)
    (hF : F = ∑ i, c i • ((⇑g) ∣[(2 : ℤ)] (β i).map (Rat.castHom ℝ)))
    (hinv : ∀ γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N),
      F ∣[(2 : ℤ)] γ = F) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma0 N) 2, ⇑h = F :=
  ⟨{ toFun := F
     slash_action_eq' := hinv
     holo' := by
       subst hF
       exact mdifferentiable_sum _ _ _ fun i _ => (CuspFormClass.holo g).slash _ _
     zero_at_cusps' := fun hc => by
       subst hF
       exact isZeroAt_sum _ _ _ fun i _ => isZeroAt_slash_map g (β i) (isCusp_SL2Z_of_isCusp_map hc) },
   rfl⟩
