import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_IsUnramifiedAt_baseChange_of_ne_maximalIdeal_of_map_maximalIdeal_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_IsUnramifiedAt_baseChange_of_ne_maximalIdeal_of_map_maximalIdeal_eq

set_option autoImplicit false

open TensorProduct

/--
@isnad1 id=isunrami.3h4v.s8.8b545133167f from=translated src=- shape=4c980ea2 vocab=3b619629
-/
theorem solution
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [IsLocalRing R] [IsLocalRing R']
    [Algebra R R'] (hmax : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    [Algebra R S] [Module.Finite R S]
    (hS : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal → Algebra.IsUnramifiedAt R 𝔮) :
    ∀ (𝔔 : Ideal (R' ⊗[R] S)) [𝔔.IsPrime], ¬ 𝔔.IsMaximal → Algebra.IsUnramifiedAt R' 𝔔 := by
  intro 𝔔 _ h𝔔
  classical
  letI : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra

  let 𝔮 : Ideal S := 𝔔.comap (algebraMap S (R' ⊗[R] S))
  haveI h𝔮p : 𝔮.IsPrime := Ideal.IsPrime.comap _
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  haveI : Algebra.IsIntegral R' (R' ⊗[R] S) := Algebra.IsIntegral.of_finite R' (R' ⊗[R] S)

  have h𝔮 : ¬ 𝔮.IsMaximal := by
    intro hmaxq
    apply h𝔔
    have h1 : (𝔮.comap (algebraMap R S)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔮
    have h2 : 𝔮.comap (algebraMap R S) = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal h1
    have h3 : IsLocalRing.maximalIdeal R' ≤ 𝔔.comap (algebraMap R' (R' ⊗[R] S)) := by
      rw [← hmax, Ideal.map_le_iff_le_comap, Ideal.comap_comap,
        ← IsScalarTower.algebraMap_eq R R' (R' ⊗[R] S),
        IsScalarTower.algebraMap_eq R S (R' ⊗[R] S), ← Ideal.comap_comap]
      exact h2.symm.le
    have hne : 𝔔.comap (algebraMap R' (R' ⊗[R] S)) ≠ ⊤ := Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top ‹_›)
    have h4 : (𝔔.comap (algebraMap R' (R' ⊗[R] S))).IsMaximal := by
      rw [← (IsLocalRing.maximalIdeal.isMaximal R').eq_of_le hne h3]
      exact IsLocalRing.maximalIdeal.isMaximal R'
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔔 h4

  have hq_unr : Algebra.IsUnramifiedAt R 𝔮 := hS 𝔮 h𝔮
  have hq' : (⟨𝔮, h𝔮p⟩ : PrimeSpectrum S) ∉ Module.support S Ω[S⁄R] := by
    have : (⟨𝔮, h𝔮p⟩ : PrimeSpectrum S) ∈ Algebra.unramifiedLocus R S := hq_unr
    rwa [Algebra.unramifiedLocus_eq_compl_support] at this
  rw [Module.mem_support_iff_of_finite] at hq'
  obtain ⟨s, hs, hsq⟩ := SetLike.not_le_iff_exists.mp hq'

  change (⟨𝔔, ‹_›⟩ : PrimeSpectrum (R' ⊗[R] S)) ∈ Algebra.unramifiedLocus R' (R' ⊗[R] S)
  rw [Algebra.unramifiedLocus_eq_compl_support, Set.mem_compl_iff,
    ← (KaehlerDifferential.tensorKaehlerEquiv R R' S (R' ⊗[R] S)).support_eq,
    Module.mem_support_iff_of_finite]
  intro hle
  apply hsq
  have hann : algebraMap S (R' ⊗[R] S) s ∈
      Module.annihilator (R' ⊗[R] S) ((R' ⊗[R] S) ⊗[S] Ω[S⁄R]) := by
    rw [Module.mem_annihilator]
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero]
    | tmul b w =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, ← Algebra.smul_def,
          TensorProduct.smul_tmul, Module.mem_annihilator.mp hs w, TensorProduct.tmul_zero]
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  have := hle hann
  simp [Ideal.mem_comap] at this
  exact this
