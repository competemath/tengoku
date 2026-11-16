import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_IsSeparable_isReduced_and_isSeparable_and_finite_tensorProduct.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_IsSeparable_isReduced_and_isSeparable_and_finite_tensorProduct

set_option autoImplicit false

open scoped TensorProduct
open Polynomial

/--
@isnad1 id=issepara.0h2v.s6.ac048e162192 from=translated src=- shape=56048a07 vocab=888b1b50
-/
theorem Ws44.SepBC.isSeparable_of_finite_of_isReduced_of_formallyUnramified
    (E A : Type*) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] [IsReduced A]
    [Algebra.FormallyUnramified E A] : Algebra.IsSeparable E A := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite E A
  rw [Algebra.isSeparable_iff]
  intro x
  refine ⟨IsIntegral.of_finite E x, ?_⟩
  have hMfin : {I : Ideal A | I.IsMaximal}.Finite := IsArtinianRing.setOfPred_isMaximal_finite A
  let p : Ideal A → E[X] := fun I => minpoly E (Ideal.Quotient.mkₐ E I x)
  let s : Finset E[X] := hMfin.toFinset.image p
  have hp : ∀ I : Ideal A, I.IsMaximal → (p I).Monic ∧ Irreducible (p I) ∧ (p I).Separable := by
    intro I hI
    haveI : I.IsMaximal := hI
    letI : Field (A ⧸ I) := Ideal.Quotient.field I
    haveI : Algebra.IsSeparable E (A ⧸ I) :=
      (Algebra.FormallyUnramified.iff_isSeparable E (A ⧸ I)).mp inferInstance
    have hint : IsIntegral E (Ideal.Quotient.mkₐ E I x) := IsIntegral.of_finite E _
    exact ⟨minpoly.monic hint, minpoly.irreducible hint, Algebra.IsSeparable.isSeparable E _⟩
  have hs : ∀ q ∈ s, q.Monic ∧ Irreducible q ∧ q.Separable := by
    intro q hq
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hq
    exact hp I (hMfin.mem_toFinset.mp hI)
  let P : E[X] := ∏ q ∈ s, q
  have hPsep : P.Separable := by
    apply Polynomial.separable_prod'
    · intro q₁ h₁ q₂ h₂ hne
      obtain ⟨hm₁, hi₁, -⟩ := hs q₁ h₁
      obtain ⟨hm₂, hi₂, -⟩ := hs q₂ h₂
      rw [hi₁.coprime_iff_not_dvd]
      intro hdvd
      exact hne (Polynomial.eq_of_monic_of_associated hm₁ hm₂ (hi₁.associated_of_dvd hi₂ hdvd))
    · intro q hq
      exact (hs q hq).2.2
  have hdvdAll : ∀ I : Ideal A, I.IsMaximal → p I ∣ P := fun I hI =>
    Finset.dvd_prod_of_mem _ (Finset.mem_image.mpr ⟨I, hMfin.mem_toFinset.mpr hI, rfl⟩)
  clear_value P
  have hmem : ∀ I : Ideal A, I.IsMaximal → aeval x P ∈ I := by
    intro I hI
    have h2 : aeval (Ideal.Quotient.mkₐ E I x) P = 0 :=
      Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero (hdvdAll I hI) (minpoly.aeval E _)
    rw [Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mp h2
  have hjac : aeval x P ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    intro J hJ
    exact hmem J hJ.2
  have hnil : IsNilpotent (aeval x P) := by
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
    refine ⟨n, ?_⟩
    have : aeval x P ^ n ∈ (⊥ : Ideal A).jacobson ^ n := Ideal.pow_mem_pow hjac n
    rw [hn] at this
    simpa using this
  exact hPsep.of_dvd (minpoly.dvd E x hnil.eq_zero)

/--
@isnad1 id=and.0h3v.s9.e5abe943ac3d from=translated src=- shape=e448d66f vocab=63d57862
-/
theorem solution
    (K₁ K E : Type*) [Field K₁] [Field K] [Field E] [Algebra K₁ K] [Algebra K₁ E]
    [FiniteDimensional K₁ K] [Algebra.IsSeparable K₁ K] :
    IsReduced (E ⊗[K₁] K) ∧ Algebra.IsSeparable E (E ⊗[K₁] K) ∧ Module.Finite E (E ⊗[K₁] K) := by
  haveI : Algebra.FormallyUnramified K₁ K := Algebra.FormallyUnramified.of_isSeparable K₁ K
  haveI hred : IsReduced (E ⊗[K₁] K) := Algebra.FormallyUnramified.isReduced_of_field E (E ⊗[K₁] K)
  exact ⟨hred, Ws44.SepBC.isSeparable_of_finite_of_isReduced_of_formallyUnramified E (E ⊗[K₁] K),
    inferInstance⟩
