import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicFourier
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace C5F2

variable (F : Type) [Field F] [NumberField F]

/--
@isnad1 id=islocall.1h4v.s5.1d6ac8044d70 from=translated src=- shape=f31dbcd4 vocab=f466ac7c
-/
theorem isLocallyConstant_finset_prod {X ι : Type*} [TopologicalSpace X] (T : Finset ι) (g : ι → X → ℂ)
    (hg : ∀ i ∈ T, IsLocallyConstant (g i)) : IsLocallyConstant (fun x => ∏ i ∈ T, g i x) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact IsLocallyConstant.const 1
  | @insert a T ha ih =>
    have h1 : IsLocallyConstant (g a) := hg a (Finset.mem_insert_self a T)
    have h2 := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have : (fun x => ∏ i ∈ insert a T, g i x) = g a * fun x => ∏ i ∈ T, g i x := by
      funext x; rw [Finset.prod_insert ha]; rfl
    rw [this]
    exact h1.mul h2

def box (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (FiniteAdeleRing (𝓞 F) F) :=
  {x | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F}

/--
@isnad1 id=isopen.0h2v.s5.0a6078ccec83 from=translated src=- shape=07a0e020 vocab=49497628
-/
theorem isOpen_box (S : Finset (HeightOneSpectrum (𝓞 F))) : IsOpen (box F S) :=
  RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)

/--
@isnad1 id=isclosed.0h2v.s5.a54e011ae197 from=translated src=- shape=07a0e020 vocab=899d184e
-/
theorem isClosed_box (S : Finset (HeightOneSpectrum (𝓞 F))) : IsClosed (box F S) := by
  have : box F S = ⋂ v : HeightOneSpectrum (𝓞 F), ⋂ (_ : v ∉ S),
      (fun x : FiniteAdeleRing (𝓞 F) F => x v) ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext x; simp [box]
  rw [this]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    (Valued.isClosed_valuationSubring _).preimage (RestrictedProduct.continuous_eval v)

open scoped Classical in

/--
@isnad1 id=islocall.0h2v.s9.9992f4cd888f from=translated src=- shape=d05f42c1 vocab=22b8b5b2
-/
theorem isLocallyConstant_ite_box (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsLocallyConstant (fun x : FiniteAdeleRing (𝓞 F) F =>
      (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F
  · refine ⟨box F S, isOpen_box F S, hx, fun x' hx' => ?_⟩
    have hx'' : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x' v ∈ v.adicCompletionIntegers F := hx'
    rw [ite_eq_left hx'', ite_eq_left hx]
  · refine ⟨(box F S)ᶜ, (isClosed_box F S).isOpen_compl, hx, fun x' hx' => ?_⟩
    have hx'' : ¬ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x' v ∈ v.adicCompletionIntegers F := hx'
    rw [ite_eq_right hx'', ite_eq_right hx]

/--
@isnad1 id=iscompac.1h3v.s9.e5a05a1b29f0 from=translated src=- shape=acc5b532 vocab=1a0a80b1
-/
theorem isCompact_box_of (S : Finset (HeightOneSpectrum (𝓞 F))) (C : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F))
    (hC : ∀ v ∈ S, IsCompact (C v)) :
    IsCompact {x : FiniteAdeleRing (𝓞 F) F |
      (∀ v ∈ S, x v ∈ C v) ∧ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F} := by
  classical

  set T : Set (HeightOneSpectrum (𝓞 F)) := (↑S : Set (HeightOneSpectrum (𝓞 F)))ᶜ with hTdef
  have hT : Filter.cofinite ≤ Filter.principal T :=
    Filter.le_principal_iff.mpr (by rw [hTdef, Filter.mem_cofinite, compl_compl]; exact S.finite_toSet)
  set D : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F) := fun v =>
    if v ∈ S then C v else (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hDdef
  have hD : ∀ v, IsCompact (D v) := fun v => by
    by_cases hv : v ∈ S
    · rw [hDdef]; simp only [ite_eq_left hv]; exact hC v hv
    · rw [hDdef]; simp only [ite_eq_right hv]
      haveI : CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
        inferInstanceAs (CompactSpace (v.adicCompletionIntegers F))
      exact isCompact_iff_compactSpace.mpr inferInstance
  have hPD : IsCompact (Set.univ.pi D) := isCompact_univ_pi hD

  let Y := RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (Filter.principal T)
  set s : Set Y := ((↑) : Y → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) ⁻¹' Set.univ.pi D with hsdef
  have hs : IsCompact s := by
    rw [(RestrictedProduct.isEmbedding_coe_of_principal).isCompact_iff]
    have himg : ((↑) : Y → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) '' s = Set.univ.pi D := by
      refine Set.Subset.antisymm (Set.image_preimage_subset _ _) fun f hf => ?_
      have hfT : ∀ᶠ v in Filter.principal T, f v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        rw [Filter.eventually_principal]
        intro v hv
        have hvS : v ∉ S := hv
        have := hf v (Set.mem_univ v)
        rw [hDdef] at this; simp only [ite_eq_right hvS] at this
        exact this
      exact ⟨⟨f, hfT⟩, hf, rfl⟩
    rw [himg]; exact hPD

  have himage : RestrictedProduct.inclusion (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hT '' s
      = {x : FiniteAdeleRing (𝓞 F) F |
          (∀ v ∈ S, x v ∈ C v) ∧ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · have := hy v (Set.mem_univ v)
        rw [hDdef] at this; simp only [ite_eq_left hv] at this
        exact this
      · have := hy v (Set.mem_univ v)
        rw [hDdef] at this; simp only [ite_eq_right hv] at this
        exact this
    · rintro ⟨h1, h2⟩
      have hxT : ∀ᶠ v in Filter.principal T, x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        rw [Filter.eventually_principal]; exact fun v hv => h2 v hv
      refine ⟨⟨fun v => x v, hxT⟩, fun v _ => ?_, ?_⟩
      · by_cases hv : v ∈ S
        · show x v ∈ D v
          rw [hDdef]; simp only [ite_eq_left hv]; exact h1 v hv
        · show x v ∈ D v
          rw [hDdef]; simp only [ite_eq_right hv]; exact h2 v hv
      · rfl
  rw [← himage]
  exact hs.image (RestrictedProduct.continuous_inclusion hT)

open scoped Classical in
/--
@isnad1 id=and.2h3v.s10.0cba40b21aa6 from=translated src=- shape=57b3cfec vocab=1f4174b1
-/
theorem main (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    IsLocallyConstant (fun x : FiniteAdeleRing (𝓞 F) F =>
        (∏ v ∈ S, h v (x v)) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0)) ∧
      HasCompactSupport (fun x : FiniteAdeleRing (𝓞 F) F =>
        (∏ v ∈ S, h v (x v)) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0)) := by
  have hP : IsLocallyConstant (fun x : FiniteAdeleRing (𝓞 F) F => ∏ v ∈ S, h v (x v)) :=
    isLocallyConstant_finset_prod S (fun v (x : FiniteAdeleRing (𝓞 F) F) => h v (x v)) fun v hv =>
      (hlc v hv).comp_continuous (RestrictedProduct.continuous_eval v)
  refine ⟨hP.mul (isLocallyConstant_ite_box F S), ?_⟩

  refine HasCompactSupport.intro (isCompact_box_of F S (fun v => tsupport (h v)) fun v hv => hcs v hv) ?_
  intro x hx
  simp only [Set.mem_ofPred_eq, not_and_or, not_forall] at hx
  rcases hx with ⟨v, hv, hxv⟩ | ⟨v, hv, hxv⟩
  · rw [Finset.prod_eq_zero hv (show h v (x v) = 0 from image_eq_zero_of_notMem_tsupport hxv), zero_mul]
  · rw [ite_eq_right (fun hall => hxv (hall v hv)), mul_zero]

end C5F2

end

open scoped Classical in
/--
@isnad1 id=and.2h3v.s10.0cba40b21aa6 from=translated src=- shape=57b3cfec vocab=1f4174b1
-/
theorem solution
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    IsLocallyConstant (fun x : FiniteAdeleRing (𝓞 F) F =>
        (∏ v ∈ S, h v (x v)) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0)) ∧
      HasCompactSupport (fun x : FiniteAdeleRing (𝓞 F) F =>
        (∏ v ∈ S, h v (x v)) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0)) :=
  C5F2.main F S h hlc hcs
