import Tengoku.NsP23.P23.Monomial.PlainMonomialIdeal
import Tengoku.NsP23.P23.Monomial.PlainNoFiveFamilies

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Small minimal ordinary monomial presentations, by exact pure-axis borders. -/
namespace P23.Monomial
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def plainAxisBound (R : Finset PlainExp) (j : Fin 3) : ℕ := R.sup (fun p => p j) + 1

/--
@isnad1 id=and.1h2v.s5.d094731d8194 from=translated src=- shape=793baf4b vocab=2fc24dac
-/
theorem plain_axis_bound_border (R : Finset PlainExp) (hv : PlainVariablesSurvive R)
    (j : Fin 3) : 2 ≤ plainAxisBound R j ∧
    Finsupp.single j (plainAxisBound R j) ∈ plainBorderFinset R := by
  obtain ⟨s,hs,hpos⟩ := plain_direction_active R hv j
  have hsj := Finset.le_sup (f := fun p : PlainExp => p j) hs
  have hR : R.Nonempty := ⟨s,hs⟩
  obtain ⟨t,ht,hmax⟩ := R.exists_max_image (fun p : PlainExp => p j) hR
  have hsup : R.sup (fun p => p j) = t j := le_antisymm
    (Finset.sup_le fun p hp => hmax p hp) (Finset.le_sup (f := fun p : PlainExp => p j) ht)
  refine ⟨by unfold plainAxisBound; omega, (mem_plainBorderFinset_iff _ _).mpr ⟨?_,?_⟩⟩
  · rintro ⟨p,hp,hdiv⟩
    have hi := hdiv j
    have hpj := Finset.le_sup (f := fun p : PlainExp => p j) hp
    simp only [Finsupp.single_eq_same] at hi
    unfold plainAxisBound at hi
    omega
  · intro r hr
    have hrj : r = j := by
      by_contra hn
      simpa [Finsupp.single_apply,hn] using hr
    subst r
    refine ⟨t,ht,?_⟩
    intro r
    by_cases he : j = r
    · subst r
      simp [plainPredecessor_apply,plainAxisBound,hsup]
    · simp [plainPredecessor_apply,Finsupp.single_apply,he]

/--
@isnad1 id=ex.2h3v.s6.b69579e3de06 from=translated src=- shape=ef736eee vocab=70d52e4f
-/
theorem exists_plain_pure_axis_border (k : Type*) [Field k] (G : Finset PlainExp)
    (hf : (plainSurvivors k G).Finite)
    (hv : PlainVariablesSurvive (plainSurvivorRoots k G hf)) (j : Fin 3) :
    ∃ A : ℕ, 2 ≤ A ∧ Finsupp.single j A ∈
      plainBorderFinset (plainSurvivorRoots k G hf) :=
  ⟨_,plain_axis_bound_border _ hv j⟩

/--
@isnad1 id=injectiv.1h1v.s5.db82fd2d2378 from=translated src=- shape=04e2796a vocab=19aecaf1
-/
theorem plain_axis_border_injective (R : Finset PlainExp) (hv : PlainVariablesSurvive R) :
    Function.Injective (fun j : Fin 3 => Finsupp.single j (plainAxisBound R j)) := by
  intro j r he
  by_contra hn
  have hc := congrArg (fun p : PlainExp => p j) he
  have hp := (plain_axis_bound_border R hv j).1
  simp [Finsupp.single_apply,Ne.symm hn] at hc
  omega

/--
@isnad1 id=le.1h1v.s4.f202af6f91b5 from=translated src=- shape=dd8a1a43 vocab=1b949ed7
-/
theorem plain_border_card_ge_three_of_variables_survive (R : Finset PlainExp)
    (hv : PlainVariablesSurvive R) : 3 ≤ (plainBorderFinset R).card := by
  let f : Fin 3 → ↥(plainBorderFinset R) := fun j =>
    ⟨_,(plain_axis_bound_border R hv j).2⟩
  have hi : Function.Injective f := fun j r he =>
    plain_axis_border_injective R hv (congrArg Subtype.val he)
  simpa using Fintype.card_le_of_injective f hi

/--
@isnad1 id=eq.2h1v.s6.bcce21794c8d from=translated src=- shape=8d56b258 vocab=d3113255
-/
theorem plain_small_border_eq_axis_triple (R : Finset PlainExp)
    (hv : PlainVariablesSurvive R) (hc : (plainBorderFinset R).card ≤ 3) :
    plainBorderFinset R = Finset.univ.image
      (fun j : Fin 3 => Finsupp.single j (plainAxisBound R j)) := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    -- Prove exhaustion from the three distinct forced elements.
    have hsub : Finset.univ.image (fun j : Fin 3 => Finsupp.single j (plainAxisBound R j))
        ⊆ plainBorderFinset R := by
      rintro q hq
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
      exact (plain_axis_bound_border R hv j).2
    have he := Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_image_of_injective _ (plain_axis_border_injective R hv)]
      simpa using hc)
    exact he.symm ▸ hp
  · rw [Finset.card_image_of_injective _ (plain_axis_border_injective R hv)]
    simpa using plain_border_card_ge_three_of_variables_survive R hv

/--
@isnad1 id=iff.4h3v.s6.39c527dd81bd from=translated src=- shape=f287826c vocab=a7b37801
-/
theorem plain_small_minimal_presentation_standard_box (k : Type*) [Field k]
    (G : Finset PlainExp) (hf : (plainSurvivors k G).Finite)
    (hv : PlainVariablesSurvive (plainSurvivorRoots k G hf))
    (he : G = plainBorderFinset (plainSurvivorRoots k G hf)) (hc : G.card ≤ 3)
    (p : PlainExp) : p ∈ plainSurvivors k G ↔
      ∀ j, p j < plainAxisBound (plainSurvivorRoots k G hf) j := by
  have ht := plain_small_border_eq_axis_triple _ hv (he ▸ hc)
  have hg := he.trans ht
  change (MvPolynomial.monomial p (1 : k) ∉ plainMonomialIdeal k G) ↔ _
  rw [monomial_mem_plainMonomialIdeal_iff]
  constructor
  · intro hn j
    by_contra hj
    apply hn
    refine ⟨_,hg.symm ▸ Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,?_⟩
    intro r
    by_cases h : j = r
    · subst r; simp only [Finsupp.single_eq_same]; omega
    · simp [Finsupp.single_apply,h]
  · intro hs ⟨g,hgmem,hdiv⟩
    have him : g ∈ Finset.univ.image (fun j : Fin 3 =>
        Finsupp.single j (plainAxisBound (plainSurvivorRoots k G hf) j)) := by
      rw [← hg]
      exact hgmem
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp him
    have h := hdiv j
    simp only [Finsupp.single_eq_same] at h
    have := hs j
    omega

/--
@isnad1 id=eq.4h2v.s5.e7e9f5c119f9 from=translated src=- shape=c3c4b7f8 vocab=2ec39727
-/
theorem plain_small_minimal_presentation_root_card_one (k : Type*) [Field k]
    (G : Finset PlainExp) (hf : (plainSurvivors k G).Finite)
    (hv : PlainVariablesSurvive (plainSurvivorRoots k G hf))
    (he : G = plainBorderFinset (plainSurvivorRoots k G hf)) (hc : G.card ≤ 3) :
    (plainSurvivorRoots k G hf).card = 1 := by
  let R := plainSurvivorRoots k G hf
  let top : PlainExp := plainExp (plainAxisBound R 0 - 1)
    (plainAxisBound R 1 - 1) (plainAxisBound R 2 - 1)
  have htop (j : Fin 3) : top j = plainAxisBound R j - 1 := by
    fin_cases j <;> simp [top]
  have hpos (j : Fin 3) : 2 ≤ plainAxisBound R j := (plain_axis_bound_border R hv j).1
  have ht : top ∈ plainSurvivors k G :=
    (plain_small_minimal_presentation_standard_box k G hf hv he hc top).mpr
      (fun j => by change top j < plainAxisBound R j; rw [htop]; have := hpos j; omega)
  have hd (p : PlainExp) (hp : p ∈ plainSurvivors k G) : plainDivides p top := by
    intro j
    have hlt : p j < plainAxisBound R j :=
      (plain_small_minimal_presentation_standard_box k G hf hv he hc p).mp hp j
    rw [htop]
    omega
  have htR : top ∈ R := by
    apply Finset.mem_filter.mpr
    refine ⟨hf.mem_toFinset.mpr ht,?_⟩
    intro q hq htopq
    exact plainDivides_antisymm htopq (hd q (hf.mem_toFinset.mp hq))
  have hR : R = {top} := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      have hps : p ∈ plainSurvivors k G := hf.mem_toFinset.mp (Finset.mem_filter.mp hp).1
      exact Finset.mem_singleton.mpr ((Finset.mem_filter.mp hp).2 top
        (hf.mem_toFinset.mpr ht) (hd p hps))
    · intro hp
      exact (Finset.mem_singleton.mp hp).symm ▸ htR
  change R.card = 1
  rw [hR]
  simp

end
end P23.Monomial
