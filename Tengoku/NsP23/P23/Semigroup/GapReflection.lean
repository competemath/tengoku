import Tengoku.NsP23.P23.Semigroup.NumericalInvariants

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Semigroup.FourGeneratedNumericalSemigroup
noncomputable section
open scoped BigOperators
variable (D : FourGeneratedNumericalSemigroup)

def doubleGapFinset : Finset ℕ :=
  D.gapFinset.filter (fun a=>D.frobenius-a∈D.gapFinset)

theorem doubleGap_reflection {a : ℕ} (ha : a∈D.doubleGapFinset) :
    D.frobenius-a∈D.doubleGapFinset := by
  have h := Finset.mem_filter.mp ha
  have hb := D.gap_le_frobenius h.1
  simp only [doubleGapFinset,Finset.mem_filter]
  exact ⟨h.2,by simpa [Nat.sub_sub_self hb] using h.1⟩

private def reflectedGoodGaps : Finset ℕ := by
  classical
  exact D.gapFinset.filter (fun a=>D.frobenius-a∈D.Gamma)

private def smallSemigroup : Finset ℕ := by
  classical
  exact (Finset.range (D.frobenius+1)).filter (fun a=>a∈D.Gamma)

private theorem small_reflection_image :
    (D.smallSemigroup.image (fun a=>D.frobenius-a))=D.reflectedGoodGaps := by
  classical
  ext a
  constructor
  · rintro h
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp h
    have hh := Finset.mem_filter.mp hs
    have hsF : s≤D.frobenius := by simpa using hh.1
    have hn : D.frobenius-s∉D.Gamma := by
      intro hmem
      apply D.frobenius_not_mem_Gamma
      have hsum := D.Gamma.add_mem hh.2 hmem
      simpa [Nat.add_sub_of_le hsF] using hsum
    exact Finset.mem_filter.mpr ⟨(D.mem_gapFinset _).mpr hn,
      by simpa [Nat.sub_sub_self hsF] using hh.2⟩
  · intro ha
    have hh := Finset.mem_filter.mp ha
    have haF := D.gap_le_frobenius hh.1
    apply Finset.mem_image.mpr
    refine ⟨D.frobenius-a,?_,Nat.sub_sub_self haF⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega),hh.2⟩

private theorem reflectedGoodGaps_card : D.reflectedGoodGaps.card=D.smallSemigroup.card := by
  classical
  rw [←D.small_reflection_image]
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  have haF : a≤D.frobenius := by
    have := (Finset.mem_filter.mp ha).1
    simpa using this
  have hbF : b≤D.frobenius := by
    have := (Finset.mem_filter.mp hb).1
    simpa using this
  change D.frobenius-a=D.frobenius-b at he
  omega

theorem two_genus_eq_frobenius_one_add_doubleGapCard :
    2*D.genus=D.frobenius+1+D.doubleGapFinset.card := by
  classical
  have hg : (Finset.range (D.frobenius+1)).filter (fun a=>a∉D.Gamma)=D.gapFinset := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_range,D.mem_gapFinset]
    constructor
    · exact fun h=>h.2
    · intro ha
      have hb := D.gap_le_frobenius ((D.mem_gapFinset a).mpr ha)
      exact ⟨by omega,ha⟩
  have hinterval := Finset.card_filter_add_card_filter_not
    (s:=Finset.range (D.frobenius+1)) (fun a=>a∈D.Gamma)
  rw [hg,Finset.card_range] at hinterval
  change D.smallSemigroup.card+D.genus=D.frobenius+1 at hinterval
  have hpartition := Finset.card_filter_add_card_filter_not
    (s:=D.gapFinset) (fun a=>D.frobenius-a∈D.Gamma)
  have hb : D.gapFinset.filter (fun a=>¬D.frobenius-a∈D.Gamma)=D.doubleGapFinset := by
    ext a
    simp [doubleGapFinset]
  rw [hb] at hpartition
  change D.reflectedGoodGaps.card+D.doubleGapFinset.card=D.genus at hpartition
  rw [D.reflectedGoodGaps_card] at hpartition
  omega

def nonFrobeniusPFFinset : Finset ℕ :=
  (Finset.univ.erase D.frobeniusPF).image D.pseudoFrobeniusNat

theorem nonFrobeniusPF_card : D.nonFrobeniusPFFinset.card=D.semigroupType-1 := by
  classical
  rw [nonFrobeniusPFFinset,Finset.card_image_of_injective _ D.pseudoFrobeniusNat_injective]
  simp [semigroupType]

theorem nonFrobeniusPF_subset_doubleGap : D.nonFrobeniusPFFinset⊆D.doubleGapFinset := by
  classical
  intro a ha
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp ha
  have hfne := (Finset.mem_erase.mp hf).1
  have hle := D.pseudoFrobeniusNat_le_frobenius f
  have hne : D.pseudoFrobeniusNat f≠D.frobenius := by
    intro he
    apply hfne
    apply Subtype.ext
    have hz := congrArg (fun n : ℕ=>(n:ℤ)) he
    simpa [frobeniusPF] using hz
  have hnot : D.frobenius-D.pseudoFrobeniusNat f∉D.Gamma := by
    intro hmem
    let g : D.Gamma := ⟨D.frobenius-D.pseudoFrobeniusNat f,hmem⟩
    have hg : g≠0 := by
      intro he
      have := congrArg Subtype.val he
      change D.frobenius-D.pseudoFrobeniusNat f=0 at this
      omega
    have hfg := f.2.2 g hg
    have he : f.1+(g.1:ℤ)=(D.frobenius:ℤ) := by
      rw [←D.pseudoFrobeniusNat_cast f]
      dsimp [g]
      omega
    rw [he] at hfg
    exact D.frobenius_not_mem_Gamma ((D.intInGamma_natCast _).mp hfg)
  apply Finset.mem_filter.mpr
  exact ⟨D.pseudoFrobeniusNat_mem_gapFinset f,(D.mem_gapFinset _).mpr hnot⟩

theorem semigroupType_pos : 0<D.semigroupType := by
  have : Nonempty D.PseudoFrobeniusIndex := ⟨D.frobeniusPF⟩
  exact Fintype.card_pos

theorem frobenius_type_le_two_genus : D.frobenius+D.semigroupType≤2*D.genus := by
  have hc := Finset.card_le_card D.nonFrobeniusPF_subset_doubleGap
  rw [D.nonFrobeniusPF_card] at hc
  have ht := D.semigroupType_pos
  have hg := D.two_genus_eq_frobenius_one_add_doubleGapCard
  omega

end
end P23.Semigroup.FourGeneratedNumericalSemigroup
