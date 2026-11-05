import Tengoku.NsP23.P23.Semigroup.GapReflection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.Semigroup.FourGeneratedNumericalSemigroup
noncomputable section
variable (D : FourGeneratedNumericalSemigroup)

/-- Standard intrinsic reflected-gap predicate, not a genus equality.-/
def IsAlmostSymmetric : Prop := ∀ a : ℕ,a∈D.gapFinset →
  D.frobenius-a∈D.gapFinset → D.IsPseudoFrobenius (a:ℤ)

private theorem doubleGap_subset_nonFrobeniusPF (has : D.IsAlmostSymmetric) :
    D.doubleGapFinset⊆D.nonFrobeniusPFFinset := by
  classical
  intro a ha
  have hh := Finset.mem_filter.mp ha
  let f : D.PseudoFrobeniusIndex := ⟨a,has a hh.1 hh.2⟩
  have hf : f≠D.frobeniusPF := by
    intro he
    have hv := congrArg Subtype.val he
    change (a:ℤ)=(D.frobenius:ℤ) at hv
    have haf : a=D.frobenius := by exact_mod_cast hv
    have hz : 0∈D.gapFinset := by simpa [haf] using hh.2
    have hn := (D.mem_gapFinset 0).mp hz
    exact hn D.Gamma.zero_mem
  apply Finset.mem_image.mpr
  refine ⟨f,Finset.mem_erase.mpr ⟨hf,Finset.mem_univ f⟩,?_⟩
  simp [pseudoFrobeniusNat,f]

theorem almostSymmetric_iff_doubleGap_card :
    D.IsAlmostSymmetric ↔ D.doubleGapFinset.card=D.semigroupType-1 := by
  classical
  constructor
  · intro has
    have he := Finset.Subset.antisymm (D.doubleGap_subset_nonFrobeniusPF has)
      D.nonFrobeniusPF_subset_doubleGap
    rw [he,D.nonFrobeniusPF_card]
  · intro hc
    have he : D.nonFrobeniusPFFinset=D.doubleGapFinset :=
      Finset.eq_of_subset_of_card_le D.nonFrobeniusPF_subset_doubleGap
        (by rw [hc,D.nonFrobeniusPF_card])
    intro a ha hra
    have hd : a∈D.doubleGapFinset := Finset.mem_filter.mpr ⟨ha,hra⟩
    rw [←he] at hd
    obtain ⟨f,_,hf⟩ := Finset.mem_image.mp hd
    have hz : f.1=(a:ℤ) := by
      have := congrArg (fun n : ℕ=>(n:ℤ)) hf
      simpa using this
    exact hz ▸ f.2

theorem almostSymmetric_iff_two_genus_eq :
    D.IsAlmostSymmetric ↔ 2*D.genus=D.frobenius+D.semigroupType := by
  rw [D.almostSymmetric_iff_doubleGap_card]
  have hg := D.two_genus_eq_frobenius_one_add_doubleGapCard
  have ht := D.semigroupType_pos
  omega

end
end P23.Semigroup.FourGeneratedNumericalSemigroup
