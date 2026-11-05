import Tengoku.NsP23.P23.OneTie.CoreBorderBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Border bounds from the frozen H5 exact cover. No realization or AS claim. -/
namespace P23.OneTie
noncomputable section
open Classical
variable {a b c : ℕ} [NeZero a]

/--
@isnad1 id=le.5h4v.s6.63eb36f066aa from=translated src=- shape=831eb82b vocab=76edb87d
-/
theorem mixed_topDeletion_border_card_le_five {S : Finset (Normal a b c)}
    (ha : 2≤a) (hb : 1≤b) (hc : 1≤c) (hlive : IsLiveTie S)
    (htop : IsTopDeletion S) : (borderFinset S).card≤5 := by
  rcases htop with ⟨T,h3,_,hstd⟩
  rcases T with ⟨r,u,v,hrA⟩
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have ht : liveTiePoint ∣ (⟨r,u,v,hrA⟩ : Normal a b c) := by
    have h := hlive.2.2.2
    rw [hstd] at h
    exact h.1
  have hbounds := (Normal.exact_divides_iff _ _).mp ht
  simp [liveTiePoint,Normal.DividesCriterion] at hbounds
  have hu : b≤u := by omega
  have hv : c≤v := by omega
  by_cases hlast : r=a-1
  · rw [topDeletionMixedLast_border_card S ha hb hc hu hv hlast hne hstd]
    omega
  · rw [topDeletionMixedBelow_border_card S ha hb hc hu hv (by omega) hne hstd]

/--
@isnad1 id=le.4h3v.s6.2b1739b84017 from=translated src=- shape=2d4ece29 vocab=76edb87d
-/
theorem pure_topDeletion_border_card_le_five {S : Finset (Normal a b 0)}
    (ha : 2≤a) (hb : 2≤b) (hlive : IsLiveTie S)
    (htop : IsTopDeletion S) : (borderFinset S).card≤5 := by
  rcases htop with ⟨T,h3,_,hstd⟩
  rcases T with ⟨r,u,v,hrA⟩
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have ht : liveTiePoint ∣ (⟨r,u,v,hrA⟩ : Normal a b 0) := by
    have h := hlive.2.2.2
    rw [hstd] at h
    exact h.1
  have hz : (Normal.zGenerator : Normal a b 0) ∣ ⟨r,u,v,hrA⟩ := by
    have h := hlive.2.2.1
    rw [hstd] at h
    exact h.1
  have hbounds := (Normal.exact_divides_iff _ _).mp ht
  have hzbounds := (Normal.exact_divides_iff _ _).mp hz
  simp [liveTiePoint,Normal.zGenerator,Normal.DividesCriterion] at hbounds hzbounds
  have hu : b≤u := by omega
  have hv : 1≤v := by omega
  rw [topDeletionPure_border_card S ha hb hu hv hrA hne hstd]
  omega

/--
@isnad1 id=le.2h4v.s5.4aa36185c476 from=translated src=- shape=d1d8a8ef vocab=688325b0
-/
theorem topDeletion_border_card_le_five {S : Finset (Normal a b c)}
    (h : CoverHypotheses S) (htop : IsTopDeletion S) : (borderFinset S).card≤5 := by
  rcases h.live_domain with hm | ⟨hb,hc⟩
  · exact mixed_topDeletion_border_card_le_five h.a_ge_two hm.1 hm.2 h.live_tie htop
  · subst c
    exact pure_topDeletion_border_card_le_five h.a_ge_two hb h.live_tie htop

private theorem typeThreeBase_border_le_five {S : Finset (Normal a b c)}
    (h : CoverHypotheses S) (h3 : S.card=3) (hs : TypeThreeBaseShape S) :
    (borderFinset S).card≤5 := by
  cases hs with
  | topDeletion ht => exact topDeletion_border_card_le_five h ht
  | pureFibreProduct hf =>
      obtain ⟨hb,hc⟩ := h.live_domain.resolve_left (by omega)
      rw [pureFibreProductShape_border_card h.a_ge_two hb h3 hf h.antichain h.live_tie]
  | m2K ha hu hv hr => rw [m2K_border_card ha hu hv hr]; split <;> omega
  | m2Z ha hu hv hr => rw [m2Z_border_card ha hu hv hr]
  | m3K ha hb hc hv => rw [m3K_border_card ha hb hc hv]
  | m4Y ha hu => rw [m4Y_border_card ha hu]
  | m5Y ha hb hc hv => rw [m5Y_border_card ha hb hc hv]; split <;> omega
  | m5Z ha hb hc hv => rw [m5Z_border_card ha hb hc hv]
  | p4Z ha hb hv => rw [p4Z_border_card ha hb hv]; omega
  | p5Z ha hb hv => rw [p5Z_border_card ha hb hv]; omega

/--
@isnad1 id=le.2h4v.s5.37855bd4517e from=translated src=- shape=7042f750 vocab=935b101f
-/
theorem three_root_nondominant_border_card_le_five
    (S : Finset (Normal a b c)) (h : CoverHypotheses S) (h3 : S.card=3) :
    (borderFinset S).card≤5 := by
  cases h5_typeThree_specialized_cover S h h3 with
  | direct hs => exact typeThreeBase_border_le_five h h3 hs
  | reflected hb hc hs =>
      have hh := coverHypotheses_swapYZ h hb hc
      have hc3 : (swapYZFinset S).card=3 := by simpa [swapYZFinset] using h3
      have hp := typeThreeBase_border_le_five hh hc3 hs
      rwa [borderFinset_swapYZ_card] at hp

private theorem base_two_border_le_four {S : Finset (Normal a b c)}
    (h : CoverHypotheses S) (h2 : S.card=2) (hs : BaseCoverShape S) :
    (borderFinset S).card≤4 := by
  cases hs with
  | topDeletion ht => obtain ⟨_,h3,_⟩ := ht; omega
  | pureFibreProduct hf =>
      obtain ⟨hb,_⟩ := h.live_domain.resolve_left (by omega)
      exact pureFibreProduct_two_border_card_le_four h.a_ge_two hb h2 hf h.live_tie
  | m2 ha hu hv hr => exact m2_core_border_card_le_four ha hu hv hr
  | m3 ha hb hc hv => exact m3_core_border_card_le_four ha hb hc hv
  | m4 ha hu => exact m4_core_border_card_le_four ha hu
  | m5 ha hb hc hv => exact m5_core_border_card_le_four ha hb hc hv
  | p3 ha hb => exact p3_core_border_card_le_four ha hb
  | p4 ha hb hv => exact p4_core_border_card_le_four ha hb hv
  | p5 ha hb hv => exact p5_core_border_card_le_four ha hb hv
  | p6 ha hb hv => exact p6_core_border_card_le_four ha hb hv
  | m2K ha hu hv hr =>
      simp [m2KSocles,m2Core,m2Partner,m2KRoot,Finset.card_insert_eq_ite,Normal.mk.injEq] at h2 <;> omega
  | m2Z ha hu hv hr =>
      simp [m2ZSocles,m2Core,m2Partner,m2ZRoot,Finset.card_insert_eq_ite,Normal.mk.injEq] at h2 <;> omega
  | m3K ha hb hc hv =>
      simp [m3KSocles,m3KCore,m3KPartner,m3KRoot,Finset.card_insert_eq_ite,Normal.mk.injEq] at h2 <;> omega
  | m4Y ha hu =>
      simp [m4YSocles,m4YCore,m4YPartner,m4YRoot,Finset.card_insert_eq_ite,Normal.mk.injEq] at h2 <;> omega
  | m5Y ha hb hc hv =>
      simp [m5YSocles,m5Core,m5Partner,m5YRoot,Finset.card_insert_eq_ite,Normal.mk.injEq] at h2 <;> omega
  | m5Z ha hb hc hv =>
      simp [m5ZSocles,m5Core,m5Partner,m5ZRoot,Finset.card_insert_eq_ite,Normal.mk.injEq] at h2
      split_ifs at h2 <;> omega
  | p4Z ha hb hv =>
      simp [p4ZSocles,Finset.card_insert_eq_ite,Normal.mk.injEq] at h2 <;> omega
  | p5Z ha hb hv =>
      simp [p5ZSocles,Finset.card_insert_eq_ite,Normal.mk.injEq] at h2 <;> omega

/--
@isnad1 id=le.2h4v.s5.070d24bb8ddb from=translated src=- shape=7042f750 vocab=935b101f
-/
theorem two_root_nondominant_border_card_le_four
    (S : Finset (Normal a b c)) (h : CoverHypotheses S) (h2 : S.card=2) :
    (borderFinset S).card≤4 := by
  cases h5_full_symbolic_cover S h with
  | direct hs => exact base_two_border_le_four h h2 hs
  | reflected hb hc hs =>
      have hh := coverHypotheses_swapYZ h hb hc
      have hc2 : (swapYZFinset S).card=2 := by simpa [swapYZFinset] using h2
      have hp := base_two_border_le_four hh hc2 hs
      rwa [borderFinset_swapYZ_card] at hp

/--
@isnad1 id=le.1h4v.s5.89b8d550bce4 from=translated src=- shape=9205a821 vocab=1fef0b34
-/
theorem oneTie_nondominant_border_card_le_type_plus_two
    (S : Finset (Normal a b c)) (h : CoverHypotheses S) :
    (borderFinset S).card≤S.card+2 := by
  have ht : S.card=2 ∨ S.card=3 := by have := h.card_ge_two; have := h.card_le_three; omega
  rcases ht with ht | ht
  · have := two_root_nondominant_border_card_le_four S h ht; omega
  · have := three_root_nondominant_border_card_le_five S h ht; omega

end
end P23.OneTie
