import Tengoku.NsP23.P23.OneTie.H5Cover
import Tengoku.NsP23.P23.OneTie.TopDeletion
import Tengoku.NsP23.P23.OneTie.PureFibreProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Phase-1 geometry closure

The H5 cover is eliminated using only exact symbolic border counts.  No
canonical-module, trace, or H-L5 statement is introduced here.
-/

namespace P23.OneTie

variable {a b c : ℕ} [NeZero a]

def IsPureResidualFourBorderShape (S : Finset (Normal a b 0)) : Prop :=
  (∃ (V : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V),
      S = p4ZSocles (a := a) (b := b) ha V) ∨
  (∃ (v : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v),
      S = p5ZSocles (a := a) (b := b) ha v)

private theorem mixed_topDeletion_card_ne_four
    {S : Finset (Normal a b c)}
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hcardS : S.card = 3) (hlive : IsLiveTie S)
    (htop : IsTopDeletion S) : (borderFinset S).card ≠ 4 := by
  rcases htop with ⟨T, _, _, hstd⟩
  rcases T with ⟨r, u, v, hrA⟩
  have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  rcases (mem_standardSet_iff S liveTiePoint).1 hlive.2.2.2 with ⟨q, hqS, hqdiv⟩
  have hqstd : q ∈ standardSet S := (mem_standardSet_iff S q).2 ⟨q, hqS, dvd_refl q⟩
  rw [hstd] at hqstd
  have htieT : liveTiePoint ∣ (⟨r, u, v, hrA⟩ : Normal a b c) :=
    dvd_trans hqdiv hqstd.1
  have hbounds := (Normal.exact_divides_iff liveTiePoint
    (⟨r, u, v, hrA⟩ : Normal a b c)).1 htieT
  have hu : b ≤ u := by
    simp [liveTiePoint, Normal.DividesCriterion] at hbounds
    omega
  have hv : c ≤ v := by
    simp [liveTiePoint, Normal.DividesCriterion] at hbounds
    omega
  by_cases hlast : r = a - 1
  · have hc3 := topDeletionMixedLast_border_card S ha hb hc hu hv hlast
      hnonempty hstd
    omega
  · have hbelow : r < a - 1 := by omega
    have hc5 := topDeletionMixedBelow_border_card S ha hb hc hu hv hbelow
      hnonempty hstd
    omega

private theorem pure_topDeletion_card_ne_four
    {S : Finset (Normal a b 0)}
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcardS : S.card = 3) (hlive : IsLiveTie S)
    (htop : IsTopDeletion S) : (borderFinset S).card ≠ 4 := by
  rcases htop with ⟨T, _, _, hstd⟩
  rcases T with ⟨r, u, v, hrA⟩
  have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  rcases (mem_standardSet_iff S liveTiePoint).1 hlive.2.2.2 with ⟨q, hqS, hqdiv⟩
  have hqstd : q ∈ standardSet S := (mem_standardSet_iff S q).2 ⟨q, hqS, dvd_refl q⟩
  rw [hstd] at hqstd
  have htieT : liveTiePoint ∣ (⟨r, u, v, hrA⟩ : Normal a b 0) :=
    dvd_trans hqdiv hqstd.1
  have hbounds := (Normal.exact_divides_iff liveTiePoint
    (⟨r, u, v, hrA⟩ : Normal a b 0)).1 htieT
  have hu : b ≤ u := by
    simp [liveTiePoint, Normal.DividesCriterion] at hbounds
    omega
  rcases (mem_standardSet_iff S (Normal.zGenerator : Normal a b 0)).1
      hlive.2.2.1 with ⟨qz, hqzS, hzdiv⟩
  have hqzstd : qz ∈ standardSet S :=
    (mem_standardSet_iff S qz).2 ⟨qz, hqzS, dvd_refl qz⟩
  rw [hstd] at hqzstd
  have hzT : (Normal.zGenerator : Normal a b 0) ∣
      (⟨r, u, v, hrA⟩ : Normal a b 0) := dvd_trans hzdiv hqzstd.1
  have hv : 1 ≤ v := by
    have hz := (Normal.exact_divides_iff
      (Normal.zGenerator : Normal a b 0) (⟨r, u, v, hrA⟩ : Normal a b 0)).1 hzT
    simp [Normal.zGenerator, Normal.DividesCriterion] at hz
    omega
  have hc3 := topDeletionPure_border_card S ha hb hu hv hrA hnonempty hstd
  omega

private theorem mixed_base_card_ne_four
    {S : Finset (Normal a b c)}
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hcardS : S.card = 3) (hlive : IsLiveTie S)
    (hshape : TypeThreeBaseShape S) : (borderFinset S).card ≠ 4 := by
  cases hshape with
  | topDeletion h => exact mixed_topDeletion_card_ne_four ha hb hc hcardS hlive h
  | pureFibreProduct h => simp_all [IsPureFibreProduct]
  | m2K ha' hu hv hr =>
      rw [m2K_border_card ha' hu hv hr]
      split <;> omega
  | m2Z ha' hu hv hr =>
      rw [m2Z_border_card ha' hu hv hr]
      omega
  | m3K ha' hb' hc' hv =>
      rw [m3K_border_card ha' hb' hc' hv]
      omega
  | m4Y ha' hu =>
      rw [m4Y_border_card ha' hu]
      omega
  | m5Y ha' hb' hc' hv =>
      rw [m5Y_border_card ha' hb' hc' hv]
      split <;> omega
  | m5Z ha' hb' hc' hv =>
      rw [m5Z_border_card ha' hb' hc' hv]
      omega
  | p4Z ha' hb' hV => simp_all
  | p5Z ha' hb' hv => simp_all

private theorem pure_base_four_residual
    {S : Finset (Normal a b 0)}
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcardS : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) (hborder : (borderFinset S).card = 4)
    (hshape : TypeThreeBaseShape S) : IsPureResidualFourBorderShape S := by
  cases hshape with
  | topDeletion h => exact False.elim ((pure_topDeletion_card_ne_four ha hb hcardS hlive h) hborder)
  | pureFibreProduct h =>
      exact False.elim ((pureFibreProductShape_border_card_ne_four
        ha hb hcardS h hanti hlive) hborder)
  | m3K ha' hb' hc' hv =>
      omega
  | m5Y ha' hb' hc' hv =>
      omega
  | m5Z ha' hb' hc' hv =>
      omega
  | p4Z ha' hb' hV => exact Or.inl ⟨_, ha', hb', hV, rfl⟩
  | p5Z ha' hb' hv => exact Or.inr ⟨_, ha', hb', hv, rfl⟩

/-- A mixed type-three four-border configuration has a dominant root.-/
theorem mixed_four_border_has_dominant
    (S : Finset (Normal a b c))
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hcardS : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) (hcentres : HasDirectionalCentres S)
    (hborder : (borderFinset S).card = 4) :
    ∃ C ∈ S, IsDominantRoot S C := by
  by_contra hdom
  push_neg at hdom
  let hcover : CoverHypotheses S :=
    { a_ge_two := ha
      live_domain := Or.inl ⟨hb, hc⟩
      live_tie := hlive
      card_ge_two := by omega
      card_le_three := by omega
      antichain := hanti
      centres := hcentres
      no_dominant := hdom }
  have hshape := h5_typeThree_specialized_cover S hcover hcardS
  cases hshape with
  | direct h => exact (mixed_base_card_ne_four ha hb hc hcardS hlive h) hborder
  | reflected hb' hc' h =>
      have hcardSwap : (borderFinset (swapYZFinset S)).card = 4 := by
        rw [borderFinset_swapYZ_card]
        exact hborder
      have hcardRoots : (swapYZFinset S).card = 3 := by
        simpa [swapYZFinset] using hcardS
      have hliveSwap : IsLiveTie (swapYZFinset S) := by
        exact (coverHypotheses_swapYZ hcover hb hc).live_tie
      exact (mixed_base_card_ne_four ha hc hb hcardRoots hliveSwap h) hcardSwap

/-- A pure type-three four-border configuration is dominant or one of the two
exact residual P4Z/P5Z shapes.-/
theorem pure_four_border_dominant_or_residual
    (S : Finset (Normal a b 0))
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcardS : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) (hcentres : HasDirectionalCentres S)
    (hborder : (borderFinset S).card = 4) :
    (∃ C ∈ S, IsDominantRoot S C) ∨ IsPureResidualFourBorderShape S := by
  by_cases hdom : ∃ C ∈ S, IsDominantRoot S C
  · exact Or.inl hdom
  · right
    push_neg at hdom
    let hcover : CoverHypotheses S :=
      { a_ge_two := ha
        live_domain := Or.inr ⟨hb, rfl⟩
        live_tie := hlive
        card_ge_two := by omega
        card_le_three := by omega
        antichain := hanti
        centres := hcentres
        no_dominant := hdom }
    have hshape := h5_typeThree_specialized_cover S hcover hcardS
    cases hshape with
    | direct h => exact pure_base_four_residual ha hb hcardS hlive hanti hborder h
    | reflected hb' hc' h => omega

end P23.OneTie
