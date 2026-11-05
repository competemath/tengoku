import Tengoku.NsP23.P23.OneTie.DominantLastLayer
import Tengoku.NsP23.P23.OneTie.CoverGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Arbitrary dominant reduction

Theorems in this module bridge an arbitrary three-root dominant configuration
to the exact frozen Run-03 families and the new Run-11 last-layer families.
-/

namespace P23.OneTie

variable {a b c : ℕ} [NeZero a]

private theorem reduction_a_pos : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)

/-- Every selected root distinct from a dominant root is a minimal border point
of the dominant principal core.-/
theorem dominant_extra_root_mem_principalBorder
    (S : Finset (Normal a b c)) (ha : 2 ≤ a)
    (hanti : IsRootAntichain S) {C R : Normal a b c}
    (hdom : IsDominantRoot S C) (hR : R ∈ S) (hne : R ≠ C) :
    R ∈ borderFinset ({C} : Finset (Normal a b c)) := by
  rw [mem_borderFinset_iff (by simp)]
  apply (isMinimalBorder_iff_isDivisibilityMinimalKilled {C} R
    (variableGenerators_ne_one_of_two_le ha)).2
  refine ⟨?_, ?_⟩
  · intro hRcore
    obtain ⟨T, hT, hRT⟩ := (mem_standardSet_iff {C} R).1 hRcore
    have hTC : T = C := by simpa using hT
    subst T
    have hRC : R ∣ C := hRT
    exact (hanti R hR C hdom.1 hne) hRC
  · intro d hdR hdne
    have hdstd : d ∈ standardSet S := (mem_standardSet_iff S d).2 ⟨R, hR, hdR⟩
    rw [hdom.2] at hdstd
    rcases hdstd with hdC | hdroot
    · exact (mem_standardSet_iff {C} d).2 ⟨C, by simp, hdC⟩
    · have hdS : d ∈ S := Finset.mem_of_mem_erase hdroot
      have hdCne : d ≠ C := Finset.ne_of_mem_erase hdroot
      exact False.elim ((hanti d hdS R hR hdne) hdR)

theorem dominant_erase_card_eq_two
    (S : Finset (Normal a b c)) {C : Normal a b c}
    (hcard : S.card = 3) (hdom : IsDominantRoot S C) :
    (S.erase C).card = 2 := by
  rw [Finset.card_erase_of_mem hdom.1, hcard]

/-! ## Mixed reduction -/

/-- In the mixed domain, a live tie cannot be one of the two extra roots of a
dominant configuration.-/
theorem mixed_dominant_tie_mem_core
    (S : Finset (Normal a b c)) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hlive : IsLiveTie S) (hanti : IsRootAntichain S)
    {C : Normal a b c} (hdom : IsDominantRoot S C) :
    liveTiePoint ∈ Normal.divisorDownset C := by
  have htstd := hlive.2.2.2
  rw [hdom.2] at htstd
  rcases htstd with htcore | htextra
  · exact htcore
  · have htS : liveTiePoint ∈ S := Finset.mem_of_mem_erase htextra
    have htne : liveTiePoint ≠ C := Finset.ne_of_mem_erase htextra
    have htborder := dominant_extra_root_mem_principalBorder S ha hanti hdom htS htne
    have htmin := (mem_borderFinset_iff (by simp) liveTiePoint).1 htborder
    have hpred := ((isMinimalBorder_iff (standardSet ({C} :
      Finset (Normal a b c))) liveTiePoint).1 htmin).2
    let qy : Normal a b c := ⟨0, b - 1, c, reduction_a_pos⟩
    let qz : Normal a b c := ⟨0, b, c - 1, reduction_a_pos⟩
    have hqyPred : Normal.predecessor .y liveTiePoint = some qy := by
      have hbpos : 0 < b := by omega
      simp [Normal.predecessor, Normal.yPredecessor, liveTiePoint, qy, hbpos]
    have hqzPred : Normal.predecessor .z liveTiePoint = some qz := by
      have hcpos : 0 < c := by omega
      simp [Normal.predecessor, Normal.zPredecessor, liveTiePoint, qz, hcpos]
    have hqyC : qy ∣ C := by
      obtain ⟨T, hmem, hdvd⟩ :=
        (mem_standardSet_iff ({C} : Finset (Normal a b c)) qy).1
          (hpred .y qy hqyPred)
      have : T = C := by simpa using hmem
      subst T
      exact hdvd
    have hqzC : qz ∣ C := by
      obtain ⟨T, hmem, hdvd⟩ :=
        (mem_standardSet_iff ({C} : Finset (Normal a b c)) qz).1
          (hpred .z qz hqzPred)
      have : T = C := by simpa using hmem
      subst T
      exact hdvd
    have hbounds : b ≤ C.y ∧ c ≤ C.z := by
      rw [Normal.exact_divides_iff] at hqyC hqzC
      simp [Normal.DividesCriterion, qy, qz] at hqyC hqzC
      omega
    have htC : liveTiePoint ∣ C := by
      rw [Normal.exact_divides_iff]
      simp [Normal.DividesCriterion, liveTiePoint, hbounds]
    exact ((hanti liveTiePoint htS C hdom.1 htne) htC).elim

theorem mixed_dominant_core_bounds
    (S : Finset (Normal a b c)) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hlive : IsLiveTie S) (hanti : IsRootAntichain S)
    {C : Normal a b c} (hdom : IsDominantRoot S C) :
    b ≤ C.y ∧ c ≤ C.z := by
  have ht := mixed_dominant_tie_mem_core S ha hb hc hlive hanti hdom
  rw [Normal.mem_divisorDownset_iff] at ht
  simp [Normal.DividesCriterion, liveTiePoint] at ht
  exact ht

def mixedSoclesForPair (pair : MixedAddedPair)
    (r u v : ℕ) (hr : r < a - 1) : Finset (Normal a b c) :=
  match pair with
  | .YZ => mixedSoclesYZ r u v hr
  | .YP => mixedSoclesYP r u v hr
  | .YQ => mixedSoclesYQ r u v hr
  | .ZP => mixedSoclesZP r u v hr
  | .ZQ => mixedSoclesZQ r u v hr
  | .PQ => mixedSoclesPQ r u v hr

theorem mixed_dominant_last_eq_family
    (S : Finset (Normal a b c)) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hcard : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) {r u v : ℕ} (hr : r < a)
    (hlast : r = a - 1)
    (hdom : IsDominantRoot S (mixedCore r u v hr)) :
    S = mixedDominantSoclesLast (a := a) (b := b) (c := c) u v := by
  have huv := mixed_dominant_core_bounds S ha hb hc hlive hanti hdom
  have hu : b ≤ u := by simpa [mixedCore] using huv.1
  have hv : c ≤ v := by simpa [mixedCore] using huv.2
  have heraseCard := dominant_erase_card_eq_two S hcard hdom
  have hsub : S.erase (mixedCore r u v hr) ⊆
      ({mixedY u, mixedZ v} : Finset (Normal a b c)) := by
    intro R hR
    have hRS : R ∈ S := Finset.mem_of_mem_erase hR
    have hne : R ≠ mixedCore r u v hr := Finset.ne_of_mem_erase hR
    have hbdr := dominant_extra_root_mem_principalBorder S ha hanti hdom hRS hne
    have hp := mixedPrincipalBorder_last (r := r) (u := u) (v := v)
      ha hb hc hu hv hlast
    have hp' : borderFinset ({mixedCore r u v hr} :
        Finset (Normal a b c)) = {mixedY u, mixedZ v} := by
      simpa [mixedCore] using hp
    rw [hp'] at hbdr
    exact hbdr
  have htarget : ({mixedY u, mixedZ v} : Finset (Normal a b c)).card = 2 := by
    simp [mixedY, mixedZ]
  have herase : S.erase (mixedCore r u v hr) = {mixedY u, mixedZ v} :=
    Finset.eq_of_subset_of_card_le hsub (by rw [htarget, heraseCard])
  calc
    S = insert (mixedCore r u v hr) (S.erase (mixedCore r u v hr)) :=
      (Finset.insert_erase hdom.1).symm
    _ = insert (mixedCore r u v hr) {mixedY u, mixedZ v} := by rw [herase]
    _ = mixedDominantSoclesLast (a := a) (b := b) (c := c) u v := by
      subst r
      simp [mixedDominantSoclesLast, mixedCore]

theorem mixed_dominant_last_border_card
    (S : Finset (Normal a b c)) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hcard : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) {r u v : ℕ} (hr : r < a)
    (hlast : r = a - 1)
    (hdom : IsDominantRoot S (mixedCore r u v hr)) :
    (borderFinset S).card = 6 := by
  have huv := mixed_dominant_core_bounds S ha hb hc hlive hanti hdom
  have hu : b ≤ u := by simpa [mixedCore] using huv.1
  have hv : c ≤ v := by simpa [mixedCore] using huv.2
  rw [mixed_dominant_last_eq_family S ha hb hc hcard hlive hanti hr hlast hdom]
  exact mixedDominantLast_border_card ha hb hc hu hv

theorem mixed_dominant_below_pair
    (S : Finset (Normal a b c)) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hcard : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) {r u v : ℕ} (hrC : r < a)
    (hr : r < a - 1)
    (hdom : IsDominantRoot S (mixedCore r u v hrC)) :
    ∃ pair : MixedAddedPair,
      S = mixedSoclesForPair (a := a) (b := b) (c := c) pair r u v hr := by
  have huv := mixed_dominant_core_bounds S ha hb hc hlive hanti hdom
  have hu : b ≤ u := by simpa [mixedCore] using huv.1
  have hv : c ≤ v := by simpa [mixedCore] using huv.2
  have heraseCard := dominant_erase_card_eq_two S hcard hdom
  obtain ⟨R, T, hRT, herase⟩ := Finset.card_eq_two.mp heraseCard
  have hRerase : R ∈ S.erase (mixedCore r u v hrC) := by simp [herase]
  have hTerase : T ∈ S.erase (mixedCore r u v hrC) := by simp [herase]
  have hRborder := dominant_extra_root_mem_principalBorder S ha hanti hdom
    (Finset.mem_of_mem_erase hRerase) (Finset.ne_of_mem_erase hRerase)
  have hTborder := dominant_extra_root_mem_principalBorder S ha hanti hdom
    (Finset.mem_of_mem_erase hTerase) (Finset.ne_of_mem_erase hTerase)
  have hp := mixedPrincipalBorder_below (r := r) (u := u) (v := v)
    ha hb hc hu hv hr
  have hp' : borderFinset ({mixedCore r u v hrC} : Finset (Normal a b c)) =
      {mixedY u, mixedZ v, mixedP r u hr, mixedQ r v hr} := by
    simpa [mixedCore] using hp
  rw [hp'] at hRborder hTborder
  have hS : S = insert (mixedCore r u v hrC) {R, T} := by
    rw [← herase]
    exact (Finset.insert_erase hdom.1).symm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hRborder hTborder
  rcases hRborder with rfl | rfl | rfl | rfl <;>
    rcases hTborder with rfl | rfl | rfl | rfl
  all_goals try { exact False.elim (hRT rfl) }
  · refine ⟨.YZ, ?_⟩
    rw [hS]
    ext x
    simp [mixedSoclesForPair, mixedSoclesYZ, mixedCore, or_comm, or_left_comm, or_assoc]
  · refine ⟨.YP, ?_⟩
    rw [hS]
    ext x
    simp [mixedSoclesForPair, mixedSoclesYP, mixedCore, or_comm, or_left_comm, or_assoc]
  · refine ⟨.YQ, ?_⟩
    rw [hS]
    ext x
    simp [mixedSoclesForPair, mixedSoclesYQ, mixedCore, or_comm, or_left_comm, or_assoc]
  · refine ⟨.YZ, ?_⟩
    rw [hS]
    ext x
    simp [mixedSoclesForPair, mixedSoclesYZ, mixedCore, or_comm, or_left_comm, or_assoc]
  · refine ⟨.ZP, ?_⟩
    rw [hS]
    ext x
    simp [mixedSoclesForPair, mixedSoclesZP, mixedCore, or_comm, or_left_comm, or_assoc]
  · refine ⟨.ZQ, ?_⟩
    rw [hS]
    ext x
    simp [mixedSoclesForPair, mixedSoclesZQ, mixedCore, or_comm, or_left_comm, or_assoc]
  · refine ⟨.YP, ?_⟩
    rw [hS]
    ext x
    simp [mixedSoclesForPair, mixedSoclesYP, mixedCore, or_comm, or_left_comm, or_assoc]
  · refine ⟨.ZP, ?_⟩
    rw [hS]
    ext x
    simp [mixedSoclesForPair, mixedSoclesZP, mixedCore, or_comm, or_left_comm, or_assoc]
  · refine ⟨.PQ, ?_⟩
    rw [hS]
    ext x
    simp [mixedSoclesForPair, mixedSoclesPQ, mixedCore, or_comm, or_left_comm, or_assoc]
  · refine ⟨.YQ, ?_⟩
    rw [hS]
    ext x
    simp [mixedSoclesForPair, mixedSoclesYQ, mixedCore, or_comm, or_left_comm, or_assoc]
  · refine ⟨.ZQ, ?_⟩
    rw [hS]
    ext x
    simp [mixedSoclesForPair, mixedSoclesZQ, mixedCore, or_comm, or_left_comm, or_assoc]
  · refine ⟨.PQ, ?_⟩
    rw [hS]
    ext x
    simp [mixedSoclesForPair, mixedSoclesPQ, mixedCore, or_comm, or_left_comm, or_assoc]

inductive MixedDominantFourBorderSurvivor
    (S : Finset (Normal a b c)) : Prop where
  | yz {r u v : ℕ} (hr : r < a - 1) (hr0 : r = 0)
      (hb1 : b = 1) (hc1 : c = 1) (hu : b ≤ u) (hv : c ≤ v)
      (roots : S = mixedSoclesYZ r u v hr) : MixedDominantFourBorderSurvivor S
  | yq {r u v : ℕ} (hr : r < a - 1) (hc1 : c = 1)
      (hu : b ≤ u) (hv : c ≤ v)
      (roots : S = mixedSoclesYQ r u v hr) : MixedDominantFourBorderSurvivor S
  | zp {r u v : ℕ} (hr : r < a - 1) (hb1 : b = 1)
      (hu : b ≤ u) (hv : c ≤ v)
      (roots : S = mixedSoclesZP r u v hr) : MixedDominantFourBorderSurvivor S
  | pq {r u v : ℕ} (hr : r < a - 1) (hrlast : r = a - 2)
      (hu : b ≤ u) (hv : c ≤ v) (nonprimitive : 1 < u ∨ 1 < v)
      (roots : S = mixedSoclesPQ r u v hr) : MixedDominantFourBorderSurvivor S

theorem mixed_dominant_four_border_survivor
    (S : Finset (Normal a b c)) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hcard : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) {C : Normal a b c}
    (hdom : IsDominantRoot S C) (hborder : (borderFinset S).card = 4) :
    MixedDominantFourBorderSurvivor S := by
  rcases C with ⟨r, u, v, hrC⟩
  have huv := mixed_dominant_core_bounds S ha hb hc hlive hanti hdom
  have hu : b ≤ u := by simpa [mixedCore] using huv.1
  have hv : c ≤ v := by simpa [mixedCore] using huv.2
  by_cases hlast : r = a - 1
  · have h6 := mixed_dominant_last_border_card S ha hb hc hcard hlive
      hanti hrC hlast hdom
    omega
  · have hr : r < a - 1 := by omega
    obtain ⟨pair, hS⟩ :=
      mixed_dominant_below_pair S ha hb hc hcard hlive hanti hrC hr hdom
    have hpairCard : mixedDominantBorderCard (a := a) (b := b) (c := c)
        pair r u v hr = 4 := by
      cases pair <;> simpa [mixedSoclesForPair, mixedDominantBorderCard, hS]
        using hborder
    rcases mixedDominant_card_eq_four_survivors pair ha hb hc hu hv hr
      hpairCard with hYZ | hYQ | hZP | hPQ
    · rcases hYZ with ⟨rfl, hr0, hb1, hc1⟩
      exact .yz hr (by omega) hb1 hc1 hu hv
        (by simpa [mixedSoclesForPair] using hS)
    · rcases hYQ with ⟨rfl, hc1⟩
      exact .yq hr hc1 hu hv (by simpa [mixedSoclesForPair] using hS)
    · rcases hZP with ⟨rfl, hb1⟩
      exact .zp hr hb1 hu hv (by simpa [mixedSoclesForPair] using hS)
    · rcases hPQ with ⟨rfl, hrlast, huv1⟩
      exact .pq hr (by omega) hu hv huv1
        (by simpa [mixedSoclesForPair] using hS)

/-! ## Pure reduction -/

inductive PureDominantBranch (S : Finset (Normal a b 0)) : Prop where
  | below {r u v : ℕ} (hr : r < a - 1) (hu : b ≤ u)
      (roots : S = pureDominantSoclesBelow r u v hr) : PureDominantBranch S
  | lastTieExtra {v : ℕ}
      (roots : S = pureDominantSoclesLast v) : PureDominantBranch S
  | lastTieCore {u v : ℕ} (hu : b ≤ u)
      (roots : S = pureDominantSoclesLastCore u v) : PureDominantBranch S

theorem pure_dominant_three_branch_reduction
    (S : Finset (Normal a b 0)) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcard : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) {C : Normal a b 0}
    (hdom : IsDominantRoot S C) : PureDominantBranch S := by
  rcases C with ⟨r, u, v, hrC⟩
  have htstd := hlive.2.2.2
  rw [hdom.2] at htstd
  rcases htstd with htcore | htextra
  · have hu : b ≤ u := by
      rw [Normal.mem_divisorDownset_iff] at htcore
      simp [Normal.DividesCriterion, liveTiePoint] at htcore
      exact htcore
    by_cases hlast : r = a - 1
    · have heraseCard := dominant_erase_card_eq_two S hcard hdom
      have heraseCard' : (S.erase (pureCore r u v hrC)).card = 2 := by
        simpa [pureCore] using heraseCard
      have hsub : S.erase (pureCore r u v hrC) ⊆
          ({pureH r u hrC, pureZ v} : Finset (Normal a b 0)) := by
        intro R hR
        have hbdr := dominant_extra_root_mem_principalBorder S ha hanti hdom
          (Finset.mem_of_mem_erase hR) (Finset.ne_of_mem_erase hR)
        change R ∈ borderFinset ({pureCore r u v hrC} :
          Finset (Normal a b 0)) at hbdr
        have hp := purePrincipalBorder_last (r := r) (u := u) (v := v)
          ha hb (by omega) hlast
        have hp' : borderFinset ({pureCore r u v hrC} :
            Finset (Normal a b 0)) = {pureH r u hrC, pureZ v} := by
          simpa [pureCore, pureH] using hp
        rw [hp'] at hbdr
        exact hbdr
      have htarget : ({pureH r u hrC, pureZ v} :
          Finset (Normal a b 0)).card = 2 := by
        simp [pureH, pureZ, hlast]
      have herase : S.erase (pureCore r u v hrC) = {pureH r u hrC, pureZ v} :=
        Finset.eq_of_subset_of_card_le hsub (by rw [htarget, heraseCard'])
      apply PureDominantBranch.lastTieCore hu
      calc
        S = insert (pureCore r u v hrC) (S.erase (pureCore r u v hrC)) :=
          (Finset.insert_erase hdom.1).symm
        _ = insert (pureCore r u v hrC) {pureH r u hrC, pureZ v} := by rw [herase]
        _ = pureDominantSoclesLastCore (a := a) (b := b) u v := by
          subst r
          simp [pureDominantSoclesLastCore, pureCore, pureH, pureZ]
    · have hr : r < a - 1 := by omega
      have heraseCard := dominant_erase_card_eq_two S hcard hdom
      have heraseCard' : (S.erase (pureCore r u v hrC)).card = 2 := by
        simpa [pureCore] using heraseCard
      have hsub : S.erase (pureCore r u v hrC) ⊆
          ({pureH r u hrC, pureZ v} : Finset (Normal a b 0)) := by
        intro R hR
        have hbdr := dominant_extra_root_mem_principalBorder S ha hanti hdom
          (Finset.mem_of_mem_erase hR) (Finset.ne_of_mem_erase hR)
        change R ∈ borderFinset ({pureCore r u v hrC} :
          Finset (Normal a b 0)) at hbdr
        have hp := purePrincipalBorder_below (r := r) (u := u) (v := v)
          ha hb hu hr
        have hp' : borderFinset ({pureCore r u v hrC} :
            Finset (Normal a b 0)) = {pureH r u hrC, pureZ v} := by
          simpa [pureCore, pureH] using hp
        rw [hp'] at hbdr
        exact hbdr
      have htarget : ({pureH r u hrC, pureZ v} :
          Finset (Normal a b 0)).card = 2 := by
        simp [pureH, pureZ, hr]
      have herase : S.erase (pureCore r u v hrC) = {pureH r u hrC, pureZ v} :=
        Finset.eq_of_subset_of_card_le hsub (by rw [htarget, heraseCard'])
      apply PureDominantBranch.below hr hu
      calc
        S = insert (pureCore r u v hrC) (S.erase (pureCore r u v hrC)) :=
          (Finset.insert_erase hdom.1).symm
        _ = insert (pureCore r u v hrC) {pureH r u hrC, pureZ v} := by rw [herase]
        _ = pureDominantSoclesBelow (a := a) (b := b) r u v hr := by
          simp [pureDominantSoclesBelow, pureCore, pureH, pureZ, hr]
  · have htS : liveTiePoint ∈ S := Finset.mem_of_mem_erase htextra
    have htne : liveTiePoint ≠ pureCore r u v hrC := Finset.ne_of_mem_erase htextra
    have htborder := dominant_extra_root_mem_principalBorder S ha hanti hdom htS htne
    have htmin := (mem_borderFinset_iff (by simp) liveTiePoint).1 htborder
    have hpred := ((isMinimalBorder_iff (standardSet ({pureCore r u v hrC} :
      Finset (Normal a b 0))) liveTiePoint).1 htmin).2
    let qy : Normal a b 0 := ⟨0, b - 1, 0, reduction_a_pos⟩
    let qx : Normal a b 0 := ⟨a - 1, 0, 0, by omega⟩
    have hqyPred : Normal.predecessor .y liveTiePoint = some qy := by
      have hbpos : 0 < b := by omega
      simp [Normal.predecessor, Normal.yPredecessor, liveTiePoint, qy, hbpos]
    have hqxPred : Normal.predecessor .x liveTiePoint = some qx := by
      simp [Normal.predecessor, Normal.wrappedXPredecessor, liveTiePoint,
        qx, hb]
    have hqyC : qy ∣ pureCore r u v hrC := by
      obtain ⟨T, hT, hdvd⟩ :=
        (mem_standardSet_iff ({pureCore r u v hrC} :
          Finset (Normal a b 0)) qy).1 (hpred .y qy hqyPred)
      have : T = pureCore r u v hrC := by simpa using hT
      subst T
      exact hdvd
    have hqxC : qx ∣ pureCore r u v hrC := by
      obtain ⟨T, hT, hdvd⟩ :=
        (mem_standardSet_iff ({pureCore r u v hrC} :
          Finset (Normal a b 0)) qx).1 (hpred .x qx hqxPred)
      have : T = pureCore r u v hrC := by simpa using hT
      subst T
      exact hdvd
    have htNotCore : ¬(liveTiePoint : Normal a b 0) ∣
        (pureCore r u v hrC : Normal a b 0) := by
      intro htC
      exact (hanti liveTiePoint htS (pureCore r u v hrC) hdom.1 htne) htC
    rw [Normal.exact_divides_iff] at hqyC hqxC htNotCore
    simp [Normal.DividesCriterion, qy, qx, pureCore, liveTiePoint] at hqyC hqxC htNotCore
    have hlast : r = a - 1 := by omega
    have hu : u = b - 1 := by omega
    have heraseCard := dominant_erase_card_eq_two S hcard hdom
    have heraseCard' : (S.erase (pureCore r u v hrC)).card = 2 := by
      simpa [pureCore] using heraseCard
    have hsub : S.erase (pureCore r u v hrC) ⊆
        ({pureH r u hrC, pureZ v} : Finset (Normal a b 0)) := by
      intro R hR
      have hbdr := dominant_extra_root_mem_principalBorder S ha hanti hdom
        (Finset.mem_of_mem_erase hR) (Finset.ne_of_mem_erase hR)
      change R ∈ borderFinset ({pureCore r u v hrC} :
        Finset (Normal a b 0)) at hbdr
      have hp := purePrincipalBorder_last (r := r) (u := u) (v := v)
        ha hb (by omega) hlast
      have hp' : borderFinset ({pureCore r u v hrC} :
          Finset (Normal a b 0)) = {pureH r u hrC, pureZ v} := by
        simpa [pureCore, pureH] using hp
      rw [hp'] at hbdr
      exact hbdr
    have htarget : ({pureH r u hrC, pureZ v} :
        Finset (Normal a b 0)).card = 2 := by
      simp [pureH, pureZ, hlast]
    have herase : S.erase (pureCore r u v hrC) = {pureH r u hrC, pureZ v} :=
      Finset.eq_of_subset_of_card_le hsub (by rw [htarget, heraseCard'])
    apply PureDominantBranch.lastTieExtra
    calc
      S = insert (pureCore r u v hrC) (S.erase (pureCore r u v hrC)) :=
        (Finset.insert_erase hdom.1).symm
      _ = insert (pureCore r u v hrC) {pureH r u hrC, pureZ v} := by rw [herase]
      _ = pureDominantSoclesLast (a := a) (b := b) v := by
        subst r
        subst u
        simp [pureDominantSoclesLast, pureCore, pureH, pureZ]

theorem pure_dominant_border_card_ne_four_general
    (S : Finset (Normal a b 0)) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcard : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) {C : Normal a b 0}
    (hdom : IsDominantRoot S C) : (borderFinset S).card ≠ 4 := by
  rcases pure_dominant_three_branch_reduction S ha hb hcard hlive hanti hdom with
    ⟨hr, hu, hroots⟩ | ⟨hroots⟩ | ⟨hu, hroots⟩
  · rw [hroots]
    exact (pureDominant_card_ne_four ha hb).1 hr hu
  · rw [hroots]
    exact (pureDominant_card_ne_four (r := 0) (u := 0) (v := _)
      ha hb).2
  · rw [hroots]
    exact pureDominantBorder_lastCore_card_ne_four ha hb hu

end P23.OneTie
