import Tengoku.NsP23.P23.OneTie.CoverShapes
import Tengoku.NsP23.P23.OneTie.SemanticBorder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact borders for the type-three top-deletion shape

The load-bearing lemma below compares the punctured principal downset with
the unpunctured one through divisibility-minimality.  The three specializations
then reuse the frozen principal-border formulas.
-/

namespace P23.OneTie

variable {a b c r u v : ℕ} [NeZero a]

private theorem standardSet_singleton (T : Normal a b c) :
    standardSet ({T} : Finset (Normal a b c)) = Normal.divisorDownset T := by
  ext p
  simp [standardSet, Normal.divisorDownset]

/-- Removing the top of a principal downset adds that top to the border,
provided no old principal-border point is divisible by the top.
@isnad1 id=eq.4h5v.s7.25ca5407e33c from=translated src=- shape=7ad56217 vocab=d9df6a70
-/
theorem topDeletion_border_eq_insert_principal
    (S : Finset (Normal a b c)) (T : Normal a b c)
    (ha : 2 ≤ a) (hS : S.Nonempty)
    (hstd : standardSet S = Normal.divisorDownset T \ {T})
    (hnodiv : ∀ m ∈ borderFinset ({T} : Finset (Normal a b c)), ¬T ∣ m) :
    borderFinset S = insert T (borderFinset ({T} : Finset (Normal a b c))) := by
  classical
  apply Finset.ext
  intro m
  rw [mem_borderFinset_iff hS, Finset.mem_insert,
    mem_borderFinset_iff (by simp),
    isMinimalBorder_iff_isDivisibilityMinimalKilled S m
      (variableGenerators_ne_one_of_two_le ha),
    isMinimalBorder_iff_isDivisibilityMinimalKilled ({T} : Finset (Normal a b c)) m
      (variableGenerators_ne_one_of_two_le ha)]
  rw [hstd, standardSet_singleton]
  constructor
  · rintro ⟨hmout, hproper⟩
    by_cases hmT : m = T
    · exact Or.inl hmT
    · right
      have hmD : m ∉ Normal.divisorDownset T := by
        intro hmD
        exact hmout ⟨hmD, by simpa [hmT]⟩
      refine ⟨hmD, ?_⟩
      intro d hdm hne
      exact (hproper d hdm hne).1
  · rintro (rfl | hm)
    · refine ⟨?_, ?_⟩
      · simp
      · intro d hdT hdne
        exact ⟨hdT, by simpa [eq_comm] using hdne⟩
    · rcases hm with ⟨hmout, hproper⟩
      have hmBorder : m ∈ borderFinset ({T} : Finset (Normal a b c)) := by
        rw [mem_borderFinset_iff (by simp),
          isMinimalBorder_iff_isDivisibilityMinimalKilled
            ({T} : Finset (Normal a b c)) m
            (variableGenerators_ne_one_of_two_le ha), standardSet_singleton]
        exact ⟨hmout, hproper⟩
      have hTnmid : ¬T ∣ m := hnodiv m hmBorder
      refine ⟨?_, ?_⟩
      · intro hmD
        exact hmout hmD.1
      · intro d hdm hne
        refine ⟨hproper d hdm hne, ?_⟩
        intro hdT
        subst d
        exact hTnmid hdm

def topDeletionMixedBelowExpected (T : Normal a b c) (hr : r < a - 1) :
    Finset (Normal a b c) :=
  insert T
    {mixedY (a := a) (b := b) (c := c) u,
      mixedZ (a := a) (b := b) (c := c) v,
      mixedP (a := a) (b := b) (c := c) r u hr,
      mixedQ (a := a) (b := b) (c := c) r v hr}

/--
@isnad1 id=eq.8h7v.s7.77d2feea2387 from=translated src=- shape=ab3dff17 vocab=92a632fd
-/
theorem topDeletionMixedBelow_border_exact
    (S : Finset (Normal a b c))
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1)
    (hS : S.Nonempty)
    (hstd : standardSet S =
      Normal.divisorDownset (mixedCore (a := a) (b := b) (c := c) r u v (by omega)) \
        {mixedCore (a := a) (b := b) (c := c) r u v (by omega)}) :
    borderFinset S =
      topDeletionMixedBelowExpected (u := u) (v := v)
        (mixedCore (a := a) (b := b) (c := c) r u v (by omega)) hr := by
  let T := mixedCore (a := a) (b := b) (c := c) r u v (by omega)
  rw [topDeletionMixedBelowExpected]
  rw [← mixedPrincipalBorder_below ha hb hc hu hv hr]
  apply topDeletion_border_eq_insert_principal S T ha hS hstd
  intro m hm hdiv
  rw [mixedPrincipalBorder_below ha hb hc hu hv hr] at hm
  rcases (Finset.mem_insert.mp hm) with rfl | hm
  · simp [T, mixedCore, mixedY, Normal.exact_divides_iff,
      Normal.DividesCriterion] at hdiv
    omega
  rcases (Finset.mem_insert.mp hm) with rfl | hm
  · simp [T, mixedCore, mixedZ, Normal.exact_divides_iff,
      Normal.DividesCriterion] at hdiv
    omega
  rcases (Finset.mem_insert.mp hm) with rfl | hm
  · simp [T, mixedCore, mixedP, Normal.exact_divides_iff,
      Normal.DividesCriterion] at hdiv
    omega
  · simp only [Finset.mem_singleton] at hm
    subst m
    simp [T, mixedCore, mixedQ, Normal.exact_divides_iff,
      Normal.DividesCriterion] at hdiv
    omega

/--
@isnad1 id=eq.8h7v.s7.7cda3b37ae7f from=translated src=- shape=a4ee4560 vocab=4bf3fd1b
-/
theorem topDeletionMixedBelow_border_card
    (S : Finset (Normal a b c))
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1)
    (hS : S.Nonempty)
    (hstd : standardSet S =
      Normal.divisorDownset (mixedCore (a := a) (b := b) (c := c) r u v (by omega)) \
        {mixedCore (a := a) (b := b) (c := c) r u v (by omega)}) :
    (borderFinset S).card = 5 := by
  rw [topDeletionMixedBelow_border_exact S ha hb hc hu hv hr hS hstd]
  rw [topDeletionMixedBelowExpected,
    ← mixedPrincipalBorder_below ha hb hc hu hv hr]
  rw [Finset.card_insert_of_notMem]
  · rw [mixedPrincipalBorder_below_card ha hb hc hu hv hr]
  · rw [mem_borderFinset_iff (by simp)]
    simp [IsMinimalBorder, standardSet]

def topDeletionMixedLastExpected (T : Normal a b c) : Finset (Normal a b c) :=
  {T, mixedY (a := a) (b := b) (c := c) u,
    mixedZ (a := a) (b := b) (c := c) v}

/--
@isnad1 id=eq.8h7v.s7.c71d2a8b2def from=translated src=- shape=074d6e08 vocab=4222a92b
-/
theorem topDeletionMixedLast_border_exact
    (S : Finset (Normal a b c))
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r = a - 1)
    (hS : S.Nonempty)
    (hstd : standardSet S =
      Normal.divisorDownset (mixedCore (a := a) (b := b) (c := c) r u v (by omega)) \
        {mixedCore (a := a) (b := b) (c := c) r u v (by omega)}) :
    borderFinset S = topDeletionMixedLastExpected (u := u) (v := v)
      (mixedCore (a := a) (b := b) (c := c) r u v (by omega)) := by
  let T := mixedCore (a := a) (b := b) (c := c) r u v (by omega)
  rw [topDeletionMixedLastExpected]
  rw [← mixedPrincipalBorder_last ha hb hc hu hv hr]
  apply topDeletion_border_eq_insert_principal S T ha hS hstd
  intro m hm hdiv
  rw [mixedPrincipalBorder_last ha hb hc hu hv hr] at hm
  rcases (Finset.mem_insert.mp hm) with rfl | hm
  · simp [T, mixedCore, mixedY, Normal.exact_divides_iff,
      Normal.DividesCriterion] at hdiv
    omega
  · simp only [Finset.mem_singleton] at hm
    subst m
    simp [T, mixedCore, mixedZ, Normal.exact_divides_iff,
      Normal.DividesCriterion] at hdiv
    omega

/--
@isnad1 id=eq.8h7v.s7.179c592cb9b2 from=translated src=- shape=c02adea1 vocab=1d349ed7
-/
theorem topDeletionMixedLast_border_card
    (S : Finset (Normal a b c))
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r = a - 1)
    (hS : S.Nonempty)
    (hstd : standardSet S =
      Normal.divisorDownset (mixedCore (a := a) (b := b) (c := c) r u v (by omega)) \
        {mixedCore (a := a) (b := b) (c := c) r u v (by omega)}) :
    (borderFinset S).card = 3 := by
  rw [topDeletionMixedLast_border_exact S ha hb hc hu hv hr hS hstd]
  simp [topDeletionMixedLastExpected, mixedCore, mixedY, mixedZ]

def topDeletionPureExpected (T : Normal a b 0) (hr : r < a) :
    Finset (Normal a b 0) :=
  {T, pureH (a := a) (b := b) r u hr, pureZ (a := a) (b := b) v}

/--
@isnad1 id=eq.7h6v.s7.8b85985e378e from=translated src=- shape=f5f02784 vocab=d7cc33ac
-/
theorem topDeletionPure_border_exact
    (S : Finset (Normal a b 0))
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hu : b ≤ u) (hv : 1 ≤ v)
    (hr : r < a) (hS : S.Nonempty)
    (hstd : standardSet S =
      Normal.divisorDownset (pureCore (a := a) (b := b) r u v hr) \
        {pureCore (a := a) (b := b) r u v hr}) :
    borderFinset S = topDeletionPureExpected (u := u) (v := v)
      (pureCore (a := a) (b := b) r u v hr) hr := by
  let T := pureCore (a := a) (b := b) r u v hr
  rw [topDeletionPureExpected]
  by_cases hlast : r = a - 1
  · rw [← purePrincipalBorder_last ha hb (by omega) hlast]
    apply topDeletion_border_eq_insert_principal S T ha hS hstd
    intro m hm hdiv
    rw [purePrincipalBorder_last ha hb (by omega) hlast] at hm
    rcases (Finset.mem_insert.mp hm) with rfl | hm
    · simp [T, pureCore, pureH, hlast, Normal.exact_divides_iff,
        Normal.DividesCriterion] at hdiv
      omega
    · simp only [Finset.mem_singleton] at hm
      subst m
      simp [T, pureCore, pureZ, Normal.exact_divides_iff,
        Normal.DividesCriterion] at hdiv
      omega
  · have hbelow : r < a - 1 := by omega
    rw [← purePrincipalBorder_below ha hb hu hbelow]
    apply topDeletion_border_eq_insert_principal S T ha hS hstd
    intro m hm hdiv
    rw [purePrincipalBorder_below ha hb hu hbelow] at hm
    rcases (Finset.mem_insert.mp hm) with rfl | hm
    · simp [T, pureCore, pureH, hbelow, Normal.exact_divides_iff,
        Normal.DividesCriterion] at hdiv
      omega
    · simp only [Finset.mem_singleton] at hm
      subst m
      simp [T, pureCore, pureZ, Normal.exact_divides_iff,
        Normal.DividesCriterion] at hdiv
      omega

/--
@isnad1 id=eq.7h6v.s7.23db9c11e9fd from=translated src=- shape=ddd60f6a vocab=3f1fbcab
-/
theorem topDeletionPure_border_card
    (S : Finset (Normal a b 0))
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hu : b ≤ u) (hv : 1 ≤ v)
    (hr : r < a) (hS : S.Nonempty)
    (hstd : standardSet S =
      Normal.divisorDownset (pureCore (a := a) (b := b) r u v hr) \
        {pureCore (a := a) (b := b) r u v hr}) :
    (borderFinset S).card = 3 := by
  rw [topDeletionPure_border_exact S ha hb hu hv hr hS hstd]
  by_cases hlast : r = a - 1
  · simp [topDeletionPureExpected, pureCore, pureH, hlast, pureZ]
  · have hbelow : r < a - 1 := by omega
    simp [topDeletionPureExpected, pureCore, pureH, hbelow, pureZ]

/-- In the live type-three H5 domain, deleting a principal top has border
cardinality three or five.  The live bounds on the deleted top are derived
from `IsLiveTie`; they are not extra classification hypotheses.
@isnad1 id=or.5h4v.s7.506d0838ba92 from=translated src=- shape=5d1b5dea vocab=76edb87d
-/
theorem typeThreeTopDeletion_border_card
    {S : Finset (Normal a b c)}
    (ha : 2 ≤ a)
    (hdomain : (1 ≤ b ∧ 1 ≤ c) ∨ (2 ≤ b ∧ c = 0))
    (hcardS : S.card = 3) (hlive : IsLiveTie S)
    (htop : IsTopDeletion S) :
    (borderFinset S).card = 3 ∨ (borderFinset S).card = 5 := by
  rcases htop with ⟨T, _, _, hstd⟩
  rcases T with ⟨r, u, v, hrA⟩
  have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  rcases (mem_standardSet_iff S liveTiePoint).1 hlive.2.2.2 with
    ⟨q, hqS, hqdiv⟩
  have hqstd : q ∈ standardSet S :=
    (mem_standardSet_iff S q).2 ⟨q, hqS, dvd_refl q⟩
  rw [hstd] at hqstd
  have htieT : liveTiePoint ∣ (⟨r, u, v, hrA⟩ : Normal a b c) :=
    dvd_trans hqdiv hqstd.1
  have hbounds := (Normal.exact_divides_iff liveTiePoint
    (⟨r, u, v, hrA⟩ : Normal a b c)).1 htieT
  have hu : b ≤ u := by
    simp [liveTiePoint, Normal.DividesCriterion] at hbounds
    omega
  rcases hdomain with ⟨hb, hc⟩ | ⟨hb, hc0⟩
  · have hv : c ≤ v := by
      simp [liveTiePoint, Normal.DividesCriterion] at hbounds
      omega
    by_cases hlast : r = a - 1
    · exact Or.inl (topDeletionMixedLast_border_card S ha hb hc hu hv hlast
        hnonempty hstd)
    · have hbelow : r < a - 1 := by omega
      exact Or.inr (topDeletionMixedBelow_border_card S ha hb hc hu hv hbelow
        hnonempty hstd)
  · subst c
    rcases (mem_standardSet_iff S (Normal.zGenerator : Normal a b 0)).1
        hlive.2.2.1 with ⟨qz, hqzS, hzdiv⟩
    have hqzstd : qz ∈ standardSet S :=
      (mem_standardSet_iff S qz).2 ⟨qz, hqzS, dvd_refl qz⟩
    rw [hstd] at hqzstd
    have hzT : (Normal.zGenerator : Normal a b 0) ∣
        (⟨r, u, v, hrA⟩ : Normal a b 0) := dvd_trans hzdiv hqzstd.1
    have hv : 1 ≤ v := by
      have hz := (Normal.exact_divides_iff
        (Normal.zGenerator : Normal a b 0)
        (⟨r, u, v, hrA⟩ : Normal a b 0)).1 hzT
      simp [Normal.zGenerator, Normal.DividesCriterion] at hz
      omega
    exact Or.inl (topDeletionPure_border_card S ha hb hu hv hrA
      hnonempty hstd)

/--
@isnad1 id=ne.5h4v.s6.f7a20090d1c4 from=translated src=- shape=8827c172 vocab=76edb87d
-/
theorem topDeletion_border_card_ne_four
    {S : Finset (Normal a b c)}
    (ha : 2 ≤ a)
    (hdomain : (1 ≤ b ∧ 1 ≤ c) ∨ (2 ≤ b ∧ c = 0))
    (hcardS : S.card = 3) (hlive : IsLiveTie S)
    (htop : IsTopDeletion S) : (borderFinset S).card ≠ 4 := by
  rcases typeThreeTopDeletion_border_card ha hdomain hcardS hlive htop with
    h3 | h5 <;> omega

end P23.OneTie
