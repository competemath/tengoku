import Tengoku.NsP23.P23.Artin.MaximalIdealTrace
import Tengoku.NsP23.P23.Presentation.MonomialQuotient
import Tengoku.Seed.LinearAlgebra.Basis.Basic
import Tengoku.Seed.RingTheory.LocalRing.Basic
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic
import Tengoku.Seed.RingTheory.Nilpotent.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Locality, algebraic socle, and type of the direct finite model

This module stays inside the direct standard-monomial algebra.  It proves
locality, identifies the algebraic socle with the selected-root span, and
computes its dimension.  No polynomial-quotient trace transport is used.
-/

namespace P23.Artin

noncomputable section

open P23.OneTie P23.Presentation

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

private theorem normalWeight_pow (p : Normal a b c) (n : ℕ) :
    normalWeight (p ^ n) = n * normalWeight p := by
  induction n with
  | zero => simp [normalWeight]
  | succ n ih =>
      rw [pow_succ, normalWeight_mul, ih]
      simp [Nat.succ_mul]

/-- A finite upper bound for the weights of all surviving monomials.-/
def standardWeightBound (S : Finset (Normal a b c)) : ℕ :=
  ∑ p ∈ standardFinset S, normalWeight p

private theorem normalWeight_le_standardWeightBound
    (S : Finset (Normal a b c)) {p : Normal a b c}
    (hp : p ∈ standardFinset S) :
    normalWeight p ≤ standardWeightBound S := by
  unfold standardWeightBound
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp

private theorem variable_pow_not_mem_standardFinset
    (S : Finset (Normal a b c)) (hdom : IsLiveParameterDomain a b c)
    (e : Direction) :
    e.generator ^ (standardWeightBound S + 1) ∉ standardFinset S := by
  intro hmem
  have hle := normalWeight_le_standardWeightBound S hmem
  rw [normalWeight_pow] at hle
  have hpos : 0 < normalWeight (e.generator : Normal a b c) :=
    normalWeight_pos_of_ne_one hdom e.generator
      (variableGenerators_ne_one_of_two_le hdom.1 e)
  nlinarith

private theorem X_pow_formula (S : Finset (Normal a b c))
    (hS : S.Nonempty) (p : Normal a b c) (hp : p ∈ standardFinset S) :
    ∀ n : ℕ,
      (X (k := k) S p hp) ^ n =
        if h : p ^ n ∈ standardFinset S then X (k := k) S (p ^ n) h else 0 := by
  intro n
  induction n with
  | zero =>
      have h1 := one_mem_standardFinset S hS
      simp [h1, MonomialArtin.X_one (k := k) S hS]
  | succ n ih =>
      rw [pow_succ, ih]
      by_cases hn : p ^ n ∈ standardFinset S
      · simp only [dite_eq_left hn]
        rw [MonomialArtin.X_mul_X]
        simp only [pow_succ]
      · have hsucc : p ^ (n + 1) ∉ standardFinset S := by
          intro hmem
          apply hn
          apply MonomialArtin.mem_standardFinset_of_mul_mem_left S
          simpa [pow_succ] using hmem
        simp [hn, hsucc]

/-- Every live variable basis vector is nilpotent.  The exponent is the sum
of the weights of the finite standard set plus one.-/
theorem variableBasis_isNilpotent (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hdom : IsLiveParameterDomain a b c)
    (hlive : IsLiveTie S) (e : Direction) :
    IsNilpotent
      (X (k := k) S e.generator
        ((mem_standardFinset_iff_standardSet S _).2 (by
          cases e with
          | x => exact hlive.1
          | y => exact hlive.2.1
          | z => exact hlive.2.2.1))) := by
  let he : e.generator ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 (by
      cases e with
      | x => exact hlive.1
      | y => exact hlive.2.1
      | z => exact hlive.2.2.1)
  refine ⟨standardWeightBound S + 1, ?_⟩
  rw [X_pow_formula (k := k) S hS e.generator he]
  simp [variable_pow_not_mem_standardFinset S hdom e]

theorem xBasis_isNilpotent (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hdom : IsLiveParameterDomain a b c)
    (hlive : IsLiveTie S) :
    IsNilpotent
      (X (k := k) S Normal.xGenerator
        ((mem_standardFinset_iff_standardSet S _).2 hlive.1)) :=
  variableBasis_isNilpotent (k := k) S hS hdom hlive .x

theorem yBasis_isNilpotent (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hdom : IsLiveParameterDomain a b c)
    (hlive : IsLiveTie S) :
    IsNilpotent
      (X (k := k) S Normal.yGenerator
        ((mem_standardFinset_iff_standardSet S _).2 hlive.2.1)) :=
  variableBasis_isNilpotent (k := k) S hS hdom hlive .y

theorem zBasis_isNilpotent (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hdom : IsLiveParameterDomain a b c)
    (hlive : IsLiveTie S) :
    IsNilpotent
      (X (k := k) S Normal.zGenerator
        ((mem_standardFinset_iff_standardSet S _).2 hlive.2.2.1)) :=
  variableBasis_isNilpotent (k := k) S hS hdom hlive .z

/-- Every maximal ideal is the frozen augmentation ideal.-/
theorem maximalIdeal_eq_augmentationIdeal
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (I : Ideal (MonomialArtin k S)) (hI : I.IsMaximal) :
    I = augmentationIdeal (k := k) S hS hdom := by
  have hvars : variableIdeal (k := k) S hlive ≤ I := by
    apply Ideal.span_le.2
    intro v hv
    simp only [variableBasisSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact (nilpotent_iff_mem_prime.mp
        (xBasis_isNilpotent (k := k) S hS hdom hlive)) I hI.isPrime
    · exact (nilpotent_iff_mem_prime.mp
        (yBasis_isNilpotent (k := k) S hS hdom hlive)) I hI.isPrime
    · exact (nilpotent_iff_mem_prime.mp
        (zBasis_isNilpotent (k := k) S hS hdom hlive)) I hI.isPrime
  have haug : augmentationIdeal (k := k) S hS hdom ≤ I := by
    rw [← variableIdeal_eq_augmentationIdeal (k := k) S hS hdom hlive]
    exact hvars
  exact (augmentationIdeal_isMaximal (k := k) S hS hdom).eq_of_le hI.ne_top haug |>.symm

/-- Scope-clean local-ring structure obtained from the unique maximal ideal.
It is a theorem rather than a global instance because liveness is proof data.-/
theorem directIsLocalRing (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S) :
    IsLocalRing (MonomialArtin k S) := by
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨augmentationIdeal (k := k) S hS hdom,
    augmentationIdeal_isMaximal (k := k) S hS hdom, ?_⟩
  intro I hI
  exact maximalIdeal_eq_augmentationIdeal (k := k) S hS hdom hlive I hI

/-- Under the locally installed structure, Mathlib's maximal ideal is the
frozen augmentation ideal.-/
theorem localMaximalIdeal_eq_augmentationIdeal
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S) :
    letI := directIsLocalRing (k := k) S hS hdom hlive
    IsLocalRing.maximalIdeal (MonomialArtin k S) =
      augmentationIdeal (k := k) S hS hdom := by
  letI := directIsLocalRing (k := k) S hS hdom hlive
  exact IsLocalRing.eq_maximalIdeal
    (augmentationIdeal_isMaximal (k := k) S hS hdom) |>.symm

/-- The ideal of algebra elements annihilating one fixed vector under
multiplication.-/
private def elementAnnihilatorIdeal (S : Finset (Normal a b c))
    (v : MonomialArtin k S) :
    Ideal (MonomialArtin k S) where
  carrier := {r | r * v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro r s hr hs
    change r * v = 0 at hr
    change s * v = 0 at hs
    simp [add_mul, hr, hs]
  smul_mem' := by
    intro r s hs
    change (r * s) * v = 0
    rw [mul_assoc, hs, mul_zero]

/-- The algebraic socle of the direct local model: the annihilator of its
frozen augmentation ideal.-/
def DirectSocle (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) : Submodule k (MonomialArtin k S) where
  carrier := {v | ∀ r ∈ augmentationIdeal (k := k) S hS hdom, r * v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw r hr
    simp [mul_add, hv r hr, hw r hr]
  smul_mem' := by
    intro t v hv r hr
    rw [MonomialArtin.mul_smul_comm', hv r hr, smul_zero]

theorem mem_directSocle_iff (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hdom : IsLiveParameterDomain a b c)
    (v : MonomialArtin k S) :
    v ∈ DirectSocle (k := k) S hS hdom ↔
      ∀ r ∈ augmentationIdeal (k := k) S hS hdom, r * v = 0 :=
  Iff.rfl

/-- Intrinsic socle membership is equivalent to annihilation by the three
live variables.-/
theorem mem_directSocle_iff_variables
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (v : MonomialArtin k S) :
    v ∈ DirectSocle (k := k) S hS hdom ↔
      X (k := k) S Normal.xGenerator
          ((mem_standardFinset_iff_standardSet S _).2 hlive.1) * v = 0 ∧
      X (k := k) S Normal.yGenerator
          ((mem_standardFinset_iff_standardSet S _).2 hlive.2.1) * v = 0 ∧
      X (k := k) S Normal.zGenerator
          ((mem_standardFinset_iff_standardSet S _).2 hlive.2.2.1) * v = 0 := by
  constructor
  · intro hv
    exact ⟨hv _ (X_variable_mem_augmentationIdeal
        (k := k) S hS hdom hlive .x),
      hv _ (X_variable_mem_augmentationIdeal
        (k := k) S hS hdom hlive .y),
      hv _ (X_variable_mem_augmentationIdeal
        (k := k) S hS hdom hlive .z)⟩
  · rintro ⟨hx, hy, hz⟩
    intro r hr
    have hspan : variableIdeal (k := k) S hlive ≤
        elementAnnihilatorIdeal (k := k) S v := by
      apply Ideal.span_le.2
      intro t ht
      simp only [variableBasisSet, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl
      · exact hx
      · exact hy
      · exact hz
    apply hspan
    rw [variableIdeal_eq_augmentationIdeal (k := k) S hS hdom hlive]
    exact hr

/-- A selected root multiplied by any live variable is killed.  This includes
wrapped x multiplication through normalized monoid multiplication.-/
theorem root_mul_variable_eq_zero
    (S : Finset (Normal a b c)) (hdom : IsLiveParameterDomain a b c)
    (hlive : IsLiveTie S) (hanti : IsRootAntichain S)
    {s : Normal a b c} (hs : s ∈ S) (e : Direction) :
    X (k := k) S s (root_mem_standardFinset S hs) *
        X (k := k) S e.generator
          ((mem_standardFinset_iff_standardSet S _).2 (by
            cases e with
            | x => exact hlive.1
            | y => exact hlive.2.1
            | z => exact hlive.2.2.1)) = 0 := by
  have hkill : s * e.generator ∉ standardFinset S := by
    intro hmem
    rcases (mem_standardFinset_iff S (s * e.generator)).1 hmem with
      ⟨t, ht, hdiv⟩
    have hst : s ∣ t := dvd_trans ⟨e.generator, rfl⟩ hdiv
    by_cases hts : t = s
    · subst t
      rcases hdiv with ⟨q, hq⟩
      have hcancel : e.generator * q = (1 : Normal a b c) := by
        apply Normal.mul_left_cancel (p := s)
        simpa [mul_assoc] using hq
      exact (variableGenerators_ne_one_of_two_le hdom.1 e)
        ((mul_eq_one_iff hdom e.generator q).1 hcancel).1
    · exact (hanti s hs t ht (Ne.symm hts)) hst
  simpa [MonomialArtin.X_mul_X, hkill]

/-- Every selected-root basis vector belongs to the algebraic socle.-/
theorem root_X_mem_directSocle
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) {s : Normal a b c} (hs : s ∈ S) :
    X (k := k) S s (root_mem_standardFinset S hs) ∈
      DirectSocle (k := k) S hS hdom := by
  rw [mem_directSocle_iff_variables (k := k) S hS hdom hlive]
  exact ⟨by simpa [Direction.generator, mul_comm] using
      root_mul_variable_eq_zero (k := k) S hdom hlive hanti hs .x,
    by simpa [Direction.generator, mul_comm] using
      root_mul_variable_eq_zero (k := k) S hdom hlive hanti hs .y,
    by simpa [Direction.generator, mul_comm] using
      root_mul_variable_eq_zero (k := k) S hdom hlive hanti hs .z⟩

/-- A surviving non-root monomial has a surviving variable multiple.-/
theorem exists_variable_mul_mem_standardFinset_of_not_root
    (S : Finset (Normal a b c)) (p : MonomialIndex S)
    (hp : p.1 ∉ S) :
    ∃ e : Direction, p.1 * e.generator ∈ standardFinset S := by
  rcases (mem_standardFinset_iff S p.1).1 p.2 with ⟨s, hs, hps⟩
  have hpne : p.1 ≠ s := fun h => hp (h ▸ hs)
  rcases properDivisor_factors_through_predecessor hps hpne with
    ⟨e, q, hpred, hpq⟩
  refine ⟨e, (mem_standardFinset_iff S _).2 ⟨s, hs, ?_⟩⟩
  rcases hpq with ⟨t, rfl⟩
  have hmul : (p.1 * t) * e.generator = s :=
    (Normal.predecessor_eq_some_iff_mul e s (p.1 * t)).1 hpred
  exact ⟨t, by simpa [mul_assoc, mul_comm, mul_left_comm] using hmul.symm⟩

/-- A surviving monomial basis vector in the socle is one of the selected
roots.-/
theorem monomial_mem_roots_of_mem_directSocle
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) (p : MonomialIndex S)
    (hpSoc : X (k := k) S p.1 p.2 ∈ DirectSocle (k := k) S hS hdom) :
    p.1 ∈ S := by
  by_contra hp
  rcases exists_variable_mul_mem_standardFinset_of_not_root S p hp with
    ⟨e, hpe⟩
  have heSet : e.generator ∈ standardSet S := by
    cases e with
    | x => exact hlive.1
    | y => exact hlive.2.1
    | z => exact hlive.2.2.1
  let he : e.generator ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 heSet
  have hzero : X (k := k) S e.generator he * X (k := k) S p.1 p.2 = 0 := by
    have hvars := (mem_directSocle_iff_variables
      (k := k) S hS hdom hlive (X (k := k) S p.1 p.2)).1 hpSoc
    cases e with
    | x => simpa [he, Direction.generator] using hvars.1
    | y => simpa [he, Direction.generator] using hvars.2.1
    | z => simpa [he, Direction.generator] using hvars.2.2
  have hprod :
      X (k := k) S e.generator he * X (k := k) S p.1 p.2 =
        X (k := k) S (p.1 * e.generator) hpe := by
    simpa [MonomialArtin.X_mul_X, hpe, mul_comm]
  exact (MonomialArtin.X_ne_zero (k := k) S (p.1 * e.generator) hpe)
    (hprod.symm.trans hzero)

private theorem coeff_eq_zero_of_mem_directSocle_of_not_root
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (v : MonomialArtin k S) (hv : v ∈ DirectSocle (k := k) S hS hdom)
    (p : MonomialIndex S) (hp : p.1 ∉ S) : v.coeff p = 0 := by
  rcases exists_variable_mul_mem_standardFinset_of_not_root S p hp with
    ⟨e, hpe⟩
  have heSet : e.generator ∈ standardSet S := by
    cases e with
    | x => exact hlive.1
    | y => exact hlive.2.1
    | z => exact hlive.2.2.1
  let he : e.generator ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S _).2 heSet
  let ei : MonomialIndex S := ⟨e.generator, he⟩
  let ti : MonomialIndex S := ⟨p.1 * e.generator, hpe⟩
  have hzero : X (k := k) S e.generator he * v = 0 := by
    have hvars := (mem_directSocle_iff_variables
      (k := k) S hS hdom hlive v).1 hv
    cases e with
    | x => simpa [he, Direction.generator] using hvars.1
    | y => simpa [he, Direction.generator] using hvars.2.1
    | z => simpa [he, Direction.generator] using hvars.2.2
  calc
    v.coeff p = coeffAt (k := k) S p v := rfl
    _ = coeffAt (k := k) S ti (X (k := k) S e.generator he * v) := by
      symm
      apply coeffAt_X_mul (k := k) S ei p ti
      simp [ei, ti, mul_comm]
    _ = 0 := by rw [hzero]; simp

/-- The selected-root basis vectors as an ambient set.-/
def rootBasisVector (S : Finset (Normal a b c)) (s : ↥S) :
    MonomialArtin k S :=
  X (k := k) S s.1 (root_mem_standardFinset S s.2)

def rootBasisSet (S : Finset (Normal a b c)) : Set (MonomialArtin k S) :=
  Set.range (rootBasisVector (k := k) S)

def rootSpan (S : Finset (Normal a b c)) : Submodule k (MonomialArtin k S) :=
  Submodule.span k (rootBasisSet (k := k) S)

/-- The algebraic socle is exactly the span of the selected-root monomials.-/
theorem directSocle_eq_rootSpan
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) :
    DirectSocle (k := k) S hS hdom = rootSpan (k := k) S := by
  apply le_antisymm
  · intro v hv
    rw [MonomialArtin.basis_expansion v]
    apply Submodule.sum_mem
    intro p hpSupport
    by_cases hp : p.1 ∈ S
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨⟨p.1, hp⟩, by simp [rootBasisSet, rootBasisVector]⟩
    · have hc := coeff_eq_zero_of_mem_directSocle_of_not_root
        (k := k) S hS hdom hlive v hv p hp
      simp [hc]
  · apply Submodule.span_le.2
    rintro v ⟨s, rfl⟩
    exact root_X_mem_directSocle (k := k) S hS hdom hlive hanti s.2

private def rootMonomialIndex (S : Finset (Normal a b c)) (s : ↥S) :
    MonomialIndex S := ⟨s.1, root_mem_standardFinset S s.2⟩

private theorem rootMonomialIndex_injective (S : Finset (Normal a b c)) :
    Function.Injective (rootMonomialIndex S) := by
  intro s t h
  apply Subtype.ext
  exact congrArg (fun p : MonomialIndex S => p.1) h

theorem rootBasis_linearIndependent (S : Finset (Normal a b c)) :
    LinearIndependent k (rootBasisVector (k := k) S) := by
  change LinearIndependent k
    ((MonomialArtin.monomialBasis k S) ∘ rootMonomialIndex S)
  exact (MonomialArtin.monomialBasis k S).linearIndependent.comp
    (rootMonomialIndex S) (rootMonomialIndex_injective S)

/-- The selected roots form a basis of the algebraic socle.-/
noncomputable def directSocleBasis
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) :
    Module.Basis ↥S k (DirectSocle (k := k) S hS hdom) := by
  rw [directSocle_eq_rootSpan (k := k) S hS hdom hlive hanti]
  exact Module.Basis.span (rootBasis_linearIndependent (k := k) S)

/-- The socle dimension is exactly the number of selected roots.-/
theorem directSocle_finrank_eq_card
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) :
    Module.finrank k (DirectSocle (k := k) S hS hdom) = S.card := by
  rw [directSocle_eq_rootSpan (k := k) S hS hdom hlive hanti]
  unfold rootSpan rootBasisSet
  rw [finrank_span_eq_card (rootBasis_linearIndependent (k := k) S)]
  exact Fintype.card_coe S

/-- Scope-explicit algebraic type of the direct local model.-/
def directType (k : Type*) [Field k] (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hdom : IsLiveParameterDomain a b c) : ℕ :=
  Module.finrank k (DirectSocle (k := k) S hS hdom)

theorem directType_eq_rootCard
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) :
    directType k S hS hdom = S.card :=
  directSocle_finrank_eq_card (k := k) S hS hdom hlive hanti

theorem directType_eq_three_iff
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) :
    directType k S hS hdom = 3 ↔ S.card = 3 := by
  rw [directType_eq_rootCard (k := k) S hS hdom hlive hanti]

/-- The frozen direct-NG predicate is literally maximal-ideal containment in
the ordinary local-ring structure supplied above.-/
theorem directNearlyGorenstein_iff_localMaximalIdeal_le_trace
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S) :
    letI := directIsLocalRing (k := k) S hS hdom hlive
    DirectNearlyGorenstein k S hS hdom ↔
      IsLocalRing.maximalIdeal (MonomialArtin k S) ≤ TraceSubmodule k S := by
  letI := directIsLocalRing (k := k) S hS hdom hlive
  rw [localMaximalIdeal_eq_augmentationIdeal (k := k) S hS hdom hlive]
  rfl

/-- Scope-explicit Run17 package.  It contains only direct-model locality,
socle/type, and local trace compatibility.-/
structure DirectLocalArtinStructure
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S) : Prop where
  uniqueMaximal : ∀ I : Ideal (MonomialArtin k S), I.IsMaximal →
    I = augmentationIdeal (k := k) S hS hdom
  localRing : IsLocalRing (MonomialArtin k S)
  socle : DirectSocle (k := k) S hS hdom = rootSpan (k := k) S
  socleFinrank : Module.finrank k (DirectSocle (k := k) S hS hdom) = S.card
  typeEq : directType k S hS hdom = S.card
  ngLocal : DirectNearlyGorenstein k S hS hdom ↔
    (letI := directIsLocalRing (k := k) S hS hdom hlive
     IsLocalRing.maximalIdeal (MonomialArtin k S) ≤ TraceSubmodule k S)

theorem directLocalArtinStructure
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) :
    DirectLocalArtinStructure (k := k) (S := S) (hS := hS)
      (hdom := hdom) (hlive := hlive) := by
  refine ⟨?_, directIsLocalRing (k := k) S hS hdom hlive,
    directSocle_eq_rootSpan (k := k) S hS hdom hlive hanti,
    directSocle_finrank_eq_card (k := k) S hS hdom hlive hanti,
    directType_eq_rootCard (k := k) S hS hdom hlive hanti, ?_⟩
  · intro I hI
    exact maximalIdeal_eq_augmentationIdeal (k := k) S hS hdom hlive I hI
  · exact directNearlyGorenstein_iff_localMaximalIdeal_le_trace
      (k := k) S hS hdom hlive

end

end P23.Artin
