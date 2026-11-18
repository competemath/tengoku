import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.Hecke.PrimeExtraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.QuasiRiemann end Tengoku.QuasiRiemann open Tengoku.QuasiRiemann
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ConcretePrimeRowBridge

section

open ActualEisensteinCubic ShortDraftHeckeBridge

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

noncomputable def idealGenerator (I : Ideal O) : O :=
  Submodule.IsPrincipal.generator I

/--
@isnad1 id=eq.0h1v.s5.c708945b1856 from=translated src=- shape=8ceaa7bc vocab=52f18cd0
-/
theorem span_idealGenerator (I : Ideal O) :
    Ideal.span {idealGenerator I} = I := by
  exact Submodule.IsPrincipal.span_singleton_generator I

/--
@isnad1 id=injectiv.0h0v.s4.f89ec7f68fb7 from=translated src=- shape=d7985952 vocab=9fff0ec6
-/
theorem idealGenerator_injective : Function.Injective idealGenerator := by
  intro I J h
  calc
    I = Ideal.span {idealGenerator I} := (span_idealGenerator I).symm
    _ = Ideal.span {idealGenerator J} := by rw [h]
    _ = J := span_idealGenerator J

noncomputable def idealsUpTo (D : ℕ) : Finset (Ideal O) :=
  (Finset.Icc 1 D).biUnion
    (fun n => (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset)

/--
@isnad1 id=iff.0h2v.s9.9d1c58dc14dd from=translated src=- shape=8c38fe34 vocab=4c539a59
-/
theorem mem_idealsUpTo {D : ℕ} {I : Ideal O} :
    I ∈ idealsUpTo D ↔ 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D := by
  classical
  simp [idealsUpTo, Finset.mem_biUnion, Finset.mem_Icc]

noncomputable def columnsUpTo (D : ℕ) : Finset O :=
  by
    classical
    exact (idealsUpTo D).image idealGenerator

noncomputable def columnWeight {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (x : O) : ℂ :=
  baseChangeWeight χ (Ideal.span {x}) * W (Ideal.absNorm (Ideal.span {x}))

noncomputable def goodLambda : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger - 1

noncomputable def primePool (F : Finset (Ideal O)) : Finset (Ideal O) :=
  F.biUnion (fun I => (UniqueFactorizationMonoid.normalizedFactors I).toFinset)

/--
@isnad1 id=iff.0h2v.s8.94e0c88b89e1 from=translated src=- shape=266d3855 vocab=921bbcbc
-/
theorem mem_primePool_iff {F : Finset (Ideal O)} {P : Ideal O} :
    P ∈ primePool F ↔
      ∃ I ∈ F, P ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  simp only [primePool, Finset.mem_biUnion, Multiset.mem_toFinset]

/--
@isnad1 id=ismaxima.1h2v.s8.fe8309ac6719 from=translated src=- shape=86dd186b vocab=5b758beb
-/
theorem primePool_maximal (F : Finset (Ideal O))
    (_hFpos : ∀ I ∈ F, I ≠ ⊥) (i : primePool F) :
    (i.1).IsMaximal := by
  obtain ⟨I, hIF, hfac⟩ := mem_primePool_iff.mp i.property
  have hp : Prime i.1 := UniqueFactorizationMonoid.prime_of_normalized_factor i.1 hfac
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

/--
@isnad1 id=not.1h2v.s9.635aadd83b76 from=translated src=- shape=0c96d15f vocab=e5b4df9e
-/
theorem primePool_good (F : Finset (Ideal O))
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (i : primePool F) : goodLambda ∉ i.1 := by
  obtain ⟨I, hIF, hfac⟩ := mem_primePool_iff.mp i.property
  exact hFgood I hIF i.1 hfac

noncomputable def idealSupport (F : Finset (Ideal O)) (I : Ideal O) :
    Finset (primePool F) :=
  Finset.univ.filter (fun i => i.1 ∈ UniqueFactorizationMonoid.normalizedFactors I)

/--
@isnad1 id=iff.0h3v.s10.907bfb9a257c from=translated src=- shape=2613b67c vocab=9282fc57
-/
theorem mem_idealSupport_iff (F : Finset (Ideal O)) (I : Ideal O)
    (i : primePool F) :
    i ∈ idealSupport F I ↔ i.1 ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  simp [idealSupport]

/--
@isnad1 id=mem.3h3v.s10.0239b0f024c4 from=translated src=- shape=f3be48f0 vocab=2a1a4044
-/
theorem idealGenerator_mem_prime_of_support
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (I : Ideal O) (hIF : I ∈ F) (i : primePool F)
    (hi : i ∈ idealSupport F I) : idealGenerator I ∈ i.1 := by
  have hfac := (mem_idealSupport_iff F I i).mp hi
  have hle := ((Ideal.mem_normalizedFactors_iff (hFpos I hIF)).mp hfac).2
  have hmem : idealGenerator I ∈ Ideal.span {idealGenerator I} :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [span_idealGenerator I] at hmem
  exact hle hmem

noncomputable def idealSexticRow
    (F : Finset (Ideal O))
    (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    (I : Ideal O) (u : O) : ℂ := by
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact ActualEisensteinCubic.finiteSquarefreeRow
    (fun i : primePool F => i.1) (primePool_good F hFgood)
    (idealSupport F I) u

/--
@isnad1 id=eq.1h3v.s7.58942797a14a from=translated src=- shape=6398bb4d vocab=bae3a638
-/
theorem baseChangeWeight_zero_of_not_squarefree {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O)
    (hI : ¬ Squarefree I) : baseChangeWeight χ I = 0 := by
  rw [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hI]
  simp

private theorem idealMoebius_norm_le_one (I : Ideal O) :
    ‖((UniqueFactorizationMonoid.moebius I : ℤ) : ℂ)‖ ≤ 1 := by
  classical
  by_cases h : Squarefree I
  · rw [h.moebius_eq]
    simp
  · rw [UniqueFactorizationMonoid.moebius_of_not_squarefree h]
    simp

/--
@isnad1 id=le.0h3v.s5.32040f0f12e6 from=translated src=- shape=2af84057 vocab=db531efa
-/
theorem baseChangeWeight_norm_le_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    ‖baseChangeWeight χ I‖ ≤ 1 := by
  rw [baseChangeWeight, norm_mul]
  have hμ := idealMoebius_norm_le_one I
  have hχ := χ.norm_le_one (Ideal.absNorm I)
  exact (mul_le_mul hμ hχ (norm_nonneg _) (by positivity)).trans (by norm_num)

/--
@isnad1 id=le.1h4v.s5.0ee390539a61 from=translated src=- shape=ec733e9e vocab=0f80b1eb
-/
theorem columnWeight_norm_le_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ)
    (hW : ∀ n, ‖W n‖ ≤ 1) (x : O) :
    ‖columnWeight χ W x‖ ≤ 1 := by
  rw [columnWeight, norm_mul]
  have hμ := baseChangeWeight_norm_le_one χ (Ideal.span {x})
  have hW' := hW (Ideal.absNorm (Ideal.span {x}))
  exact (mul_le_mul hμ hW' (norm_nonneg _) (by positivity)).trans (by norm_num)

noncomputable def elementRow
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (u : O) : ℂ := by
  classical
  letI : ∀ i : primePool F, (i.1).IsMaximal := primePool_maximal F hFpos
  exact ∑ x ∈ F.image idealGenerator,
    columnWeight χ W x *
      finiteSquarefreeRow (fun i : primePool F => i.1)
        (primePool_good F hFgood)
        (idealSupport F (Ideal.span {x})) u

noncomputable def idealRowSum
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
        goodLambda ∉ P)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (W : ℕ → ℂ) (u : O) : ℂ :=
  ∑ I ∈ F,
    baseChangeWeight χ I * W (Ideal.absNorm I) *
      idealSexticRow F hFpos hFgood I u

open ActualEisensteinCubic ShortDraftHeckeBridge
open scoped Classical

noncomputable def rowNormDisk (H : ℕ) : Finset O := by
  classical
  exact (ShortDraftLatticeCount.rowNormBall H).filter
    (fun u => 0 < Ideal.absNorm (Ideal.span {u}) ∧
      Ideal.absNorm (Ideal.span {u}) ≤ H)

/--
@isnad1 id=iff.0h2v.s9.7cbb649af331 from=translated src=- shape=213dd3f3 vocab=a927fca1
-/
theorem mem_rowNormDisk {H : ℕ} {u : O} :
    u ∈ rowNormDisk H ↔
      0 < Ideal.absNorm (Ideal.span {u}) ∧
      Ideal.absNorm (Ideal.span {u}) ≤ H := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le H u h.2, h⟩

/--
@isnad1 id=le.4h5v.s8.e4e29c422055 from=translated src=- shape=f804f6e3 vocab=9bb50747
-/
theorem sixth_power_rows_in_rowNormDisk
    {β : Type*} (selected : Finset β) (p : β → O)
    (D H : ℕ) (hD : 1 ≤ D)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : Nat.floor ((D : ℝ) ^ (11 / 10 : ℝ)) ≤ H) :
    selected.image (fun i => p i ^ 6) ⊆ rowNormDisk H := by
  classical
  intro u hu
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  rw [mem_rowNormDisk]
  have hpNorm : Ideal.absNorm (Ideal.span {p i}) ≠ 0 :=
    (Ideal.absNorm_eq_zero_iff).not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (hp i hi))
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hupper : (Ideal.absNorm (Ideal.span {p i ^ 6}) : ℝ) ≤
      (D : ℝ) ^ (11 / 10 : ℝ) := by
    calc
      (Ideal.absNorm (Ideal.span {p i ^ 6}) : ℝ) =
          (Ideal.absNorm (Ideal.span {p i}) : ℝ) ^ 6 := by
            exact_mod_cast ActualEisensteinCubic.principal_absNorm_pow (p i) 6
      _ ≤ ((D : ℝ) ^ (11 / 60 : ℝ)) ^ 6 := by
        gcongr
        exact hnormupper i hi
      _ = (D : ℝ) ^ (11 / 10 : ℝ) := by
        rw [← Real.rpow_mul_natCast hDpos.le (11 / 60 : ℝ) 6]
        congr 1
        norm_num
  constructor
  · rw [ActualEisensteinCubic.principal_absNorm_pow]
    exact pow_pos (Nat.pos_of_ne_zero hpNorm) 6
  · exact (Nat.le_floor hupper).trans hH

end

open ShortDraftHeckeBridge FiniteSFactor

noncomputable def outsideIdealsUpTo (S : Finset (Ideal O)) (D : ℕ) :
    Finset (Ideal O) := by
  classical
  exact (idealsUpTo D).filter (fun I => ∀ P ∈ S, ¬ P ∣ I)

/--
@isnad1 id=iff.0h3v.s9.672f965baaf1 from=translated src=- shape=1069cb2b vocab=17f67b0e
-/
theorem mem_outsideIdealsUpTo {S : Finset (Ideal O)} {D : ℕ}
    {I : Ideal O} :
    I ∈ outsideIdealsUpTo S D ↔
      1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D ∧
        (∀ P ∈ S, ¬ P ∣ I) := by
  classical
  simp [outsideIdealsUpTo, mem_idealsUpTo, and_assoc]

/--
@isnad1 id=ne.1h3v.s7.7a697212ae74 from=translated src=- shape=08334fe4 vocab=1ccd784c
-/
theorem outsideIdealsUpTo_ne_bot (S : Finset (Ideal O)) (D : ℕ)
    (I : Ideal O) (hI : I ∈ outsideIdealsUpTo S D) : I ≠ ⊥ := by
  have hn := (mem_outsideIdealsUpTo.mp hI).1
  intro h
  subst I
  simp at hn

/--
@isnad1 id=prime.0h0v.s4.6d9c6cb77fb8 from=translated src=- shape=25b03439 vocab=466fbc42
-/
theorem goodLambda_prime : Prime goodLambda := by
  let : IsCyclotomicExtension {3} ℚ K :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

/--
@isnad1 id=ismaxima.0h0v.s5.55d8079f180c from=translated src=- shape=4016e43a vocab=3639e6a6
-/
theorem goodLambdaIdeal_maximal :
    (Ideal.span {goodLambda} : Ideal O).IsMaximal := by
  have hp : (Ideal.span {goodLambda} : Ideal O).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime goodLambda_prime
  have hne : (Ideal.span {goodLambda} : Ideal O) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr goodLambda_prime.ne_zero
  exact hp.isMaximal hne

/--
@isnad1 id=mem.3h2v.s8.d95f67522ca5 from=translated src=- shape=08d75346 vocab=a0a4e829
-/
theorem badPrime_cover_of_lambdaIdeal_mem
    (S : Finset (Ideal O))
    (hS : (Ideal.span {goodLambda} : Ideal O) ∈ S) :
    ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S := by
  intro P hP hmem
  have hle : (Ideal.span {goodLambda} : Ideal O) ≤ P :=
    (Ideal.span_singleton_le_iff_mem P).mpr hmem
  have heq : (Ideal.span {goodLambda} : Ideal O) = P :=
    goodLambdaIdeal_maximal.eq_of_le hP.ne_top hle
  rwa [heq] at hS

/--
@isnad1 id=not.3h4v.s9.b003ac87e82c from=translated src=- shape=d8fb2bde vocab=897b7013
-/
theorem outsideIdealsUpTo_good
    (S : Finset (Ideal O)) (D : ℕ)
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (I : Ideal O) (hI : I ∈ outsideIdealsUpTo S D)
    (Q : Ideal O) (hQ : Q ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    goodLambda ∉ Q := by
  intro hmemLam
  have hne : I ≠ ⊥ := outsideIdealsUpTo_ne_bot S D I hI
  have hp : Prime Q := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
  have hmax : Q.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hQS : Q ∈ S := hSbad Q hmax hmemLam
  have hdiv : Q ∣ I := (Ideal.dvd_iff_le).mpr
    ((Ideal.mem_normalizedFactors_iff hne).mp hQ).2
  exact (mem_outsideIdealsUpTo.mp hI).2.2 Q hQS hdiv

/--
@isnad1 id=eq.0h1v.s7.cf21ef631b6b from=translated src=- shape=dd0890ec vocab=dc32d7cd
-/
theorem idealsUpTo_eq_biUnion_fibers (D : ℕ) :
    idealsUpTo D =
      (Finset.Icc 1 D).biUnion FiniteSFactor.fiber := by
  rfl

private theorem normFibers_pairwiseDisjoint (D : ℕ) :
    ((Finset.Icc 1 D : Finset ℕ) : Set ℕ).PairwiseDisjoint
      FiniteSFactor.fiber := by
  intro n hn m hm hnm
  apply Finset.disjoint_left.mpr
  intro I hIn hIm
  exact hnm ((FiniteSFactor.mem_fiber.mp hIn).symm.trans
    (FiniteSFactor.mem_fiber.mp hIm))

/--
@isnad1 id=eq.0h4v.s8.4cf1ca43a866 from=translated src=- shape=49c8bfb4 vocab=130d603f
-/
theorem outsideIdealSum_eq_outsideCoeff_sum
    (S : Finset (Ideal O)) (D : ℕ)
    (w : Ideal O → ℂ) (W : ℕ → ℂ) :
    (∑ I ∈ outsideIdealsUpTo S D,
      w I * W (Ideal.absNorm I)) =
      ∑ n ∈ Finset.Icc 1 D,
        FiniteSFactor.outsideCoeff S w n * W n := by
  classical
  have hsets : outsideIdealsUpTo S D =
      (Finset.Icc 1 D).biUnion (fun n =>
        (FiniteSFactor.fiber n).filter (fun I => ∀ P ∈ S, ¬P ∣ I)) := by
    ext I
    simp [outsideIdealsUpTo, idealsUpTo_eq_biUnion_fibers,
      FiniteSFactor.mem_fiber, Finset.mem_biUnion]
  rw [hsets, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [FiniteSFactor.outsideCoeff, Finset.sum_mul, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro I hI
    rw [FiniteSFactor.mem_fiber.mp hI]
    by_cases hgood : ∀ P ∈ S, ¬P ∣ I <;>
      simp [FiniteSFactor.outsideWeight, hgood]
  · intro n hn m hm hnm
    exact Finset.disjoint_filter_filter
      (normFibers_pairwiseDisjoint D hn hm hnm)

open ShortDraftHeckeBridge FiniteSFactor Filter

/--
@isnad1 id=ex.2h3v.s6.ab2b6d11778d from=translated src=- shape=f7f55eac vocab=58f4c843
-/
theorem eventually_absorb_MS_and_count_constants
    (Cmean Ccount eta : ℝ) (hcount : 0 < Ccount) (heta : 0 < eta) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      Cmean ≤ (D : ℝ) ^ eta ∧ 1 ≤ Ccount * (D : ℝ) ^ eta := by
  have hpow : Tendsto (fun D : ℕ => (D : ℝ) ^ eta) atTop atTop :=
    (tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp
    (hpow.eventually_ge_atTop (max Cmean Ccount⁻¹))
  refine ⟨D₀, fun D hD => ?_⟩
  have hlarge := hD₀ D hD
  constructor
  · exact (le_max_left _ _).trans hlarge
  · have hinv : Ccount⁻¹ ≤ (D : ℝ) ^ eta :=
      (le_max_right _ _).trans hlarge
    have hmul := mul_le_mul_of_nonneg_left hinv hcount.le
    simpa [hcount.ne'] using hmul

end ConcretePrimeRowBridge

end

end OAI
-- Tengoku: root names of this library moved to Tengoku.QuasiRiemann so they do not collide with other libraries (generated)
