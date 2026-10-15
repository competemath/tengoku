/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.HighSetLaw
public import Tengoku.LeanPool.LeanPool.Feige.TwoPointMixture
import Tengoku.LeanPool.LeanPool.Feige.BoundaryNull

/-!
# Product laws for two-point random variables
-/

@[expose] public section

open scoped BigOperators ENNReal
open Set MeasureTheory ProbabilityTheory

namespace Feige

noncomputable section

/-- The Bernoulli law assigning mass `p` to `true`. -/
def boolHighMeasure (p : ℝ) : Measure Bool :=
  ENNReal.ofReal (1 - p) • Measure.dirac false +
    ENNReal.ofReal p • Measure.dirac true

/--
@isnad1 id=isprobab.2h1v.s4.2d5fb9d27c53 from=translated src=- shape=a0756b3a vocab=cc44e94f
-/
theorem boolHighMeasure_isProbability {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (boolHighMeasure p) := by
  constructor
  simp [boolHighMeasure, ← ENNReal.ofReal_add (sub_nonneg.mpr hp1) hp0]

/-- The coordinates at which a Boolean vector takes the high value. -/
def boolHighSet {m : ℕ} (ω : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ ω i

/--
@isnad1 id=measurab.0h1v.s4.a8cad0b004df from=translated src=- shape=19f6a8fe vocab=d2c95315
-/
theorem measurable_boolHighSet {m : ℕ} :
    Measurable (boolHighSet : (Fin m → Bool) → Finset (Fin m)) :=
  measurable_of_finite _

/--
@isnad1 id=injectiv.0h1v.s3.1921b2f4a495 from=translated src=- shape=19f6a8fe vocab=dab32134
-/
theorem boolHighSet_injective {m : ℕ} :
    Function.Injective (boolHighSet : (Fin m → Bool) → Finset (Fin m)) := by
  intro ω η h
  funext i
  have hi : (i ∈ boolHighSet ω) = (i ∈ boolHighSet η) := by
    rw [h]
  simpa [boolHighSet] using hi

/--
@isnad1 id=surjecti.0h1v.s3.f196bb81996f from=translated src=- shape=19f6a8fe vocab=49a9a4b4
-/
theorem boolHighSet_surjective {m : ℕ} :
    Function.Surjective
      (boolHighSet : (Fin m → Bool) → Finset (Fin m)) := by
  intro S
  refine ⟨fun i ↦ decide (i ∈ S), ?_⟩
  ext i
  simp [boolHighSet]

/--
@isnad1 id=eq.0h2v.s5.466cfb1d37f7 from=translated src=- shape=f80c2aff vocab=aea1a582
-/
theorem boolHighMeasure_singleton (p : ℝ) (b : Bool) :
    boolHighMeasure p {b} =
      ENNReal.ofReal (if b then p else 1 - p) := by
  cases b <;> simp [boolHighMeasure]

/--
@isnad1 id=eq.2h2v.s6.bac7488cb027 from=translated src=- shape=525cc1dd vocab=80c3de67
-/
theorem map_boolHighSet_pi_eq_highSetMeasure {m : ℕ}
    (p : Fin m → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) :
    Measure.map boolHighSet
        (Measure.pi fun i ↦ boolHighMeasure (p i)) =
      highSetMeasure p hp0 hp1 := by
  let : ∀ i, IsProbabilityMeasure (boolHighMeasure (p i)) :=
    fun i ↦ boolHighMeasure_isProbability (hp0 i) (hp1 i)
  apply Measure.ext_of_singleton
  intro S
  let ω : Fin m → Bool :=
    (boolHighSet_surjective (m := m) S).choose
  have hω : boolHighSet ω = S :=
    (boolHighSet_surjective (m := m) S).choose_spec
  rw [Measure.map_apply measurable_boolHighSet
    (measurableSet_singleton S)]
  have hpre :
      boolHighSet ⁻¹' ({S} : Set (Finset (Fin m))) =
        {ω} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    constructor
    · exact hω
    · intro η hη
      exact boolHighSet_injective (hη.trans hω.symm)
  rw [hpre, Measure.pi_singleton]
  rw [show highSetMeasure p hp0 hp1 {S} =
      ENNReal.ofReal (highSetMass p S) by
        simpa using highSetMeasure_apply_finset p hp0 hp1 {S}]
  simp_rw [boolHighMeasure_singleton]
  rw [← ENNReal.ofReal_prod_of_nonneg]
  · congr 1
    classical
    have hfactor :
        (∏ i, if i ∈ S then p i else 1 - p i) =
          highSetMass p S := by
      unfold highSetMass
      rw [Finset.prod_ite]
      have hfilter :
          Finset.univ.filter (fun i : Fin m ↦ i ∈ S) = S := by
        ext i
        simp
      have hfilterc :
          Finset.univ.filter (fun i : Fin m ↦ ¬i ∈ S) =
            Finset.univ \ S := by
        ext i
        simp
      rw [hfilter, hfilterc]
    rw [← hfactor]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ S
    · have hb :
          ω i = true := by
        have := congrArg (fun T : Finset (Fin m) ↦ i ∈ T) hω
        simpa [boolHighSet, hi] using this
      simp [hb, hi]
    · have hb :
          ω i = false := by
        cases h : ω i with
        | false => rfl
        | true =>
            exfalso
            have := congrArg (fun T : Finset (Fin m) ↦ i ∈ T) hω
            simp [boolHighSet, hi, h] at this
      simp [hb, hi]
  · intro i _
    split
    · exact hp0 i
    · exact sub_nonneg.mpr (hp1 i)

/--
@isnad1 id=eq.2h2v.s5.459e34269319 from=translated src=- shape=9e95021e vocab=fdb462d9
-/
theorem map_boolHighMeasure_twoPoint
    {γ β : ℝ} (hγ : 0 ≤ γ) (hβ : 0 < β) :
    Measure.map
        (fun b : Bool ↦ if b then highValue β else lowValue γ)
        (boolHighMeasure (highProbability γ β)) =
      twoPointMeasure (lowValue γ) (highValue β) := by
  have hsum : γ + β ≠ 0 :=
    (add_pos_of_nonneg_of_pos hγ hβ).ne'
  have hlo :
      twoPointLowerWeight (lowValue γ) (highValue β) =
        1 - highProbability γ β := by
    rw [show twoPointLowerWeight (lowValue γ) (highValue β) =
        β / (γ + β) by
      unfold twoPointLowerWeight lowValue highValue
      congr 1 <;> ring]
    exact (one_sub_highProbability hsum).symm
  have hhi :
      twoPointUpperWeight (lowValue γ) (highValue β) =
        highProbability γ β := by
    unfold twoPointUpperWeight lowValue highValue highProbability
    congr 1 <;> ring
  rw [boolHighMeasure, Measure.map_add, Measure.map_smul,
    Measure.map_smul, Measure.map_dirac, Measure.map_dirac]
  · simp [twoPointMeasure, hlo, hhi]
  all_goals fun_prop

/--
@isnad1 id=eq.2h3v.s7.a68758aefe34 from=translated src=- shape=6d8ac40d vocab=72033f2d
-/
theorem map_canonicalTwoPointPiVector {m : ℕ}
    (γ β : Fin m → ℝ) (hγ : ∀ i, 0 ≤ γ i)
    (hβ : ∀ i, 0 < β i) :
    Measure.map (canonicalTwoPointPiVector γ β)
        (Measure.pi fun i ↦
          boolHighMeasure (twoPointHighProbability γ β i)) =
      Measure.pi (fun i ↦
        twoPointMeasure (lowValue (γ i)) (highValue (β i))) := by
  let : ∀ i, IsProbabilityMeasure
      (boolHighMeasure (twoPointHighProbability γ β i)) :=
    fun i ↦ boolHighMeasure_isProbability
      (twoPointHighProbability_nonneg hγ hβ i)
      (twoPointHighProbability_le_one hγ hβ i)
  let f := fun i : Fin m ↦
    fun b : Bool ↦ if b then highValue (β i) else lowValue (γ i)
  have hfun :
      canonicalTwoPointPiVector γ β =
        fun ω i ↦ f i (ω i) := by rfl
  rw [hfun, Measure.pi_map_pi]
  · congr 1
    funext i
    exact map_boolHighMeasure_twoPoint (hγ i) (hβ i)
  · intro i
    exact (measurable_of_finite _).aemeasurable

end

end Feige
