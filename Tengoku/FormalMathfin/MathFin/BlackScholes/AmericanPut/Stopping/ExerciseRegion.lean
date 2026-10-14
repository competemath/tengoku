/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Stopping.SpotShape

/-!
# The in-the-money exercise threshold defined from the stopping value

Spot continuity and convexity make the in-the-money contact set a closed
interval containing zero. Its supremum is attained and defines a threshold
in `[0,K]`. Restriction to `S≤K` deliberately preserves the correct maturity
convention: at expiry the unrestricted contact set is all nonnegative spots.
Strict positivity and separation from the strike at positive maturity are
not asserted by these elementary results.

## Result

Public entry points include `exerciseSet`, `exerciseThreshold`, `value_at_zero_spot`, `value_continuousOn_spot`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open MeasureTheory Set
open scoped NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The in-the-money contact set: the spots `S` in `[0,K]` at which the American put value
equals the immediate payoff `K-S`. -/
noncomputable def exerciseSet (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → ℝ) (K r q σ : ℝ) (T : ℝ≥0) : Set ℝ :=
  {S | 0 ≤ S ∧ S ≤ K ∧ americanPutValue P 𝓕 W K r q σ S T = K-S}

/-- The supremum of the in-the-money contact set. -/
noncomputable def exerciseThreshold (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → ℝ) (K r q σ : ℝ) (T : ℝ≥0) : ℝ :=
  sSup (exerciseSet P 𝓕 W K r q σ T)

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
  {K r q σ : ℝ} {T : ℝ≥0}

/--
@isnad1 id=eq.4h9v.s7.aa462f5eaee0 from=translated src=- shape=211695a4 vocab=20b0124b
-/
theorem value_at_zero_spot (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) : americanPutValue P 𝓕 W K r q σ 0 T = K := by
  apply le_antisymm (value_le_strike hW hK hr le_rfl)
  simpa only [sub_zero,max_eq_left hK] using payoff_le_value (S := 0) hW hzero hK hr le_rfl

/--
@isnad1 id=continuo.4h9v.s7.6ea2b991615a from=translated src=- shape=c6a2d94f vocab=5e947ea8
-/
theorem value_continuousOn_spot (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) :
    ContinuousOn (fun S => americanPutValue P 𝓕 W K r q σ S T) (Ici 0) := by
  intro x hx
  change 0 ≤ x at hx
  rcases eq_or_lt_of_le hx with he | hpos
  · subst x
    apply Metric.continuousWithinAt_iff.mpr
    intro ε hε
    refine ⟨ε,hε,?_⟩
    intro y hy hnear
    change 0 ≤ y at hy
    have hlo : K-y ≤ americanPutValue P 𝓕 W K r q σ y T :=
      (le_max_left _ _).trans (payoff_le_value hW hzero hK hr hy)
    have hhi := value_le_strike (P := P) (𝓕 := 𝓕) (q := q) (σ := σ) (T := T) hW hK hr hy
    have hyε : y < ε := by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg hy] using hnear
    rw [value_at_zero_spot hW hzero hK hr,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hhi)]
    linarith
  · have hc : ContinuousOn (fun S => americanPutValue P 𝓕 W K r q σ S T) (Ioi 0) := by
      simpa only [interior_Ici] using (value_convexOn_spot (P := P) (𝓕 := 𝓕) (q := q) (σ := σ)
        (T := T) hW hK hr).continuousOn_interior
    exact (hc.continuousAt (Ioi_mem_nhds hpos)).continuousWithinAt

/--
@isnad1 id=mem.4h9v.s7.c8e39b724607 from=translated src=- shape=a9a68a0f vocab=4ab307e8
-/
theorem zero_mem_exerciseSet (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) : 0 ∈ exerciseSet P 𝓕 W K r q σ T :=
  ⟨le_rfl,hK,by simpa only [sub_zero] using value_at_zero_spot hW hzero hK hr⟩

/--
@isnad1 id=convex.4h9v.s7.ff694224350e from=translated src=- shape=05781a54 vocab=89e1f9ea
-/
theorem exerciseSet_convex (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) : Convex ℝ (exerciseSet P 𝓕 W K r q σ T) := by
  intro x hx y hy a b ha hb hab
  have hmix : 0 ≤ a*x+b*y := add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  have hlin : a*(K-x)+b*(K-y) = K-(a*x+b*y) := by
    have hh := congrArg (fun z : ℝ => z*K) hab
    nlinarith
  have hbound : a*x+b*y ≤ K := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left hx.2.1 ha) (mul_le_mul_of_nonneg_left hy.2.1 hb)
    nlinarith [congrArg (fun z : ℝ => z*K) hab]
  have hv := (value_convexOn_spot (P := P) (𝓕 := 𝓕) (q := q) (σ := σ) (T := T) hW hK hr).2
    hx.1 hy.1 ha hb hab
  simp only [smul_eq_mul] at hv ⊢
  rw [hx.2.2,hy.2.2,hlin] at hv
  exact ⟨hmix,hbound,le_antisymm hv ((le_max_left _ _).trans (payoff_le_value hW hzero hK hr hmix))⟩

/--
@isnad1 id=isclosed.4h9v.s6.c6afe707ec4a from=translated src=- shape=aaf950c5 vocab=1893ad5f
-/
theorem exerciseSet_closed (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) : IsClosed (exerciseSet P 𝓕 W K r q σ T) := by
  have hc : Continuous (fun S => americanPutValue P 𝓕 W K r q σ (max S 0) T) :=
    continuousOn_univ.mp ((value_continuousOn_spot hW hzero hK hr).comp
      (show ContinuousOn (fun S : ℝ => max S 0) univ by fun_prop) (fun S _ => le_max_right S 0))
  have heq : exerciseSet P 𝓕 W K r q σ T =
      Icc 0 K ∩ {S | americanPutValue P 𝓕 W K r q σ (max S 0) T = K-S} := by
    ext S
    constructor
    · rintro ⟨hS,hSK,he⟩
      exact ⟨⟨hS,hSK⟩,by simpa only [mem_ofPred_eq,max_eq_left hS] using he⟩
    · rintro ⟨⟨hS,hSK⟩,he⟩
      exact ⟨hS,hSK,by simpa only [mem_ofPred_eq,max_eq_left hS] using he⟩
  rw [heq]
  exact isClosed_Icc.inter (isClosed_eq hc (by fun_prop))

omit [IsProbabilityMeasure P] in
/--
@isnad1 id=bddabove.0h9v.s5.1870991b7f1d from=translated src=- shape=602f4219 vocab=df844f70
-/
theorem exerciseSet_bddAbove : BddAbove (exerciseSet P 𝓕 W K r q σ T) :=
  ⟨K,fun _ hS => hS.2.1⟩

/--
@isnad1 id=mem.4h9v.s7.a656a3196dd1 from=translated src=- shape=0c1dec3f vocab=203ac9e9
-/
theorem threshold_mem_exerciseSet (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) : exerciseThreshold P 𝓕 W K r q σ T ∈ exerciseSet P 𝓕 W K r q σ T :=
  (exerciseSet_closed hW hzero hK hr).csSup_mem ⟨0,zero_mem_exerciseSet hW hzero hK hr⟩ exerciseSet_bddAbove

/--
@isnad1 id=eq.4h9v.s7.d2bc8d7cb6ca from=translated src=- shape=4d6b0914 vocab=fc4f4641
-/
theorem exerciseSet_eq_interval (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) :
    exerciseSet P 𝓕 W K r q σ T = Icc 0 (exerciseThreshold P 𝓕 W K r q σ T) := by
  ext S
  constructor
  · intro hS
    exact ⟨hS.1,le_csSup exerciseSet_bddAbove hS⟩
  · intro hS
    exact (exerciseSet_convex hW hzero hK hr).ordConnected.out (zero_mem_exerciseSet hW hzero hK hr)
      (threshold_mem_exerciseSet hW hzero hK hr) hS

/--
@isnad1 id=and.4h9v.s7.f2c6c6280003 from=translated src=- shape=c67ea53e vocab=df0c8397
-/
theorem threshold_bounds (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) :
    0 ≤ exerciseThreshold P 𝓕 W K r q σ T ∧ exerciseThreshold P 𝓕 W K r q σ T ≤ K := by
  have hm := threshold_mem_exerciseSet (P := P) (𝓕 := 𝓕) (q := q) (σ := σ) (T := T) hW hzero hK hr
  exact ⟨hm.1,hm.2.1⟩

/--
@isnad1 id=eq.4h8v.s6.aee7aa9ea618 from=translated src=- shape=ea4c49e9 vocab=df0c8397
-/
theorem threshold_at_expiry (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) : exerciseThreshold P 𝓕 W K r q σ 0 = K := by
  apply le_antisymm (threshold_bounds hW hzero hK hr).2
  apply le_csSup exerciseSet_bddAbove
  refine ⟨hK,le_rfl,?_⟩
  rw [value_at_expiry hW hzero hK hr hK]
  simp

/--
@isnad1 id=le.5h10v.s7.c958f666d66a from=translated src=- shape=aa7cb77e vocab=5f2b7a8d
-/
theorem exerciseSet_antitone_horizon (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) {U : ℝ≥0} (hTU : T ≤ U) :
    exerciseSet P 𝓕 W K r q σ U ⊆ exerciseSet P 𝓕 W K r q σ T := by
  intro S hS
  refine ⟨hS.1,hS.2.1,le_antisymm ?_ ?_⟩
  · exact (value_mono_horizon hW hK hr hS.1 hTU).trans hS.2.2.le
  · exact (le_max_left _ _).trans (payoff_le_value hW hzero hK hr hS.1)

/--
@isnad1 id=antitone.4h8v.s6.71dc2b146af5 from=translated src=- shape=86d5fd44 vocab=ab09cf4d
-/
theorem threshold_antitone_horizon (hW : Measurable W.uncurry) (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hK : 0 ≤ K) (hr : 0 ≤ r) : Antitone (exerciseThreshold P 𝓕 W K r q σ) := by
  intro T U hTU
  apply csSup_le ⟨0,zero_mem_exerciseSet hW hzero hK hr⟩
  intro S hS
  exact le_csSup exerciseSet_bddAbove (exerciseSet_antitone_horizon hW hzero hK hr hTU hS)

end MathFin.BlackScholes.AmericanPut.Stopping
