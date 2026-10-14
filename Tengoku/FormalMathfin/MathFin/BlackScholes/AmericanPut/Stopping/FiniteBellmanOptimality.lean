/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Stopping.DiscreteContactMartingale

/-! # First-contact attainment of the finite conditional-expectation Bellman value 
## Result

Public entry points include `finiteBellmanContact`, `finiteBellmanContact_le`, `finiteBellmanContact_stopping`, `finiteBellmanContact_contact`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Stopping

open Set Filter MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℕ ‹MeasurableSpace Ω›} {Z : ℕ → Ω → ℝ}

/-- The first index in `[0,N]` at which the Bellman value meets the reward, that is at which
`finiteBellman P 𝓕 Z N i-Z (min i N)` vanishes. -/
noncomputable def finiteBellmanContact (P : Measure Ω) (𝓕 : Filtration ℕ ‹MeasurableSpace Ω›)
    (Z : ℕ → Ω → ℝ) (N : ℕ) : Ω → ℕ :=
  hittingBtwn (fun i ω => finiteBellman P 𝓕 Z N i ω-Z (min i N) ω) {0} 0 N

/--
@isnad1 id=le.0h6v.s5.7de6490965c0 from=translated src=- shape=e2c9f777 vocab=06badec8
-/
theorem finiteBellmanContact_le (N : ℕ) (ω : Ω) : finiteBellmanContact P 𝓕 Z N ω ≤ N :=
  hittingBtwn_le ω

/--
@isnad1 id=isstoppi.1h5v.s5.18321532fce9 from=translated src=- shape=0ceb03b2 vocab=1a1c8855
-/
theorem finiteBellmanContact_stopping (ha : Adapted 𝓕 Z) (N : ℕ) :
    IsStoppingTime 𝓕 (fun ω => (finiteBellmanContact P 𝓕 Z N ω : WithTop ℕ)) := by
  apply Adapted.isStoppingTime_hittingBtwn ?_ (measurableSet_singleton 0)
  intro i
  exact ((finiteBellman_stronglyAdapted ha N i).measurable).sub
    ((ha (min i N)).mono (𝓕.mono (min_le_left _ _)) le_rfl)

/--
@isnad1 id=eq.0h6v.s5.9a7dff51bd12 from=translated src=- shape=8fcc6173 vocab=1495d2f7
-/
theorem finiteBellmanContact_contact (N : ℕ) (ω : Ω) :
    finiteBellman P 𝓕 Z N (finiteBellmanContact P 𝓕 Z N ω) ω =
      Z (finiteBellmanContact P 𝓕 Z N ω) ω := by
  have he : ∃ j ∈ Icc 0 N, finiteBellman P 𝓕 Z N j ω-Z (min j N) ω ∈ ({0} : Set ℝ) := by
    refine ⟨N,⟨Nat.zero_le _,le_rfl⟩,?_⟩
    simp [finiteBellman_after_horizon le_rfl]
  have hh := hittingBtwn_mem_set
    (u := fun i ω => finiteBellman P 𝓕 Z N i ω-Z (min i N) ω) (ω := ω) he
  have hbound := finiteBellmanContact_le (P := P) (𝓕 := 𝓕) (Z := Z) N ω
  change finiteBellman P 𝓕 Z N (finiteBellmanContact P 𝓕 Z N ω) ω-
    Z (min (finiteBellmanContact P 𝓕 Z N ω) N) ω = 0 at hh
  rw [min_eq_left hbound] at hh
  exact sub_eq_zero.mp hh

/--
@isnad1 id=eq.1h7v.s6.11d790fabcf7 from=translated src=- shape=290804d8 vocab=3dfb55e2
-/
theorem finiteBellmanContact_before (N i : ℕ) (ω : Ω)
    (ht : i < finiteBellmanContact P 𝓕 Z N ω) :
    P[finiteBellman P 𝓕 Z N (i+1) | 𝓕 i] ω = finiteBellman P 𝓕 Z N i ω := by
  have hiN : i < N := ht.trans_le (finiteBellmanContact_le N ω)
  have hn := notMem_of_lt_hittingBtwn (u := fun i ω => finiteBellman P 𝓕 Z N i ω-Z (min i N) ω)
    (s := ({0} : Set ℝ)) ht (Nat.zero_le i)
  have hne : finiteBellman P 𝓕 Z N i ω ≠ Z i ω := by
    simpa only [mem_singleton_iff,min_eq_left hiN.le,sub_eq_zero] using hn
  have hv : Z i ω < finiteBellman P 𝓕 Z N i ω := lt_of_le_of_ne
    (by simpa only [min_eq_left hiN.le] using finiteBellman_dominates (P := P) (𝓕 := 𝓕) (Z := Z) N i ω)
    hne.symm
  have he := congrFun (finiteBellman_recursion (P := P) (𝓕 := 𝓕) (Z := Z) hiN) ω
  rw [he] at hv
  have hc := (lt_max_iff.mp hv).resolve_left (lt_irrefl _)
  exact (he.trans (max_eq_right hc.le)).symm

variable [IsProbabilityMeasure P]

/--
@isnad1 id=martinga.2h5v.s6.6ab8516652eb from=translated src=- shape=bd6dc433 vocab=8dca4fa7
-/
theorem finiteBellmanContact_martingale (ha : Adapted 𝓕 Z)
    (hi : ∀ i, Integrable (Z i) P) (N : ℕ) :
    Martingale (stoppedProcess (finiteBellman P 𝓕 Z N)
      (fun ω => (finiteBellmanContact P 𝓕 Z N ω : WithTop ℕ))) 𝓕 P :=
  discrete_stopped_martingale_of_before (finiteBellman_stronglyAdapted ha N)
    (finiteBellman_integrable hi N) (finiteBellmanContact_stopping ha N)
    (finiteBellmanContact_before N)

/--
@isnad1 id=eq.2h5v.s7.16ba0d8b4b8f from=translated src=- shape=325f6ac2 vocab=5e9e1b18
-/
theorem finiteBellmanContact_expected_payoff (ha : Adapted 𝓕 Z)
    (hi : ∀ i, Integrable (Z i) P) (N : ℕ) :
    (∫ ω, Z (finiteBellmanContact P 𝓕 Z N ω) ω ∂P) =
      ∫ ω, finiteBellman P 𝓕 Z N 0 ω ∂P := by
  have hm := finiteBellmanContact_martingale ha hi N
  have h0 : stoppedProcess (finiteBellman P 𝓕 Z N)
      (fun ω => (finiteBellmanContact P 𝓕 Z N ω : WithTop ℕ)) 0 = finiteBellman P 𝓕 Z N 0 := by
    ext ω
    change finiteBellman P 𝓕 Z N (min 0 (finiteBellmanContact P 𝓕 Z N ω)) ω = _
    simp
  have hN : stoppedProcess (finiteBellman P 𝓕 Z N)
      (fun ω => (finiteBellmanContact P 𝓕 Z N ω : WithTop ℕ)) N =
        fun ω => Z (finiteBellmanContact P 𝓕 Z N ω) ω := by
    ext ω
    change finiteBellman P 𝓕 Z N (min N (finiteBellmanContact P 𝓕 Z N ω)) ω = _
    rw [min_eq_right (finiteBellmanContact_le N ω)]
    exact finiteBellmanContact_contact N ω
  have he := hm.setIntegral_eq (i := 0) (j := N) (Nat.zero_le _) (s := univ) MeasurableSet.univ
  rw [h0,hN] at he
  simpa only [Measure.restrict_univ] using he.symm

/--
@isnad1 id=le.4h6v.s7.b84c127c90ef from=translated src=- shape=0dd27f88 vocab=975757d4
-/
theorem expected_discrete_payoff_le_bellman (ha : Adapted 𝓕 Z)
    (hi : ∀ i, Integrable (Z i) P) {N : ℕ} {τ : Ω → ℕ}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℕ))) (hb : ∀ ω, τ ω ≤ N) :
    (∫ ω, Z (τ ω) ω ∂P) ≤ ∫ ω, finiteBellman P 𝓕 Z N 0 ω ∂P := by
  have hU := finiteBellman_supermartingale ha hi N
  have hbound : ∀ ω, (τ ω : WithTop ℕ) ≤ (N : WithTop ℕ) := fun ω => by exact_mod_cast hb ω
  have hiZ : Integrable (fun ω => Z (τ ω) ω) P := by
    convert! integrable_stoppedValue ℕ hτ hi hbound using 1
  have hiU : Integrable (fun ω => finiteBellman P 𝓕 Z N (τ ω) ω) P := by
    convert! integrable_stoppedValue ℕ hτ (finiteBellman_integrable hi N) hbound using 1
  have hle : (∫ ω, Z (τ ω) ω ∂P) ≤ ∫ ω, finiteBellman P 𝓕 Z N (τ ω) ω ∂P := by
    apply integral_mono hiZ hiU
    intro ω
    simpa only [min_eq_left (hb ω)] using finiteBellman_dominates (P := P) (𝓕 := 𝓕) (Z := Z) N (τ ω) ω
  have ho := hU.neg.expected_stoppedValue_mono (isStoppingTime_const 𝓕 0) hτ
    (fun ω => bot_le) hbound
  have ho' : (∫ ω, finiteBellman P 𝓕 Z N (τ ω) ω ∂P) ≤
      ∫ ω, finiteBellman P 𝓕 Z N 0 ω ∂P := by
    simp only [stoppedValue,Pi.neg_apply,integral_neg,neg_le_neg_iff] at ho
    convert! ho using 1
  exact hle.trans ho'

/--
@isnad1 id=le.4h6v.s7.411b7e9b698c from=translated src=- shape=9b0a5977 vocab=2cba14f0
-/
theorem finiteBellmanContact_optimal (ha : Adapted 𝓕 Z)
    (hi : ∀ i, Integrable (Z i) P) {N : ℕ} {τ : Ω → ℕ}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℕ))) (hb : ∀ ω, τ ω ≤ N) :
    (∫ ω, Z (τ ω) ω ∂P) ≤ ∫ ω, Z (finiteBellmanContact P 𝓕 Z N ω) ω ∂P := by
  rw [finiteBellmanContact_expected_payoff ha hi N]
  exact expected_discrete_payoff_le_bellman ha hi hτ hb

end MathFin.BlackScholes.AmericanPut.Stopping
