import Tengoku.EocLeanVerification.EOC.TaoLike.TaoInterface
import Tengoku.EocLeanVerification.EOC.Confinement
import Tengoku.Seed.Analysis.Convex.SpecificFunctions.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometric persistence upper bound (Milestone 6)

**EXPONENTIAL-RATE UPPER BOUND.** A Chernoff/exponential-Markov bound for the "persistence"
event — the centered partial sums of an iid `Geom(2)^n` vector staying below a threshold `c`
at every prefix — under the concrete `iidGeom2VectorProb n` law from Milestone 4B.

This is a statement about the abstract iid `Geom(2)^n` probability model only. It is **not**
a theorem about real Collatz trajectories; that transfer is reserved for a later milestone
(`shifted_persistence_transfer`). It proves only an exponential-rate upper bound: the sharp
`n^(-3/2)` polynomial ballot-theorem prefactor is **not** claimed.
-/

namespace EOC
namespace TaoExternal

/-! ## Part 4: `geomPersistenceEvent` and the endpoint-event reduction -/

/-- The partial digit sum `Σ_{i<j} a_i`, real-valued.-/
noncomputable def digitSum (n : ℕ) (a : Fin n → ℕ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), (a i : ℝ)

/-- The centered partial sum `Σ_{i<j} (a_i - α)` at prefix length `j`.-/
noncomputable def centeredSum (α : ℝ) (n : ℕ) (a : Fin n → ℕ) (j : ℕ) : ℝ :=
  digitSum n a j - (j : ℝ) * α

/-- The **persistence event**: the centered partial sum stays `≤ c` at every prefix
`1 ≤ j ≤ n`.-/
def geomPersistenceEvent (α c : ℝ) (n : ℕ) : Set (Fin n → ℕ) :=
  {a | ∀ j, 1 ≤ j → j ≤ n → centeredSum α n a j ≤ c}

/-- The endpoint total sum `Σ_i a_i` (all of `Fin n`).-/
noncomputable def totalSum (n : ℕ) (a : Fin n → ℕ) : ℝ := ∑ i : Fin n, (a i : ℝ)

/-- The endpoint centered sum `Σ_i a_i - n·α`.-/
noncomputable def totalCenteredSum (α : ℝ) (n : ℕ) (a : Fin n → ℕ) : ℝ :=
  totalSum n a - (n : ℝ) * α

/--
@isnad1 id=eq.0h2v.s4.4b66f850b034 from=translated src=- shape=c93af49c vocab=314a3fa7
-/
theorem digitSum_eq_totalSum (n : ℕ) (a : Fin n → ℕ) : digitSum n a n = totalSum n a := by
  unfold digitSum totalSum
  congr 1
  exact Finset.filter_true_of_mem (fun i _ => i.isLt)

/--
@isnad1 id=eq.0h3v.s4.28df7b4d8f02 from=translated src=- shape=c66446be vocab=f2f8aafc
-/
theorem centeredSum_eq_totalCenteredSum (α : ℝ) (n : ℕ) (a : Fin n → ℕ) :
    centeredSum α n a n = totalCenteredSum α n a := by
  unfold centeredSum totalCenteredSum
  rw [digitSum_eq_totalSum]

/-- **Endpoint-event reduction.** The persistence event is contained in the (weaker) endpoint
event `{a | totalCenteredSum α n a ≤ c}` — it suffices to Chernoff-bound the latter.
@isnad1 id=le.2h4v.s5.429e16a025e3 from=translated src=- shape=ff90f831 vocab=dfee27f5
-/
theorem geomPersistenceEvent_subset_endpoint (α c : ℝ) (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℕ)
    (ha : a ∈ geomPersistenceEvent α c n) : totalCenteredSum α n a ≤ c := by
  have h := ha n hn (le_refl n)
  rwa [centeredSum_eq_totalCenteredSum] at h

/-! ## Part 5: generic product-tsum-equals-power lemma

Generalizes `atomWeight_tsum_eq_one`'s induction pattern to an arbitrary nonnegative summable
single-digit weight `w`, rather than rebuilding independence machinery from scratch. -/

/--
@isnad1 id=eq.0h4v.s6.eeea31b4c65e from=translated src=- shape=a99657ff vocab=195c6893
-/
theorem genProdWeight_cons {w : ℕ → ℝ} (n k : ℕ) (a : Fin n → ℕ) :
    (∏ i, w ((Fin.cons k a : Fin (n + 1) → ℕ) i)) = w k * ∏ i, w (a i) := by
  rw [Fin.prod_univ_succ]
  simp

set_option maxHeartbeats 1000000 in
-- w is an abstract (uninterpreted) weight function, so unification here is
-- much slower than for the concrete geom2/atomWeight case it generalizes.
/--
@isnad1 id=summable.2h2v.s6.c0c00c0aa40f from=translated src=- shape=8918c3aa vocab=004e8eeb
-/
theorem genProdWeight_summable {w : ℕ → ℝ} (hw_nonneg : ∀ k, 0 ≤ w k) (hw_summable : Summable w)
    (n : ℕ) : Summable (fun a : Fin n → ℕ => ∏ i, w (a i)) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
      have hmul : Summable (fun p : ℕ × (Fin n → ℕ) => w p.1 * ∏ i, w (p.2 i)) :=
        Summable.mul_of_nonneg hw_summable ih
          hw_nonneg (fun a => Finset.prod_nonneg (fun i _ => hw_nonneg _))
      have heq : (fun p : ℕ × (Fin n → ℕ) => w p.1 * ∏ i, w (p.2 i))
          = (fun a : Fin (n + 1) → ℕ => ∏ i, w (a i))
            ∘ (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)) := by
        funext p
        simp only [Function.comp_apply]
        rw [← genProdWeight_cons n p.1 p.2]
        congr 1
      rw [heq] at hmul
      exact (Equiv.summable_iff (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))).mp hmul

set_option maxHeartbeats 1000000 in
-- same reason as genProdWeight_summable above: w is abstract.
/--
@isnad1 id=eq.2h2v.s7.99d819573a18 from=translated src=- shape=545d4239 vocab=9d6cc45e
-/
theorem genProdWeight_tsum_succ {w : ℕ → ℝ} (hw_nonneg : ∀ k, 0 ≤ w k) (hw_summable : Summable w)
    (n : ℕ) :
    ∑' a : Fin (n + 1) → ℕ, ∏ i, w (a i)
      = (∑' k, w k) * ∑' a : Fin n → ℕ, ∏ i, w (a i) := by
  rw [← Equiv.tsum_eq (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ))]
  have heq : ∀ p : ℕ × (Fin n → ℕ),
      ∏ i, w ((Fin.consEquiv (fun _ : Fin (n + 1) => ℕ) p) i) = w p.1 * ∏ i, w (p.2 i) := by
    intro p
    rw [← genProdWeight_cons n p.1 p.2]
    congr 1
  simp_rw [heq]
  exact (Summable.tsum_mul_tsum hw_summable (genProdWeight_summable hw_nonneg hw_summable n)
    (Summable.mul_of_nonneg hw_summable (genProdWeight_summable hw_nonneg hw_summable n) hw_nonneg
      (fun a => Finset.prod_nonneg (fun i _ => hw_nonneg _)))).symm

/-- **Generic product-tsum-equals-power** (generalizing `atomWeight_tsum_eq_one`): for any
nonnegative summable single-digit weight `w`, the length-`n` iid product law normalizes to
`(Σ' w)^n`.
@isnad1 id=eq.2h2v.s6.48f15d43f094 from=translated src=- shape=03378721 vocab=6d46106e
-/
theorem genProdWeight_tsum_eq_pow {w : ℕ → ℝ} (hw_nonneg : ∀ k, 0 ≤ w k)
    (hw_summable : Summable w) (n : ℕ) :
    ∑' a : Fin n → ℕ, ∏ i, w (a i) = (∑' k, w k) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [genProdWeight_tsum_succ hw_nonneg hw_summable, ih, pow_succ']

/-! ## Part 6: the tilted digit weight and its moment generating function `Mfun` -/

/-- The exponentially-tilted single-digit weight `geom2(k) · exp(-lam(k-α))`.-/
noncomputable def tiltedDigitWeight (α lam : ℝ) (k : ℕ) : ℝ :=
  geom2 k * Real.exp (-lam * ((k : ℝ) - α))

/-- The moment generating function value `M(lam) = exp(lamα) / (2·exp(lam) - 1)`.-/
noncomputable def Mfun (α lam : ℝ) : ℝ := Real.exp (lam * α) / (2 * Real.exp lam - 1)

/--
@isnad1 id=le.0h3v.s4.f7747169995c from=translated src=- shape=bad53a6c vocab=ea08b663
-/
theorem tiltedDigitWeight_nonneg (α lam : ℝ) (k : ℕ) : 0 ≤ tiltedDigitWeight α lam k :=
  mul_nonneg (geom2_nonneg k) (Real.exp_pos _).le

/--
@isnad1 id=le.1h3v.s5.e1c5db96a147 from=translated src=- shape=8aa84d4c vocab=7c243bff
-/
theorem tiltedDigitWeight_le_geom2_mul_const (α lam : ℝ) (hlam : 0 ≤ lam) (k : ℕ) :
    tiltedDigitWeight α lam k ≤ Real.exp (lam * α) * geom2 k := by
  unfold tiltedDigitWeight
  have hexp_le : Real.exp (-lam * ((k : ℝ) - α)) ≤ Real.exp (lam * α) * Real.exp (-lam * k) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc geom2 k * Real.exp (-lam * ((k : ℝ) - α))
      ≤ geom2 k * (Real.exp (lam * α) * Real.exp (-lam * k)) :=
        mul_le_mul_of_nonneg_left hexp_le (geom2_nonneg k)
    _ ≤ geom2 k * (Real.exp (lam * α) * 1) := by
        apply mul_le_mul_of_nonneg_left _ (geom2_nonneg k)
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rw [Real.exp_le_one_iff]
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
    _ = Real.exp (lam * α) * geom2 k := by ring

/--
@isnad1 id=summable.1h2v.s4.5cff63ae3c2c from=translated src=- shape=09b6a055 vocab=7098e560
-/
theorem tiltedDigitWeight_summable (α lam : ℝ) (hlam : 0 ≤ lam) :
    Summable (tiltedDigitWeight α lam) := by
  apply Summable.of_nonneg_of_le (tiltedDigitWeight_nonneg α lam)
    (tiltedDigitWeight_le_geom2_mul_const α lam hlam)
  exact geom2_summable.mul_left _

/--
@isnad1 id=eq.1h2v.s5.bf63eefac88a from=translated src=- shape=beebb8e4 vocab=9640c771
-/
theorem tiltedDigitWeight_tsum (α lam : ℝ) (hlam : 0 < lam) :
    ∑' k, tiltedDigitWeight α lam k = Mfun α lam := by
  unfold Mfun
  have hstep : ∀ k : ℕ, tiltedDigitWeight α lam k
      = Real.exp (lam * α) * (geom2 k * Real.exp (-lam * (k : ℝ))) := by
    intro k
    unfold tiltedDigitWeight
    rw [show (-lam * ((k : ℝ) - α)) = lam * α + (-lam * (k : ℝ)) by ring, Real.exp_add]
    ring
  rw [tsum_congr hstep, tsum_mul_left]
  have hr_lt : Real.exp (-lam) / 2 < 1 := by
    have : Real.exp (-lam) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hr_nonneg : (0:ℝ) ≤ Real.exp (-lam) / 2 := by positivity
  have hsum0 : Summable (fun n : ℕ => (Real.exp (-lam) / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one hr_nonneg hr_lt
  have hgsummable : Summable geom2 := geom2_summable
  have hterm0 : geom2 0 * Real.exp (-lam * ((0:ℕ) : ℝ)) = 0 := by
    rw [geom2_eq_zero]; ring
  have hsplit : Summable (fun k : ℕ => geom2 k * Real.exp (-lam * (k : ℝ))) := by
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg (geom2_nonneg k) (Real.exp_pos _).le)
      (fun k => ?_) hgsummable
    calc geom2 k * Real.exp (-lam * (k : ℝ)) ≤ geom2 k * 1 := by
          apply mul_le_mul_of_nonneg_left _ (geom2_nonneg k)
          rw [Real.exp_le_one_iff]
          nlinarith [Nat.cast_nonneg (α := ℝ) k]
      _ = geom2 k := by ring
  rw [hsplit.tsum_eq_zero_add, hterm0, zero_add]
  have hterm1 : ∀ n : ℕ,
      geom2 (n + 1) * Real.exp (-lam * (((n : ℕ) + 1 : ℕ) : ℝ))
        = (Real.exp (-lam) / 2) * (Real.exp (-lam) / 2) ^ n := by
    intro n
    rw [geom2_eq_of_pos (by omega : 1 ≤ n + 1),
      mul_comm (-lam) (((n : ℕ) + 1 : ℕ) : ℝ), Real.exp_nat_mul, ← mul_pow,
      show (1 / 2 : ℝ) * Real.exp (-lam) = Real.exp (-lam) / 2 by ring, pow_succ]
    ring
  rw [tsum_congr hterm1, tsum_mul_left, tsum_geometric_of_lt_one hr_nonneg hr_lt]
  have hexp_pos : (0:ℝ) < Real.exp lam := Real.exp_pos lam
  have hden_pos : (0:ℝ) < 2 * Real.exp lam - 1 := by
    have h1 : (1:ℝ) < Real.exp lam := by
      rw [show (1:ℝ) = Real.exp 0 by simp]
      exact Real.exp_lt_exp.mpr hlam
    linarith
  rw [Real.exp_neg]
  field_simp

/-! ## Part 7: the pointwise Chernoff inequality and the generic Chernoff bound -/

/--
@isnad1 id=eq.0h4v.s5.44409dd3e0a5 from=translated src=- shape=0466160d vocab=612a5ca0
-/
theorem tiltedAtomWeight_eq (α lam : ℝ) (n : ℕ) (a : Fin n → ℕ) :
    (∏ i, tiltedDigitWeight α lam (a i))
      = atomWeight n a * Real.exp (-lam * totalCenteredSum α n a) := by
  unfold tiltedDigitWeight atomWeight totalCenteredSum totalSum
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

/--
@isnad1 id=le.2h5v.s6.fad2dbd16b0a from=translated src=- shape=4a5fdf18 vocab=7712eb83
-/
theorem geom_persistence_pointwise_chernoff (α c lam : ℝ) (hlam : 0 < lam) (n : ℕ) (hn : 1 ≤ n)
    (a : Fin n → ℕ) :
    Set.indicator (geomPersistenceEvent α c n) (atomWeight n) a
      ≤ Real.exp (lam * c) * ∏ i, tiltedDigitWeight α lam (a i) := by
  rw [tiltedAtomWeight_eq]
  by_cases ha : a ∈ geomPersistenceEvent α c n
  · have hend : totalCenteredSum α n a ≤ c := geomPersistenceEvent_subset_endpoint α c n hn a ha
    have hexp_ge : (1:ℝ) ≤ Real.exp (lam * c) * Real.exp (-lam * totalCenteredSum α n a) := by
      rw [← Real.exp_add]
      have h0le : (0:ℝ) ≤ lam * c + -lam * totalCenteredSum α n a := by nlinarith
      calc (1:ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp (lam * c + -lam * totalCenteredSum α n a) := Real.exp_le_exp.mpr h0le
    simp only [Set.indicator, ha, ite_true]
    nlinarith [atomWeight_nonneg n a, hexp_ge]
  · simp only [Set.indicator, ha, ite_false]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (atomWeight_nonneg n a) (Real.exp_pos _).le)

/-- **Concrete specialized helper** (fixes `w := tiltedDigitWeight α lam` once, rather than
letting `iid_geom_chernoff_bound` repeatedly instantiate the fully generic
`genProdWeight_summable` machinery inline — this is what keeps that theorem's elaboration
cost practical).
@isnad1 id=summable.1h3v.s5.c6db29450586 from=translated src=- shape=8f5c48c2 vocab=a6b589ac
-/
theorem tiltedVectorWeight_summable (α lam : ℝ) (hlam : 0 ≤ lam) (n : ℕ) :
    Summable (fun a : Fin n → ℕ => ∏ i, tiltedDigitWeight α lam (a i)) :=
  genProdWeight_summable (tiltedDigitWeight_nonneg α lam) (tiltedDigitWeight_summable α lam hlam) n

/-- **Concrete specialized helper**, companion to `tiltedVectorWeight_summable`.
@isnad1 id=eq.1h3v.s6.cbbfef2db3c7 from=translated src=- shape=7f724112 vocab=d740f76a
-/
theorem tiltedVectorWeight_tsum (α lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ∑' a : Fin n → ℕ, ∏ i, tiltedDigitWeight α lam (a i) = (Mfun α lam) ^ n := by
  rw [genProdWeight_tsum_eq_pow (tiltedDigitWeight_nonneg α lam)
      (tiltedDigitWeight_summable α lam hlam.le) n, tiltedDigitWeight_tsum α lam hlam]

/-- **Generic-λ Chernoff bound.** The persistence event's probability under `iidGeom2VectorProb`
is bounded by `exp(λc)·M(λ)^n` for every `λ > 0`.

Proved via `tsum_nonneg`/`Summable.tsum_sub` rather than `Summable.tsum_mono` inside a `calc`:
the latter (which mixes a `≤`-step through a generic `Summable.tsum_mono` invocation with
subsequent `=`-steps under `Trans` resolution) was measured to blow up elaboration time on
this abstract `Fin n → ℕ`-indexed goal — plausibly the `SummationFilter`/`[L.NeBot]` instance
search this Mathlib's generalized `Summable.tsum_mono` carries, compounded across the several
pending metavariables from neighboring `have`s. The `tsum_nonneg`/`Summable.tsum_sub`/`linarith`
route proves the identical inequality without ever invoking that lemma.
@isnad1 id=le.2h4v.s6.04c664592d1f from=translated src=- shape=07578f5a vocab=1c2fbf82
-/
theorem iid_geom_chernoff_bound (α c lam : ℝ) (hlam : 0 < lam) (n : ℕ) (hn : 1 ≤ n) :
    iidGeom2VectorProb n (geomPersistenceEvent α c n) ≤ Real.exp (lam * c) * (Mfun α lam) ^ n := by
  unfold iidGeom2VectorProb genEventProb
  have hsummable_rhs : Summable (fun a : Fin n → ℕ =>
      Real.exp (lam * c) * ∏ i, tiltedDigitWeight α lam (a i)) :=
    (tiltedVectorWeight_summable α lam hlam.le n).mul_left _
  have hbound : ∀ a : Fin n → ℕ, Set.indicator (geomPersistenceEvent α c n) (atomWeight n) a
      ≤ Real.exp (lam * c) * ∏ i, tiltedDigitWeight α lam (a i) :=
    fun a => geom_persistence_pointwise_chernoff α c lam hlam n hn a
  have hsummable_lhs : Summable (fun a : Fin n → ℕ =>
      Set.indicator (geomPersistenceEvent α c n) (atomWeight n) a) :=
    Summable.of_nonneg_of_le (fun a => Set.indicator_nonneg (fun x _ => atomWeight_nonneg n x) a)
      hbound hsummable_rhs
  have hle : ∑' a : Fin n → ℕ, Set.indicator (geomPersistenceEvent α c n) (atomWeight n) a
      ≤ ∑' a : Fin n → ℕ, Real.exp (lam * c) * ∏ i, tiltedDigitWeight α lam (a i) := by
    have hsub_nonneg : ∀ a : Fin n → ℕ, 0 ≤
        Real.exp (lam * c) * (∏ i, tiltedDigitWeight α lam (a i))
          - Set.indicator (geomPersistenceEvent α c n) (atomWeight n) a := fun a => by
      linarith [hbound a]
    have hsub_summable : Summable (fun a : Fin n → ℕ =>
        Real.exp (lam * c) * (∏ i, tiltedDigitWeight α lam (a i))
          - Set.indicator (geomPersistenceEvent α c n) (atomWeight n) a) :=
      hsummable_rhs.sub hsummable_lhs
    have h0le : (0:ℝ) ≤ ∑' a : Fin n → ℕ,
        (Real.exp (lam * c) * (∏ i, tiltedDigitWeight α lam (a i))
          - Set.indicator (geomPersistenceEvent α c n) (atomWeight n) a) := tsum_nonneg hsub_nonneg
    rwa [Summable.tsum_sub hsummable_rhs hsummable_lhs, sub_nonneg] at h0le
  have heq : ∑' a : Fin n → ℕ, Real.exp (lam * c) * ∏ i, tiltedDigitWeight α lam (a i)
      = Real.exp (lam * c) * (Mfun α lam) ^ n := by
    rw [tsum_mul_left, tiltedVectorWeight_tsum α lam hlam n]
  linarith [hle, heq]

/-! ## Part 8: `collatzAlpha` and its order facts

`EOC.Confinement` already defines `alpha := Real.logb 2 3` with `one_lt_alpha : 1 < alpha`
(used throughout the repo's drift/confinement arguments, e.g. `EOC.BoundedDrift`,
`EOC.Periodic`). No `alpha < 2` or `4/3 < alpha` fact exists anywhere in the repo (checked via
grep). `collatzAlpha` below is a **thin alias for that existing constant** — not a competing
definition — so this milestone's Layer B statements can use the name the brief specifies. -/

noncomputable def collatzAlpha : ℝ := alpha

/--
@isnad1 id=eq.0h0v.s4.3b407ec6e371 from=translated src=- shape=b1ada3a6 vocab=f6a1e4dd
-/
theorem collatzAlpha_eq_log_div_log : collatzAlpha = Real.log 3 / Real.log 2 := by
  rfl

/--
@isnad1 id=lt.0h0v.s3.d2922cb34006 from=translated src=- shape=ff3a10fc vocab=f456223c
-/
theorem one_lt_collatzAlpha : 1 < collatzAlpha := one_lt_alpha

/-- `3 < 4 = 2^2` gives `log 3 < 2 log 2`, i.e. `collatzAlpha < 2`.
@isnad1 id=lt.0h0v.s3.02c5181bf555 from=translated src=- shape=ffdda526 vocab=368f9a30
-/
theorem collatzAlpha_lt_two : collatzAlpha < 2 := by
  rw [collatzAlpha_eq_log_div_log, div_lt_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))]
  have h4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]; push_cast; ring
  calc Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    _ = 2 * Real.log 2 := h4

/-- `2^4 = 16 < 27 = 3^3` gives `4 log 2 < 3 log 3`, i.e. `4/3 < collatzAlpha`. Used to prove
`rateNats > 0` via the factorization `-3(α-2)²(α-4/3) ≤ 0`.
@isnad1 id=lt.0h0v.s4.94093e22486d from=translated src=- shape=5ccaf027 vocab=3a9a64ce
-/
theorem four_thirds_lt_collatzAlpha : (4:ℝ) / 3 < collatzAlpha := by
  rw [collatzAlpha_eq_log_div_log, lt_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))]
  have h27 : Real.log (27:ℝ) = 3 * Real.log 3 := by
    rw [show (27:ℝ) = 3 ^ (3:ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have h16 : Real.log (16:ℝ) = 4 * Real.log 2 := by
    rw [show (16:ℝ) = 2 ^ (4:ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlt : Real.log (16:ℝ) < Real.log (27:ℝ) := Real.log_lt_log (by norm_num) (by norm_num)
  nlinarith [hlt, h27, h16]

/--
@isnad1 id=lt.0h0v.s4.7297d67d9561 from=translated src=- shape=3b25bc41 vocab=be69854b
-/
theorem collatzAlpha_sub_one_pos : 0 < collatzAlpha - 1 := by linarith [one_lt_collatzAlpha]

/-! ## Part 9: the optimal tilt `lambdaStar` -/

/--
@isnad1 id=lt.0h0v.s5.8d7b707013ed from=translated src=- shape=c1494c87 vocab=52081518
-/
theorem collatzAlpha_div_pos : 0 < collatzAlpha / (2 * (collatzAlpha - 1)) :=
  div_pos (by linarith [one_lt_collatzAlpha]) (by linarith [collatzAlpha_sub_one_pos])

/-- `α / (2(α-1)) > 1 ⟺ α > 2(α-1) ⟺ 2 > α`, i.e. this is exactly `collatzAlpha_lt_two`.
@isnad1 id=lt.0h0v.s5.f6505c8e75d9 from=translated src=- shape=c1494c87 vocab=52081518
-/
theorem collatzAlpha_div_gt_one : 1 < collatzAlpha / (2 * (collatzAlpha - 1)) := by
  rw [lt_div_iff₀ (by linarith [collatzAlpha_sub_one_pos] : (0:ℝ) < 2 * (collatzAlpha - 1))]
  nlinarith [collatzAlpha_lt_two]

noncomputable def lambdaStar : ℝ := Real.log (collatzAlpha / (2 * (collatzAlpha - 1)))

/--
@isnad1 id=lt.0h0v.s3.2fb7220af669 from=translated src=- shape=ff3a10fc vocab=519b9ea5
-/
theorem lambdaStar_pos : 0 < lambdaStar :=
  Real.log_pos collatzAlpha_div_gt_one

/--
@isnad1 id=eq.0h0v.s5.0fe7b83110e5 from=translated src=- shape=718f6602 vocab=a2aafe42
-/
theorem exp_lambdaStar : Real.exp lambdaStar = collatzAlpha / (2 * (collatzAlpha - 1)) :=
  Real.exp_log collatzAlpha_div_pos

/-! ## Part 10: `rateNats` and its positivity -/

/--
@isnad1 id=lt.0h0v.s5.37845ec0f0cd from=translated src=- shape=a4e990a1 vocab=777c5cea
-/
theorem two_exp_lambdaStar_sub_one_pos : 0 < 2 * Real.exp lambdaStar - 1 := by
  have h1 : (1:ℝ) < Real.exp lambdaStar := by
    rw [show (1:ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr lambdaStar_pos
  linarith

/--
@isnad1 id=lt.0h0v.s3.0d3c129bfead from=translated src=- shape=7164367e vocab=6890d4c3
-/
theorem Mfun_collatzAlpha_lambdaStar_pos : 0 < Mfun collatzAlpha lambdaStar := by
  unfold Mfun
  exact div_pos (Real.exp_pos _) two_exp_lambdaStar_sub_one_pos

/-- **Key positivity step.** At the optimal tilt, `M(λ*) < 1`. Proved via strict convexity of
`exp` (the exponent `collatzAlpha * lambdaStar` is the convex combination
`(collatzAlpha/2) • (2·lambdaStar) + (1 - collatzAlpha/2) • 0`, since `0 < collatzAlpha < 2`),
which reduces the claim to the purely algebraic fact `3(α-2)²(α-4/3) ≥ 0` — true since
`α > 4/3` (`four_thirds_lt_collatzAlpha`).
@isnad1 id=lt.0h0v.s3.f34590d3d4f8 from=translated src=- shape=b3c4969c vocab=6890d4c3
-/
theorem Mfun_collatzAlpha_lambdaStar_lt_one : Mfun collatzAlpha lambdaStar < 1 := by
  unfold Mfun
  rw [div_lt_one two_exp_lambdaStar_sub_one_pos]
  have hexp2 : Real.exp (2 * lambdaStar) = (collatzAlpha / (2 * (collatzAlpha - 1))) ^ 2 := by
    rw [two_mul, Real.exp_add, exp_lambdaStar]; ring
  have hconv := strictConvexOn_exp.2 (Set.mem_univ (2 * lambdaStar)) (Set.mem_univ (0:ℝ))
      (ne_of_gt (by linarith [lambdaStar_pos] : (0:ℝ) < 2 * lambdaStar))
      (show (0:ℝ) < collatzAlpha / 2 by linarith [one_lt_collatzAlpha])
      (show (0:ℝ) < 1 - collatzAlpha / 2 by linarith [collatzAlpha_lt_two])
      (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hconv
  rw [show collatzAlpha / 2 * (2 * lambdaStar) = lambdaStar * collatzAlpha by ring, hexp2] at hconv
  have halg : collatzAlpha / 2 * (collatzAlpha / (2 * (collatzAlpha - 1))) ^ 2
        + (1 - collatzAlpha / 2)
      ≤ 2 * Real.exp lambdaStar - 1 := by
    rw [exp_lambdaStar, ← sub_nonneg]
    have hd0 : (collatzAlpha - 1) ≠ 0 := ne_of_gt collatzAlpha_sub_one_pos
    have expand : 2 * (collatzAlpha / (2 * (collatzAlpha - 1))) - 1
          - (collatzAlpha / 2 * (collatzAlpha / (2 * (collatzAlpha - 1))) ^ 2
             + (1 - collatzAlpha / 2))
        = 3 * (collatzAlpha - 2) ^ 2 * (collatzAlpha - 4 / 3)
            / (2 * (2 * (collatzAlpha - 1)) ^ 2) := by
      field_simp
      ring
    rw [expand]
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    linarith [four_thirds_lt_collatzAlpha]
  linarith [hconv, halg]

noncomputable def rateNats : ℝ := -Real.log (Mfun collatzAlpha lambdaStar)

/--
@isnad1 id=lt.0h0v.s3.c38010909ca4 from=translated src=- shape=ff3a10fc vocab=fc52dd5c
-/
theorem rateNats_pos : 0 < rateNats := by
  unfold rateNats
  have := Real.log_neg Mfun_collatzAlpha_lambdaStar_pos Mfun_collatzAlpha_lambdaStar_lt_one
  linarith

/--
@isnad1 id=eq.0h0v.s3.bb971480eda9 from=translated src=- shape=2117893d vocab=8274c737
-/
theorem Mfun_collatzAlpha_lambdaStar_eq_exp_neg_rateNats :
    Mfun collatzAlpha lambdaStar = Real.exp (-rateNats) := by
  unfold rateNats
  rw [neg_neg, Real.exp_log Mfun_collatzAlpha_lambdaStar_pos]

/-! ## Part 11: the specialized exponential-rate persistence upper bound

**EXPONENTIAL-RATE UPPER BOUND** — not the sharp `n^(-3/2)` ballot-theorem prefactor, no
lower bound, no matching asymptotics. This is a statement about the abstract iid `Geom(2)^n`
law only, not (yet) about real Collatz trajectories. -/

/-- Specializes `iid_geom_chernoff_bound` at the optimal tilt `lambdaStar`, exposing the exact
positive natural-log rate `rateNats`.
@isnad1 id=le.1h2v.s5.caa95051d8f3 from=translated src=- shape=0b6dc42f vocab=1b66fecf
-/
theorem geometric_persistence_upper_bound (c : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iidGeom2VectorProb n (geomPersistenceEvent collatzAlpha c n)
      ≤ Real.exp (lambdaStar * c) * Real.exp (-(rateNats * (n : ℝ))) := by
  have hbound := iid_geom_chernoff_bound collatzAlpha c lambdaStar lambdaStar_pos n hn
  have hpow : (Mfun collatzAlpha lambdaStar) ^ n = Real.exp (-(rateNats * (n : ℝ))) := by
    rw [Mfun_collatzAlpha_lambdaStar_eq_exp_neg_rateNats, ← Real.exp_nat_mul]
    congr 1
    ring
  rwa [hpow] at hbound

/-! ## Part 12: the bit-rate `I0` and `rateNats = I0 * ln 2`

Uses Mathlib's existing `Real.logb 2` as the binary log — no new `log2` helper is introduced. -/

noncomputable def I0 : ℝ :=
  collatzAlpha - collatzAlpha * Real.logb 2 collatzAlpha
    + (collatzAlpha - 1) * Real.logb 2 (collatzAlpha - 1)

/--
@isnad1 id=eq.0h0v.s5.38f2b9339cf8 from=translated src=- shape=a275eebf vocab=08e7e5d0
-/
theorem two_exp_lambdaStar_sub_one_eq_inv : 2 * Real.exp lambdaStar - 1 = (collatzAlpha - 1)⁻¹ := by
  have hd0 : (collatzAlpha - 1) ≠ 0 := ne_of_gt collatzAlpha_sub_one_pos
  rw [exp_lambdaStar]
  field_simp
  ring

/--
@isnad1 id=eq.0h0v.s4.b7216f859d95 from=translated src=- shape=08abebb0 vocab=11239e3c
-/
theorem rateNats_eq_I0_mul_log_two : rateNats = I0 * Real.log 2 := by
  have hd0 : (collatzAlpha - 1) ≠ 0 := ne_of_gt collatzAlpha_sub_one_pos
  have ha0 : collatzAlpha ≠ 0 := ne_of_gt (by linarith [one_lt_collatzAlpha])
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold rateNats Mfun
  rw [two_exp_lambdaStar_sub_one_eq_inv,
    Real.log_div (Real.exp_pos _).ne' (inv_ne_zero hd0), Real.log_exp, Real.log_inv]
  unfold lambdaStar
  rw [Real.log_div ha0 (by positivity : (2 * (collatzAlpha - 1)) ≠ 0),
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hd0]
  unfold I0
  rw [Real.logb, Real.logb]
  field_simp
  ring

/-! ## Part 13 (optional): bit-rate corollary -/

/-- Same bound as `geometric_persistence_upper_bound`, expressed in bits via `(2:ℝ)^(-I0·n)`
(`Real.rpow`, forced by the real-valued exponent `-(I0 * (n:ℝ))`).
@isnad1 id=le.1h2v.s6.88127d3081a6 from=translated src=- shape=25427186 vocab=c61a1af6
-/
theorem geometric_persistence_upper_bound_bits (c : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iidGeom2VectorProb n (geomPersistenceEvent collatzAlpha c n)
      ≤ Real.exp (lambdaStar * c) * (2:ℝ) ^ (-(I0 * (n : ℝ))) := by
  have hbase := geometric_persistence_upper_bound c n hn
  have heq : Real.exp (-(rateNats * (n : ℝ))) = (2:ℝ) ^ (-(I0 * (n : ℝ))) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), rateNats_eq_I0_mul_log_two]
    congr 1
    ring
  rwa [heq] at hbase

end TaoExternal
end EOC
