import Tengoku.EocLeanVerification.EOC.LogCorridor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Upper-wall escape: returning anchors cross every upper drift wall

Complement to `EOC.LogCorridor` (lower-wall escape for divergent anchors). Everything here is
unconditional except where `LogFloorExclusion` (the external García–Tal/Curry interface) appears as
an explicit hypothesis.

**Orbit types.** Every accelerated orbit is either injective or eventually periodic
(`orbit_dichotomy`); injective orbits tend to infinity (`injective_orbit_tendsto`); bounded orbits
are not injective (`bounded_orbit_not_injective`). There is no third, bounded-but-aperiodic type.

**Size–drift identity.** `m_n · 2^{R_n} = m_0 · U_n` with `U_n = ∏_{k<n} (1 + 1/(3 m_k)) ≥ 1`
(`HarmonicPacking.orbit_mul_two_rpow_R`). Consequences:

* `R_gt_iff` — **upper exit is a modified stopping time**: `c < R_n ↔ 2^c · m_n < m_0 · U_n`.
* `upper_exit_of_descent` — `2^c · m_n < m_0` forces `c < R_n`.
* `orbit_mul_two_rpow_R_mono` / `window_drift_gain` — `m_t 2^{R_t}` is nondecreasing, so a
  contraction `m_{t'} ≤ m_t 2^{−c}` between times `t ≤ t'` raises the drift by at least `c`.

**Periodic anchors.** The repository already has the positive cycle gain
(`three_pow_lt_two_pow_of_evPeriodic_orbit`) and the exact law `R_periodic`. Added here:

* `evPeriodic_orbit_exit_at` / `evPeriodic_orbit_exit` — explicit upper-wall exit time
  `j0 + (⌈(c − R_{j0})/Δ⌉ + 1)·L`, `Δ = blockSum − L·log₂3 > 0`.
* `bounded_orbit_not_upper_confined` — bounded orbits cross every upper wall.
* `R_after_one`, `two_rpow_R_at_one`, `reach_one_upper_exit` — after reaching `1` the drift grows
  by exactly `2 − log₂3` per step, and `m_0 ≤ 2^{R_h}` already holds at the hitting time `h`.

**Exceptional class.** `exceptional_class` / `exceptional_class_of_exclusion`: an odd seed whose
drift stays `≤ U` forever has an injective, divergent orbit that never descends below `m_0 2^{−U}`
and crosses every lower wall `−B log₂ n − K` infinitely often for `B < 8/9` (and for `B < Bstar`
under `LogFloorExclusion Bstar`).

**Rebasing.** `rebased_upper_log_wall`: an injective orbit, rebased at its global minimum, stays
under the upper logarithmic wall `R_n ≤ (1/9) log₂ n + 7/(9 ln 2)` forever (unconditional).

**Prescribed matching.** `descent_prescribed_matching_le` / `reach_one_prescribed_matching_le` —
upper exit of the anchor bounds the matching of every `U`-confined prescribed future.

None of this proves EOC, `CriticalCrossing`, or the Collatz conjecture.

No `sorry`, `admit`, `axiom`, or `opaque`.
-/

namespace EOC
namespace UpperEscape

open Finset HarmonicPacking PrescribedMatching TransportCollapse LogCorridor PeriodicCore

/-! ## 1. Orbit types -/

/-- A bounded orbit repeats a value (pigeonhole on `K + 2` times into `K + 1` values).
@isnad1 id=ex.1h2v.s5.0d480fd1f6d2 from=translated src=- shape=b9b1ce6b vocab=51522e10
-/
theorem bounded_orbit_not_injective (M K : ℕ) (hb : ∀ n, orbit M n ≤ K) :
    ∃ i j, i ≠ j ∧ orbit M i = orbit M j := by
  obtain ⟨x, _, y, _, hxy, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := range (K + 2)) (t := range (K + 1))
      (by simp) (fun n _ => by simpa [Nat.lt_succ_iff] using hb n)
  exact ⟨x, y, hxy, heq⟩

/-- An injective orbit tends to infinity: each value bound is exceeded from some time on.
@isnad1 id=ex.1h2v.s5.25a2a940abad from=translated src=- shape=8843d6e5 vocab=53bfe2c1
-/
theorem injective_orbit_tendsto (M : ℕ) (hinj : ∀ i j, orbit M i = orbit M j → i = j) (K : ℕ) :
    ∃ N₀, ∀ n ≥ N₀, K < orbit M n := by
  have hfin : (orbit M ⁻¹' Set.Iic K).Finite :=
    Set.Finite.preimage (fun x _ y _ h => hinj x y h) (Set.finite_Iic K)
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨B + 1, fun n hn => ?_⟩
  by_contra h
  push Not at h
  have := hB (show n ∈ orbit M ⁻¹' Set.Iic K from h)
  omega

/-- **Orbit dichotomy.** Every orbit is injective or has an eventually periodic word.
@isnad1 id=or.0h1v.s5.c4d3dde00bbb from=translated src=- shape=1794f59e vocab=f917629a
-/
theorem orbit_dichotomy (M : ℕ) :
    (∀ i j, orbit M i = orbit M j → i = j) ∨
      ∃ j0 L, 1 ≤ L ∧ EvPeriodic (orbWord M) j0 L := by
  by_cases hinj : ∀ i j, orbit M i = orbit M j → i = j
  · exact Or.inl hinj
  · right
    push Not at hinj
    obtain ⟨i, j, heq, hne⟩ := hinj
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j - i, by omega, evPeriodic_of_noninj M i j h heq⟩
    · exact ⟨j, i - j, by omega, evPeriodic_of_noninj M j i h heq.symm⟩

/-! ## 2. Size–drift identity consequences -/

/--
@isnad1 id=le.0h3v.s4.1cd470e3a11f from=translated src=- shape=d2642528 vocab=b8567eb2
-/
theorem carryU_mono (M t : ℕ) : ∀ k, carryU M t ≤ carryU M (t + k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, carryU_succ]
    have hf : (1 : ℝ) ≤ 1 + 1 / (3 * (orbit M (t + k) : ℝ)) := by
      have : (0 : ℝ) ≤ 1 / (3 * (orbit M (t + k) : ℝ)) := by positivity
      linarith
    nlinarith [carryU_pos M (t + k)]

/--
@isnad1 id=eq.0h1v.s4.2d7b0e78a66d from=translated src=- shape=ab70bd0f vocab=7bb10480
-/
theorem R_zero (d : ℕ → ℕ) : R d 0 = 0 := by simp [R]

/-- `m_t · 2^{R_t}` is nondecreasing along the orbit.
@isnad1 id=le.2h3v.s6.9cfabbb529b1 from=translated src=- shape=8b7713f0 vocab=283b1998
-/
theorem orbit_mul_two_rpow_R_mono (M t t' : ℕ) (hM : Odd M) (h : t ≤ t') :
    (orbit M t : ℝ) * (2 : ℝ) ^ R (orbWord M) t
      ≤ (orbit M t' : ℝ) * (2 : ℝ) ^ R (orbWord M) t' := by
  rw [orbit_mul_two_rpow_R M t hM, orbit_mul_two_rpow_R M t' hM]
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  obtain ⟨k, rfl⟩ : ∃ k, t' = t + k := ⟨t' - t, by omega⟩
  exact mul_le_mul_of_nonneg_left (carryU_mono M t k) hM0

/-- `m_0 ≤ m_n · 2^{R_n}` for every `n`.
@isnad1 id=le.1h2v.s5.085dffc6463f from=translated src=- shape=f99f8200 vocab=283b1998
-/
theorem seed_le_orbit_mul_two_rpow_R (M n : ℕ) (hM : Odd M) :
    (M : ℝ) ≤ (orbit M n : ℝ) * (2 : ℝ) ^ R (orbWord M) n := by
  have h := orbit_mul_two_rpow_R_mono M 0 n hM (Nat.zero_le n)
  rwa [R_zero, orbit_zero, Real.rpow_zero, mul_one] at h

/-- **Window drift gain.** For `t ≤ t'`, `m_t ≤ m_{t'} · 2^{R_{t'} − R_t}`: a contraction of the
orbit by a factor `2^c` raises the drift by at least `c`.
@isnad1 id=le.2h3v.s6.27a25190c83f from=translated src=- shape=37055d0b vocab=c4f85eb0
-/
theorem window_drift_gain (M t t' : ℕ) (hM : Odd M) (h : t ≤ t') :
    (orbit M t : ℝ) ≤ (orbit M t' : ℝ) * (2 : ℝ) ^ (R (orbWord M) t' - R (orbWord M) t) := by
  have hmono := orbit_mul_two_rpow_R_mono M t t' hM h
  have hpos : (0 : ℝ) < (2 : ℝ) ^ R (orbWord M) t := by positivity
  rw [Real.rpow_sub (by norm_num)]
  rw [mul_div_assoc', le_div_iff₀ hpos]
  exact hmono

/-- **Upper exit is a modified stopping time.** `c < R_n ↔ 2^c · m_n < m_0 · U_n`.
@isnad1 id=iff.1h3v.s6.8d13561c9cbf from=translated src=- shape=5904de9a vocab=12b313ed
-/
theorem R_gt_iff (M n : ℕ) (hM : Odd M) (c : ℝ) :
    c < R (orbWord M) n ↔ (2 : ℝ) ^ c * (orbit M n : ℝ) < (M : ℝ) * carryU M n := by
  have hid := orbit_mul_two_rpow_R M n hM
  have hmpos : (0 : ℝ) < (orbit M n : ℝ) := by exact_mod_cast (odd_orbit hM n).pos
  rw [← hid, mul_comm ((orbit M n : ℝ)), mul_lt_mul_iff_left₀ hmpos,
    Real.rpow_lt_rpow_left_iff (by norm_num)]

/-- **Descent forces upper exit.** If `2^c · m_n < m_0` then `c < R_n`.
@isnad1 id=lt.2h3v.s5.0d929906fffd from=translated src=- shape=cc549a84 vocab=63b0332d
-/
theorem upper_exit_of_descent (M n : ℕ) (hM : Odd M) (c : ℝ)
    (h : (2 : ℝ) ^ c * (orbit M n : ℝ) < (M : ℝ)) : c < R (orbWord M) n := by
  have hle := seed_le_orbit_mul_two_rpow_R M n hM
  have hmpos : (0 : ℝ) < (orbit M n : ℝ) := by exact_mod_cast (odd_orbit hM n).pos
  have h2 : (2 : ℝ) ^ c * (orbit M n : ℝ) < (2 : ℝ) ^ R (orbWord M) n * (orbit M n : ℝ) := by
    linarith
  have h3 := lt_of_mul_lt_mul_right h2 hmpos.le
  exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mp h3

/-! ## 3. Periodic anchors: explicit upper-wall exit -/

/-- The per-period drift gain of an eventually periodic genuine orbit is positive.
@isnad1 id=lt.3h3v.s5.1faaa4132b7d from=translated src=- shape=7893c42c vocab=b264f4bb
-/
theorem cycle_gain_pos (m0 j0 L : ℕ) (hm0 : Odd m0) (hL : 1 ≤ L)
    (hper : EvPeriodic (orbWord m0) j0 L) :
    0 < (blockSum (orbWord m0) j0 L : ℝ) - alpha * L := by
  have := alpha_mul_lt_of_pow_lt L _ (three_pow_lt_two_pow_of_evPeriodic_orbit m0 j0 L hm0 hL hper)
  linarith

/-- Exit at any `k` with `k · Δ > c − R_{j0}`.
@isnad1 id=lt.2h5v.s6.9b1616144846 from=translated src=- shape=578ca5cf vocab=7c0d2016
-/
theorem evPeriodic_orbit_exit_at (m0 j0 L : ℕ) (hper : EvPeriodic (orbWord m0) j0 L) (c : ℝ)
    (k : ℕ) (hk : c - R (orbWord m0) j0
      < (k : ℝ) * ((blockSum (orbWord m0) j0 L : ℝ) - alpha * L)) :
    c < R (orbWord m0) (j0 + k * L) := by
  rw [R_periodic (orbWord m0) j0 L hper k]
  linarith

/-- **Explicit upper-wall exit for eventually periodic anchors.** With
`Δ = blockSum − L·log₂3 > 0`, the drift exceeds `c` at step `j0 + (⌈(c − R_{j0})/Δ⌉ + 1)·L`.
@isnad1 id=lt.3h4v.s6.6a357037d1d3 from=translated src=- shape=61ea52ce vocab=eb7937c0
-/
theorem evPeriodic_orbit_exit (m0 j0 L : ℕ) (hm0 : Odd m0) (hL : 1 ≤ L)
    (hper : EvPeriodic (orbWord m0) j0 L) (c : ℝ) :
    c < R (orbWord m0)
      (j0 + (Nat.ceil ((c - R (orbWord m0) j0)
        / ((blockSum (orbWord m0) j0 L : ℝ) - alpha * L)) + 1) * L) := by
  set Δ := (blockSum (orbWord m0) j0 L : ℝ) - alpha * L with hΔ
  have hΔpos : 0 < Δ := cycle_gain_pos m0 j0 L hm0 hL hper
  apply evPeriodic_orbit_exit_at m0 j0 L hper c
  have hceil := Nat.le_ceil ((c - R (orbWord m0) j0) / Δ)
  have h1 : (c - R (orbWord m0) j0) / Δ
      < ((Nat.ceil ((c - R (orbWord m0) j0) / Δ) + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  rwa [div_lt_iff₀ hΔpos] at h1

/-- **Bounded orbits cross every upper wall.**
@isnad1 id=ex.2h3v.s4.d8e26f811c78 from=translated src=- shape=a764384f vocab=754801ee
-/
theorem bounded_orbit_not_upper_confined (M K : ℕ) (hM : Odd M) (hb : ∀ n, orbit M n ≤ K)
    (c : ℝ) : ∃ N, ¬ Confined c (orbWord M) N := by
  obtain ⟨i, j, hne, heq⟩ := bounded_orbit_not_injective M K hb
  exact noninjective_orbit_not_upper_confined c M hM ⟨i, j, hne, heq⟩

/-! ## 4. Anchors reaching 1 -/

/--
@isnad1 id=eq.0h0v.s3.c3618a5f92e8 from=translated src=- shape=3c26ae4f vocab=0b2d2679
-/
theorem a_one : a 1 = 2 := by
  change padicValNat 2 (3 * 1 + 1) = 2
  rw [show 3 * 1 + 1 = 2 ^ 2 by norm_num, padicValNat.prime_pow]

/--
@isnad1 id=eq.0h0v.s3.8d4fb36f49df from=translated src=- shape=3c26ae4f vocab=ddf8ebb1
-/
theorem T_one : T 1 = 1 := by
  unfold T
  rw [a_one]
  norm_num

/--
@isnad1 id=eq.0h1v.s4.9b9c8273ecf2 from=translated src=- shape=fe2c2146 vocab=adf1cd18
-/
theorem orbit_one (t : ℕ) : orbit 1 t = 1 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [orbit_succ, ih, T_one]

/-- After hitting `1`, every valuation is `2`.
@isnad1 id=eq.1h3v.s5.d2732e197cf7 from=translated src=- shape=c1261997 vocab=824c4e35
-/
theorem word_after_one (m0 h : ℕ) (hh : orbit m0 h = 1) (t : ℕ) : orbWord m0 (h + t) = 2 := by
  change a (orbit m0 (h + t)) = 2
  rw [orbit_add, hh, orbit_one, a_one]

/-- After hitting `1` at time `h`, `R_{h+t} = R_h + t·(2 − log₂3)`.
@isnad1 id=eq.1h3v.s6.a7b8e105873d from=translated src=- shape=e484b7cc vocab=09331c6f
-/
theorem R_after_one (m0 h : ℕ) (hh : orbit m0 h = 1) (t : ℕ) :
    R (orbWord m0) (h + t) = R (orbWord m0) h + (t : ℝ) * (2 - alpha) := by
  have hs : ∀ t, s (orbWord m0) (h + t) = s (orbWord m0) h + 2 * t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [← add_assoc, s_succ, ih, word_after_one m0 h hh t]; ring
  unfold R
  rw [hs t]
  push_cast
  ring

/-- At the hitting time of `1`, the drift already satisfies `m_0 ≤ 2^{R_h}`.
@isnad1 id=le.2h2v.s5.f3ef1fb43587 from=translated src=- shape=0188d767 vocab=eaeaecac
-/
theorem two_rpow_R_at_one (m0 h : ℕ) (hm0 : Odd m0) (hh : orbit m0 h = 1) :
    (m0 : ℝ) ≤ (2 : ℝ) ^ R (orbWord m0) h := by
  have := seed_le_orbit_mul_two_rpow_R m0 h hm0
  rwa [hh, Nat.cast_one, one_mul] at this

/-- **Reach-1 upper exit.** If the orbit hits `1` at time `h`, the drift exceeds `c` at every
`h + t` with `t·(2 − log₂3) > c − R_h`; if moreover `2^c < m_0`, already at `h`.
@isnad1 id=and.2h3v.s6.e962441c2a46 from=translated src=- shape=64c233a9 vocab=b33c62bf
-/
theorem reach_one_upper_exit (m0 h : ℕ) (hm0 : Odd m0) (hh : orbit m0 h = 1) (c : ℝ) :
    (∀ t : ℕ, c - R (orbWord m0) h < (t : ℝ) * (2 - alpha) → c < R (orbWord m0) (h + t)) ∧
    ((2 : ℝ) ^ c < (m0 : ℝ) → c < R (orbWord m0) h) := by
  refine ⟨fun t ht => ?_, fun hc => ?_⟩
  · rw [R_after_one m0 h hh t]; linarith
  · have := two_rpow_R_at_one m0 h hm0 hh
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mp (lt_of_lt_of_le hc this)

/-! ## 5. The exceptional class of forever upper-confined anchors -/

/-- The drift of `M` stays at most `U` forever.-/
def UpperConfinedForever (U : ℝ) (M : ℕ) : Prop := ∀ n, R (orbWord M) n ≤ U

/-- **Exceptional-class characterization (conditional form).** Under `LogFloorExclusion Bstar`, a
forever `U`-confined odd seed has an injective, divergent orbit that never descends below
`m_0 · 2^{−U}` and crosses every lower wall `−B log₂ n − K` (`B < Bstar`) infinitely often.
@isnad1 id=and.3h3v.s7.b62907d2cb0f from=translated src=- shape=4f7ef395 vocab=a0aebd46
-/
theorem exceptional_class_of_exclusion {Bstar : ℝ} (hX : LogFloorExclusion Bstar)
    (M : ℕ) (hM : Odd M) (U : ℝ) (hE : UpperConfinedForever U M) :
    (∀ i j, orbit M i = orbit M j → i = j) ∧
    (∀ K, ∃ N₀, ∀ n ≥ N₀, K < orbit M n) ∧
    (∀ n, (M : ℝ) ≤ (2 : ℝ) ^ U * (orbit M n : ℝ)) ∧
    (∀ B < Bstar, ∀ K : ℝ, ∀ N₀ : ℕ, ∃ n ≥ N₀,
      R (orbWord M) n < -B * Real.logb 2 (n : ℝ) - K) := by
  have hinj : ∀ i j, orbit M i = orbit M j → i = j := by
    by_contra h
    push Not at h
    obtain ⟨i, j, heq, hne⟩ := h
    obtain ⟨N, hN⟩ := noninjective_orbit_not_upper_confined U M hM ⟨i, j, hne, heq⟩
    exact hN (fun k _ => hE k)
  refine ⟨hinj, injective_orbit_tendsto M hinj, fun n => ?_, fun B hB K N₀ => ?_⟩
  · have h1 := seed_le_orbit_mul_two_rpow_R M n hM
    have h2 : (2 : ℝ) ^ R (orbWord M) n ≤ (2 : ℝ) ^ U :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (hE n)
    have hm : (0 : ℝ) ≤ (orbit M n : ℝ) := by positivity
    nlinarith
  · have h := hX M hM hinj B hB K
    push Not at h
    obtain ⟨n, hn, hlt⟩ := h N₀
    exact ⟨n, hn, hlt⟩

/-- **Exceptional-class characterization (unconditional, `B < 8/9`).**
@isnad1 id=and.2h2v.s7.50033c803ffd from=translated src=- shape=28008897 vocab=ab4614c6
-/
theorem exceptional_class (M : ℕ) (hM : Odd M) (U : ℝ) (hE : UpperConfinedForever U M) :
    (∀ i j, orbit M i = orbit M j → i = j) ∧
    (∀ K, ∃ N₀, ∀ n ≥ N₀, K < orbit M n) ∧
    (∀ n, (M : ℝ) ≤ (2 : ℝ) ^ U * (orbit M n : ℝ)) ∧
    (∀ B < (8 : ℝ) / 9, ∀ K : ℝ, ∀ N₀ : ℕ, ∃ n ≥ N₀,
      R (orbWord M) n < -B * Real.logb 2 (n : ℝ) - K) :=
  exceptional_class_of_exclusion logFloorExclusion_eight_ninths M hM U hE

/-- **Rebasing an injective orbit at its minimum.** If `orbit M` is injective, then from the time
`n₀` of its global minimum the rebased seed `μ = orbit M n₀` has drift under the upper logarithmic
wall `R_n ≤ (1/9)·log₂ n + 7/(9 ln 2)` for every `n` (unconditional; from the carry budget
`carryE_le`). So a divergent orbit, if one exists, produces a forever upper-log-confined anchor.
@isnad1 id=ex.2h1v.s7.4d4b2d644bcb from=translated src=- shape=d93716a8 vocab=e04f3f0d
-/
theorem rebased_upper_log_wall (M : ℕ) (hM : Odd M)
    (hinj : ∀ i j, orbit M i = orbit M j → i = j) :
    ∃ n₀, ∀ n,
      R (orbWord (orbit M n₀)) n ≤ (1 / 9) * Real.logb 2 (n : ℝ) + 7 / (9 * Real.log 2) := by
  have hne : (Set.range (orbit M)).Nonempty := ⟨_, 0, rfl⟩
  obtain ⟨n₀, hn₀⟩ := Nat.sInf_mem hne
  refine ⟨n₀, fun n => ?_⟩
  have hμ : Odd (orbit M n₀) := odd_orbit hM n₀
  have hmin : orbit M n₀ ≤ orbit (orbit M n₀) n := by
    rw [← orbit_add, hn₀]
    exact Nat.sInf_le ⟨_, rfl⟩
  have hinj' : ∀ i < n, ∀ j < n, orbit (orbit M n₀) i = orbit (orbit M n₀) j → i = j := by
    intro i _ j _ h
    rw [← orbit_add, ← orbit_add] at h
    have := hinj _ _ h
    omega
  have hid := orbit_mul_two_rpow_R (orbit M n₀) n hμ
  rw [carryU_eq_two_rpow_carryE] at hid
  have hE := carryE_le (orbit M n₀) n hμ hinj'
  have hpos : (0 : ℝ) < (orbit (orbit M n₀) n : ℝ) := by exact_mod_cast (odd_orbit hμ n).pos
  have h1 : (orbit (orbit M n₀) n : ℝ) * (2 : ℝ) ^ R (orbWord (orbit M n₀)) n
      ≤ (orbit (orbit M n₀) n : ℝ) * (2 : ℝ) ^ carryE (orbit M n₀) n := by
    rw [hid]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmin) (by positivity)
  have h2 := le_of_mul_le_mul_left h1 hpos
  have hR := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h2
  linarith

/-! ## 6. Upper exit and prescribed matching -/

/-- **Descent bounds prescribed matching.** If the anchor orbit has contracted by more than `2^U`
at step `L` (`2^U · m_L < μ_j`), every prescribed block `e` (length `m ≥ L`) with `R ≤ U` through
`m` has prescribed matching at most `U + L·log₂3`.
@isnad1 id=le.5h6v.s7.41d0f096a8dd from=translated src=- shape=e521d800 vocab=be677071
-/
theorem descent_prescribed_matching_le (d e : ℕ → ℕ) (j m L : ℕ) (U : ℝ) (hLm : L ≤ m)
    (he_pos : ∀ i < m, 1 ≤ e i) (hU : ∀ n ≤ m, R e n ≤ U) (hodd : Odd (anchorState d j))
    (hdesc : (2 : ℝ) ^ U * (orbit (anchorState d j) L : ℝ) < (anchorState d j : ℝ)) :
    ((padicValInt 2 ((leastRealizer e m : ℤ) - anchorState d j) : ℕ) : ℝ)
      ≤ U + (L : ℝ) * alpha := by
  apply matching_le_of_R_ne d e j m L U hLm he_pos hU
  intro heq
  have hup := upper_exit_of_descent (anchorState d j) L hodd U hdesc
  have hle := hU L hLm
  change R e L = R (orbWord (anchorState d j)) L at heq
  linarith

/-- **Reach-1 bound on prescribed matching.** If the anchor orbit hits `1` at step `h ≤ m` and
`2^U < μ_j`, every `U`-confined prescribed block of length `m` has matching at most
`U + h·log₂3`.
@isnad1 id=le.6h6v.s7.7a3ff9a4c255 from=translated src=- shape=5b8a629d vocab=be677071
-/
theorem reach_one_prescribed_matching_le (d e : ℕ → ℕ) (j m h : ℕ) (U : ℝ) (hhm : h ≤ m)
    (he_pos : ∀ i < m, 1 ≤ e i) (hU : ∀ n ≤ m, R e n ≤ U) (hodd : Odd (anchorState d j))
    (hh : orbit (anchorState d j) h = 1) (hbig : (2 : ℝ) ^ U < (anchorState d j : ℝ)) :
    ((padicValInt 2 ((leastRealizer e m : ℤ) - anchorState d j) : ℕ) : ℝ)
      ≤ U + (h : ℝ) * alpha := by
  apply matching_le_of_R_ne d e j m h U hhm he_pos hU
  intro heq
  have hup := (reach_one_upper_exit (anchorState d j) h hodd hh U).2 hbig
  have hle := hU h hhm
  change R e h = R (orbWord (anchorState d j)) h at heq
  linarith

end UpperEscape
end EOC
