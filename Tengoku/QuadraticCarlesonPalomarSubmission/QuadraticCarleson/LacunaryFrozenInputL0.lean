import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.LacunaryMiddleOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The genuine frozen block input belongs to the paper's test domain

Every stopping cell meets the support of the original input and has length
at most the data-dependent root length. Thus all stopping cells lie in one
bounded enlargement of a compact set supporting the original input. Exact
disjointness also gives a pointwise `2 A_k` bound for any frozen scale block,
with no factor depending on its number of scales.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace LacunaryFrozenInputL0

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CalderonZygmundLevelAtoms CanonicalScaleAtoms
open PositiveEndpointOptimization LacunaryMiddleRange LacunaryMiddleOperator

set_option autoImplicit false

/-- A selected cell cannot be disjoint from the actual support of the
original input: otherwise its norm average would be zero.
@isnad1 id=ex.0h2v.s5.9fe05443717d from=translated src=- shape=9477d626 vocab=e9bf8d37
-/
theorem stoppingCell_exists_mem_support {f : ℝ → ℂ} (c : stoppingCell f) :
    ∃ y : ℝ, y ∈ c.1.interval (rootLength f) ∧ f y ≠ 0 := by
  by_contra hn
  push Not at hn
  have hz : (∫ y in c.1.interval (rootLength f), ‖f y‖) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun y hy ↦ by rw [hn y hy, norm_zero]
  have hc := stoppingCell_lower_average c
  rw [DyadicCell.normAverage, dyadicNormAverage_eq rootLength_pos] at hc
  change 1 < (∫ y in c.1.interval (rootLength f), ‖f y‖) /
    dyadicLength (rootLength f) c.1.depth at hc
  rw [hz, zero_div] at hc
  exact (by norm_num : ¬ (1 : ℝ) < 0) hc

/--
@isnad1 id=le.0h2v.s4.f5949d74938a from=translated src=- shape=9f3da328 vocab=549e5d2c
-/
theorem stoppingCell_length_le_rootLength {f : ℝ → ℂ} (c : stoppingCell f) :
    dyadicLength (rootLength f) c.1.depth ≤ rootLength f := by
  unfold dyadicLength
  exact div_le_self rootLength_pos.le (one_le_pow₀ (by norm_num))

/-- A concrete bounded enlargement contains the entire canonical stopping
union, not merely almost every point of it.
@isnad1 id=le.1h2v.s5.7f981d2ce5e1 from=translated src=- shape=9285faae vocab=32863fcd
-/
theorem stoppingBadUnion_subset_Icc_of_support_subset
    {f : ℝ → ℂ} {R : ℝ} (hR : ∀ y, f y ≠ 0 → |y| ≤ R) :
    stoppingBadUnion f ⊆ Icc (-R - rootLength f) (R + rootLength f) := by
  intro x hx
  obtain ⟨c, hc⟩ := mem_iUnion.mp hx
  obtain ⟨y, hy, hfy⟩ := stoppingCell_exists_mem_support c
  have hyR := abs_le.mp (hR y hfy)
  have hlen := stoppingCell_length_le_rootLength c
  change (c.1.index : ℝ) * dyadicLength (rootLength f) c.1.depth ≤ x ∧
    x < ((c.1.index : ℝ) + 1) * dyadicLength (rootLength f) c.1.depth at hc
  change (c.1.index : ℝ) * dyadicLength (rootLength f) c.1.depth ≤ y ∧
    y < ((c.1.index : ℝ) + 1) * dyadicLength (rootLength f) c.1.depth at hy
  constructor <;> nlinarith

/-- Compact support of the original input confines every function supported
in its canonical stopping union to a common compact interval.
@isnad1 id=hascompa.1h2v.s4.20120c64dae3 from=translated src=- shape=6959b811 vocab=4b069cc5
-/
theorem hasCompactSupport_of_support_subset_stoppingBadUnion
    (f : L0Infinity) {g : ℝ → ℂ}
    (hg : Function.support g ⊆ stoppingBadUnion f) : HasCompactSupport g := by
  obtain ⟨R, hR⟩ := f.hasCompactSupport_toFun.isBounded.exists_norm_le
  have hfR : ∀ y, f y ≠ 0 → |y| ≤ R := by
    intro y hy
    simpa only [Real.norm_eq_abs] using hR y (subset_tsupport f hy)
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (hg.trans (stoppingBadUnion_subset_Icc_of_support_subset hfR))

/--
@isnad1 id=le.1h4v.s5.9f5ebcd08392 from=translated src=- shape=d3b74e38 vocab=152a9607
-/
theorem norm_canonicalLevelBadPart_le_two_mul
    {A : ℕ → ℝ} (f : ℝ → ℂ) {k : ℕ} (hAk : 0 ≤ A k) (x : ℝ) :
    ‖canonicalLevelBadPart A f k x‖ ≤ 2 * A k := by
  by_cases hx : x ∈ stoppingBadUnion f
  · obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    rw [canonicalLevelBadPart_eq_atom_of_mem A c hc]
    exact norm_levelAtom_le_two_mul hAk (stoppingLength_pos c) x
  · rw [canonicalLevelBadPart_eq_zero_of_notMem A hx, norm_zero]
    positivity

/-- A finite frozen block either keeps the single active spatial scale or
removes it. This uses the exact canonical disjointness, not a triangle loss.
@isnad1 id=or.0h7v.s5.5d3df66700c3 from=translated src=- shape=a1d9f8df vocab=65e3255c
-/
theorem frozenBlockInput_eq_zero_or_canonicalLevelBadPart
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (τ : ℤ) (x : ℝ) :
    frozenBlockInput A f k B c τ x = 0 ∨
      frozenBlockInput A f k B c τ x = canonicalLevelBadPart A f k x := by
  classical
  obtain ⟨j₀, hj₀⟩ := stoppingScaleLevelBadPart_eq_single_scale A f k x
  unfold frozenBlockInput
  simp_rw [hj₀]
  by_cases hj : j₀ ∈ R B c τ
  · right
    simp [hj]
  · left
    simp [hj]

/--
@isnad1 id=le.1h7v.s5.85826079e1ad from=translated src=- shape=81ad2cdf vocab=fd563503
-/
theorem norm_frozenBlockInput_le_two_mul
    {A : ℕ → ℝ} (f : ℝ → ℂ) {k : ℕ} (hAk : 0 ≤ A k)
    (B c : ℕ) (τ : ℤ) (x : ℝ) :
    ‖frozenBlockInput A f k B c τ x‖ ≤ 2 * A k := by
  rcases frozenBlockInput_eq_zero_or_canonicalLevelBadPart A f k B c τ x with h | h
  · rw [h, norm_zero]
    positivity
  · rw [h]
    exact norm_canonicalLevelBadPart_le_two_mul f hAk x

/--
@isnad1 id=le.0h6v.s5.b535b9bc4853 from=translated src=- shape=630dbded vocab=99cbb3d7
-/
theorem support_frozenBlockInput_subset_stoppingBadUnion
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (τ : ℤ) :
    Function.support (frozenBlockInput A f k B c τ) ⊆ stoppingBadUnion f := by
  intro x hx
  by_contra hnot
  apply hx
  unfold frozenBlockInput
  simp only [stoppingScaleLevelBadPart_eq_zero_of_notMem A hnot, Finset.sum_const_zero]

/--
@isnad1 id=hascompa.0h6v.s4.5640b85d8979 from=translated src=- shape=debfb1b1 vocab=91945781
-/
theorem hasCompactSupport_frozenBlockInput
    (A : ℕ → ℝ) (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    HasCompactSupport (frozenBlockInput A f k B c τ) :=
  hasCompactSupport_of_support_subset_stoppingBadUnion f
    (support_frozenBlockInput_subset_stoppingBadUnion A f k B c τ)

/-- The actual frozen input for the paper's lacunary magnitude amplitudes,
packaged in the domain of the finite-modulation sparse theorem. No condition
on the block size or auxiliary geometric parameter is needed.-/
noncomputable def frozenBlockInputL0
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) : L0Infinity where
  toFun := frozenBlockInput lacunaryAmplitude f k B c τ
  measurable_toFun := measurable_frozenBlockInput f.measurable_toFun k B c τ
  bounded_toFun := ⟨2 * lacunaryAmplitude k,
    norm_frozenBlockInput_le_two_mul f (lacunaryAmplitude_pos k).le B c τ⟩
  hasCompactSupport_toFun := hasCompactSupport_frozenBlockInput lacunaryAmplitude f k B c τ

/--
@isnad1 id=eq.0h6v.s4.c55fe70aea26 from=translated src=- shape=61fc11db vocab=faf26efa
-/
@[simp] theorem frozenBlockInputL0_apply
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) (x : ℝ) :
    frozenBlockInputL0 f k B c τ x = frozenBlockInput lacunaryAmplitude f k B c τ x := rfl

/--
@isnad1 id=eq.0h5v.s4.68bff67d941c from=translated src=- shape=c3821c88 vocab=faf26efa
-/
theorem coe_frozenBlockInputL0
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    (frozenBlockInputL0 f k B c τ : ℝ → ℂ) =
      frozenBlockInput lacunaryAmplitude f k B c τ := rfl

/--
@isnad1 id=measurab.0h5v.s4.951af288010a from=translated src=- shape=1440cc86 vocab=33c553c2
-/
theorem measurable_frozenBlockInputL0
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    Measurable (frozenBlockInputL0 f k B c τ : ℝ → ℂ) :=
  (frozenBlockInputL0 f k B c τ).measurable_toFun

/--
@isnad1 id=integrab.0h5v.s5.7962f33721ba from=translated src=- shape=c688c41c vocab=ae183c86
-/
theorem integrable_frozenBlockInputL0
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    Integrable (frozenBlockInputL0 f k B c τ : ℝ → ℂ) :=
  (frozenBlockInputL0 f k B c τ).integrable

/--
@isnad1 id=le.0h6v.s5.05510e45086b from=translated src=- shape=2187114a vocab=1fde4b60
-/
theorem norm_frozenBlockInputL0_le
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) (x : ℝ) :
    ‖frozenBlockInputL0 f k B c τ x‖ ≤ 2 * lacunaryAmplitude k :=
  norm_frozenBlockInput_le_two_mul f (lacunaryAmplitude_pos k).le B c τ x

/-- The wrapper preserves the exact `L¹` mass used by the block budget.
@isnad1 id=eq.0h5v.s6.d18042523829 from=translated src=- shape=58cc2f16 vocab=0bb0f9d7
-/
theorem lintegral_enorm_frozenBlockInputL0_eq
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    (∫⁻ x, ‖frozenBlockInputL0 f k B c τ x‖ₑ) =
      frozenBlockInputL1Mass lacunaryAmplitude f k B c τ := rfl

/--
@isnad1 id=eq.0h5v.s6.2bc53e2a0724 from=translated src=- shape=1f5b9949 vocab=16a950bc
-/
theorem eLpNorm_one_frozenBlockInputL0_eq
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    eLpNorm (frozenBlockInputL0 f k B c τ : ℝ → ℂ) 1 volume =
      frozenBlockInputL1Mass lacunaryAmplitude f k B c τ := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  exact lintegral_enorm_frozenBlockInputL0_eq f k B c τ

/--
@isnad1 id=eq.0h5v.s5.9975c0b10296 from=translated src=- shape=a90e93ee vocab=21637243
-/
theorem integral_norm_frozenBlockInputL0_eq
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    (∫ x, ‖frozenBlockInputL0 f k B c τ x‖) =
      (frozenBlockInputL1Mass lacunaryAmplitude f k B c τ).toReal := by
  rw [integral_norm_eq_lintegral_enorm
    (frozenBlockInputL0 f k B c τ).measurable_toFun.aestronglyMeasurable]
  rfl

/--
@isnad1 id=eq.0h5v.s5.0e2e2be24860 from=translated src=- shape=2266049e vocab=419a1e06
-/
theorem ofReal_integral_norm_frozenBlockInputL0_eq
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    ENNReal.ofReal (∫ x, ‖frozenBlockInputL0 f k B c τ x‖) =
      frozenBlockInputL1Mass lacunaryAmplitude f k B c τ :=
  ofReal_integral_norm_eq_lintegral_enorm (frozenBlockInputL0 f k B c τ).integrable

/--
@isnad1 id=lt.0h5v.s4.e6045d2d74b2 from=translated src=- shape=ac76abe2 vocab=83a6021f
-/
theorem frozenBlockInputL1Mass_lt_top
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) :
    frozenBlockInputL1Mass lacunaryAmplitude f k B c τ < ∞ :=
  (frozenBlockInputL0 f k B c τ).integrable.hasFiniteIntegral

/-- The finite maximally truncated operator used in the sparse application
acts on exactly this wrapper, with pointwise equality and no a.e. transport.
@isnad1 id=eq.0h6v.s5.f2362d251e16 from=translated src=- shape=a23daf67 vocab=e45ff0f5
-/
theorem frozenBlockHilbertMaxEnorm_eq_wrapper
    (f : L0Infinity) (k B c : ℕ) (τ : ℤ) (x : ℝ) :
    frozenBlockHilbertMaxEnorm lacunaryAmplitude f k B c τ x =
      (Q B τ).sup fun m ↦ quadraticHilbertMaximalTruncation (dyadicModulation m)
        (frozenBlockInputL0 f k B c τ) x := rfl

end LacunaryFrozenInputL0
end QuadraticCarleson
