import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Interval
import Tengoku.Seed.Analysis.Asymptotics.SpecificAsymptotics
import Tengoku.Seed.Analysis.Complex.ExponentialBounds
import Tengoku.Seed.Analysis.Fourier.FourierTransform
import Tengoku.Seed.Analysis.Fourier.ZMod
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Tengoku.Seed.Analysis.InnerProductSpace.l2Space
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.CircleAddChar
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Summable
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Bounds
import Tengoku.Seed.Data.ZMod.ValMinAbs
import Tengoku.Seed.FieldTheory.Finite.Extension
import Tengoku.Seed.FieldTheory.Finite.GaloisField
import Tengoku.Seed.FieldTheory.Finite.Trace
import Tengoku.Seed.LinearAlgebra.Lagrange
import Tengoku.Seed.MeasureTheory.Integral.Gamma
import Tengoku.Seed.MeasureTheory.Function.L2Space
import Tengoku.Seed.MeasureTheory.Measure.SeparableMeasure
import Tengoku.Seed.MeasureTheory.Group.Convolution
import Tengoku.Seed.NumberTheory.LegendreSymbol.AddCharacter
import Tengoku.Seed.NumberTheory.Harmonic.Bounds
import Tengoku.Seed.Probability.ProductMeasure
import Tengoku.Seed.Probability.Independence.InfinitePi
import Tengoku.Seed.Probability.Independence.CharacteristicFunction
import Tengoku.Seed.RingTheory.Polynomial.DegreeLT
import Tengoku.Seed.RingTheory.PowerSeries.Derivative
import Tengoku.Seed.RingTheory.PowerSeries.Expand
import Tengoku.Seed.Topology.MetricSpace.HausdorffDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Homogeneous Moran sets and measures

This file defines homogeneous Moran sets, their associated probability measures,
and digit mask functions. It proves their Fourier product formula and constructs
spectral Moran measures with prescribed Fourier and Hausdorff dimensions.
The construction uses linear block lengths, finite-field power digits, and the
least odd primes satisfying the scale and logarithmic cost bounds.
A sharp degree-dependent bound for additive character sums supplies the mask estimates.
The Fourier decay, Salem property, and explicit spectrum are established for
this same construction.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators BoundedContinuousFunction ENNReal Topology

namespace Moran

/-- Bases and nonempty digit sets for a homogeneous Moran construction, indexed from zero.-/
structure Data where
  /-- The integer base at each level.-/
  base : ℕ → ℕ
  /-- The base at each level is at least two.-/
  two_le_base : ∀ n, 2 ≤ base n
  /-- The finite digit set at each level.-/
  digits : ℕ → Finset ℕ
  /-- Every digit set is nonempty.-/
  digits_nonempty : ∀ n, (digits n).Nonempty
  /-- Every digit is strictly smaller than its base.-/
  digit_lt_base : ∀ n d, d ∈ digits n → d < base n

namespace Data

variable (A : Data)

/-- The product of the bases through level `n`, including level zero.-/
def scale (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.range (n + 1), A.base k

/-- The real number encoded by a sequence of digits.-/
def coding (d : ℕ → ℕ) : ℝ :=
  ∑' n, (d n : ℝ) / (A.scale n : ℝ)

/-- The homogeneous Moran set consisting of all admissible digit expansions.-/
def carrier : Set ℝ :=
  {x | ∃ d : ℕ → ℕ, (∀ n, d n ∈ A.digits n) ∧ A.coding d = x}

private lemma two_pow_mul_base_le_scale (n : ℕ) :
    2 ^ n * A.base n ≤ A.scale n := by
  simpa [scale, Finset.prod_range_succ] using
    Nat.mul_le_mul_right (A.base n)
      (Finset.prod_le_prod (s := Finset.range n) (f := fun _ ↦ 2) (g := A.base)
        (fun _ _ ↦ Nat.zero_le 2) (fun k _ ↦ A.two_le_base k))

private lemma coding_term_le (n d : ℕ) (hd : d ∈ A.digits n) :
    (d : ℝ) / (A.scale n : ℝ) ≤ (1 / 2 : ℝ) ^ n := by
  have hb : (0 : ℝ) < A.base n := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide)
    (A.two_le_base n))
  have hs : (2 : ℝ) ^ n * A.base n ≤ A.scale n := by
    exact_mod_cast A.two_pow_mul_base_le_scale n
  have hd' : (d : ℝ) ≤ A.base n := Nat.cast_le.mpr (A.digit_lt_base n d hd).le
  calc
    (d : ℝ) / (A.scale n : ℝ) ≤ (A.base n : ℝ) / (2 ^ n * A.base n) :=
      div_le_div₀ hb.le hd' (mul_pos (pow_pos (by norm_num) n) hb) hs
    _ = (1 / 2 : ℝ) ^ n := by
      field_simp
      simp

/-- Every admissible digit expansion is summable.-/
theorem summable_coding (d : ℕ → ℕ) (hd : ∀ n, d n ∈ A.digits n) :
    Summable (fun n ↦ (d n : ℝ) / (A.scale n : ℝ)) := by
  exact Summable.of_nonneg_of_le (fun n ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun n ↦ A.coding_term_le n (d n) (hd n))
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1))

private lemma prefix_product_pos (n : ℕ) : 0 < ∏ j ∈ Finset.range n, A.base j := by
  exact Finset.prod_pos (fun j _ ↦ lt_of_lt_of_le Nat.zero_lt_two (A.two_le_base j))

private lemma continuousOn_coding :
    ContinuousOn A.coding {d | ∀ n, d n ∈ A.digits n} := by
  refine continuousOn_tsum (fun n ↦ ?_)
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)) ?_
  · exact ((continuous_of_discreteTopology : Continuous (fun k : ℕ ↦ (k : ℝ))).comp
      (continuous_apply n)).div_const _ |>.continuousOn
  · intro n x hx
    simpa only [norm_div, Real.norm_natCast] using A.coding_term_le n (x n) (hx n)

/-- The homogeneous Moran set is nonempty and compact.-/
theorem nonempty_isCompact_carrier :
    A.carrier.Nonempty ∧ IsCompact A.carrier := by
  change (A.coding '' {d | ∀ n, d n ∈ A.digits n}).Nonempty ∧
    IsCompact (A.coding '' {d | ∀ n, d n ∈ A.digits n})
  constructor
  · exact Set.Nonempty.image A.coding
      ⟨fun n ↦ (A.digits_nonempty n).choose, fun n ↦ (A.digits_nonempty n).choose_spec⟩
  · exact (isCompact_pi_infinite
      (fun n ↦ (A.digits n).finite_toSet.isCompact)).image_of_continuousOn A.continuousOn_coding

/-- The uniform probability distribution on the digits at level `n`.-/
def digitLaw (n : ℕ) : Measure ℕ :=
  ((A.digits n).card : ℝ≥0∞)⁻¹ •
    ∑ d ∈ A.digits n, Measure.dirac d

/-- The atomic distribution of the scaled digit at level `n`.-/
def factor (n : ℕ) : Measure ℝ :=
  ((A.digits n).card : ℝ≥0∞)⁻¹ •
    ∑ d ∈ A.digits n, Measure.dirac ((d : ℝ) / (A.scale n : ℝ))

/-- The convolution of the first `n` scaled digit distributions.-/
def partialConvolution (A : Data) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => (partialConvolution A n).conv (A.factor n)

/-- The Cantor–Moran measure is the distribution of the independent digit series.-/
def measure : Measure ℝ :=
  Measure.map A.coding (Measure.infinitePi A.digitLaw)

private lemma isProbabilityMeasure_digitLaw (n : ℕ) :
    IsProbabilityMeasure (A.digitLaw n) := by
  refine ⟨?_⟩
  simp [digitLaw, ENNReal.inv_mul_cancel,
    Nat.ne_of_gt (A.digits_nonempty n).card_pos]

private lemma ae_mem_digits (n : ℕ) : ∀ᵐ d ∂A.digitLaw n, d ∈ A.digits n := by
  simp [ae_iff, digitLaw]

private lemma ae_all_mem_digits :
    ∀ᵐ d ∂Measure.infinitePi A.digitLaw, ∀ n, d n ∈ A.digits n := by
  letI (n : ℕ) : IsProbabilityMeasure (A.digitLaw n) := A.isProbabilityMeasure_digitLaw n
  refine ae_all_iff.mpr (fun n ↦ ?_)
  exact ae_of_ae_map (measurable_pi_apply n).aemeasurable
    ((Measure.infinitePi_map_eval A.digitLaw n).symm ▸ A.ae_mem_digits n)

private lemma measurable_coding : Measurable A.coding := by
  exact Measurable.tsum (fun n ↦
    ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
      (measurable_pi_apply n)).div_const (A.scale n : ℝ))

/-- The Cantor–Moran measure is a probability measure.-/
instance instIsProbabilityMeasure : IsProbabilityMeasure A.measure := by
  letI (n : ℕ) : IsProbabilityMeasure (A.digitLaw n) := A.isProbabilityMeasure_digitLaw n
  exact Measure.isProbabilityMeasure_map A.measurable_coding.aemeasurable

/-- The Cantor–Moran measure is concentrated on its homogeneous Moran set.-/
theorem measure_compl_carrier :
    A.measure A.carrierᶜ = 0 := by
  rw [measure, Measure.map_apply A.measurable_coding
    A.nonempty_isCompact_carrier.2.measurableSet.compl]
  exact ae_iff.mp (A.ae_all_mem_digits.mono (fun d hd ↦ ⟨d, hd, rfl⟩))

private lemma measurable_coding_term (n : ℕ) :
    Measurable (fun d : ℕ → ℕ ↦ (d n : ℝ) / (A.scale n : ℝ)) := by
  exact ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
    (measurable_pi_apply n)).div_const _

private lemma map_digitLaw (n : ℕ) :
    (A.digitLaw n).map (fun d : ℕ ↦ (d : ℝ) / (A.scale n : ℝ)) = A.factor n := by
  simp [digitLaw, factor, Measure.map_smul,
    Measure.map_finset_sum (measurable_of_countable _).aemeasurable]

private lemma map_coding_term (n : ℕ) :
    (Measure.infinitePi A.digitLaw).map
      (fun d : ℕ → ℕ ↦ (d n : ℝ) / (A.scale n : ℝ)) = A.factor n := by
  letI (n : ℕ) : IsProbabilityMeasure (A.digitLaw n) := A.isProbabilityMeasure_digitLaw n
  change (Measure.infinitePi A.digitLaw).map
    ((fun d : ℕ ↦ (d : ℝ) / (A.scale n : ℝ)) ∘ (fun d : ℕ → ℕ ↦ d n)) = _
  rw [← Measure.map_map (μ := Measure.infinitePi A.digitLaw)
    (f := fun d : ℕ → ℕ ↦ d n) (g := fun d : ℕ ↦ (d : ℝ) / (A.scale n : ℝ))
    (measurable_of_countable _) (measurable_pi_apply n),
    Measure.infinitePi_map_eval, A.map_digitLaw]

private lemma indep_coding_terms :
    ProbabilityTheory.iIndepFun
      (fun n (d : ℕ → ℕ) ↦ (d n : ℝ) / (A.scale n : ℝ))
      (Measure.infinitePi A.digitLaw) := by
  letI (n : ℕ) : IsProbabilityMeasure (A.digitLaw n) := A.isProbabilityMeasure_digitLaw n
  exact ProbabilityTheory.iIndepFun_infinitePi (fun n ↦
    measurable_of_countable (fun d : ℕ ↦ (d : ℝ) / (A.scale n : ℝ)))

private lemma measurable_partial_coding (n : ℕ) :
    Measurable
      (fun d : ℕ → ℕ ↦ ∑ k ∈ Finset.range n, (d k : ℝ) / (A.scale k : ℝ)) := by
  exact Finset.measurable_sum _ (fun k _ ↦ A.measurable_coding_term k)

private lemma map_partial_coding (n : ℕ) :
    (Measure.infinitePi A.digitLaw).map
      (fun d : ℕ → ℕ ↦ ∑ k ∈ Finset.range n, (d k : ℝ) / (A.scale k : ℝ)) =
      A.partialConvolution n := by
  letI (n : ℕ) : IsProbabilityMeasure (A.digitLaw n) := A.isProbabilityMeasure_digitLaw n
  induction n with
  | zero => simp [partialConvolution, Measure.map_const]
  | succ n ih =>
    have hi := A.indep_coding_terms.indepFun_finsetSum_of_notMem
      A.measurable_coding_term (Finset.notMem_range_self (n := n))
    simp only [Finset.sum_fn] at hi
    simpa only [Finset.sum_range_succ, partialConvolution, Pi.add_def, ih, A.map_coding_term]
      using hi.map_add_eq_map_conv_map
        (A.measurable_partial_coding n) (A.measurable_coding_term n)

private lemma tendsto_integral_finset_coding {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ →ᵇ E) :
    Tendsto (fun s : Finset ℕ ↦ ∫ d, f (∑ k ∈ s, (d k : ℝ) / (A.scale k : ℝ))
      ∂Measure.infinitePi A.digitLaw)
      atTop (𝓝 (∫ d, f (A.coding d) ∂Measure.infinitePi A.digitLaw)) := by
  letI (n : ℕ) : IsProbabilityMeasure (A.digitLaw n) := A.isProbabilityMeasure_digitLaw n
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖f‖) ?_ ?_
    (integrable_const _) ?_
  · exact Filter.Eventually.of_forall (fun s ↦ (f.continuous.stronglyMeasurable.comp_measurable
      (Finset.measurable_sum s (fun k _ ↦ A.measurable_coding_term k))).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun _ ↦
      Filter.Eventually.of_forall (fun _ ↦ f.norm_coe_le_norm _))
  · exact A.ae_all_mem_digits.mono (fun d hd ↦
      f.continuous.continuousAt.tendsto.comp (A.summable_coding d hd).hasSum)

private lemma tendsto_integral_partial_coding {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ →ᵇ E) :
    Tendsto (fun n ↦ ∫ d, f (∑ k ∈ Finset.range n, (d k : ℝ) / (A.scale k : ℝ))
      ∂Measure.infinitePi A.digitLaw)
      atTop (𝓝 (∫ d, f (A.coding d) ∂Measure.infinitePi A.digitLaw)) := by
  exact (A.tendsto_integral_finset_coding f).comp tendsto_finset_range

private lemma tendsto_integral_partialConvolution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ →ᵇ E) :
    Tendsto (fun n ↦ ∫ x, f x ∂A.partialConvolution n)
      atTop (𝓝 (∫ x, f x ∂A.measure)) := by
  simpa only [← A.map_partial_coding, measure,
    integral_map_of_stronglyMeasurable (A.measurable_partial_coding _)
      f.continuous.stronglyMeasurable,
    integral_map_of_stronglyMeasurable A.measurable_coding f.continuous.stronglyMeasurable]
    using A.tendsto_integral_partial_coding f

/-- Finite digit convolutions converge weakly to the Cantor–Moran measure.-/
theorem tendsto_partialConvolution (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ x, f x ∂(A.partialConvolution n))
      atTop (𝓝 (∫ x, f x ∂A.measure)) := by
  exact A.tendsto_integral_partialConvolution f

end Data

private lemma finite_fourier_orthogonality {F : Type*} [CommRing F] [Fintype F]
    [DecidableEq F] (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (k l : F) :
    ∑ x : F, ψ (x * (k - l)) = if k = l then Fintype.card F else 0 := by
  rw [AddChar.sum_mulShift (k - l) hψ]
  simp only [sub_eq_zero]

private def fieldResidueEquiv {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F) :
    F ≃ Fin (p ^ r) :=
  b.equivFun.toEquiv.trans
    ((Equiv.piCongrRight fun _ ↦ (ZMod.finEquiv p).toEquiv.symm).trans
      finFunctionFinEquiv)

private def powerCoordinateBlock {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F)
    (hr : 0 < r) (m : ℕ) (x : F) : Fin (p ^ m) :=
  finFunctionFinEquiv fun j : Fin m ↦
    (ZMod.finEquiv p).symm
      (b.equivFun (x ^ (j.val / r + 2)) ⟨j.val % r, Nat.mod_lt _ hr⟩)

private def powerDigit {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F)
    (hr : 0 < r) (m : ℕ) (x : F) : ℕ :=
  (fieldResidueEquiv b x).val + p ^ r * (powerCoordinateBlock b hr m x).val

private lemma powerDigit_lt {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F)
    (hr : 0 < r) (m : ℕ) (x : F) : powerDigit b hr m x < p ^ (r + m) := by
  simpa only [powerDigit, pow_add] using
    (Nat.add_lt_add_right (fieldResidueEquiv b x).isLt
      (p ^ r * (powerCoordinateBlock b hr m x).val)).trans_le
      (by simpa only [Nat.mul_succ, add_comm] using
        Nat.mul_le_mul_left (p ^ r) (powerCoordinateBlock b hr m x).isLt)

private lemma powerDigit_mod {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F)
    (hr : 0 < r) (m : ℕ) (x : F) :
    powerDigit b hr m x % p ^ r = (fieldResidueEquiv b x).val := by
  simp [powerDigit, Nat.mod_eq_of_lt (fieldResidueEquiv b x).isLt]

private lemma powerDigit_injective {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F)
    (hr : 0 < r) (m : ℕ) : Function.Injective (powerDigit b hr m) := by
  exact fun x y h ↦ (fieldResidueEquiv b).injective (Fin.ext
    (by simpa only [powerDigit_mod] using congrArg (· % p ^ r) h))

private def powerDigitSet {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (m : ℕ) : Finset ℕ :=
  Finset.univ.image (powerDigit b hr m)

private lemma card_powerDigitSet {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (m : ℕ) :
    (powerDigitSet b hr m).card = p ^ r := by
  simpa only [powerDigitSet, Finset.card_image_of_injective _
    (powerDigit_injective b hr m), Finset.card_univ, Fintype.card_fin] using
      Fintype.card_congr (fieldResidueEquiv b)

private lemma powerDigitSet_nonempty {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (m : ℕ) :
    (powerDigitSet b hr m).Nonempty :=
  Finset.univ_nonempty.image (powerDigit b hr m)

private lemma mem_powerDigitSet_lt {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (m : ℕ)
    {d : ℕ} (hd : d ∈ powerDigitSet b hr m) : d < p ^ (r + m) := by
  exact (Finset.mem_image.mp hd).elim fun x hx ↦ hx.2 ▸ powerDigit_lt b hr m x

private lemma natCast_finEquiv {n : ℕ} [NeZero n] (i : Fin n) :
    (i.val : ZMod n) = ZMod.finEquiv n i := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact ZMod.natCast_zmod_val (n := n + 1) i

private def fieldCyclicEquiv {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F) :
    F ≃ ZMod (p ^ r) :=
  (fieldResidueEquiv b).trans (ZMod.finEquiv (p ^ r)).toEquiv

private lemma powerDigit_cast {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Algebra (ZMod p) F] (b : Module.Basis (Fin r) (ZMod p) F)
    (hr : 0 < r) (m : ℕ) (x : F) :
    (powerDigit b hr m x : ZMod (p ^ r)) = fieldCyclicEquiv b x := by
  simpa only [ZMod.natCast_mod, natCast_finEquiv, fieldCyclicEquiv,
    Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe] using
      congrArg (fun n : ℕ ↦ (n : ZMod (p ^ r))) (powerDigit_mod b hr m x)

private lemma powerDigit_orthogonality {p r : ℕ} [NeZero p] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (m : ℕ)
    (k l : ZMod (p ^ r)) :
    ∑ x : F, ZMod.stdAddChar ((powerDigit b hr m x : ZMod (p ^ r)) * (k - l)) =
      if k = l then (p ^ r : ℕ) else 0 := by
  simpa only [powerDigit_cast] using
    ((fieldCyclicEquiv b).sum_comp (fun x ↦ ZMod.stdAddChar (x * (k - l)))).trans
      (by
        simpa only [ZMod.card] using finite_fourier_orthogonality
          ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar (p ^ r)) k l)

private def powerFrequency (p r m : ℕ) (k : ZMod (p ^ r)) : ℤ :=
  (p ^ m : ℕ) * k.valMinAbs

private def powerPhasePolynomial {p r q : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r) (a : Fin q → ZMod p) :
    Polynomial F :=
  ∑ j, Polynomial.monomial (j.val / r + 1)
    (a j • b.traceDual ⟨j.val % r, Nat.mod_lt _ hr⟩)

private def logarithmicSeries {F : Type*} [Field F] (g : PowerSeries F) :
    PowerSeries F :=
  PowerSeries.derivative F g * g⁻¹

private def rootPowerSum {F : Type*} [Field F] (g : Polynomial F) : ℕ → F
  | 0 => g.natDegree
  | n + 1 => -PowerSeries.coeff n (logarithmicSeries (g.reverse : PowerSeries F))

private def polynomialRootPhase {F : Type*} [Field F] (f g : Polynomial F) : F :=
  ∑ n ∈ Finset.range (f.natDegree + 1), f.coeff n * rootPowerSum g n

private lemma monic_add_monomial_of_lt {F : Type*} [Field F]
    (g : Polynomial F) (hg : g.Monic) {j : ℕ} (hj : j < g.natDegree) (t : F) :
    (g + Polynomial.monomial j t).Monic ∧
      (g + Polynomial.monomial j t).natDegree = g.natDegree := by
  have hlt := (Polynomial.natDegree_monomial_le t).trans_lt hj
  exact ⟨hg.add_of_left (Polynomial.degree_lt_degree hlt),
    Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt⟩

private def monicCoefficientShift {F : Type*} [Field F] {n j : ℕ}
    (hj : j < n) (t : F) :
    {g : Polynomial F // g.Monic ∧ g.natDegree = n} ≃
      {g : Polynomial F // g.Monic ∧ g.natDegree = n} where
  toFun g := ⟨(g : Polynomial F) + Polynomial.monomial j t, by
    have h := monic_add_monomial_of_lt (g : Polynomial F) g.property.1
      (hj.trans_eq g.property.2.symm) t
    exact ⟨h.1, h.2.trans g.property.2⟩⟩
  invFun g := ⟨(g : Polynomial F) + Polynomial.monomial j (-t), by
    have h := monic_add_monomial_of_lt (g : Polynomial F) g.property.1
      (hj.trans_eq g.property.2.symm) (-t)
    exact ⟨h.1, h.2.trans g.property.2⟩⟩
  left_inv g := by
    apply Subtype.ext
    simp
  right_inv g := by
    apply Subtype.ext
    simp

private instance monicFixedDegreeFintype (F : Type*) [Field F] [Fintype F] (n : ℕ) :
    Fintype {g : Polynomial F // g.Monic ∧ g.natDegree = n} :=
  Fintype.ofEquiv (Fin n → F)
    ((Polynomial.monicEquivDegreeLT (R := F) n).trans
      (Polynomial.degreeLTEquiv F n).toEquiv).symm

private def additiveLPolynomial {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (f : Polynomial F) : Polynomial ℂ :=
  ∑ n ∈ Finset.range f.natDegree, Polynomial.monomial n
    (∑ g : {g : Polynomial F // g.Monic ∧ g.natDegree = n},
      ψ (polynomialRootPhase f g))

private def fieldEquivMonicLinear (F : Type*) [Field F] :
    F ≃ {g : Polynomial F // g.Monic ∧ g.natDegree = 1} where
  toFun x := ⟨Polynomial.X - Polynomial.C x, Polynomial.monic_X_sub_C x, by simp⟩
  invFun g := -(g : Polynomial F).coeff 0
  left_inv x := by simp
  right_inv g := by
    apply Subtype.ext
    simpa only [Polynomial.C_neg, sub_neg_eq_add] using
      (g.property.1.eq_X_add_C g.property.2).symm

private def monicIrreduciblesUpTo (F : Type*) [Field F] [Fintype F] (n : ℕ) :
    Finset (Polynomial F) := by
  classical
  exact ((Finset.range (n + 1)).biUnion fun k ↦
    (Finset.univ : Finset {g : Polynomial F // g.Monic ∧ g.natDegree = k}).image
      Subtype.val).filter Irreducible

private def monicMulEmbedding {F : Type*} [Field F] (p : Polynomial F) (hp : p.Monic)
    (n : ℕ) :
    {g : Polynomial F // g.Monic ∧ g.natDegree = n} ↪
      {g : Polynomial F // g.Monic ∧ g.natDegree = p.natDegree + n} where
  toFun g := ⟨p * g, hp.mul g.property.1, by
    rw [Polynomial.natDegree_mul hp.ne_zero g.property.1.ne_zero, g.property.2]⟩
  inj' := by
    intro g h heq
    exact Subtype.ext (mul_left_cancel₀ hp.ne_zero (congrArg Subtype.val heq))

private def sievedMonicWeight {F : Type*} [Field F]
    (w : Polynomial F → ℂ) (s : Finset (Polynomial F)) (g : Polynomial F) : ℂ := by
  classical
  exact if ∀ p ∈ s, ¬p ∣ g then w g else 0

private def sievedMonicSeries {F : Type*} [Field F] [Fintype F]
    (w : Polynomial F → ℂ) (s : Finset (Polynomial F)) : PowerSeries ℂ :=
  PowerSeries.mk fun n ↦
    ∑ g : {g : Polynomial F // g.Monic ∧ g.natDegree = n}, sievedMonicWeight w s g

private def linearPhaseIndices (p r q : ℕ) : Set (Fin q → ZMod p) :=
  {a | ∀ j, r ≤ j.val → a j = 0}

private def finiteFrequency (A : Data) (L : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, (∏ j ∈ Finset.range k, A.base j : ℕ) * L k

private def powerMoranData (p r m : ℕ → ℕ) [∀ n, NeZero (p n)] (F : ℕ → Type*)
    [∀ n, Field (F n)] [∀ n, Fintype (F n)] [∀ n, Algebra (ZMod (p n)) (F n)]
    (b : ∀ n, Module.Basis (Fin (r n)) (ZMod (p n)) (F n))
    (hp : ∀ n, 2 ≤ p n) (hr : ∀ n, 0 < r n) : Data where
  base n := p n ^ (r n + m n)
  two_le_base n := (hp n).trans (Nat.le_pow (Nat.add_pos_left (hr n) _))
  digits n := powerDigitSet (b n) (hr n) (m n)
  digits_nonempty n := powerDigitSet_nonempty (b n) (hr n) (m n)
  digit_lt_base n _ hd := mem_powerDigitSet_lt (b n) (hr n) (m n) hd

private def galoisPowerBasis (p r : ℕ) [Fact p.Prime] (hr : 0 < r) :
    Module.Basis (Fin r) (ZMod p) (GaloisField p r) :=
  let b := Field.powerBasisOfFiniteOfSeparable (ZMod p) (GaloisField p r)
  b.basis.reindex (finCongr (b.finrank.symm.trans (GaloisField.finrank p hr.ne')))

private def galoisPowerMoranData (p r m : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hr : ∀ n, 0 < r n) : Data :=
  letI : ∀ n, Fintype (GaloisField (p n) (r n)) := fun _ ↦ Fintype.ofFinite _
  powerMoranData p r m (fun n ↦ GaloisField (p n) (r n))
    (fun n ↦ galoisPowerBasis (p n) (r n) (hr n))
    (fun n ↦ (Fact.out : (p n).Prime).two_le) hr

private lemma galoisPowerMoranData_card_digits (p r m : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hr : ∀ n, 0 < r n) (n : ℕ) :
    ((galoisPowerMoranData p r m hr).digits n).card = p n ^ r n := by
  simp only [galoisPowerMoranData, powerMoranData, card_powerDigitSet]

/-- The normalized trigonometric mask of a finite digit set.-/
def mask (B : Finset ℕ) (ξ : ℝ) : ℂ :=
  (B.card : ℂ)⁻¹ *
    ∑ d ∈ B, Complex.exp
      ((-2 * Real.pi * (d : ℝ) * ξ : ℝ) * Complex.I)

private def multisetMask (B : Multiset ℕ) (ξ : ℝ) : ℂ :=
  (B.card : ℂ)⁻¹ * (B.map fun d : ℕ ↦
    Complex.exp ((-2 * Real.pi * (d : ℝ) * ξ : ℝ) * Complex.I)).sum

private def digitPhase {p : ℕ} [NeZero p] (θ : ℝ) (z : ZMod p) : ℂ :=
  Complex.exp ((-2 * Real.pi * θ * ((ZMod.finEquiv p).symm z).val : ℝ) * Complex.I)

private def centeredGridIndex (p : ℕ) (θ : ℝ) (a : Fin p) : ℤ :=
  a.val - p * round (θ + (a.val : ℝ) / p) + round (p * θ)

private def gridWeight (k : ℤ) : ℝ :=
  if k.natAbs ≤ 1 then 1 else (2 * (k.natAbs - 1 : ℕ) : ℝ)⁻¹

/-- The Fourier integral of the constant one function is the measure Fourier transform.-/
theorem fourierIntegral_one_eq (μ : Measure ℝ) (ξ : ℝ) :
    Fourier.fourierIntegral Real.fourierChar μ (fun _ ↦ (1 : ℂ)) ξ =
      ∫ x : ℝ, Complex.exp
        ((-2 * Real.pi * ξ * x : ℝ) * Complex.I) ∂μ := by
  simp only [Fourier.fourierIntegral, Real.vector_fourierIntegral_eq_integral_exp_smul,
    LinearMap.mul_apply', smul_eq_mul, one_mul, mul_comm, mul_left_comm, mul_assoc]

private lemma charFun_factor (A : Data) (n : ℕ) (ξ : ℝ) :
    charFun (A.factor n) (-2 * Real.pi * ξ) =
      mask (A.digits n) (ξ / (A.scale n : ℝ)) := by
  simp [charFun_apply_real, Data.factor, mask, integral_smul_measure,
    integral_finsetSum_measure, integrable_dirac, ← Complex.exp_conj,
    div_eq_mul_inv, map_ofNat, mul_comm, mul_left_comm, mul_assoc]

private lemma integral_char_finset_coding (A : Data) (s : Finset ℕ) (t : ℝ) :
    (∫ d, BoundedContinuousFunction.innerProbChar t
      (∑ k ∈ s, (d k : ℝ) / (A.scale k : ℝ)) ∂Measure.infinitePi A.digitLaw) =
      ∏ k ∈ s, charFun (A.factor k) t := by
  have h := congrFun ((A.indep_coding_terms.restrict s).charFun_map_fun_finsetSum_eq_prod
    (fun k _ ↦ (A.measurable_coding_term k).aemeasurable)) t
  simpa only [A.map_coding_term, Finset.prod_apply, charFun_eq_integral_innerProbChar,
    integral_map_of_stronglyMeasurable
      (Finset.measurable_sum s (fun k _ ↦ A.measurable_coding_term k))
      (BoundedContinuousFunction.innerProbChar t).continuous.stronglyMeasurable] using h

private lemma hasProd_charFun_factor (A : Data) (t : ℝ) :
    HasProd (fun n ↦ charFun (A.factor n) t) (charFun A.measure t) := by
  have h := A.tendsto_integral_finset_coding (BoundedContinuousFunction.innerProbChar t)
  simpa only [HasProd, SummationFilter.unconditional_filter,
    integral_char_finset_coding, charFun_eq_integral_innerProbChar,
    Data.measure, integral_map_of_stronglyMeasurable A.measurable_coding
      (BoundedContinuousFunction.innerProbChar t).continuous.stronglyMeasurable] using h

/-- The Fourier transform of a Cantor–Moran measure is the convergent product of its masks.-/
theorem Data.hasProd_mask (A : Data) (ξ : ℝ) :
    HasProd (fun n ↦ mask (A.digits n) (ξ / (A.scale n : ℝ)))
      (Fourier.fourierIntegral Real.fourierChar A.measure
        (fun _ ↦ (1 : ℂ)) ξ) := by
  have h := hasProd_charFun_factor A (-2 * Real.pi * ξ)
  simp only [charFun_factor] at h
  simpa only [fourierIntegral_one_eq, charFun_apply_real, Complex.ofReal_mul] using h

private def tailData (A : Data) (n : ℕ) : Data where
  base k := A.base (n + k)
  two_le_base k := A.two_le_base (n + k)
  digits k := A.digits (n + k)
  digits_nonempty k := A.digits_nonempty (n + k)
  digit_lt_base k := A.digit_lt_base (n + k)

private def prefixInterval (A : Data) (n : ℕ) (d : ∀ j : Fin n, A.digits j) : Set ℝ :=
  let a := ∑ j : Fin n, ((d j : ℕ) : ℝ) / A.scale j
  Set.Icc a (a + ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ)⁻¹)

private lemma eventually_mul_log_pow_le_rpow (C : ℝ) (q : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ q ≤ x ^ δ := by
  filter_upwards [((isLittleO_log_rpow_rpow_atTop (q : ℝ) hδ).const_mul_left C).bound
    zero_lt_one, eventually_ge_atTop (0 : ℝ)] with x hx hx₀
  simp only [Real.rpow_natCast, one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx₀ δ)] at hx
  exact (le_abs_self _).trans hx

private lemma eventually_mul_mask_log_pow_le_rpow {C : ℝ} (hC : 0 ≤ C) (q : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, C * (2 * Real.log (2 * x)) ^ q ≤ x ^ δ := by
  filter_upwards [eventually_mul_log_pow_le_rpow (C * 4 ^ q) q hδ,
    eventually_ge_atTop (2 : ℝ)] with x hx hx₂
  have hlog : 2 * Real.log (2 * x) ≤ 4 * Real.log x := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    linarith [Real.log_le_log (by norm_num) hx₂]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))) hlog q) hC).trans
    (by simpa only [mul_pow, mul_assoc] using hx)

private lemma mask_add_int (B : Finset ℕ) (ξ : ℝ) (z : ℤ) :
    mask B (ξ + z) = mask B ξ := by
  refine congrArg ((B.card : ℂ)⁻¹ * ·) (Finset.sum_congr rfl (fun d _ ↦ ?_))
  have heq : ((-2 * Real.pi * d * (ξ + z) : ℝ) : ℂ) * Complex.I =
      ((-2 * Real.pi * d * ξ : ℝ) : ℂ) * Complex.I +
        ((-(d : ℤ) * z : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma exp_powerFrequency_sub_eq_char {p r m : ℕ} [NeZero p]
    (d : ℕ) (k l : ZMod (p ^ r)) :
    Complex.exp ((-2 * Real.pi * d *
      ((powerFrequency p r m k - powerFrequency p r m l : ℤ) : ℝ) /
        (p ^ (r + m) : ℕ) : ℝ) * Complex.I) =
      ZMod.stdAddChar ((d : ZMod (p ^ r)) * (l - k)) := by
  have h := ZMod.stdAddChar_coe (N := p ^ r) ((d : ℤ) * (l.valMinAbs - k.valMinAbs))
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, ZMod.coe_valMinAbs] at h
  rw [h]
  congr 1
  simp only [powerFrequency]
  push_cast
  field_simp [pow_add, NeZero.ne p]
  simp only [pow_add]
  ring

private lemma mask_powerFrequency_sub_eq_zero {p r m : ℕ} [NeZero p] {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod p) F]
    (b : Module.Basis (Fin r) (ZMod p) F) (hr : 0 < r)
    {k l : ZMod (p ^ r)} (hkl : k ≠ l) :
    mask (powerDigitSet b hr m)
      ((powerFrequency p r m k - powerFrequency p r m l : ℤ) / (p ^ (r + m) : ℕ)) = 0 := by
  simp only [mask, powerDigitSet, Finset.sum_image
    (fun _ _ _ _ h ↦ powerDigit_injective b hr m h), ← mul_div_assoc,
    exp_powerFrequency_sub_eq_char, powerDigit_orthogonality, ite_eq_right hkl.symm,
    Nat.cast_zero, mul_zero]

private lemma finiteFrequency_sub_eq_sum_erase (A : Data) (L M : ℕ → ℤ)
    {j n : ℕ} (hj : j < n) :
    finiteFrequency A L n - finiteFrequency A M n -
      (∏ i ∈ Finset.range j, A.base i : ℕ) * (L j - M j) =
        ∑ i ∈ (Finset.range n).erase j,
          (∏ k ∈ Finset.range i, A.base k : ℕ) * (L i - M i) := by
  simp only [finiteFrequency, ← Finset.sum_sub_distrib, ← mul_sub]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr hj), add_sub_cancel_right]

private lemma scale_dvd_finiteFrequency_sub (A : Data) (L M : ℕ → ℤ)
    {j n : ℕ} (hj : j < n) (hLM : ∀ i, i < j → L i = M i) :
    (A.scale j : ℤ) ∣ finiteFrequency A L n - finiteFrequency A M n -
      (∏ i ∈ Finset.range j, A.base i : ℕ) * (L j - M j) := by
  rw [finiteFrequency_sub_eq_sum_erase A L M hj]
  refine Finset.dvd_sum (fun i hi ↦ ?_)
  rcases lt_or_gt_of_ne (Finset.mem_erase.mp hi).1 with hij | hji
  · simp [hLM i hij]
  · apply dvd_mul_of_dvd_left
    exact_mod_cast Finset.prod_dvd_prod_of_subset _ _ A.base (Finset.range_mono hji)

private lemma mask_finiteFrequency_sub_eq (A : Data) (L M : ℕ → ℤ)
    {j n : ℕ} (hj : j < n) (hLM : ∀ i, i < j → L i = M i) :
    mask (A.digits j)
      (((finiteFrequency A L n - finiteFrequency A M n : ℤ) : ℝ) / A.scale j) =
        mask (A.digits j) (((L j - M j : ℤ) : ℝ) / A.base j) := by
  obtain ⟨z, hz⟩ := scale_dvd_finiteFrequency_sub A L M hj hLM
  rw [← mask_add_int _ (((L j - M j : ℤ) : ℝ) / A.base j) z]
  congr 1
  have hz' := congrArg (fun t : ℤ ↦ (t : ℝ)) hz
  simp only [Data.scale, Finset.prod_range_succ, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast, Nat.cast_mul] at hz' ⊢
  field_simp [(A.prefix_product_pos j).ne',
    (lt_of_lt_of_le Nat.zero_lt_two (A.two_le_base j)).ne']
  apply (div_eq_iff (by exact_mod_cast (A.prefix_product_pos j).ne')).mpr
  linarith

private lemma galoisPowerMoranData_mask_zero (p r m : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hr : ∀ n, 0 < r n) (n : ℕ) {k l : ZMod (p n ^ r n)} (hkl : k ≠ l) :
    let A := galoisPowerMoranData p r m hr
    mask (A.digits n)
      (((powerFrequency (p n) (r n) (m n) k - powerFrequency (p n) (r n) (m n) l : ℤ) : ℝ) /
        A.base n) = 0 := by
  letI : Fintype (GaloisField (p n) (r n)) := Fintype.ofFinite _
  exact mask_powerFrequency_sub_eq_zero
    (galoisPowerBasis (p n) (r n) (hr n)) (hr n) hkl

private def galoisPowerSpectrum (p r m : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hr : ∀ n, 0 < r n) : Set ℝ :=
  {ξ | ∃ L : ℕ → ℤ, (∀ j, ∃ k : ZMod (p j ^ r j), L j = powerFrequency (p j) (r j) (m j) k) ∧
    ∃ n, (∀ j, n ≤ j → L j = 0) ∧ ξ = finiteFrequency (galoisPowerMoranData p r m hr) L n}

private lemma finiteFrequency_mem_galoisPowerSpectrum (p r m : ℕ → ℕ)
    [∀ n, Fact (p n).Prime] (hr : ∀ n, 0 < r n)
    (k : ∀ j, ZMod (p j ^ r j)) (n : ℕ) :
    (finiteFrequency (galoisPowerMoranData p r m hr)
      (fun j ↦ powerFrequency (p j) (r j) (m j) (k j)) n : ℝ) ∈
        galoisPowerSpectrum p r m hr := by
  refine ⟨fun j ↦ if j < n then powerFrequency (p j) (r j) (m j) (k j) else 0, ?_, n, ?_, ?_⟩
  · intro j
    by_cases hj : j < n
    · exact ⟨k j, ite_eq_left hj⟩
    · exact ⟨0, by simp [hj, powerFrequency]⟩
  · exact fun j hj ↦ ite_eq_right (not_lt.mpr hj)
  · exact congrArg (fun z : ℤ ↦ (z : ℝ)) (Finset.sum_congr rfl (fun j hj ↦ by
      simp only [ite_eq_left (Finset.mem_range.mp hj)]))

private def spectralVector (μ : Measure ℝ) [IsFiniteMeasure μ] (ξ : ℝ) : Lp ℂ 2 μ :=
  BoundedContinuousFunction.toLp 2 μ ℂ
    (BoundedContinuousFunction.innerProbChar (2 * Real.pi * ξ))

private lemma prod_masks_eq_finite_sum (A : Data) (n : ℕ) (ξ : ℝ) :
    (∏ j : Fin n, mask (A.digits j) (ξ / A.scale j)) =
      (Fintype.card (∀ j : Fin n, A.digits j) : ℂ)⁻¹ *
        ∑ d : (∀ j : Fin n, A.digits j), Complex.exp
          ((-2 * Real.pi * ξ * (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) *
            Complex.I) := by
  simp only [mask, Finset.prod_mul_distrib, ← Finset.prod_inv_distrib,
    Fintype.card_pi, Nat.cast_prod, Fintype.card_coe]
  congr 1
  conv_lhs => enter [2, j]; rw [← Finset.sum_coe_sort (A.digits j)]
  simp only [Fintype.prod_sum, ← Complex.exp_sum]
  refine Finset.sum_congr rfl fun d _ ↦ congrArg Complex.exp ?_
  simp only [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ ↦ by congr 2; ring

private lemma normalized_exp_inner (c x y : ℝ) :
    inner ℂ ((c : ℂ)⁻¹ * Complex.exp (x * Complex.I))
      ((c : ℂ)⁻¹ * Complex.exp (y * Complex.I)) =
        ((c : ℂ)⁻¹) ^ 2 * Complex.exp ((y - x : ℝ) * Complex.I) := by
  simp only [RCLike.inner_apply, map_mul, map_inv₀, Complex.conj_ofReal,
    ← Complex.exp_conj, Complex.conj_I, Complex.ofReal_sub]
  rw [sub_mul, Complex.exp_sub, mul_neg, Complex.exp_neg]
  ring

private def finiteFourierVector (A : Data) (n : ℕ) (ξ : ℝ) :
    EuclideanSpace ℂ (∀ j : Fin n, A.digits j) :=
  WithLp.toLp 2 fun d ↦ (Real.sqrt (Fintype.card (∀ j : Fin n, A.digits j)) : ℂ)⁻¹ *
    Complex.exp ((2 * Real.pi * ξ * (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) *
      Complex.I)

private lemma finiteFourierVector_inner (A : Data) (n : ℕ) (ξ η : ℝ) :
    inner ℂ (finiteFourierVector A n ξ) (finiteFourierVector A n η) =
      ∏ j : Fin n, mask (A.digits j) ((ξ - η) / A.scale j) := by
  simp only [PiLp.inner_apply, finiteFourierVector, normalized_exp_inner,
    ← Finset.mul_sum, inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    prod_masks_eq_finite_sum, Complex.ofReal_natCast]
  exact congrArg (_ * ·) (Finset.sum_congr rfl fun _ _ ↦ by congr 3; ring)

private lemma prod_masks_finiteFrequency_sub_eq_zero (A : Data) (L M : ℕ → ℤ) (n : ℕ)
    (hex : ∃ j, j < n ∧ L j ≠ M j)
    (hzero : ∀ j, j < n → L j ≠ M j →
      mask (A.digits j) (((L j - M j : ℤ) : ℝ) / A.base j) = 0) :
    (∏ j : Fin n, mask (A.digits j)
      (((finiteFrequency A L n - finiteFrequency A M n : ℤ) : ℝ) / A.scale j)) = 0 := by
  have hj := Nat.find_spec hex
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨Nat.find hex, hj.1⟩ : Fin n))
  exact (mask_finiteFrequency_sub_eq A L M hj.1 (fun i hi ↦
    not_ne_iff.mp (fun h ↦ Nat.find_min hex hi ⟨hi.trans hj.1, h⟩))).trans
      (hzero _ hj.1 hj.2)

private lemma powerFrequency_injective {p r m : ℕ} [NeZero p] :
    Function.Injective (powerFrequency p r m) := by
  intro k l hkl
  exact ZMod.injective_valMinAbs ((mul_left_cancel₀
    (by exact_mod_cast pow_ne_zero m (NeZero.ne p))) hkl)

private def finitePowerChoice (p r m : ℕ → ℕ) {n : ℕ}
    (k : ∀ j : Fin n, ZMod (p j ^ r j)) (j : ℕ) : ℤ :=
  powerFrequency (p j) (r j) (m j) (if hj : j < n then k ⟨j, hj⟩ else 0)

private lemma finitePowerChoice_different (p r m : ℕ → ℕ) [∀ j, NeZero (p j)] {n : ℕ}
    {k l : ∀ j : Fin n, ZMod (p j ^ r j)} (hkl : k ≠ l) :
    ∃ j, j < n ∧ finitePowerChoice p r m k j ≠ finitePowerChoice p r m l j := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hkl
  exact ⟨j, j.isLt, by simpa only [finitePowerChoice, dite_eq_left j.isLt] using
    (powerFrequency_injective (p := p j) (r := r j) (m := m j)).ne hj⟩

private lemma finitePowerFourier_orthonormal (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime]
    (hr : ∀ j, 0 < r j) (n : ℕ) :
    let A := galoisPowerMoranData p r m hr
    Orthonormal ℂ (fun k : (∀ j : Fin n, ZMod (p j ^ r j)) ↦
      finiteFourierVector A n (finiteFrequency A (finitePowerChoice p r m k) n)) := by
  classical
  refine orthonormal_iff_ite.mpr fun k l ↦ ?_
  rw [finiteFourierVector_inner, ← Int.cast_sub]
  split_ifs with hkl
  · simp [hkl, mask, galoisPowerMoranData_card_digits, NeZero.ne (p _)]
  · refine prod_masks_finiteFrequency_sub_eq_zero _ _ _ n
      (finitePowerChoice_different p r m hkl) fun j hj hdiff ↦ ?_
    simp only [finitePowerChoice, dite_eq_left hj] at hdiff ⊢
    exact galoisPowerMoranData_mask_zero p r m hr j (fun h ↦ hdiff (congrArg _ h))

private def finitePowerFourierBasis (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime]
    (hr : ∀ j, 0 < r j) (n : ℕ) :
    OrthonormalBasis (∀ j : Fin n, ZMod (p j ^ r j)) ℂ
      (EuclideanSpace ℂ (∀ j : Fin n, (galoisPowerMoranData p r m hr).digits j)) :=
  (basisOfOrthonormalOfCardEqFinrank (finitePowerFourier_orthonormal p r m hr n)
    (by simp only [finrank_euclideanSpace, Fintype.card_pi, Fintype.card_coe,
      galoisPowerMoranData_card_digits, ZMod.card])).toOrthonormalBasis
    (by simpa only [coe_basisOfOrthonormalOfCardEqFinrank] using
      finitePowerFourier_orthonormal p r m hr n)

private lemma finitePowerFrequency_injective (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime]
    (hr : ∀ j, 0 < r j) (n : ℕ) :
    Function.Injective (fun k : (∀ j : Fin n, ZMod (p j ^ r j)) ↦
      finiteFrequency (galoisPowerMoranData p r m hr) (finitePowerChoice p r m k) n) := by
  intro k l hkl
  exact (finitePowerFourier_orthonormal p r m hr n).linearIndependent.injective
    (congrArg (fun ξ : ℤ ↦ finiteFourierVector (galoisPowerMoranData p r m hr) n ξ) hkl)

private def finitePowerSpectrumEmbedding (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime]
    (hr : ∀ j, 0 < r j) (n : ℕ) :
    (∀ j : Fin n, ZMod (p j ^ r j)) ↪ galoisPowerSpectrum p r m hr where
  toFun k := ⟨finiteFrequency (galoisPowerMoranData p r m hr) (finitePowerChoice p r m k) n,
    finiteFrequency_mem_galoisPowerSpectrum p r m hr
      (fun j ↦ if hj : j < n then k ⟨j, hj⟩ else 0) n⟩
  inj' := by
    intro k l hkl
    exact finitePowerFrequency_injective p r m hr n
      (Int.cast_injective (α := ℝ) (congrArg Subtype.val hkl))

/-- The Fourier dimension of a finite Borel measure on the real line.-/
def fourierDim (μ : Measure ℝ) [IsFiniteMeasure μ] : ℝ :=
  sSup {t : ℝ | t ∈ Set.Icc 0 1 ∧
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖Fourier.fourierIntegral Real.fourierChar μ (fun _ ↦ (1 : ℂ)) ξ‖ ≤
        C * Real.rpow (1 + |ξ|) (-t / 2)}

/-- A spectral measure is a probability measure whose real-frequency exponentials
form a Hilbert basis of its `L²`.-/
def is_spectral (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∃ Λ : Set ℝ, ∃ b : HilbertBasis Λ ℂ (Lp ℂ 2 μ),
    ∀ ξ : Λ, ∀ᵐ x ∂μ,
      (b ξ : ℝ → ℂ) x =
        Complex.exp ((2 * Real.pi * (ξ : ℝ) * x : ℝ) * Complex.I)

private def admissiblePrefix (A : Data) (n : ℕ) (d : ℕ → ℕ) :
    ∀ j : Fin n, A.digits j := fun j ↦
  if h : d j ∈ A.digits j then ⟨d j, h⟩ else ⟨(A.digits_nonempty j).choose,
    (A.digits_nonempty j).choose_spec⟩

private lemma measurable_admissiblePrefix (A : Data) (n : ℕ) :
    Measurable (admissiblePrefix A n) := by
  apply measurable_pi_lambda
  intro j
  convert (measurable_of_countable (fun x : ℕ ↦ if h : x ∈ A.digits j then
      (⟨x, h⟩ : A.digits j) else ⟨(A.digits_nonempty j).choose,
        (A.digits_nonempty j).choose_spec⟩)).comp
      (@measurable_pi_apply ℕ (fun _ ↦ ℕ) _ (j : ℕ)) using 1
  rfl

private def productCylinderFunction (A : Data) (n : ℕ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) (d : ℕ → ℕ) : ℂ :=
  w (admissiblePrefix A n d)

private lemma measurable_productCylinderFunction (A : Data) (n : ℕ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    Measurable (productCylinderFunction A n w) := by
  exact (measurable_of_countable w).comp (measurable_admissiblePrefix A n)

private lemma memLp_productCylinderFunction (A : Data) (n : ℕ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    MemLp (productCylinderFunction A n w) 2 (Measure.infinitePi A.digitLaw) := by
  letI (j : ℕ) : IsProbabilityMeasure (A.digitLaw j) := A.isProbabilityMeasure_digitLaw j
  apply MemLp.of_bound (measurable_productCylinderFunction A n w).aestronglyMeasurable
    (∑ d, ‖w d‖)
  exact Filter.Eventually.of_forall fun d ↦ Finset.single_le_sum (fun _ _ ↦ norm_nonneg _)
    (Finset.mem_univ (admissiblePrefix A n d))

private def productCylinderVector (A : Data) (n : ℕ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    Lp ℂ 2 (Measure.infinitePi A.digitLaw) :=
  (memLp_productCylinderFunction A n w).toLp (productCylinderFunction A n w)

private def rangeEquivFin (n : ℕ) : (Finset.range n : Set ℕ) ≃ Fin n where
  toFun j := ⟨j, Finset.mem_range.mp j.property⟩
  invFun j := ⟨j, Finset.mem_range.mpr j.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma coding_measurePreserving (A : Data) :
    MeasurePreserving A.coding (Measure.infinitePi A.digitLaw) A.measure := by
  exact ⟨A.measurable_coding, rfl⟩

private def codingPullback (A : Data) :
    Lp ℂ 2 A.measure →ₗᵢ[ℂ] Lp ℂ 2 (Measure.infinitePi A.digitLaw) :=
  Lp.compMeasurePreservingₗᵢ ℂ A.coding (coding_measurePreserving A)

private def productSpectralVector (A : Data) (ξ : ℝ) :
    Lp ℂ 2 (Measure.infinitePi A.digitLaw) :=
  codingPullback A (spectralVector A.measure ξ)

private def prefixFourierCylinder (A : Data) (n : ℕ) (ξ : ℝ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) : (ℕ → ℕ) → ℂ :=
  productCylinderFunction A n fun d ↦ w d * Complex.exp
    ((-2 * Real.pi * ξ * (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) * Complex.I)

private def finiteTailFourierFunction (A : Data) (n N : ℕ) (ξ : ℝ)
    (d : ℕ → ℕ) : ℂ :=
  Complex.exp ((-2 * Real.pi * ξ *
    (∑ j ∈ Finset.Ico n (n + N), (d j : ℝ) / (A.scale j : ℝ)) : ℝ) * Complex.I)

private def finiteCylinderCoefficient (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime]
    (hr : ∀ j, 0 < r j) (n : ℕ)
    (w : (∀ j : Fin n, (galoisPowerMoranData p r m hr).digits j) → ℂ)
    (k : ∀ j : Fin n, ZMod (p j ^ r j)) : ℂ :=
  let A := galoisPowerMoranData p r m hr
  (Real.sqrt (Fintype.card (∀ j : Fin n, A.digits j)) : ℂ)⁻¹ *
    ((Real.sqrt (Fintype.card (∀ j : Fin n, A.digits j)) : ℂ)⁻¹ *
      ∑ d, w d * Complex.exp
        ((-2 * Real.pi * finiteFrequency A (finitePowerChoice p r m k) n *
          (∑ j : Fin n, (d j : ℕ) / (A.scale j : ℝ)) : ℝ) * Complex.I))

private def finiteTailFactor (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime]
    (hr : ∀ j, 0 < r j) (n : ℕ) (k : ∀ j : Fin n, ZMod (p j ^ r j)) : ℂ :=
  let A := galoisPowerMoranData p r m hr
  Fourier.fourierIntegral Real.fourierChar (tailData A n).measure
    (fun _ ↦ (1 : ℂ))
    ((finiteFrequency A (finitePowerChoice p r m k) n : ℝ) /
      ((∏ j ∈ Finset.range n, A.base j : ℕ) : ℝ))

private def promoteCylinderWeight (A : Data) {m n : ℕ} (hmn : m ≤ n)
    (w : (∀ j : Fin m, A.digits j) → ℂ) :
    (∀ j : Fin n, A.digits j) → ℂ := fun d ↦
  w fun j ↦ d ⟨j, j.isLt.trans_le hmn⟩

private lemma productCylinderVector_promote (A : Data) {m n : ℕ} (hmn : m ≤ n)
    (w : (∀ j : Fin m, A.digits j) → ℂ) :
    productCylinderVector A n (promoteCylinderWeight A hmn w) =
      productCylinderVector A m w := by
  apply Lp.ext
  filter_upwards [(memLp_productCylinderFunction A n
      (promoteCylinderWeight A hmn w)).coeFn_toLp,
    (memLp_productCylinderFunction A m w).coeFn_toLp] with d hn hm
  rw [show (productCylinderVector A n (promoteCylinderWeight A hmn w) :
      (ℕ → ℕ) → ℂ) d = productCylinderFunction A n
        (promoteCylinderWeight A hmn w) d by
      simpa only [productCylinderVector] using hn,
    show (productCylinderVector A m w : (ℕ → ℕ) → ℂ) d =
      productCylinderFunction A m w d by
      simpa only [productCylinderVector] using hm]
  unfold productCylinderFunction promoteCylinderWeight
  congr 1

private lemma productCylinderVector_add (A : Data) (n : ℕ)
    (w u : (∀ j : Fin n, A.digits j) → ℂ) :
    productCylinderVector A n (w + u) =
      productCylinderVector A n w + productCylinderVector A n u := by
  unfold productCylinderVector
  rw [← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun _ ↦ rfl

private lemma productCylinderVector_smul (A : Data) (n : ℕ) (c : ℂ)
    (w : (∀ j : Fin n, A.digits j) → ℂ) :
    productCylinderVector A n (c • w) = c • productCylinderVector A n w := by
  unfold productCylinderVector
  rw [← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun _ ↦ rfl

private lemma productCylinderVector_zero (A : Data) (n : ℕ) :
    productCylinderVector A n 0 = 0 := by
  simpa only [zero_smul] using productCylinderVector_smul A n 0 (0 :
    (∀ j : Fin n, A.digits j) → ℂ)

private def positiveCylinderSubmodule (A : Data) :
    Submodule ℂ (Lp ℂ 2 (Measure.infinitePi A.digitLaw)) where
  carrier := {f | ∃ n, ∃ w : (∀ j : Fin (n + 1), A.digits j) → ℂ,
    f = productCylinderVector A (n + 1) w}
  zero_mem' := ⟨0, 0, (productCylinderVector_zero A 1).symm⟩
  add_mem' := by
    rintro f g ⟨n, w, rfl⟩ ⟨m, u, rfl⟩
    let N := max n m
    let w' := promoteCylinderWeight A (Nat.succ_le_succ (le_max_left n m)) w
    let u' := promoteCylinderWeight A (Nat.succ_le_succ (le_max_right n m)) u
    refine ⟨N, w' + u', ?_⟩
    rw [productCylinderVector_add,
      productCylinderVector_promote A (Nat.succ_le_succ (le_max_left n m)),
      productCylinderVector_promote A (Nat.succ_le_succ (le_max_right n m))]
  smul_mem' := by
    rintro c f ⟨n, w, rfl⟩
    exact ⟨n, c • w, (productCylinderVector_smul A (n + 1) c w).symm⟩

private def cylinderWeight (A : Data) (I : Finset ℕ) (S : Set (I → ℕ)) (c : ℂ) :
    (∀ j : Fin (I.sup id + 1), A.digits j) → ℂ := by
  classical
  exact fun d ↦
    if (fun i : I ↦
      (d ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩ : ℕ)) ∈ S
      then c else 0

/-- The Fourier dimension of a set, using probability measures concentrated on it.-/
def setFourierDim (K : Set ℝ) : ℝ :=
  sSup {t : ℝ | ∃ μ : Measure ℝ, ∃ hμ : IsProbabilityMeasure μ,
    letI := hμ
    μ Kᶜ = 0 ∧ fourierDim μ = t}

/-- A Salem set has equal Fourier and Hausdorff dimensions.-/
def is_salem (K : Set ℝ) : Prop :=
  ENNReal.ofReal (setFourierDim K) = dimH K

private def gaussianEnergy (μ : Measure ℝ) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ENNReal.ofReal (Real.exp (-a * (x - y) ^ 2)) ∂μ ∂μ

private def rieszPotential (μ : Measure ℝ) (d x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, edist x y ^ (-d) ∂μ

private def rieszEnergy (μ : Measure ℝ) (d : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, rieszPotential μ d x ∂μ

private def constructionLength (s : ℝ) (n : ℕ) : ℕ :=
  n + 1 + ⌈2 / s⌉₊

private def constructionRank (s : ℝ) (n : ℕ) : ℕ :=
  if s = 1 then n + 2 else ⌊s * constructionLength s n⌋₊

private lemma constructionLength_pos (s : ℝ) (n : ℕ) :
    0 < constructionLength s n := by
  exact Nat.add_pos_left (Nat.succ_pos n) _

private lemma constructionLength_mul_lower {s : ℝ} (hs : 0 < s) (n : ℕ) :
    2 ≤ s * constructionLength s n := by
  have hceil : 2 ≤ s * (⌈2 / s⌉₊ : ℝ) := by
    simpa only [mul_comm s] using (div_le_iff₀ hs).mp (Nat.le_ceil (2 / s))
  exact hceil.trans (mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr (Nat.le_add_left ⌈2 / s⌉₊ (n + 1))) hs.le)

private lemma constructionRank_two_le {s : ℝ} (hs : 0 < s) (n : ℕ) :
    2 ≤ constructionRank s n := by
  exact if h : s = 1 then by simp [constructionRank, h] else by
    simpa only [constructionRank, ite_eq_right h] using Nat.le_floor (constructionLength_mul_lower hs n)

private lemma constructionRank_pos {s : ℝ} (hs : 0 < s) (n : ℕ) :
    0 < constructionRank s n := by
  exact Nat.zero_lt_two.trans_le (constructionRank_two_le hs n)

private lemma constructionRank_lt {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) :
    constructionRank s n < constructionLength s n := by
  by_cases h : s = 1
  · simp [h, constructionRank, constructionLength]
  · simpa only [constructionRank, ite_eq_right h] using
      (Nat.floor_lt (mul_nonneg hs.le (Nat.cast_nonneg _))).mpr
        (mul_lt_of_lt_one_left (Nat.cast_pos.mpr (constructionLength_pos s n))
          (lt_of_le_of_ne hs₁ h))

private def constructionRatio (s : ℝ) (n : ℕ) : ℝ :=
  (constructionRank s n : ℝ) / constructionLength s n

private def constructionExponent (s : ℝ) (n : ℕ) : ℝ :=
  ((constructionRank s n : ℝ) - 1) / constructionLength s n

private def constructionDegree (s : ℝ) (n : ℕ) : ℕ :=
  1 + ⌈((constructionLength s n - constructionRank s n : ℕ) : ℝ) /
    constructionRank s n⌉₊

private lemma constructionDegree_two_le {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) :
    2 ≤ constructionDegree s n := by
  simpa only [constructionDegree, Nat.add_comm 1, Nat.succ_eq_add_one] using
    Nat.succ_le_succ (Nat.ceil_pos.mpr (div_pos (G₀ := ℝ)
    (Nat.cast_pos.mpr (Nat.sub_pos_of_lt (constructionRank_lt hs hs₁ n)))
    (Nat.cast_pos.mpr (constructionRank_pos hs n))))

private def constructionPrimeCondition (s : ℝ) (n P p : ℕ) : Prop :=
  p.Prime ∧ Odd p ∧ constructionDegree s n < p ∧
    P ^ (n + 1) < p ^ constructionLength s n ∧
    (constructionDegree s n - 1 : ℝ) * (2 * Real.log (2 * p)) ^ constructionLength s n ≤
      (p : ℝ) ^ (1 / 2 : ℝ)

private lemma eventually_constructionPrime_cost {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1)
    (n : ℕ) :
    ∀ᶠ p : ℕ in atTop,
      (constructionDegree s n - 1 : ℝ) * (2 * Real.log (2 * p)) ^ constructionLength s n ≤
        (p : ℝ) ^ (1 / 2 : ℝ) := by
  exact tendsto_natCast_atTop_atTop.eventually
    (eventually_mul_mask_log_pow_le_rpow (sub_nonneg.mpr
      (by exact_mod_cast (Nat.le_trans (by decide : 1 ≤ 2)
        (constructionDegree_two_le hs hs₁ n)))) (constructionLength s n) (by norm_num))

private lemma exists_constructionPrime {s : ℝ} (hs : 0 < s) (hs₁ : s ≤ 1) (n P : ℕ) :
    ∃ p, constructionPrimeCondition s n P p := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (eventually_constructionPrime_cost hs hs₁ n)
  obtain ⟨p, hp, hpprime⟩ := Nat.exists_infinite_primes
    (max M (P ^ (n + 1) + constructionDegree s n + 3))
  exact ⟨p, hpprime, hpprime.odd_of_ne_two (by omega), by omega,
    (show P ^ (n + 1) < p by omega).trans_le (Nat.le_pow (constructionLength_pos s n)),
    hM p (by omega)⟩

private def constructionPrime (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_constructionPrime hs hs₁ n
    (∏ j : Fin n, constructionPrime s hs hs₁ j ^ constructionLength s j))
termination_by n

private lemma constructionPrime_spec (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) :
    constructionPrimeCondition s n
      (∏ j : Fin n, constructionPrime s hs hs₁ j ^ constructionLength s j)
      (constructionPrime s hs hs₁ n) := by
  classical
  rw [constructionPrime.eq_def]
  exact Nat.find_spec (exists_constructionPrime hs hs₁ n
    (∏ j : Fin n, constructionPrime s hs hs₁ j ^ constructionLength s j))

private instance constructionPrime_isPrime (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) (n : ℕ) :
    Fact (constructionPrime s hs hs₁ n).Prime :=
  ⟨(constructionPrime_spec s hs hs₁ n).1⟩

/-- A Moran construction with prescribed dimension, using least admissible odd primes.-/
def spectralMoranData (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) : Data :=
  galoisPowerMoranData (constructionPrime s hs hs₁) (constructionRank s)
    (fun n ↦ constructionLength s n - constructionRank s n) (constructionRank_pos hs)

private structure HadamardTower (A : Data) where
  frequencies : ℕ → Finset ℤ
  zero_mem : ∀ n, 0 ∈ frequencies n
  card_eq : ∀ n, (frequencies n).card = (A.digits n).card
  mask_zero : ∀ n (k l : frequencies n), k ≠ l →
    mask (A.digits n) (((k : ℤ) - (l : ℤ) : ℤ) / A.base n) = 0

private def HadamardTower.choice {A : Data} (T : HadamardTower A) {n : ℕ}
    (k : ∀ j : Fin n, T.frequencies j) (j : ℕ) : ℤ :=
  if hj : j < n then k ⟨j, hj⟩ else 0

private lemma HadamardTower.choice_mem {A : Data} (T : HadamardTower A) {n : ℕ}
    (k : ∀ j : Fin n, T.frequencies j) (j : ℕ) : T.choice k j ∈ T.frequencies j := by
  by_cases hj : j < n <;> simp only [HadamardTower.choice, hj, ↓reduceDIte]
  · exact (k ⟨j, hj⟩).property
  · exact T.zero_mem j

private lemma HadamardTower.finite_orthonormal {A : Data} (T : HadamardTower A) (n : ℕ) :
    Orthonormal ℂ (fun k : (∀ j : Fin n, T.frequencies j) ↦
      finiteFourierVector A n (finiteFrequency A (T.choice k) n)) := by
  classical
  refine orthonormal_iff_ite.mpr fun k l ↦ ?_
  rw [finiteFourierVector_inner, ← Int.cast_sub]
  split_ifs with hkl
  · simp [hkl, mask, Nat.ne_of_gt (A.digits_nonempty _).card_pos]
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp hkl
    refine prod_masks_finiteFrequency_sub_eq_zero A _ _ n
      ⟨j, j.isLt, by simpa only [HadamardTower.choice, dite_eq_left j.isLt] using
        (Subtype.val_injective.ne hj)⟩ ?_
    intro i hi hdiff
    exact T.mask_zero i ⟨T.choice k i, T.choice_mem k i⟩
      ⟨T.choice l i, T.choice_mem l i⟩ (fun h ↦ hdiff (congrArg Subtype.val h))

private def HadamardTower.finiteBasis {A : Data} (T : HadamardTower A) (n : ℕ) :
    OrthonormalBasis (∀ j : Fin n, T.frequencies j) ℂ
      (EuclideanSpace ℂ (∀ j : Fin n, A.digits j)) :=
  letI : Nonempty (∀ j : Fin n, T.frequencies j) := ⟨fun j ↦ ⟨0, T.zero_mem j⟩⟩
  (basisOfOrthonormalOfCardEqFinrank (T.finite_orthonormal n)
    (by simp only [finrank_euclideanSpace, Fintype.card_pi, Fintype.card_coe, T.card_eq]))
    |>.toOrthonormalBasis (by
      simpa only [coe_basisOfOrthonormalOfCardEqFinrank] using T.finite_orthonormal n)

private def HadamardTower.spectrum {A : Data} (T : HadamardTower A) : Set ℝ :=
  {ξ | ∃ n, ∃ k : (∀ j : Fin n, T.frequencies j),
    ξ = (finiteFrequency A (T.choice k) n : ℝ)}

private def HadamardTower.finiteEmbedding {A : Data} (T : HadamardTower A) (n : ℕ) :
    (∀ j : Fin n, T.frequencies j) ↪ T.spectrum where
  toFun k := ⟨finiteFrequency A (T.choice k) n, n, k, rfl⟩
  inj' := fun _ _ h ↦ (T.finite_orthonormal n).linearIndependent.injective
    (congrArg (finiteFourierVector A n) (congrArg Subtype.val h))

private def galoisPowerHadamardTower (p r m : ℕ → ℕ) [∀ j, Fact (p j).Prime]
    (hr : ∀ j, 0 < r j) : HadamardTower (galoisPowerMoranData p r m hr) where
  frequencies j := Finset.univ.image (powerFrequency (p j) (r j) (m j))
  zero_mem j := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp [powerFrequency]⟩
  card_eq j := by simp only [Finset.card_image_of_injective _ powerFrequency_injective,
    Finset.card_univ, ZMod.card, galoisPowerMoranData_card_digits]
  mask_zero j k l hkl := by
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp k.property
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp l.property
    have hab : a ≠ b := fun h ↦ hkl (Subtype.ext (ha.symm.trans ((congrArg _ h).trans hb)))
    simpa only [ha, hb] using galoisPowerMoranData_mask_zero p r m hr j hab

private def tailSquareError (r : ℕ) : ℝ :=
  Real.pi ^ 2 / (4 * 27 ^ (2 * (r + 1)))

private def uniformTailLower : ℝ :=
  (Real.pi ^ 2)⁻¹ * ∏' r, (1 - tailSquareError r)

/-- The finite sums of centered digit frequencies for the prescribed-dimension construction.-/
def spectralMoranSpectrum (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) : Set ℝ :=
  galoisPowerSpectrum (constructionPrime s hs hs₁) (constructionRank s)
    (fun j ↦ constructionLength s j - constructionRank s j) (constructionRank_pos hs)

/-- The constructed spectrum is countable.-/
theorem spectralMoranSpectrum_countable (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) :
    (spectralMoranSpectrum s hs hs₁).Countable := by
  refine (Set.countable_range (fun z : ℤ ↦ (z : ℝ))).mono ?_
  rintro ξ ⟨L, _, n, _, hξ⟩
  exact ⟨_, hξ.symm⟩

end Moran
