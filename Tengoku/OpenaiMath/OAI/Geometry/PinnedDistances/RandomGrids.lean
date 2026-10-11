import Tengoku.OpenaiMath.OAI.Geometry.PinnedDistances.Hierarchy

namespace OAI

universe u1 u2 u3

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology

/- Square-grid construction and the finite-shift sharing law. -/

noncomputable section
open MeasureTheory
open scoped Topology ENNReal
namespace WeakPinned.Grid

def bin (l s x : ℝ) : ℤ := ⌊(x-s)/l⌋
def shares (l s x y : ℝ) : ℝ := if bin l s x = bin l s y then 1 else 0

lemma bin_period {l : ℝ} (hl : 0 < l) (s x : ℝ) :
    bin l (s+l) x = bin l s x - 1 := by
  unfold bin
  rw [show (x-(s+l))/l = (x-s)/l - 1 by field_simp; ring]
  exact Int.floor_sub_one _

lemma shares_period {l : ℝ} (hl : 0 < l) (x y : ℝ) :
    Function.Periodic (fun s => shares l s x y) l := by
  intro s
  simp [shares, bin_period hl]

lemma shares_symm (l s x y : ℝ) : shares l s x y = shares l s y x := by
  simp only [shares, eq_comm]

lemma measurable_shares (l x y : ℝ) : Measurable (fun s => shares l s x y) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_eq_fun
    (((measurable_const.sub measurable_id).div_const l).floor)
    (((measurable_const.sub measurable_id).div_const l).floor)

lemma bin_small_shift {l x s : ℝ} (hl : 0 < l) (hs : s ∈ Set.Ioc x (x+l)) :
    bin l s x = -1 := by
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ hl).mpr
    norm_num
    linarith [hs.2]
  · apply (div_lt_iff₀ hl).mpr
    norm_num
    linarith [hs.1]

lemma shares_small_shift {l x y s : ℝ} (hl : 0 < l) (hxy : x ≤ y)
    (hs : s ∈ Set.Ioc x (x+l)) : shares l s x y = if y < s then 1 else 0 := by
  have he : bin l s y = -1 ↔ y < s := by
    simp only [bin, Int.floor_eq_iff]
    constructor
    · intro h
      have := (div_lt_iff₀ hl).mp h.2
      norm_num at this
      linarith
    · intro h
      constructor
      · apply (le_div_iff₀ hl).mpr
        norm_num
        linarith [hs.2]
      · apply (div_lt_iff₀ hl).mpr
        norm_num
        linarith
  simp only [shares, bin_small_shift hl hs, eq_comm (a := (-1 : ℤ))]
  simp only [he]

lemma shares_integral {l : ℝ} (hl : 0 < l) (x y : ℝ) :
    (∫ s : ℝ in Set.Ioc 0 l, shares l s x y) = max 0 (l-|x-y|) := by
  wlog hxy : x ≤ y
  · simpa only [shares_symm l _ x y, abs_sub_comm x y] using this hl y x (le_of_not_ge hxy)
  have hp := (shares_period hl x y).intervalIntegral_add_eq 0 x
  simp only [zero_add] at hp
  rw [intervalIntegral.integral_of_le hl.le,
    intervalIntegral.integral_of_le (by linarith : x ≤ x+l)] at hp
  rw [hp]
  have he : (∫ s : ℝ in Set.Ioc x (x+l), shares l s x y) =
      ∫ s : ℝ in Set.Ioc x (x+l), if y < s then (1 : ℝ) else 0 := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    exact shares_small_shift hl hxy hs
  rw [he]
  change (∫ s : ℝ in Set.Ioc x (x+l), (Set.Ioi y).indicator (fun _ => (1 : ℝ)) s) = _
  rw [setIntegral_indicator measurableSet_Ioi]
  rw [show Set.Ioc x (x+l) ∩ Set.Ioi y = Set.Ioc y (x+l) by
    ext s; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]; constructor
    · rintro ⟨⟨h₁,h₂⟩,h₃⟩; exact ⟨h₃,h₂⟩
    · intro h; exact ⟨⟨hxy.trans_lt h.1,h.2⟩,h.1⟩]
  rw [setIntegral_const]
  simp only [Measure.real, Real.volume_Ioc, smul_eq_mul, mul_one, ENNReal.toReal_ofReal']
  rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
  rw [max_comm]
  congr 1
  ring

lemma shares_integrableOn (l x y a b : ℝ) :
    IntegrableOn (fun s => shares l s x y) (Set.Ioc a b) := by
  apply IntegrableOn.of_bound measure_Ioc_lt_top (measurable_shares l x y).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun s => by unfold shares; split_ifs <;> norm_num)

/-- Independent uniform shifts in the two axes give a product of overlap lengths.
    This integral is unnormalized planar Lebesgue mass. -/
lemma square_shares_integral {l : ℝ} (hl : 0 < l) (x y : ℝ × ℝ) :
    (∫ s₁ : ℝ in Set.Ioc 0 l, ∫ s₂ : ℝ in Set.Ioc 0 l,
      shares l s₁ x.1 y.1 * shares l s₂ x.2 y.2) =
      max 0 (l-|x.1-y.1|) * max 0 (l-|x.2-y.2|) := by
  simp_rw [integral_const_mul]
  rw [integral_mul_const, shares_integral hl, shares_integral hl]

lemma shares_gap {l : ℝ} (hl : 0 < l) {s x y : ℝ}
    (h : bin l s x = bin l s y) : |x-y| < l := by
  have hx := Int.floor_le ((x-s)/l)
  have hy := Int.lt_floor_add_one ((y-s)/l)
  have hx' := Int.floor_le ((y-s)/l)
  have hy' := Int.lt_floor_add_one ((x-s)/l)
  change (bin l s x : ℝ) ≤ (x-s)/l at hx
  change (y-s)/l < (bin l s y : ℝ) + 1 at hy
  change (bin l s y : ℝ) ≤ (y-s)/l at hx'
  change (x-s)/l < (bin l s x : ℝ) + 1 at hy'
  rw [h] at hx hy'
  rw [abs_lt]
  constructor
  · have : (y-s)/l < (x-s)/l+1 := by linarith
    have hh := (div_lt_iff₀ hl).mp this
    field_simp at hh
    linarith
  · have : (x-s)/l < (y-s)/l+1 := by linarith
    have hh := (div_lt_iff₀ hl).mp this
    field_simp at hh
    linarith

lemma bin_double {l : ℝ} (hl : 0 < l) (s x : ℝ) (b : ℤ) :
    bin (2*l) (s+b*l) x = (bin l s x-b)/2 := by
  unfold bin
  rw [show (x-(s+b*l))/(2*l) = ((x-s)/l-b)/2 by field_simp; ring]
  have hh := Int.floor_div_natCast (((x-s)/l)-(b:ℝ)) 2
  norm_num only [Nat.cast_ofNat, Int.floor_sub_intCast] at hh
  exact hh

lemma nested_bins {l : ℝ} (hl : 0 < l) (s x y : ℝ) (b : ℤ)
    (h : bin l s x = bin l s y) : bin (2*l) (s+b*l) x = bin (2*l) (s+b*l) y := by
  rw [bin_double hl, bin_double hl, h]

/-- Normalized Lebesgue measure on a half-open interval of positive length. -/
def uniformInterval (l : ℝ) : Measure ℝ :=
  (ENNReal.ofReal l)⁻¹ • volume.restrict (Set.Ioc 0 l)

lemma uniformInterval_probability {l : ℝ} (hl : 0 < l) :
    IsProbabilityMeasure (uniformInterval l) := by
  constructor
  simp only [uniformInterval, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ioc, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hl)) ENNReal.ofReal_ne_top

lemma translate_restrict_Ioc (l : ℝ) :
    (volume.restrict (Set.Ioc 0 l)).map (fun x => x+l) =
      volume.restrict (Set.Ioc l (l+l)) := by
  have hh := (measurePreserving_add_right volume l).restrict_preimage
    (measurableSet_Ioc (a := l) (b := l+l))
  have he : (fun x : ℝ => x+l) ⁻¹' Set.Ioc l (l+l) = Set.Ioc 0 l := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [he] at hh
  exact hh.map_eq

open ProbabilityTheory in
/-- A fair binary step of length `l`. -/
def binaryStep (l : ℝ) : Measure ℝ := bernoulliMeasure 0 l ⟨1/2, by norm_num⟩

instance binaryStep_probability (l : ℝ) : IsProbabilityMeasure (binaryStep l) := by
  unfold binaryStep
  infer_instance

lemma binaryStep_eq (l : ℝ) :
    binaryStep l = (2 : ℝ≥0∞)⁻¹ • Measure.dirac 0 + (2 : ℝ≥0∞)⁻¹ • Measure.dirac l := by
  simp only [binaryStep, ProbabilityTheory.bernoulliMeasure_def]
  rw [← Measure.coe_nnreal_smul, ← Measure.coe_nnreal_smul]
  congr 2
  · rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal ((1:ℝ)/2) = _
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  · rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal (1-(1:ℝ)/2) = _
    norm_num only [show (1-(1:ℝ)/2) = 1/2 by norm_num]
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num

lemma uniform_double {l : ℝ} (hl : 0 < l) :
    (uniformInterval l).conv (binaryStep l) = uniformInterval (2*l) := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/-- One initial uniform shift followed by independent fair coarsening bits,
    before introducing phase and orientation. -/
def incrementLaw : ℕ → Measure ℝ
  | 0 => uniformInterval 1
  | n+1 => binaryStep (2^n)

instance incrementLaw_probability (n : ℕ) : IsProbabilityMeasure (incrementLaw n) := by
  cases n with
  | zero => exact uniformInterval_probability zero_lt_one
  | succ n => exact binaryStep_probability _

def axisLaw : Measure (ℕ → ℝ) := Measure.infinitePi incrementLaw
instance axisLaw_probability : IsProbabilityMeasure axisLaw := by
  unfold axisLaw
  infer_instance

def shift (n : ℕ) (ω : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range (n+1), ω i

lemma measurable_shift (n : ℕ) : Measurable (shift n) := by
  exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

lemma shift_zero (ω : ℕ → ℝ) : shift 0 ω = ω 0 := by simp [shift]
lemma shift_succ (n : ℕ) (ω : ℕ → ℝ) :
    shift (n+1) ω = shift n ω + ω (n+1) := by simp [shift, Finset.sum_range_succ]

lemma map_shift (n : ℕ) : axisLaw.map (shift n) = uniformInterval (2^n) := by
  induction n with
  | zero =>
      simp only [pow_zero]
      rw [show shift 0 = (fun ω => ω 0) by funext ω; exact shift_zero ω]
      exact Measure.infinitePi_map_eval incrementLaw 0
  | succ n ih =>
      have hind := ProbabilityTheory.iIndepFun_infinitePi
        (P := incrementLaw) (X := fun _ => id) (fun _ => measurable_id)
      have hi := hind.indepFun_finsetSum_of_notMem
        (fun i => measurable_pi_apply i) (s := Finset.range (n+1)) (i := n+1) (by simp)
      have he : (∑ j ∈ Finset.range (n+1), (fun ω : ℕ → ℝ => id (ω j))) = shift n := by
        funext ω
        simp [shift]
      rw [he] at hi
      have hm := hi.map_add_eq_map_conv_map₀ (measurable_shift n).aemeasurable
        (measurable_pi_apply (n+1)).aemeasurable
      change axisLaw.map (fun ω => shift n ω + ω (n+1)) = _ at hm
      simp only [← shift_succ] at hm
      change axisLaw.map (shift (n+1)) = (axisLaw.map (shift n)).conv ((Measure.infinitePi incrementLaw).map (fun f => f (n+1))) at hm
      rw [ih, Measure.infinitePi_map_eval incrementLaw (n+1)] at hm
      rw [incrementLaw, uniform_double (by positivity)] at hm
      simpa only [pow_succ, mul_comm (2^n) (2:ℝ)] using hm

lemma integral_uniform_shares {l : ℝ} (hl : 0 < l) (x y : ℝ) :
    (∫ s, shares l s x y ∂uniformInterval l) = max 0 (1-|x-y|/l) := by
  rw [uniformInterval, integral_smul_measure, shares_integral hl]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hl.le, smul_eq_mul]
  rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr hl.le), mul_zero]
  congr 1
  field_simp

lemma integral_shares_nat_periods {l : ℝ} (hl : 0 < l) (k : ℕ) (x y : ℝ) :
    (∫ s in Set.Ioc 0 (k*l), shares l s x y) = (k:ℝ)*max 0 (l-|x-y|) := by
  have hh := (shares_period hl x y).intervalIntegral_add_zsmul_eq (k:ℤ) 0
    (fun a b => ⟨shares_integrableOn l x y a b, shares_integrableOn l x y b a⟩)
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast,
    intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ k*l),
    intervalIntegral.integral_of_le hl.le, shares_integral hl] at hh
  exact hh

lemma binaryStep_ae (l : ℝ) : ∀ᵐ x ∂binaryStep l, x = 0 ∨ x = l := by
  rw [binaryStep_eq]
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff (by measurability)).mpr (Or.inl rfl)
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff (by measurability)).mpr (Or.inr rfl)

lemma axis_increment_ae (n : ℕ) :
    ∀ᵐ ω ∂axisLaw, ω (n+1) = 0 ∨ ω (n+1) = (2:ℝ)^n := by
  have hh : ∀ᵐ x ∂incrementLaw (n+1), x = 0 ∨ x = (2:ℝ)^n := binaryStep_ae _
  apply ae_of_ae_map (μ := axisLaw) (f := fun ω : ℕ → ℝ => ω (n+1))
    (p := fun x : ℝ => x = 0 ∨ x = (2:ℝ)^n) (measurable_pi_apply (n+1)).aemeasurable
  simpa only [axisLaw, Measure.infinitePi_map_eval] using hh

lemma bins_nested_ae (n : ℕ) (x y : ℝ) :
    ∀ᵐ ω ∂axisLaw, bin (2^n) (shift n ω) x = bin (2^n) (shift n ω) y →
      bin (2^(n+1)) (shift (n+1) ω) x = bin (2^(n+1)) (shift (n+1) ω) y := by
  filter_upwards [axis_increment_ae n] with ω hω
  intro h
  rcases hω with hω | hω
  · simpa only [shift_succ, hω, pow_succ, mul_comm (2^n) (2:ℝ),
      Int.cast_zero, zero_mul, add_zero] using nested_bins (by positivity) (shift n ω) x y 0 h
  · simpa only [shift_succ, hω, pow_succ, mul_comm (2^n) (2:ℝ),
      Int.cast_one, one_mul] using nested_bins (by positivity) (shift n ω) x y 1 h

/-- Both independent axis constructions, before phase and rotation. -/
abbrev GridSample := (ℕ → ℝ) × (ℕ → ℝ)
def squareLaw : Measure GridSample := axisLaw.prod axisLaw
instance squareLaw_probability : IsProbabilityMeasure squareLaw := by
  unfold squareLaw
  infer_instance

def shiftZ (m : ℤ) (ω : ℕ → ℝ) : ℝ := shift m.toNat ω

def shareAt (m : ℤ) (ω : GridSample) (x y : ℝ × ℝ) : Prop :=
  bin ((2:ℝ)^m) (shiftZ m ω.1) x.1 = bin ((2:ℝ)^m) (shiftZ m ω.1) y.1 ∧
  bin ((2:ℝ)^m) (shiftZ m ω.2) x.2 = bin ((2:ℝ)^m) (shiftZ m ω.2) y.2

lemma measurableSet_shareAt (m : ℤ) (x y : ℝ × ℝ) :
    MeasurableSet {ω | shareAt m ω x y} := by
  unfold shareAt bin shiftZ
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun
      (((measurable_const.sub ((measurable_shift _).comp measurable_fst)).div_const _).floor)
      (((measurable_const.sub ((measurable_shift _).comp measurable_fst)).div_const _).floor)
  · exact measurableSet_eq_fun
      (((measurable_const.sub ((measurable_shift _).comp measurable_snd)).div_const _).floor)
      (((measurable_const.sub ((measurable_shift _).comp measurable_snd)).div_const _).floor)

lemma max_sharing_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 - max 0 (1-a) * max 0 (1-b) ≤ a+b := by
  by_cases ha' : a ≤ 1
  · by_cases hb' : b ≤ 1
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      nlinarith [mul_nonneg ha hb]
    · rw [max_eq_left (show 1-b ≤ 0 by linarith)]
      nlinarith
  · rw [max_eq_left (by linarith)]
    nlinarith

lemma axis_nestedZ_ae (m : ℤ) (x y : ℝ) :
    ∀ᵐ ω ∂axisLaw, bin ((2:ℝ)^m) (shiftZ m ω) x = bin ((2:ℝ)^m) (shiftZ m ω) y →
      bin ((2:ℝ)^(m+1)) (shiftZ (m+1) ω) x = bin ((2:ℝ)^(m+1)) (shiftZ (m+1) ω) y := by
  by_cases hm : 0 ≤ m
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [show (n:ℤ)+1 = ((n+1:ℕ):ℤ) by omega]
    simpa only [shiftZ, Int.toNat_natCast, zpow_natCast] using bins_nested_ae n x y
  · have hm' : m+1 ≤ 0 := by omega
    filter_upwards with ω
    intro h
    simp only [shiftZ, Int.toNat_of_nonpos (by omega : m ≤ 0)] at h
    have hh := nested_bins (by positivity : 0 < (2:ℝ)^m) (shift 0 ω) x y 0
    simpa only [shiftZ, Int.toNat_of_nonpos (by omega : m ≤ 0),
      Int.toNat_of_nonpos hm', zpow_add₀ (by norm_num : (2:ℝ)≠0), zpow_one,
      mul_comm ((2:ℝ)^m) (2:ℝ), Int.cast_zero, zero_mul, add_zero] using hh h

lemma shareAt_nested_ae (m : ℤ) (x y : ℝ × ℝ) :
    ∀ᵐ ω ∂squareLaw, shareAt m ω x y → shareAt (m+1) ω x y := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (axis_nestedZ_ae m x.1 y.1),
    Measure.quasiMeasurePreserving_snd.ae (axis_nestedZ_ae m x.2 y.2)] with ω hx hy
  exact fun h => ⟨hx h.1, hy h.2⟩

lemma shareAt_symm (m : ℤ) (ω : GridSample) (x y : ℝ × ℝ) :
    shareAt m ω x y ↔ shareAt m ω y x := by simp [shareAt, eq_comm]
lemma shareAt_trans (m : ℤ) (ω : GridSample) (x y z : ℝ × ℝ)
    (hxy : shareAt m ω x y) (hyz : shareAt m ω y z) : shareAt m ω x z :=
  ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩

lemma shareAt_bddBelow (ω : GridSample) {x y : ℝ × ℝ} (hxy : x ≠ y) :
    BddBelow {m : ℤ | shareAt m ω x y} := by
  have bound {a b : ℝ} (h : a ≠ b) (f : ℤ → ℝ) :
      BddBelow {m : ℤ | bin ((2:ℝ)^m) (f m) a = bin ((2:ℝ)^m) (f m) b} := by
    obtain ⟨k,hk⟩ := exists_mem_Ico_zpow (abs_pos.mpr (sub_ne_zero.mpr h)) (by norm_num : (1:ℝ)<2)
    refine ⟨k, fun m hm => ?_⟩
    have hh := shares_gap (by positivity : 0 < (2:ℝ)^m) hm
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp (hk.1.trans hh.le)
  by_cases h₁ : x.1 = y.1
  · have h₂ : x.2 ≠ y.2 := fun h₂ => hxy (Prod.ext h₁ h₂)
    exact (bound h₂ (fun m => shiftZ m ω.2)).mono (fun _ h => h.2)
  · exact (bound h₁ (fun m => shiftZ m ω.1)).mono (fun _ h => h.1)

def minScale (ω : GridSample) (x y : ℝ × ℝ) : ℤ := sInf {m | shareAt m ω x y}

def gridDepth (ω : GridSample) (x y : ℝ × ℝ) : ℝ :=
  -(minScale ω x y : ℝ) * Real.log 2

lemma minScale_symm (ω : GridSample) (x y : ℝ × ℝ) :
    minScale ω x y = minScale ω y x := by
  unfold minScale
  congr 1
  ext m
  exact shareAt_symm m ω x y

lemma minScale_mem {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y)
    (he : ∃ m, shareAt m ω x y) : shareAt (minScale ω x y) ω x y :=
  Int.csInf_mem he (shareAt_bddBelow ω hxy)

lemma minScale_le {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y)
    {m : ℤ} (hm : shareAt m ω x y) : minScale ω x y ≤ m :=
  csInf_le (shareAt_bddBelow ω hxy) hm

lemma shareAt_iff_minScale_le {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y)
    (he : ∃ m, shareAt m ω x y)
    (hn : ∀ m, shareAt m ω x y → shareAt (m+1) ω x y) (m : ℤ) :
    shareAt m ω x y ↔ minScale ω x y ≤ m := by
  constructor
  · exact minScale_le hxy
  · intro hm
    have hmono : Monotone (fun k => shareAt k ω x y) := monotone_int_of_le_succ hn
    exact hmono hm (minScale_mem hxy he)

lemma minScale_eq_iff {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y) (m : ℤ) :
    minScale ω x y = m ↔
      (shareAt m ω x y ∧ ∀ k : ℤ, k < m → ¬ shareAt k ω x y) ∨
      (m = 0 ∧ ¬ ∃ k : ℤ, shareAt k ω x y) := by
  by_cases he : ∃ k, shareAt k ω x y
  · have hs := minScale_mem hxy he
    constructor
    · intro h
      left
      rw [h] at hs
      refine ⟨hs, fun k hk hks => ?_⟩
      have hh := minScale_le hxy hks
      omega
    · rintro (⟨hm,hmin⟩ | ⟨_,hn⟩)
      · apply le_antisymm (minScale_le hxy hm)
        by_contra h
        exact hmin _ (by omega) hs
      · exact False.elim (hn he)
  · have hz : minScale ω x y = 0 := by
      unfold minScale
      rw [show {m | shareAt m ω x y} = ∅ by ext m; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]; exact iff_false_intro (fun h => he ⟨m,h⟩)]
      exact Int.csInf_empty
    simp only [hz]
    constructor
    · intro hm
      exact Or.inr ⟨hm.symm,he⟩
    · rintro (⟨hm,_⟩ | ⟨rfl,_⟩)
      · exact False.elim (he ⟨m,hm⟩)
      · rfl

lemma measurable_minScale {x y : ℝ × ℝ} (hxy : x ≠ y) :
    Measurable (fun ω => minScale ω x y) := by
  apply measurable_to_countable'
  intro m
  change MeasurableSet {ω | minScale ω x y = m}
  have he : {ω : GridSample | minScale ω x y = m} =
      ({ω | shareAt m ω x y} ∩ {ω | ∀ k < m, ¬shareAt k ω x y}) ∪
      ({ω | m = 0} ∩ {ω | ¬∃ k, shareAt k ω x y}) := by
    ext ω
    exact minScale_eq_iff hxy m
  rw [he]
  apply MeasurableSet.union
  · apply (measurableSet_shareAt m x y).inter
    have he : {ω : GridSample | ∀ k < m, ¬shareAt k ω x y} =
        ⋂ k : ℤ, ⋂ (_ : k < m), {ω : GridSample | shareAt k ω x y}ᶜ := by
      ext ω
      simp
    rw [he]
    exact MeasurableSet.iInter fun k =>
      MeasurableSet.iInter fun (_ : k < m) => (measurableSet_shareAt k x y).compl
  · apply (MeasurableSet.const (m = 0)).inter
    have he : {ω : GridSample | ¬∃ k, shareAt k ω x y} =
        (⋃ k : ℤ, {ω : GridSample | shareAt k ω x y})ᶜ := by
      ext ω
      simp
    rw [he]
    exact (MeasurableSet.iUnion fun k => measurableSet_shareAt k x y).compl

lemma measurable_gridDepth {x y : ℝ × ℝ} (hxy : x ≠ y) :
    Measurable (fun ω => gridDepth ω x y) := by
  exact (((measurable_of_countable (fun n : ℤ => (n:ℝ))).comp (measurable_minScale hxy)).neg).mul_const _

/-- Parameter measurability, needed before integrating orientation and phase. -/
lemma measurableSet_shareAt_param {T : Type u1} [MeasurableSpace T]
    {W : T → GridSample} {X Y : T → ℝ × ℝ}
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y) (m : ℤ) :
    MeasurableSet {t | shareAt m (W t) (X t) (Y t)} := by
  unfold shareAt bin shiftZ
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun
      ((hX.fst.sub ((measurable_shift _).comp hW.fst)).div_const _).floor
      ((hY.fst.sub ((measurable_shift _).comp hW.fst)).div_const _).floor
  · exact measurableSet_eq_fun
      ((hX.snd.sub ((measurable_shift _).comp hW.snd)).div_const _).floor
      ((hY.snd.sub ((measurable_shift _).comp hW.snd)).div_const _).floor

lemma measurable_minScale_param {T : Type u2} [MeasurableSpace T]
    {W : T → GridSample} {X Y : T → ℝ × ℝ}
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y) (hne : ∀ t, X t ≠ Y t) :
    Measurable (fun t => minScale (W t) (X t) (Y t)) := by
  apply measurable_to_countable'
  intro m
  change MeasurableSet {t | minScale (W t) (X t) (Y t) = m}
  have he : {t | minScale (W t) (X t) (Y t) = m} =
      ({t | shareAt m (W t) (X t) (Y t)} ∩
        ⋂ k : ℤ, ⋂ (_ : k < m), {t | shareAt k (W t) (X t) (Y t)}ᶜ) ∪
      ({t | m = 0} ∩ (⋃ k : ℤ, {t | shareAt k (W t) (X t) (Y t)})ᶜ) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_compl_iff, Set.mem_iUnion]
    exact minScale_eq_iff (hne t) m
  rw [he]
  exact ((measurableSet_shareAt_param hW hX hY m).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun (_ : k < m) =>
      (measurableSet_shareAt_param hW hX hY k).compl)).union
    ((MeasurableSet.const (m = 0)).inter (MeasurableSet.iUnion fun k =>
      measurableSet_shareAt_param hW hX hY k).compl)

lemma measurable_gridDepth_param {T : Type u3} [MeasurableSpace T]
    {W : T → GridSample} {X Y : T → ℝ × ℝ}
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y) (hne : ∀ t, X t ≠ Y t) :
    Measurable (fun t => gridDepth (W t) (X t) (Y t)) := by
  exact (((measurable_of_countable (fun n : ℤ => (n:ℝ))).comp
    (measurable_minScale_param hW hX hY hne)).neg).mul_const _

def polarPair (t θ : ℝ) : ℝ × ℝ := (Real.exp t * Real.cos θ, Real.exp t * Real.sin θ)

def polarMean (t θ : ℝ) : ℝ :=
  (∫ ω, gridDepth ω (0,0) (polarPair t θ) ∂squareLaw) + t

lemma zero_ne_polarPair (t θ : ℝ) : (0,0) ≠ polarPair t θ := by
  intro h
  have he : Real.exp t ≠ 0 := Real.exp_ne_zero t
  have h₁ : Real.cos θ = 0 := (mul_eq_zero.mp (congrArg Prod.fst h).symm).resolve_left he
  have h₂ : Real.sin θ = 0 := (mul_eq_zero.mp (congrArg Prod.snd h).symm).resolve_left he
  have hh := Real.sin_sq_add_cos_sq θ
  rw [h₁,h₂] at hh
  norm_num at hh

lemma polarPair_gaps (t θ : ℝ) :
    Real.exp t ≤ |(polarPair t θ).1|+|(polarPair t θ).2| ∧
    |(polarPair t θ).1|+|(polarPair t θ).2| ≤ 2*Real.exp t := by
  have hsum : 1 ≤ |Real.cos θ|+|Real.sin θ| := by
    have hsq := Real.sin_sq_add_cos_sq θ
    have hpos := mul_nonneg (abs_nonneg (Real.cos θ)) (abs_nonneg (Real.sin θ))
    have hc := abs_nonneg (Real.cos θ)
    have hs := abs_nonneg (Real.sin θ)
    nlinarith [sq_abs (Real.cos θ), sq_abs (Real.sin θ)]
  have hsum' : |Real.cos θ|+|Real.sin θ| ≤ 2 := by
    linarith [Real.abs_cos_le_one θ, Real.abs_sin_le_one θ]
  simp only [polarPair, abs_mul, abs_of_pos (Real.exp_pos t)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg t)]
  · nlinarith [mul_le_mul_of_nonneg_left hsum' (Real.exp_nonneg t)]

lemma measurable_polarPair : Measurable (fun p : ℝ × ℝ => polarPair p.1 p.2) := by
  exact (measurable_fst.exp.mul measurable_snd.cos).prodMk
    (measurable_fst.exp.mul measurable_snd.sin)

lemma measurable_polarMean : Measurable (fun p : ℝ × ℝ => polarMean p.1 p.2) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × GridSample =>
      gridDepth p.2 (0,0) (polarPair p.1.1 p.1.2)) :=
    measurable_gridDepth_param measurable_snd measurable_const
      (measurable_polarPair.comp measurable_fst) (fun p => zero_ne_polarPair _ _)
  have hi : StronglyMeasurable (fun p : ℝ × ℝ => ∫ ω,
      gridDepth ω (0,0) (polarPair p.1 p.2) ∂squareLaw) :=
    hm.stronglyMeasurable.integral_prod_right
  exact hi.measurable.add measurable_fst

lemma polarPair_double (t θ : ℝ) : polarPair (t+Real.log 2) θ =
    (2*(polarPair t θ).1,2*(polarPair t θ).2) := by
  simp only [polarPair,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
  congr 1 <;> ring

lemma polarMean_period_angle (t : ℝ) : Function.Periodic (polarMean t) (2*Real.pi) := by
  intro θ
  simp only [polarMean,polarPair,Real.cos_periodic θ,Real.sin_periodic θ]

lemma uniformInterval_integral {l : ℝ} (hl : 0 < l) (f : ℝ → ℝ) :
    (∫ x, f x ∂uniformInterval l) = l⁻¹ * ∫ x in (0:ℝ)..l, f x := by
  rw [uniformInterval, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hl.le, smul_eq_mul, intervalIntegral.integral_of_le hl.le]

lemma uniformInterval_period_shift {l : ℝ} (hl : 0 < l) {f : ℝ → ℝ}
    (hf : Function.Periodic f l) (a : ℝ) :
    (∫ x, f (x+a) ∂uniformInterval l) = ∫ x, f x ∂uniformInterval l := by
  rw [uniformInterval_integral hl, uniformInterval_integral hl,
    intervalIntegral.integral_comp_add_right]
  congr 1
  simpa only [zero_add, add_comm l a] using hf.intervalIntegral_add_eq a 0

lemma uniformInterval_period_sub {l : ℝ} (hl : 0 < l) {f : ℝ → ℝ}
    (hf : Function.Periodic f l) (a : ℝ) :
    (∫ x, f (a-x) ∂uniformInterval l) = ∫ x, f (-x) ∂uniformInterval l := by
  have hp : Function.Periodic (fun x => f (-x)) l := by
    intro x
    simpa only [neg_add, sub_eq_add_neg] using hf.sub_eq (-x)
  have hh := uniformInterval_period_shift hl hp (-a)
  simpa only [neg_add, neg_neg, sub_eq_add_neg, add_comm] using hh

/-- The universal archimedean error mean, before any configuration is chosen. -/
def kappa : ℝ := ∫ ξ, ∫ θ, polarMean (-ξ) θ
  ∂uniformInterval (2*Real.pi) ∂uniformInterval (Real.log 2)

def rotateC (ξ θ : ℝ) (z : ℂ) : ℂ :=
  (Real.exp (-ξ) : ℂ) * Complex.exp ((θ : ℂ)*Complex.I) * z

def rotatePair (ξ θ : ℝ) (z : ℂ) : ℝ × ℝ :=
  ((rotateC ξ θ z).re, (rotateC ξ θ z).im)

lemma rotateC_sub (ξ θ : ℝ) (z w : ℂ) :
    rotateC ξ θ (z-w) = rotateC ξ θ z - rotateC ξ θ w := by
  exact mul_sub _ _ _

lemma norm_rotateC (ξ θ : ℝ) (z : ℂ) :
    ‖rotateC ξ θ z‖ = Real.exp (-ξ) * ‖z‖ := by
  simp only [rotateC, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp_ofReal_mul_I, mul_one]

lemma rotatePair_ne (ξ θ : ℝ) {z w : ℂ} (hne : z ≠ w) :
    rotatePair ξ θ z ≠ rotatePair ξ θ w := by
  intro he
  have h : rotateC ξ θ z = rotateC ξ θ w := Complex.ext
    (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hn := norm_rotateC ξ θ (z-w)
  rw [rotateC_sub, h, sub_self, norm_zero] at hn
  have hz : ‖z-w‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  exact (mul_ne_zero (Real.exp_ne_zero _) hz) hn.symm

lemma rotatePair_gaps (ξ θ : ℝ) (z w : ℂ) :
    Real.exp (-ξ)*‖z-w‖ ≤
      |(rotatePair ξ θ z).1-(rotatePair ξ θ w).1| +
      |(rotatePair ξ θ z).2-(rotatePair ξ θ w).2| ∧
    |(rotatePair ξ θ z).1-(rotatePair ξ θ w).1| +
      |(rotatePair ξ θ z).2-(rotatePair ξ θ w).2| ≤ 2*(Real.exp (-ξ)*‖z-w‖) := by
  have hh := Complex.norm_le_abs_re_add_abs_im (rotateC ξ θ (z-w))
  have hr := Complex.abs_re_le_norm (rotateC ξ θ (z-w))
  have hi := Complex.abs_im_le_norm (rotateC ξ θ (z-w))
  rw [norm_rotateC, rotateC_sub] at hh hr hi
  simp only [Complex.sub_re, Complex.sub_im] at hh hr hi
  exact ⟨hh, by dsimp only [rotatePair]; linarith⟩

lemma rotateC_polar (ξ θ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    rotateC ξ θ z = (Real.exp (Real.log ‖z‖-ξ) : ℂ) *
      Complex.exp (((θ+z.arg : ℝ) : ℂ)*Complex.I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add,
    Real.exp_sub, Real.exp_log (norm_pos_iff.mpr hz),
    div_eq_mul_inv, ← Real.exp_neg, Complex.ofReal_mul]
  calc
    _ = (Real.exp (-ξ) : ℂ) * Complex.exp ((θ:ℂ)*Complex.I) *
        ((‖z‖:ℂ) * Complex.exp ((z.arg:ℂ)*Complex.I)) := by
      rw [Complex.norm_mul_exp_arg_mul_I]
      rfl
    _ = _ := by ring

lemma exp_polarPair (t θ : ℝ) :
    ((Real.exp t : ℂ) * Complex.exp ((θ:ℂ)*Complex.I)).re = (polarPair t θ).1 ∧
    ((Real.exp t : ℂ) * Complex.exp ((θ:ℂ)*Complex.I)).im = (polarPair t θ).2 := by
  simp [polarPair, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]

abbrev FullSample := (ℝ × ℝ) × GridSample

def phaseLaw : Measure (ℝ × ℝ) :=
  (uniformInterval (Real.log 2)).prod (uniformInterval (2*Real.pi))

def fullLaw : Measure FullSample := phaseLaw.prod squareLaw

/-- Actual jointly defined hierarchy depth in the original complex plane. -/
def depth (ω : FullSample) (z w : ℂ) : ℝ :=
  gridDepth ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w) - ω.1.1

def error (ω : FullSample) (z w : ℂ) : ℝ := depth ω z w + Real.log ‖z-w‖

lemma measurable_rotatePair (z : ℂ) : Measurable (fun p : ℝ × ℝ => rotatePair p.1 p.2 z) := by
  unfold rotatePair rotateC
  fun_prop

lemma measurable_depth {z w : ℂ} (hne : z ≠ w) : Measurable (fun ω => depth ω z w) := by
  unfold depth
  exact (measurable_gridDepth_param measurable_snd
    ((measurable_rotatePair z).comp measurable_fst)
    ((measurable_rotatePair w).comp measurable_fst)
    (fun p => rotatePair_ne _ _ hne)).sub measurable_fst.fst

lemma measurable_error {z w : ℂ} (hne : z ≠ w) : Measurable (fun ω => error ω z w) :=
  (measurable_depth hne).add_const _

lemma error_fixed_phase {z w : ℂ} (hne : z ≠ w) (p : ℝ × ℝ) (ω : GridSample) :
    error (p,ω) z w = gridDepth ω (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w) +
      Real.log (Real.exp (-p.1)*‖z-w‖) := by
  rw [Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)), Real.log_exp]
  simp only [error, depth]
  ring

lemma measurable_shifted_polarMean (t φ : ℝ) :
    Measurable (fun p : ℝ × ℝ => polarMean (t-p.1) (p.2+φ)) := by
  have h₁ : Measurable (fun p : ℝ × ℝ => t-p.1) := measurable_const.sub measurable_fst
  have h₂ : Measurable (fun p : ℝ × ℝ => p.2+φ) := measurable_snd.add_const φ
  change Measurable ((fun p : ℝ × ℝ => polarMean p.1 p.2) ∘
    (fun p : ℝ × ℝ => (t-p.1,p.2+φ)))
  apply Measurable.comp measurable_polarMean
  exact h₁.prodMk h₂

lemma depth_symm (ω : FullSample) (z w : ℂ) : depth ω z w = depth ω w z := by
  simp only [depth,gridDepth,minScale_symm ω.2 (rotatePair ω.1.1 ω.1.2 z)
    (rotatePair ω.1.1 ω.1.2 w)]

end WeakPinned.Grid

end
end
end
end

end OAI
