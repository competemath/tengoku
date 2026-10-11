import Tengoku.OpenaiMath.OAI.Geometry.LatticeCovering.GridCounts

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section

namespace SingleLatticeCovering.SharpYoung

structure PositiveDensity where
  toFun : ℝ → ℝ
  continuous : Continuous toFun
  positive : ∀ x, 0 < toFun x
  integrable : Integrable toFun volume
  integral_one : ∫ x, toFun x = 1

instance : CoeFun PositiveDensity (fun _ => ℝ → ℝ) := ⟨PositiveDensity.toFun⟩

def densityCDF (f : PositiveDensity) (x : ℝ) : ℝ := ∫ t in Iic x, f t

lemma densityCDF_hasDerivAt (f : PositiveDensity) (x : ℝ) :
    HasDerivAt (densityCDF f) (f x) x := by
  have h := (intervalIntegral.integral_hasDerivAt_right
    (f.integrable.intervalIntegrable (a := 0) (b := x))
    (f.continuous.stronglyMeasurableAtFilter volume (𝓝 x)) f.continuous.continuousAt).const_add
      (densityCDF f 0)
  convert! h using 1
  funext u
  have hdiff := intervalIntegral.integral_Iic_sub_Iic
    (f.integrable.integrableOn (s := Iic 0)) (f.integrable.integrableOn (s := Iic u))
  dsimp [densityCDF] at *
  linarith

lemma densityCDF_continuous (f : PositiveDensity) : Continuous (densityCDF f) :=
  continuous_iff_continuousAt.mpr (fun x => (densityCDF_hasDerivAt f x).continuousAt)

lemma densityCDF_strictMono (f : PositiveDensity) : StrictMono (densityCDF f) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(densityCDF_hasDerivAt f x).deriv]
  exact f.positive x

lemma densityCDF_add_tail (f : PositiveDensity) (x : ℝ) :
    densityCDF f x + (∫ t in Ioi x, f t) = 1 := by
  simpa [densityCDF, f.integral_one] using integral_add_compl measurableSet_Iic f.integrable

lemma densityCDF_mem_Ioo (f : PositiveDensity) (x : ℝ) : densityCDF f x ∈ Ioo 0 1 := by
  have hnonneg (y : ℝ) : 0 ≤ densityCDF f y := integral_nonneg (fun t => (f.positive t).le)
  have hle (y : ℝ) : densityCDF f y ≤ 1 := by
    have ht : 0 ≤ ∫ t in Ioi y, f t := integral_nonneg (fun t => (f.positive t).le)
    linarith [densityCDF_add_tail f y]
  constructor
  · exact lt_of_le_of_lt (hnonneg (x-1)) (densityCDF_strictMono f (by linarith))
  · exact lt_of_lt_of_le (densityCDF_strictMono f (show x < x+1 by linarith)) (hle (x+1))

lemma densityCDF_tendsto_bot (f : PositiveDensity) :
    Tendsto (densityCDF f) atBot (𝓝 0) := tendsto_integral_Iic_zero tendsto_id

lemma densityCDF_tendsto_top (f : PositiveDensity) :
    Tendsto (densityCDF f) atTop (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => 1 - ∫ t in Ioi x, f t) atTop (𝓝 (1-0)) :=
    tendsto_const_nhds.sub (tendsto_integral_Ioi_zero tendsto_id)
  convert h using 1
  · funext x
    linarith [densityCDF_add_tail f x]
  · norm_num

lemma densityCDF_surjOn (f : PositiveDensity) :
    SurjOn (densityCDF f) univ (Ioo 0 1) := by
  exact isPreconnected_univ.intermediate_value_Ioo (by simp) (by simp)
    (densityCDF_continuous f).continuousOn (densityCDF_tendsto_bot f) (densityCDF_tendsto_top f)

def densityCDFIso (f : PositiveDensity) : ℝ ≃o Ioo (0 : ℝ) 1 :=
  StrictMono.orderIsoOfSurjective (fun x => ⟨densityCDF f x, densityCDF_mem_Ioo f x⟩)
    (fun _ _ h => densityCDF_strictMono f h)
    (fun y => by
      obtain ⟨x, _, hx⟩ := densityCDF_surjOn f y.property
      exact ⟨x, Subtype.ext hx⟩)

@[simp] lemma densityCDFIso_apply (f : PositiveDensity) (x : ℝ) :
    (densityCDFIso f x : ℝ) = densityCDF f x := rfl

def densityTransport (f g : PositiveDensity) : ℝ ≃o ℝ :=
  (densityCDFIso f).trans (densityCDFIso g).symm

lemma densityCDF_transport (f g : PositiveDensity) (x : ℝ) :
    densityCDF g (densityTransport f g x) = densityCDF f x := by
  change ((densityCDFIso g) ((densityCDFIso g).symm (densityCDFIso f x)) : ℝ) = _
  simp

lemma densityTransport_hasDerivAt (f g : PositiveDensity) (x : ℝ) :
    HasDerivAt (densityTransport f g) (f x / g (densityTransport f g x)) x := by
  apply HasDerivAt.of_comp_left (densityTransport f g).continuous.continuousAt
    (densityCDF_hasDerivAt g _) (densityCDF_hasDerivAt f x) (ne_of_gt (g.positive _))
  exact Filter.Eventually.of_forall (densityCDF_transport f g)

def normalizedGaussianDensity : PositiveDensity where
  toFun := fun x => Real.exp (-x^2) / Real.sqrt Real.pi
  continuous := by fun_prop
  positive := fun x => div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr Real.pi_pos)
  integrable := by
    have h := integrable_exp_neg_mul_sq (show (0:ℝ) < 1 by norm_num)
    simpa using h.div_const (Real.sqrt Real.pi)
  integral_one := by
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const]
    have h := integral_gaussian (1 : ℝ)
    simp only [neg_mul, one_mul, div_one] at h
    rw [h, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))]

lemma gaussian_transport_density (f : PositiveDensity) (x : ℝ) :
    Real.exp (-(densityTransport f normalizedGaussianDensity x)^2) *
      (f x / normalizedGaussianDensity (densityTransport f normalizedGaussianDensity x)) =
      Real.sqrt Real.pi * f x := by
  change Real.exp _ * (f x / (Real.exp _ / Real.sqrt Real.pi)) = _
  field_simp

end SingleLatticeCovering.SharpYoung

namespace SingleLatticeCovering.SimplexYoung
open SingleLatticeCovering.SharpYoung
open MeasureTheory Filter Set
open scoped Topology ENNReal

def simplexConstant (r : ℕ) : ℝ :=
  (Real.sqrt ((r:ℝ)/(r+1:ℕ)))⁻¹^r / Real.sqrt (r+1:ℕ)

lemma simplexConstant_nonneg (r : ℕ) : 0 ≤ simplexConstant r := by
  unfold simplexConstant; positivity

lemma simplex_positiveDensity_integral {r : ℕ} (hr : 0 < r)
    (f : Fin (r+1) → PositiveDensity) :
    (∫⁻ x : V r, ENNReal.ofReal (∏ i, (f i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)))) ≤
      ENNReal.ofReal (simplexConstant r) := by
  let T (i : Fin (r+1)) := densityTransport (f i) normalizedGaussianDensity
  let T' (i : Fin (r+1)) (t : ℝ) := f i t / normalizedGaussianDensity (T i t)
  have ht := simplex_transport_integral hr (T := fun i => T i) (T' := T')
    (fun i => (T i).strictMono) (fun i => densityTransport_hasDerivAt (f i) _)
    (fun i t => div_pos ((f i).positive t) (normalizedGaussianDensity.positive _))
  have hpoint (x : V r) :
      (∏ i, (Real.exp (-(T i (simplexForm i x))^2) * T' i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ))) =
        (Real.sqrt Real.pi)^r * ∏ i, (f i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)) := by
    change (∏ i, (Real.exp (-(densityTransport (f i) normalizedGaussianDensity
      (simplexForm i x))^2) * (f i (simplexForm i x) /
      normalizedGaussianDensity (densityTransport (f i) normalizedGaussianDensity
        (simplexForm i x)))) ^ ((r:ℝ)/(r+1:ℕ))) = _
    simp_rw [gaussian_transport_density,
      Real.mul_rpow (Real.sqrt_nonneg _) ((f _).positive _).le]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [←Real.rpow_natCast, ←Real.rpow_mul (Real.sqrt_nonneg _), div_mul_cancel₀ _ (by positivity : (r+1:ℕ) ≠ (0:ℝ)), Real.rpow_natCast]
  simp_rw [hpoint, ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg _) r)] at ht
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at ht
  have hp : 0 < (Real.sqrt Real.pi)^r := pow_pos (Real.sqrt_pos.mpr Real.pi_pos) r
  have hh : (∫⁻ x : V r, ENNReal.ofReal (∏ i, (f i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)))) ≤
      ENNReal.ofReal ((Real.sqrt (Real.pi/((r:ℝ)/(r+1:ℕ))))^r / Real.sqrt (r+1:ℕ)) /
        ENNReal.ofReal ((Real.sqrt Real.pi)^r) :=
    (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hp)))
      (Or.inl ENNReal.ofReal_ne_top)).mpr (by rw [mul_comm]; exact ht)
  rw [←ENNReal.ofReal_div_of_pos hp] at hh
  have he : ((Real.sqrt (Real.pi/((r:ℝ)/(r+1:ℕ))))^r / Real.sqrt (r+1:ℕ)) /
      (Real.sqrt Real.pi)^r = simplexConstant r := by
    unfold simplexConstant
    rw [Real.sqrt_div Real.pi_pos.le, div_pow]
    have hc : 0 < Real.sqrt ((r:ℝ)/(r+1:ℕ)) := by positivity
    field_simp [hc.ne']
    simp only [←mul_pow, one_div, mul_inv_cancel₀ hc.ne', one_pow]
  simpa only [he] using hh
lemma integral_pos_of_continuous_density {f : ℝ → ℝ}
    (hp : ∀ x, 0 < f x) (hi : Integrable f volume) : 0 < ∫ x, f x := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le) hi).mpr
  have he : Function.support f = univ := by
    ext x
    simp [Function.mem_support, ne_of_gt (hp x)]
  rw [he]
  simp

def normalizePositiveDensity (f : ℝ → ℝ) (hc : Continuous f) (hp : ∀ x, 0 < f x)
    (hi : Integrable f volume) : PositiveDensity where
  toFun := fun x => f x / ∫ t, f t
  continuous := hc.div_const _
  positive := fun x => div_pos (hp x) (integral_pos_of_continuous_density hp hi)
  integrable := hi.div_const _
  integral_one := by
    rw [integral_div, div_self (ne_of_gt (integral_pos_of_continuous_density hp hi))]

lemma simplex_positive_integral {r : ℕ} (hr : 0 < r) (f : Fin (r+1) → ℝ → ℝ)
    (hc : ∀ i, Continuous (f i)) (hp : ∀ i x, 0 < f i x)
    (hi : ∀ i, Integrable (f i) volume) :
    (∫⁻ x : V r, ENNReal.ofReal (∏ i, (f i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)))) ≤
      ENNReal.ofReal (simplexConstant r * ∏ i, (∫ t, f i t) ^ ((r:ℝ)/(r+1:ℕ))) := by
  let g (i : Fin (r+1)) := normalizePositiveDensity (f i) (hc i) (hp i) (hi i)
  have hmass (i : Fin (r+1)) := integral_pos_of_continuous_density (hp i) (hi i)
  have he (i : Fin (r+1)) (x : ℝ) : f i x = (∫ t, f i t) * g i x := by
    dsimp [g, normalizePositiveDensity]
    field_simp [ne_of_gt (hmass i)]
  have hpoint (x : V r) : (∏ i, (f i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ))) =
      (∏ i, (∫ t, f i t) ^ ((r:ℝ)/(r+1:ℕ))) * ∏ i, (g i (simplexForm i x)) ^ ((r:ℝ)/(r+1:ℕ)) := by
    conv_lhs => arg 2; ext i; rw [he i (simplexForm i x)]
    simp_rw [Real.mul_rpow (hmass _).le ((g _).positive _).le]
    rw [Finset.prod_mul_distrib]
  have hn : 0 ≤ ∏ i, (∫ t, f i t) ^ ((r:ℝ)/(r+1:ℕ)) :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hmass i).le _)
  simp_rw [hpoint, ENNReal.ofReal_mul hn]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ENNReal.ofReal_mul (simplexConstant_nonneg r)]
  rw [mul_comm (ENNReal.ofReal (simplexConstant r))]
  exact mul_le_mul' le_rfl (simplex_positiveDensity_integral hr g)

end SingleLatticeCovering.SimplexYoung

open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
namespace SingleLatticeCovering.SharpYoung

lemma continuous_finTail {d : ℕ} {E : Type*} [TopologicalSpace E] :
    Continuous (Fin.tail : (Fin (d+1) → E) → (Fin d → E)) := by
  exact continuous_pi (fun j => continuous_apply j.succ)

lemma hasCompactSupport_finCons {d : ℕ} {f : (Fin (d+1) → ℝ) → ℝ}
    (hf : HasCompactSupport f) :
    HasCompactSupport (fun p : ℝ × (Fin d → ℝ) => f (Fin.cons p.1 p.2)) := by
  apply HasCompactSupport.intro
    (hf.isCompact.image ((continuous_apply 0).prodMk continuous_finTail))
  intro p hp
  by_contra hn
  apply hp
  refine ⟨Fin.cons p.1 p.2, subset_tsupport f hn, ?_⟩
  simp

lemma hasCompactSupport_finSlice {d : ℕ} {f : (Fin (d+1) → ℝ) → ℝ}
    (hf : HasCompactSupport f) (y : Fin d → ℝ) :
    HasCompactSupport (fun t : ℝ => f (Fin.cons t y)) := by
  apply HasCompactSupport.intro (hf.isCompact.image (continuous_apply 0))
  intro t ht
  by_contra hn
  exact ht ⟨Fin.cons t y, subset_tsupport f hn, by simp⟩

def finMarginal {d : ℕ} (f : (Fin (d+1) → ℝ) → ℝ) (y : Fin d → ℝ) : ℝ :=
  ∫ t : ℝ, f (Fin.cons t y)

lemma hasCompactSupport_finMarginal {d : ℕ} {f : (Fin (d+1) → ℝ) → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (finMarginal f) := by
  apply HasCompactSupport.intro (hf.isCompact.image continuous_finTail)
  intro y hy
  have hz (t : ℝ) : f (Fin.cons t y) = 0 := by
    by_contra hn
    exact hy ⟨Fin.cons t y, subset_tsupport f hn, by simp⟩
  simp [finMarginal, hz]

lemma continuous_finMarginal {d : ℕ} {f : (Fin (d+1) → ℝ) → ℝ}
    (hc : Continuous f) (hk : HasCompactSupport f) : Continuous (finMarginal f) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (hk.isCompact.image (continuous_apply 0))
  · exact (hc.comp (continuous_snd.finCons continuous_fst)).continuousOn
  · intro y t _ ht
    by_contra hn
    exact ht ⟨Fin.cons t y, subset_tsupport f hn, by simp⟩

lemma finMarginal_nonneg {d : ℕ} {f : (Fin (d+1) → ℝ) → ℝ}
    (hf : 0 ≤ f) : 0 ≤ finMarginal f := fun y => integral_nonneg (fun t => hf (Fin.cons t y))

lemma integral_finMarginal {d : ℕ} {f : (Fin (d+1) → ℝ) → ℝ}
    (hc : Continuous f) (hk : HasCompactSupport f) :
    ∫ y, finMarginal f y = ∫ x, f x := by
  have hm := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm
  have he := hm.integral_comp' f
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero] at he
  rw [← he]
  symm
  exact integral_prod_symm (fun p : ℝ × (Fin d → ℝ) => f (Fin.cons p.1 p.2))
    ((hc.comp (continuous_fst.finCons continuous_snd)).integrable_of_hasCompactSupport
      (hasCompactSupport_finCons hk))

lemma lintegral_finCons {d : ℕ} {E : Type*} [MeasureSpace E]
    [SigmaFinite (volume : Measure E)]
    (f : (Fin (d+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ y : Fin d → E, ∫⁻ t : E, f (Fin.cons t y) := by
  have hm := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => E) 0).symm
  have he := hm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero] at he
  rw [← he]
  apply lintegral_prod_symm _
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero, Function.comp_def, Fin.consEquiv_apply] using
    (hf.comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => E) 0).symm.measurable).aemeasurable

end SingleLatticeCovering.SharpYoung

namespace SingleLatticeCovering.SimplexYoung
open SingleLatticeCovering.SharpYoung
open MeasureTheory Filter Set
open scoped Topology ENNReal
def simplexSpatial {r d : ℕ} (i : Fin (r+1)) (x : Fin d → V r) : Fin d → ℝ :=
  fun j => simplexForm i (x j)

lemma continuous_simplexSpatial {r d : ℕ} (i : Fin (r+1)) :
    Continuous (simplexSpatial (d := d) i) := by
  exact continuous_pi (fun j => (simplexForm i).continuous_of_finiteDimensional.comp
    (continuous_apply j))

lemma simplexSpatial_cons {r d : ℕ} (i : Fin (r+1)) (t : V r) (x : Fin d → V r) :
    simplexSpatial i (Fin.cons t x) = Fin.cons (simplexForm i t) (simplexSpatial i x) := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [simplexSpatial]

end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Filter Set
open scoped Topology ENNReal

def simplexConfiguration {r d : ℕ} (J : Fin (r+1) → Set (Fin d → ℝ)) :
    Set (Fin d → V r) := {x | ∀ i, simplexSpatial i x ∈ J i}

lemma simplexConfiguration_measurable {r d : ℕ} {J : Fin (r+1) → Set (Fin d → ℝ)}
    (hJ : ∀ i, MeasurableSet (J i)) : MeasurableSet (simplexConfiguration J) := by
  unfold simplexConfiguration
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (hJ i).preimage (continuous_simplexSpatial i).measurable

end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Measure Set Matrix
open scoped ENNReal Pointwise

def weightedSimplexConfiguration {r d : ℕ} (J : Set (Fin d → ℝ))
    (c : Fin r → ℝ) : Set (Fin d → V r) :=
  {x | (∀ j, (fun a => x a j) ∈ J) ∧ (fun a => ∑ j, c j * x a j) ∈ J}

def simplexDiagonal {r d : ℕ} (c : Fin r → ℝ) :
    (Fin d → V r) →ₗ[ℝ] (Fin d → V r) :=
  LinearMap.pi (fun a : Fin d => (Matrix.diagonal c).mulVecLin.comp (LinearMap.proj a))

lemma simplexDiagonal_apply {r d : ℕ} (c : Fin r → ℝ) (x : Fin d → V r)
    (a : Fin d) (j : Fin r) : simplexDiagonal c x a j = c j * x a j := by
  simp [simplexDiagonal, Matrix.mulVec_diagonal]

lemma simplexDiagonal_det {r d : ℕ} (c : Fin r → ℝ) :
    LinearMap.det (simplexDiagonal (d := d) c) = (∏ j, c j)^d := by
  unfold simplexDiagonal
  rw [LinearMap.det_pi]
  have h : LinearMap.det (Matrix.diagonal c).mulVecLin = ∏ j, c j := by
    rw [←Matrix.toLin'_apply', LinearMap.det_toLin', Matrix.det_diagonal]
  simp [h]

def scaledCircuitFamily {r d : ℕ} (J : Set (Fin d → ℝ)) (c : Fin r → ℝ) :
    Fin (r+1) → Set (Fin d → ℝ) := Fin.cons ((-1:ℝ) • J) (fun j => c j • J)

lemma scaledCircuitFamily_compact {r d : ℕ} {J : Set (Fin d → ℝ)}
    (hJ : IsCompact J) (c : Fin r → ℝ) (i : Fin (r+1)) :
    IsCompact (scaledCircuitFamily J c i) := by
  refine Fin.cases ?_ (fun j => ?_) i <;>
    exact hJ.image (by fun_prop)

lemma weightedSimplexConfiguration_preimage {r d : ℕ} (J : Set (Fin d → ℝ))
    (c : Fin r → ℝ) (hc : ∀ j, c j ≠ 0) :
    weightedSimplexConfiguration J c =
      simplexDiagonal c ⁻¹' simplexConfiguration (scaledCircuitFamily J c) := by
  ext x
  change (_ ∧ _) ↔ ∀ i, simplexSpatial i (simplexDiagonal c x) ∈ scaledCircuitFamily J c i
  rw [Fin.forall_fin_succ]
  have h0 : simplexSpatial 0 (simplexDiagonal c x) =
      (-1:ℝ) • (fun a => ∑ j, c j * x a j) := by
    ext a
    simp [simplexSpatial, simplexForm_zero, simplexDiagonal_apply]
  have hs (j : Fin r) : simplexSpatial j.succ (simplexDiagonal c x) =
      c j • (fun a => x a j) := by
    ext a
    simp [simplexSpatial, simplexForm_succ, simplexDiagonal_apply]
  simp only [scaledCircuitFamily, Fin.cons_zero, Fin.cons_succ, h0, hs,
    smul_mem_smul_set_iff₀ (by norm_num : (-1:ℝ) ≠ 0), smul_mem_smul_set_iff₀ (hc _)]
  exact and_comm

lemma volume_scaledCircuitFamily {r d : ℕ} (J : Set (Fin d → ℝ)) (c : Fin r → ℝ) :
    (volume (scaledCircuitFamily J c 0)).toReal = (volume J).toReal ∧
      ∀ j, (volume (scaledCircuitFamily J c j.succ)).toReal =
        |c j|^d * (volume J).toReal := by
  constructor
  · simp [scaledCircuitFamily]
  · intro j
    simp [scaledCircuitFamily, Measure.addHaar_smul, abs_pow,
      ENNReal.toReal_mul]

end SingleLatticeCovering.SimplexYoung

noncomputable section
namespace SingleLatticeCovering.SimplexYoung
open scoped BigOperators

lemma weightedCircuitFactor {r d : ℕ} (hr : 0 < r) (a : Fin r → ℝ)
    (ha : ∀ j, 0 < a j) (u C : ℝ) (hu : 0 ≤ u) :
    (∏ j, a j)⁻¹^d * C^d *
        (u^((r:ℝ)/(r+1:ℕ)) * ∏ j, (a j^d*u)^((r:ℝ)/(r+1:ℕ))) =
      C^d * (∏ j, a j^(-((d:ℝ)/(r+1:ℕ)))) * u^r := by
  have hn : (r+1:ℝ) ≠ 0 := by positivity
  have hp : 0 < (r:ℝ)/(r+1:ℕ) := div_pos (by exact_mod_cast hr) (by positivity)
  by_cases hz : u = 0
  · rw [hz, Real.zero_rpow hp.ne', zero_mul, mul_zero, zero_pow hr.ne', mul_zero]
  have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
  let p : ℝ := (r:ℝ)/(r+1:ℕ)
  change _ * _ * (u^p * ∏ j, (a j^d*u)^p) = _
  have hdist (j : Fin r) : (a j^d*u)^p = (a j)^(d*p) * u^p := by
    rw [Real.mul_rpow (pow_nonneg (ha j).le _) hu, ←Real.rpow_natCast, ←Real.rpow_mul (ha j).le]
  simp_rw [hdist]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have he : p*(r+1:ℕ) = (r:ℝ) := by
    dsimp [p]; exact div_mul_cancel₀ _ (by positivity)
  have huPow : u^p*(u^p)^r = u^r := by
    rw [←pow_succ', ←Real.rpow_natCast, ←Real.rpow_mul hu, he, Real.rpow_natCast]
  have hprod : (∏ j, a j)⁻¹^d * (∏ j, (a j)^((d:ℝ)*p)) =
      ∏ j, a j^(-((d:ℝ)/(r+1:ℕ))) := by
    rw [←Finset.prod_inv_distrib, ←Finset.prod_pow, ←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [←Real.rpow_natCast, ←Real.rpow_neg_one, ←Real.rpow_mul (ha j).le,
      ←Real.rpow_add (ha j)]
    congr 1
    dsimp [p]
    push_cast
    field_simp
    ring
  calc
    _ = C^d * ((∏ j, a j)⁻¹^d * (∏ j, (a j)^((d:ℝ)*p))) * (u^p*(u^p)^r) := by ring
    _ = _ := by rw [hprod, huPow]

end SingleLatticeCovering.SimplexYoung

end
end
end
end
end
end
end

end OAI
