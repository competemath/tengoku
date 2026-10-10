import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.LogIncrement

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def orientedDifference (positive : Bool) (a z : ℂ) : ℂ :=
  if positive then z-a else conj (z-a)

@[simp] lemma norm_orientedDifference (p : Bool) (a z : ℂ) :
    ‖orientedDifference p a z‖ = ‖z-a‖ := by cases p <;> simp only [orientedDifference, Bool.false_eq_true, ↓reduceIte, RCLike.norm_conj]

@[simp] lemma orientedDifference_eq_zero (p : Bool) (a z : ℂ) :
    orientedDifference p a z = 0 ↔ z = a := by
  rw [← norm_eq_zero, norm_orientedDifference, norm_eq_zero, sub_eq_zero]

lemma continuous_orientedDifference (p : Bool) (a : ℂ) :
    Continuous (orientedDifference p a) := by
  unfold orientedDifference
  cases p <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

def radialCutoff (a : ℂ) (r : ℝ) (z : ℂ) : ℝ :=
  max 0 (min 1 (2-2*‖z-a‖/r))

lemma continuous_radialCutoff (a : ℂ) (r : ℝ) : Continuous (radialCutoff a r) := by
  unfold radialCutoff
  fun_prop

lemma radialCutoff_one {a z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z-a‖ ≤ r/2) :
    radialCutoff a r z = 1 := by
  have hb : 2*‖z-a‖/r ≤ 1 := (div_le_iff₀ hr).mpr (by linarith)
  simp [radialCutoff, min_eq_left (by linarith : 1 ≤ 2-2*‖z-a‖/r)]

lemma radialCutoff_zero {a z : ℂ} {r : ℝ} (hr : 0 < r) (hz : r ≤ ‖z-a‖) :
    radialCutoff a r z = 0 := by
  rw [radialCutoff, max_eq_left]
  apply min_le_of_right_le
  rw [sub_nonpos, le_div_iff₀ hr]
  linarith

def surgeryLog (X : ℂ → ℂ) (p : Bool) (a c : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  (radialCutoff a r z : ℂ) * Complex.log (X z / (c*orientedDifference p a z))

lemma continuousAt_surgeryLog {X : ℂ → ℂ} (hX : Continuous X)
    {p : Bool} {a c z : ℂ} {r : ℝ} (hr : 0 < r) (hc : c ≠ 0) (hz : z ≠ a)
    (hlocal : ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
      X w / (c*orientedDifference p a w) ∈ Complex.slitPlane) :
    ContinuousAt (surgeryLog X p a c r) z := by
  by_cases hb : ‖z-a‖ < 2*r
  · apply (Complex.continuous_ofReal.comp (continuous_radialCutoff a r)).continuousAt.mul
    apply ContinuousAt.clog
    · exact hX.continuousAt.div
        (continuous_const.mul (continuous_orientedDifference p a)).continuousAt
        (mul_ne_zero hc (mt (orientedDifference_eq_zero p a z).mp hz))
    · exact hlocal z hb hz
  · have hlt : r < ‖z-a‖ := by linarith
    have he : surgeryLog X p a c r =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [((show ContinuousAt (fun w : ℂ => ‖w-a‖) z by fun_prop).eventually
        (Ioi_mem_nhds hlt))] with w hw
      simp [surgeryLog, radialCutoff_zero hr (le_of_lt hw)]
    exact continuousAt_const.congr he.symm

lemma surgeryLog_eq_zero_eventually {X : ℂ → ℂ} {p : Bool} {a c z : ℂ} {r : ℝ}
    (hr : 0 < r) (hz : r < ‖z-a‖) : surgeryLog X p a c r =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [((show ContinuousAt (fun w : ℂ => ‖w-a‖) z by fun_prop).eventually
    (Ioi_mem_nhds hz))] with w hw
  simp [surgeryLog, radialCutoff_zero hr (le_of_lt hw)]

def removeZero (X : ℂ → ℂ) (p : Bool) (a c : ℂ) (r : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if z = a then c else X z / orientedDifference p a z *
    Complex.exp (-surgeryLog X p a c r z)

lemma removeZero_eq_const_near {X : ℂ → ℂ} {p : Bool} {a c z : ℂ} {r : ℝ}
    (hr : 0 < r) (hc : c ≠ 0) (hz : ‖z-a‖ < r/2)
    (hlocal : ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
      X w / (c*orientedDifference p a w) ∈ Complex.slitPlane) :
    removeZero X p a c r z = c := by
  classical
  by_cases hza : z = a
  · simp [removeZero,hza]
  · have hd : orientedDifference p a z ≠ 0 := mt (orientedDifference_eq_zero p a z).mp hza
    have hslit := hlocal z (by linarith) hza
    have hx : X z ≠ 0 := by
      intro hx
      simpa [hx] using Complex.slitPlane_ne_zero hslit
    simp only [removeZero, ite_eq_right hza, surgeryLog, radialCutoff_one hr hz.le,
      Complex.ofReal_one, one_mul, Complex.exp_neg,
      Complex.exp_log (Complex.slitPlane_ne_zero hslit)]
    field_simp

lemma continuous_removeZero {X : ℂ → ℂ} (hX : Continuous X)
    {p : Bool} {a c : ℂ} {r : ℝ} (hr : 0 < r) (hc : c ≠ 0)
    (hlocal : ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
      X w / (c*orientedDifference p a w) ∈ Complex.slitPlane) :
    Continuous (removeZero X p a c r) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = a
  · subst z
    have he : removeZero X p a c r =ᶠ[𝓝 a] fun _ => c := by
      filter_upwards [Metric.ball_mem_nhds a (by positivity : 0 < r/2)] with w hw
      exact removeZero_eq_const_near hr hc (by simpa [Metric.mem_ball,dist_eq_norm] using hw) hlocal
    exact continuousAt_const.congr he.symm
  · have he : removeZero X p a c r =ᶠ[𝓝 z] fun w =>
        X w / orientedDifference p a w * Complex.exp (-surgeryLog X p a c r w) := by
      filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz] with w hw
      have hwn : w ≠ a := hw
      simp [removeZero,hwn]
    apply ContinuousAt.congr ?_ he.symm
    exact (hX.continuousAt.div (continuous_orientedDifference p a).continuousAt
      (mt (orientedDifference_eq_zero p a z).mp hz)).mul
      ((continuousAt_surgeryLog hX hr hc hz hlocal).neg.cexp)

lemma removeZero_eq_zero_iff {X : ℂ → ℂ} {p : Bool} {a c z : ℂ} {r : ℝ}
    (hc : c ≠ 0) : removeZero X p a c r z = 0 ↔ X z = 0 ∧ z ≠ a := by
  classical
  by_cases hz : z = a
  · simp [removeZero,hz,hc]
  · simp [removeZero,hz,div_eq_zero_iff,
      mt (orientedDifference_eq_zero p a z).mp hz,Complex.exp_ne_zero]

lemma removeZero_factorization {X : ℂ → ℂ} {p : Bool} {a c z : ℂ} {r : ℝ}
    (hz : z ≠ a) : X z = orientedDifference p a z * removeZero X p a c r z *
      Complex.exp (surgeryLog X p a c r z) := by
  classical
  have hd : orientedDifference p a z ≠ 0 := mt (orientedDifference_eq_zero p a z).mp hz
  simp only [removeZero,ite_eq_right hz,Complex.exp_neg]
  field_simp

lemma exists_slit_radius_of_derivative {X : ℂ → ℂ} {a c : ℂ} {A : ℂ →L[ℝ] ℂ}
    {p : Bool} (hzero : X a = 0) (hd : HasFDerivAt X A a)
    {b : ℝ} (hb : b < ‖c‖)
    (herr : ∀ w : ℂ, ‖A w-c*orientedDifference p 0 w‖ ≤ b*‖w‖) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
      X w / (c*orientedDifference p a w) ∈ Complex.slitPlane := by
  have hrem := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hd).bound
    (by linarith : 0 < (‖c‖-b)/2)
  obtain ⟨δ,hδ,hbound⟩ := Metric.eventually_nhds_iff.mp hrem
  refine ⟨δ/3, by positivity, fun w hw hwa => ?_⟩
  have hwn : 0 < ‖w-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwa)
  have hremw := hbound (show dist (w-a) 0 < δ by simpa only [dist_zero_right] using (show ‖w-a‖ < δ by linarith))
  simp only [add_sub_cancel, hzero, sub_zero] at hremw
  have her := herr (w-a)
  have he : orientedDifference p 0 (w-a) = orientedDifference p a w := by
    simp [orientedDifference]
  rw [he] at her
  have hlt : ‖X w-c*orientedDifference p a w‖ < ‖c*orientedDifference p a w‖ := by
    calc
      ‖X w-c*orientedDifference p a w‖ =
          ‖(X w-A (w-a))+(A (w-a)-c*orientedDifference p a w)‖ := by congr 1; ring
      _ ≤ ‖X w-A (w-a)‖+‖A (w-a)-c*orientedDifference p a w‖ := norm_add_le _ _
      _ ≤ (‖c‖-b)/2*‖w-a‖+b*‖w-a‖ := add_le_add hremw her
      _ < ‖c*orientedDifference p a w‖ := by
        rw [norm_mul,norm_orientedDifference]
        nlinarith
  have hcn : c*orientedDifference p a w ≠ 0 :=
    norm_pos_iff.mp ((norm_nonneg _).trans_lt hlt)
  have hratio : X w/(c*orientedDifference p a w) =
      1 + (X w-c*orientedDifference p a w)/(c*orientedDifference p a w) := by
    field_simp [left_ne_zero_of_mul hcn, right_ne_zero_of_mul hcn]
    ring
  rw [hratio]
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [norm_div,div_lt_one (norm_pos_iff.mpr hcn)]
  exact hlt

lemma exists_slit_radius_pos {X : ℂ → ℂ} {a : ℂ} {A : ℂ →L[ℝ] ℂ}
    (hzero : X a = 0) (hd : HasFDerivAt X A a)
    (hdet : 0 < LinearMap.det A.toLinearMap) :
    linearPart A ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
      X w / (linearPart A*orientedDifference true a w) ∈ Complex.slitPlane := by
  have hn : ‖antiLinearPart A‖ < ‖linearPart A‖ := by
    rw [det_eq_linearParts] at hdet
    nlinarith [norm_nonneg (linearPart A),norm_nonneg (antiLinearPart A)]
  refine ⟨norm_pos_iff.mp ((norm_nonneg _).trans_lt hn),
    exists_slit_radius_of_derivative hzero hd hn ?_⟩
  intro w
  simp [realLinear_decomposition,orientedDifference]

lemma exists_slit_radius_neg {X : ℂ → ℂ} {a : ℂ} {A : ℂ →L[ℝ] ℂ}
    (hzero : X a = 0) (hd : HasFDerivAt X A a)
    (hdet : LinearMap.det A.toLinearMap < 0) :
    antiLinearPart A ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
      X w / (antiLinearPart A*orientedDifference false a w) ∈ Complex.slitPlane := by
  have hn : ‖linearPart A‖ < ‖antiLinearPart A‖ := by
    rw [det_eq_linearParts] at hdet
    nlinarith [norm_nonneg (linearPart A),norm_nonneg (antiLinearPart A)]
  refine ⟨norm_pos_iff.mp ((norm_nonneg _).trans_lt hn),
    exists_slit_radius_of_derivative hzero hd hn ?_⟩
  intro w
  simp [realLinear_decomposition,orientedDifference]

lemma differentiable_orientedDifference (p : Bool) (a : ℂ) :
    Differentiable ℝ (orientedDifference p a) := by
  unfold orientedDifference
  cases p <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact Complex.conjCLE.differentiable.comp (differentiable_id.sub_const a)
  · exact differentiable_id.sub_const a

lemma hasFDerivAt_removeZero_other {X : ℂ → ℂ} {p : Bool} {a b c : ℂ} {r : ℝ}
    (hr : 0 < r) (hb : b ≠ a) (hzero : X b = 0) {A : ℂ →L[ℝ] ℂ}
    (hX : HasFDerivAt X A b)
    (hlocal : ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
      X w / (c*orientedDifference p a w) ∈ Complex.slitPlane) :
    HasFDerivAt (removeZero X p a c r) ((orientedDifference p a b)⁻¹ • A) b := by
  have hbfar : r < ‖b-a‖ := by
    by_contra hn
    have he := Complex.slitPlane_ne_zero (hlocal b (by linarith) hb)
    simp [hzero] at he
  have he : removeZero X p a c r =ᶠ[𝓝 b] fun w => X w * (orientedDifference p a w)⁻¹ := by
    filter_upwards [surgeryLog_eq_zero_eventually (X := X) (p := p) (c := c) hr hbfar,
      isClosed_singleton.isOpen_compl.mem_nhds hb] with w hw hwa
    have hwn : w ≠ a := hwa
    simp [removeZero,hwn,hw,div_eq_mul_inv]
  have hdn : orientedDifference p a b ≠ 0 := mt (orientedDifference_eq_zero p a b).mp hb
  have hinv := ((hasDerivAt_inv hdn).hasFDerivAt.restrictScalars ℝ).comp b
    ((differentiable_orientedDifference p a b).hasFDerivAt)
  have hm := hX.fun_mul hinv
  simp only [hzero,zero_smul,zero_add] at hm
  exact hm.congr_of_eventuallyEq he

lemma det_complex_smul (c : ℂ) (A : ℂ →L[ℝ] ℂ) :
    LinearMap.det (c • A).toLinearMap = ‖c‖^2 * LinearMap.det A.toLinearMap := by
  rw [determinant_complex_real,determinant_complex_real,← Complex.normSq_eq_norm_sq]
  simp only [ContinuousLinearMap.coe_coe,smul_apply,smul_eq_mul,
    Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
  ring

lemma windingNumber_comp_zero_of_nonvanishing (X : C(ℂ,ℂ)) (hX : ∀ z, X z ≠ 0)
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    windingNumber (X.comp γ) = 0 := by
  obtain ⟨B,hB⟩ := exists_log_lift_of_simplyConnected (0 : ℂ) X hX
  apply windingNumber_eq_of_logIncrement (by simp [hloop])
  simpa using HasLogIncrement.of_global_log X B hB γ hloop

lemma windingNumber_comp_zero_on_convex (X : C(ℂ,ℂ)) {K : Set ℂ}
    (hK : Convex ℝ K) (hX : ∀ z ∈ K, X z ≠ 0)
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ∈ K) :
    windingNumber (X.comp γ) = 0 := by
  let := hK.contractibleSpace ⟨γ 0,hγ 0⟩
  let := hK.locallyPathConnectedSpace
  let XK : C(K,ℂ) := ⟨fun z => X z, by fun_prop⟩
  obtain ⟨B,hB⟩ := exists_log_lift_of_simplyConnected (⟨γ 0,hγ 0⟩ : K) XK
    (fun z => hX z z.property)
  apply windingNumber_eq_of_logIncrement (by simp [hloop])
  refine ⟨⟨fun t => B ⟨γ t,hγ t⟩, by fun_prop⟩, ?_, ?_⟩
  · intro t
    exact hB ⟨γ t,hγ t⟩
  · simp only [Int.cast_zero,zero_mul]
    change B ⟨γ 1,hγ 1⟩-B ⟨γ 0,hγ 0⟩=0
    simp only [hloop,sub_self]

def planeIndex (A : ℂ →L[ℝ] ℂ) : ℤ :=
  if 0 < LinearMap.det A.toLinearMap then 1 else -1

lemma planeIndex_complex_smul {c : ℂ} (hc : c ≠ 0) (A : ℂ →L[ℝ] ℂ) :
    planeIndex (c • A) = planeIndex A := by
  have hp : 0 < ‖c‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
  simp only [planeIndex,det_complex_smul,mul_pos_iff_of_pos_left hp]

lemma exists_countable_injective_partition {f : ℂ → ℂ} {s : Set ℂ}
    (hs : MeasurableSet s) (hf : ∀ z ∈ s, ContDiffAt ℝ 1 f z)
    (hreg : ∀ z ∈ s, LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0) :
    ∃ p : ℕ → Set ℂ, (∀ n, MeasurableSet (p n)) ∧
      Pairwise (Disjoint on p) ∧ (⋃ n, p n) = s ∧ ∀ n, InjOn f (p n) := by
  classical
  have hlocal (z : s) : ∃ U : Set ℂ, IsOpen U ∧ (z : ℂ) ∈ U ∧ InjOn f U := by
    let e : ℂ ≃L[ℝ] ℂ :=
      (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr (hreg z z.2))).toContinuousLinearEquiv
    have he : (e : ℂ →L[ℝ] ℂ) = fderiv ℝ f z := by
      ext v
      exact LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr (hreg z z.2)) v
    have hd := (hf z z.2).hasStrictFDerivAt (by norm_num)
    rw [← he] at hd
    let e' := hd.toOpenPartialHomeomorph f
    exact ⟨e'.source,e'.open_source,hd.mem_toOpenPartialHomeomorph_source,e'.injOn⟩
  choose U hUo hUz hUi using hlocal
  by_cases he : s = ∅
  · subst s
    exact ⟨fun _ => ∅,by simp,by simp [Pairwise],by simp,by simp⟩
  · have : Nonempty s := Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr he)
    obtain ⟨j,hj⟩ := (show IsLindelof s from HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover
      U hUo (fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hUz ⟨z,hz⟩⟩)
    let q : ℕ → Set ℂ := fun n => s ∩ U (j n)
    refine ⟨disjointed q,?_,?_,?_,?_⟩
    · intro n
      exact MeasurableSet.disjointed (fun n => hs.inter (hUo (j n)).measurableSet) n
    · exact disjoint_disjointed q
    · rw [iUnion_disjointed]
      ext z
      simp only [mem_iUnion,mem_inter_iff,q]
      exact ⟨fun ⟨_,hz,_⟩ => hz,fun hz => by obtain ⟨n,hn⟩ := mem_iUnion.mp (hj hz); exact ⟨n,hz,hn⟩⟩
    · intro n
      exact (hUi (j n)).mono ((disjointed_subset q n).trans inter_subset_right)

def fiberMultiplicity (f : ℂ → ℂ) (s : Set ℂ) (w : ℂ) : ℝ≥0∞ :=
  Measure.count {z | z ∈ s ∧ f z = w}

lemma fiber_subsingleton_of_injOn {f : ℂ → ℂ} {s : Set ℂ} (hf : InjOn f s) (w : ℂ) :
    ({z | z ∈ s ∧ f z = w} : Set ℂ).Subsingleton := by
  intro z hz z' hz'
  exact hf hz.1 hz'.1 (hz.2.trans hz'.2.symm)

lemma fiberMultiplicity_of_injOn {f : ℂ → ℂ} {s : Set ℂ} (hf : InjOn f s) (w : ℂ) :
    fiberMultiplicity f s w = (f '' s).indicator (fun _ => (1 : ℝ≥0∞)) w := by
  classical
  by_cases hw : w ∈ f '' s
  · obtain ⟨z,hz,rfl⟩ := hw
    have he : {a | a ∈ s ∧ f a = f z} = {z} := by
      ext a
      exact ⟨fun h => hf h.1 hz h.2,fun h => by rcases h with rfl; exact ⟨hz,rfl⟩⟩
    rw [fiberMultiplicity,he,Measure.count_singleton,indicator_of_mem (mem_image_of_mem f hz)]
  · have he : {a | a ∈ s ∧ f a = w} = ∅ := by
      ext a
      exact ⟨fun h => (hw ⟨a,h.1,h.2⟩).elim,False.elim⟩
    simp [fiberMultiplicity,he,hw]

lemma fiberMultiplicity_partition {f : ℂ → ℂ} {s : Set ℂ} {p : ℕ → Set ℂ}
    (hd : Pairwise (Disjoint on p)) (hu : (⋃ n, p n) = s) (hi : ∀ n, InjOn f (p n))
    (w : ℂ) : fiberMultiplicity f s w =
      ∑' n, (f '' p n).indicator (fun _ => (1 : ℝ≥0∞)) w := by
  have he : {z | z ∈ s ∧ f z = w} = ⋃ n, {z | z ∈ p n ∧ f z = w} := by
    rw [← hu]
    ext z
    simp only [mem_ofPred_eq,mem_iUnion]
    aesop
  rw [fiberMultiplicity,he,measure_iUnion]
  · exact tsum_congr (fun n => fiberMultiplicity_of_injOn (hi n) w)
  · exact pairwise_disjoint_mono hd (fun n => inter_subset_left)
  · intro n
    exact (fiber_subsingleton_of_injOn (hi n) w).finite.measurableSet

lemma area_formula_regular {f : ℂ → ℂ} {s : Set ℂ}
    (hs : MeasurableSet s) (hf : ∀ z ∈ s, ContDiffAt ℝ 1 f z)
    (hreg : ∀ z ∈ s, LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0) :
    Measurable (fiberMultiplicity f s) ∧
      (∫⁻ z in s, ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| ∂volume) =
        ∫⁻ w, fiberMultiplicity f s w ∂volume := by
  obtain ⟨p,hpm,hpd,hpu,hpi⟩ := exists_countable_injective_partition hs hf hreg
  have hps (n) : p n ⊆ s := hpu ▸ subset_iUnion p n
  have hder (n) (z) (hz : z ∈ p n) : HasFDerivWithinAt f (fderiv ℝ f z) (p n) z :=
    ((hf z (hps n hz)).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  have him (n) : MeasurableSet (f '' p n) :=
    measurable_image_of_fderivWithin (hpm n) (hder n) (hpi n)
  have he := funext (fiberMultiplicity_partition hpd hpu hpi)
  refine ⟨?_,?_⟩
  · rw [he]
    exact Measurable.tsum (fun n => measurable_const.indicator (him n))
  · calc
      (∫⁻ z in s, ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| ∂volume) =
          ∑' n, ∫⁻ z in p n, ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| ∂volume := by
        conv_lhs => rw [← hpu]
        exact lintegral_iUnion hpm hpd _
      _ = ∑' n, volume (f '' p n) := tsum_congr (fun n =>
        lintegral_abs_det_fderiv_eq_addHaar_image volume (hpm n) (hder n) (hpi n))
      _ = ∫⁻ w, fiberMultiplicity f s w ∂volume := by
        rw [he,lintegral_tsum]
        · apply tsum_congr
          intro n
          rw [lintegral_indicator (him n)]
          simp
        · exact fun n => (measurable_const.indicator (him n)).aemeasurable

lemma lintegral_positive_part_eq {g : ℂ → ℝ} (hg : Measurable g) (s : Set ℂ) :
    (∫⁻ z in s, ENNReal.ofReal (g z) ∂volume) =
      ∫⁻ z in {z | z ∈ s ∧ 0 < g z}, ENNReal.ofReal |g z| ∂volume := by
  classical
  have hm : MeasurableSet {z | 0 < g z} := measurableSet_lt measurable_const hg
  have he : (fun z => ENNReal.ofReal (g z)) =
      {z | 0 < g z}.indicator (fun z => ENNReal.ofReal |g z|) := by
    funext z
    by_cases hz : 0 < g z
    · simp [hz,abs_of_pos hz]
    · simp [hz,ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hz)]
  rw [he,lintegral_indicator hm,Measure.restrict_restrict hm]
  exact congrArg (fun t : Set ℂ => ∫⁻ z in t, ENNReal.ofReal |g z| ∂volume) (inter_comm _ _)

lemma integral_det_nonpos_of_fiberMultiplicity {f : ℂ → ℂ} {s : Set ℂ}
    (hs : MeasurableSet s) (hf : ContDiff ℝ 1 f)
    (hj : IntegrableOn (fun z => LinearMap.det (fderiv ℝ f z).toLinearMap) s volume)
    (hcount : ∀ᵐ w ∂volume,
      fiberMultiplicity f {z | z ∈ s ∧ 0 < LinearMap.det (fderiv ℝ f z).toLinearMap} w ≤
      fiberMultiplicity f {z | z ∈ s ∧ LinearMap.det (fderiv ℝ f z).toLinearMap < 0} w) :
    ∫ z in s, LinearMap.det (fderiv ℝ f z).toLinearMap ∂volume ≤ 0 := by
  let J : ℂ → ℝ := fun z => LinearMap.det (fderiv ℝ f z).toLinearMap
  have hJ : Continuous J := ContinuousLinearMap.continuous_det.comp
    (hf.continuous_fderiv (by norm_num))
  have hp : MeasurableSet {z | z ∈ s ∧ 0 < J z} :=
    hs.inter (measurableSet_lt measurable_const hJ.measurable)
  have hm : MeasurableSet {z | z ∈ s ∧ J z < 0} :=
    hs.inter (measurableSet_lt hJ.measurable measurable_const)
  have hap := (area_formula_regular hp (fun z _ => hf.contDiffAt)
    (fun z hz => ne_of_gt hz.2)).2
  have ham := (area_formula_regular hm (fun z _ => hf.contDiffAt)
    (fun z hz => ne_of_lt hz.2)).2
  have hle : (∫⁻ z in s, ENNReal.ofReal (J z) ∂volume) ≤
      ∫⁻ z in s, ENNReal.ofReal (-J z) ∂volume := by
    rw [lintegral_positive_part_eq hJ.measurable,lintegral_positive_part_eq (g := fun z => -J z) hJ.neg.measurable]
    simp only [neg_pos,abs_neg]
    rw [hap,ham]
    exact lintegral_mono_ae hcount
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hj]
  exact sub_nonpos.mpr (ENNReal.toReal_mono (by
    exact (lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hj.neg.2).ne) hle)

lemma finite_regular_zeros_on_compact {K : Set ℂ} (hK : IsCompact K)
    {X : ℂ → ℂ} (hc : ContinuousOn X K)
    (hd : ∀ z ∈ K, X z = 0 → DifferentiableAt ℝ X z ∧
      LinearMap.det (fderiv ℝ X z).toLinearMap ≠ 0) :
    {z | z ∈ K ∧ X z = 0}.Finite := by
  have hZ : IsCompact {z | z ∈ K ∧ X z = 0} :=
    hK.of_isClosed_subset (hc.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton)
      inter_subset_left
  apply hZ.finite
  rw [isDiscrete_iff_nhdsNE]
  intro z hz
  obtain ⟨hzD,hzd⟩ := hd z hz.1 hz.2
  let e : ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hzd)).toContinuousLinearEquiv
  have he : (e : ℂ → ℂ) = fderiv ℝ X z := by
    funext w
    exact LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr hzd) w
  have ha : ∃ C, AntilipschitzWith C (fderiv ℝ X z) := by
    rw [← he]
    exact ⟨_,e.antilipschitz⟩
  rw [Filter.inf_principal_eq_bot]
  filter_upwards [hzD.hasFDerivAt.eventually_ne ha] with w hw
  exact fun h => hw (h.2.trans hz.2.symm)

lemma loopIndex_circle_inside {r : ℝ} (hr : 0 < r) {a : ℂ} (ha : ‖a‖ < r) :
    loopIndex ((r : ℂ) • circleLoop) a = 1 := by
  let γ : C(unitInterval,ℂ) := (r : ℂ) • circleLoop
  have hγloop : γ 1 = γ 0 := by simp [γ]
  have hγnorm (t) : ‖γ t‖ = r := by simp [γ,abs_of_pos hr]
  have hγne (t) : γ t ≠ 0 := norm_pos_iff.mp (by rw [hγnorm]; exact hr)
  have hwone : windingNumber γ = 1 := by
    apply windingNumber_eq_of_logIncrement hγloop
    simpa using circleLoop_logIncrement (r : ℂ) (by exact_mod_cast hr.ne')
  unfold loopIndex
  rw [← hwone]
  apply windingNumber_perturb hγloop (by simp) hγne
  intro t
  simpa [γ,sub_sub_cancel_left,abs_of_pos hr] using ha

lemma ae_regular_value {f : ℂ → ℂ} (hf : Differentiable ℝ f) :
    ∀ᵐ w ∂volume, ∀ z, f z = w → LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0 := by
  have hm : volume (f '' {z | LinearMap.det (fderiv ℝ f z).toLinearMap = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun z _ => (hf z).hasFDerivAt.hasFDerivWithinAt) (fun _ h => h)
  have ha : ∀ᵐ w ∂volume, w ∉ f '' {z | LinearMap.det (fderiv ℝ f z).toLinearMap = 0} :=
    ae_iff.mpr (by simpa only [not_not,Set.ofPred_mem_eq] using hm)
  filter_upwards [ha] with w hw z hz hd
  exact hw ⟨z,hd,hz⟩

lemma signed_sum_eq_card_sub (s : Finset ℂ) (J : ℂ → ℝ)
    (hJ : ∀ z ∈ s, J z ≠ 0) :
    (∑ z ∈ s, if 0 < J z then (1 : ℤ) else -1) =
      (s.filter (fun z => 0 < J z)).card - (s.filter (fun z => J z < 0)).card := by
  classical
  rw [← Finset.sum_boole (R := ℤ) (fun z => 0 < J z) s,
    ← Finset.sum_boole (R := ℤ) (fun z => J z < 0) s,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rcases lt_or_gt_of_ne (hJ z hz) with hn | hp
  · simp [hn,not_lt.mpr hn.le]
  · simp [hp,not_lt.mpr hp.le]

end Brennan

end

end OAI
