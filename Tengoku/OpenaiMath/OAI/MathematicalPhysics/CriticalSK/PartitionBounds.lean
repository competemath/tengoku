import Tengoku.OpenaiMath.OAI.MathematicalPhysics.CriticalSK.EdgeAsymptotics
import Tengoku.OpenaiMath.OAI.MathematicalPhysics.CriticalSK.OverlapMoments

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal

open scoped BigOperators NNReal

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open Module

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal BigOperators

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set Real

namespace CriticalSK

section

lemma log_le_square_half {x : ℝ} (hx : 0 < x) : Real.log x ≤ (x^2-1)/2 := by
  have hh := Real.log_le_sub_one_of_pos (sq_pos_of_pos hx)
  rw [Real.log_pow] at hh
  norm_num at hh
  linarith

lemma gaussian_radial_shape_bound (p : ℕ) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hp : (p:ℝ) ≤ R) :
    r^p * Real.exp (-r^2/2) ≤
      Real.exp ((R-p)/2) * (Real.sqrt R)^p * Real.exp (-R/2) := by
  have hs := Real.sqrt_pos.mpr hR
  have hs2 := Real.sq_sqrt hR.le
  let x := r / Real.sqrt R
  have hx : 0 < x := div_pos hr hs
  have hxid : Real.sqrt R*x = r := by dsimp [x]; field_simp
  have hx2 : R*x^2 = r^2 := by nlinarith [sq_nonneg (Real.sqrt R*x-r)]
  have hlog := mul_le_mul_of_nonneg_left (log_le_square_half hx) (Nat.cast_nonneg p : (0:ℝ) ≤ p)
  have hn : 0 ≤ (R-p)*x^2 := mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg x)
  have he : (p:ℝ)*Real.log x-r^2/2 ≤ (R-p)/2-R/2 := by nlinarith
  have he' := Real.exp_le_exp.mpr he
  rw [Real.exp_sub,Real.exp_nat_mul,Real.exp_log hx,Real.exp_sub] at he'
  have he'' : x^p * Real.exp (-r^2/2) ≤ Real.exp ((R-p)/2)*Real.exp (-R/2) := by
    rw [show -r^2/2 = -(r^2/2) by ring, show -R/2 = -(R/2) by ring, Real.exp_neg, Real.exp_neg]
    simpa only [div_eq_mul_inv] using he'
  calc
    r^p * Real.exp (-r^2/2) = (Real.sqrt R)^p*(x^p*Real.exp (-r^2/2)) := by
      rw [← mul_assoc,← mul_pow,hxid]
    _ ≤ (Real.sqrt R)^p*(Real.exp ((R-p)/2)*Real.exp (-R/2)) :=
      mul_le_mul_of_nonneg_left he'' (pow_nonneg hs.le _)
    _ = _ := by ring

open Set Filter

variable {ι : Type*} [Fintype ι]

lemma diagonalGaussian_normSq_integrable (v : ι → ℝ≥0) :
    Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖^2) (diagonalGaussian v) := by
  unfold diagonalGaussian
  apply (integrable_map_measure (by fun_prop) (WithLp.measurable_toLp 2 _).aemeasurable).mpr
  have hi := (piSquareSum_memLp v).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  unfold piSquareSum at hi
  simpa only [Function.comp_def,EuclideanSpace.real_norm_sq_eq] using hi

lemma diagonalGaussian_normSq_mean (v : ι → ℝ≥0) :
    (∫ x : EuclideanSpace ℝ ι, ‖x‖^2 ∂diagonalGaussian v) = ∑ i, (v i : ℝ) := by
  rw [diagonalGaussian,integral_map (WithLp.measurable_toLp 2 _).aemeasurable (by fun_prop)]
  simpa only [EuclideanSpace.real_norm_sq_eq,piSquareSum] using piSquareSum_mean v

lemma diagonalGaussian_singleton_zero [Nonempty ι] (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    diagonalGaussian v ({0} : Set (EuclideanSpace ℝ ι)) = 0 := by
  rw [diagonalGaussian_density v hv]
  exact withDensity_absolutelyContinuous _ _ (measure_singleton 0)

variable (n : ℕ)

lemma diagonalSquareDensity_standard_formula :
    diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) =
      (Real.sqrt (n+2))^n * gaussianPiPrefactor (fun _ : Fin (n+2) => 1) *
        Real.exp (-(n+2)/2) * sphereArea (ι := Fin (n+2)) / 2 := by
  rw [diagonalSquareDensity,radialDensity_standard]
  simp only [Fintype.card_fin,show n+2-1=n+1 by omega,pow_succ,
    Real.sq_sqrt (show (0:ℝ) ≤ n+2 by positivity)]
  field_simp

lemma standard_radial_density_upper {r : ℝ} (hr : 0 ≤ r) :
    radialDensity volume (fun x : EuclideanSpace ℝ (Fin (n+2)) => gaussianPiPDF (fun _ => 1) x) r ≤
      2*r*Real.exp 1*diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) := by
  rw [radialDensity_standard,diagonalSquareDensity_standard_formula]
  simp only [Fintype.card_fin,show n+2-1=n+1 by omega,pow_succ]
  rcases hr.eq_or_lt with h | h
  · simp [← h]
  · have hp := gaussian_radial_shape_bound n (by positivity : (0:ℝ) < n+2) h (by linarith : (n:ℝ) ≤ n+2)
    rw [show ((n:ℝ)+2-n)/2=1 by ring] at hp
    have hmul := mul_le_mul_of_nonneg_right hp
      (show 0 ≤ r*gaussianPiPrefactor (fun _ : Fin (n+2) => 1)*sphereArea (ι := Fin (n+2)) by
        exact mul_nonneg (mul_nonneg h.le (gaussianPiPrefactor_pos (by simp)).le) sphereArea_pos.le)
    convert hmul using 1 <;> first | rfl | ring_nf

end

section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def spectralTop (lam : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty lam

lemma le_spectralTop (lam : ι → ℝ) (i : ι) : lam i ≤ spectralTop lam :=
  Finset.le_sup' lam (Finset.mem_univ i)

lemma spectralTop_attained (lam : ι → ℝ) : ∃ i, lam i = spectralTop lam := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty lam
  exact ⟨i,hi.symm⟩

def spectralStieltjes (lam : ι → ℝ) (r : ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, (r-lam i)⁻¹

def spectralStieltjesSlope (lam : ι → ℝ) (r : ℝ) : ℝ :=
  -(Fintype.card ι : ℝ)⁻¹ * ∑ i, ((r-lam i)⁻¹)^2

lemma cardinal_pos_real : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos

lemma spectralStieltjes_pos (lam : ι → ℝ) {r : ℝ} (hr : spectralTop lam < r) :
    0 < spectralStieltjes lam r := by
  unfold spectralStieltjes
  apply mul_pos (inv_pos.mpr cardinal_pos_real)
  apply Finset.sum_pos (fun i _ => inv_pos.mpr (by linarith [le_spectralTop lam i])) Finset.univ_nonempty

lemma spectralStieltjes_strictAnti (lam : ι → ℝ) : StrictAntiOn (spectralStieltjes lam) (Ioi (spectralTop lam)) := by
  intro r hr s _ hrs
  change spectralTop lam < r at hr
  unfold spectralStieltjes
  apply mul_lt_mul_of_pos_left _ (inv_pos.mpr cardinal_pos_real)
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro i _
  exact inv_strictAnti₀ (by linarith [le_spectralTop lam i] : 0 < r-lam i) (by linarith)

lemma spectralStieltjes_hasStrictDerivAt (lam : ι → ℝ) {r : ℝ} (hr : spectralTop lam < r) :
    HasStrictDerivAt (spectralStieltjes lam) (spectralStieltjesSlope lam r) r := by
  have h (i : ι) := (hasStrictDerivAt_inv (ne_of_gt (show 0 < r-lam i by linarith [le_spectralTop lam i]))).comp r ((hasStrictDerivAt_id r).sub_const (lam i))
  have hd := (HasStrictDerivAt.sum (u := Finset.univ) (fun i _ => h i)).const_mul (Fintype.card ι : ℝ)⁻¹
  convert! hd using 1
  · funext x; simp [spectralStieltjes, Finset.sum_apply]
  · unfold spectralStieltjesSlope
    simp only [mul_one,inv_pow,Finset.sum_neg_distrib,neg_mul,mul_neg]

lemma spectralStieltjesSlope_neg (lam : ι → ℝ) {r : ℝ} (hr : spectralTop lam < r) :
    spectralStieltjesSlope lam r < 0 := by
  unfold spectralStieltjesSlope
  apply mul_neg_of_neg_of_pos (neg_neg_of_pos (inv_pos.mpr cardinal_pos_real))
  exact Finset.sum_pos (fun i _ => sq_pos_of_pos (inv_pos.mpr (by linarith [le_spectralTop lam i]))) Finset.univ_nonempty

lemma spectralStieltjes_continuous (lam : ι → ℝ) : ContinuousOn (spectralStieltjes lam) (Ioi (spectralTop lam)) :=
  fun _ hr => (spectralStieltjes_hasStrictDerivAt lam hr).hasDerivAt.continuousAt.continuousWithinAt

lemma spectralStieltjes_exists (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    ∃ r, spectralTop lam < r ∧ spectralStieltjes lam r = a := by
  let N : ℝ := Fintype.card ι
  have hN : 0 < N := cardinal_pos_real
  have hN1 : 1 ≤ N := by
    change (1:ℝ) ≤ Fintype.card ι
    exact_mod_cast (Fintype.card_pos (α := ι))
  let l := spectralTop lam + (N*a)⁻¹
  let u := spectralTop lam + a⁻¹
  have hl : spectralTop lam < l := by
    exact lt_add_of_pos_right _ (inv_pos.mpr (mul_pos hN ha))
  have hlu : l ≤ u := by
    dsimp [l,u]
    gcongr
    nlinarith
  have hlow : a ≤ spectralStieltjes lam l := by
    obtain ⟨i,hi⟩ := spectralTop_attained lam
    have hp (j : ι) : 0 ≤ (l-lam j)⁻¹ := by exact (inv_pos.mpr (by linarith [le_spectralTop lam j])).le
    have hsum := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
    have hmul := mul_le_mul_of_nonneg_left hsum (inv_pos.mpr hN).le
    have heq : N⁻¹ * (l-lam i)⁻¹ = a := by
      rw [hi]
      dsimp [l]
      rw [add_sub_cancel_left, inv_inv]
      field_simp
    rw [heq] at hmul
    exact hmul
  have hupp : spectralStieltjes lam u ≤ a := by
    have hh (i : ι) : (u-lam i)⁻¹ ≤ a := by
      have hle : a⁻¹ ≤ u-lam i := by dsimp [u]; linarith [le_spectralTop lam i]
      have hh := inv_anti₀ (inv_pos.mpr ha) hle
      simpa only [inv_inv] using hh
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hh i)
    have ht := mul_le_mul_of_nonneg_left hs (inv_pos.mpr hN).le
    change N⁻¹ * ∑ i, (u-lam i)⁻¹ ≤ a
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← mul_assoc, show (Fintype.card ι : ℝ) = N from rfl, inv_mul_cancel₀ hN.ne',one_mul] using ht
  have hc := (spectralStieltjes_continuous lam).mono (show Icc l u ⊆ Ioi (spectralTop lam) from fun _ hx => hl.trans_le hx.1)
  obtain ⟨r,hr,heq⟩ := intermediate_value_Icc' hlu hc ⟨hupp,hlow⟩
  exact ⟨r,hl.trans_le hr.1,heq⟩

def saddleRadius (lam : ι → ℝ) (a : ℝ) : ℝ :=
  if h : 0 < a then (spectralStieltjes_exists lam h).choose else 0

lemma saddleRadius_spec (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    spectralTop lam < saddleRadius lam a ∧ spectralStieltjes lam (saddleRadius lam a) = a := by
  simpa only [saddleRadius,dite_eq_left ha] using (spectralStieltjes_exists lam ha).choose_spec

lemma saddleRadius_unique (lam : ι → ℝ) {a r : ℝ} (hr : spectralTop lam < r)
    (heq : spectralStieltjes lam r = a) : saddleRadius lam a = r := by
  have ha : 0 < a := heq ▸ spectralStieltjes_pos lam hr
  exact (spectralStieltjes_strictAnti lam).injOn (saddleRadius_spec lam ha).1 hr
    ((saddleRadius_spec lam ha).2.trans heq.symm)

lemma saddleRadius_hasStrictDerivAt (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    HasStrictDerivAt (saddleRadius lam) (spectralStieltjesSlope lam (saddleRadius lam a))⁻¹ a := by
  obtain ⟨hr,heq⟩ := saddleRadius_spec lam ha
  have hd := spectralStieltjes_hasStrictDerivAt lam hr
  have hg : ∀ᶠ r in 𝓝 (saddleRadius lam a), saddleRadius lam (spectralStieltjes lam r) = r := by
    filter_upwards [eventually_gt_nhds hr] with r hr
    exact saddleRadius_unique lam hr rfl
  have h := hd.to_local_left_inverse (spectralStieltjesSlope_neg lam hr).ne hg
  rwa [heq] at h

def saddleObjective (lam : ι → ℝ) (a z : ℝ) : ℝ :=
  (z-1)/2 - (2*(Fintype.card ι : ℝ))⁻¹ * ∑ i, Real.log (z-a*lam i)

def sphericalVariational (lam : ι → ℝ) (a : ℝ) : ℝ :=
  sInf (saddleObjective lam a '' Set.Ioi (a*spectralTop lam))

def saddleZ (lam : ι → ℝ) (a : ℝ) : ℝ :=
  if a = 0 then 1 else a*saddleRadius lam a

lemma saddleZ_pos_gap (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    a*spectralTop lam < saddleZ lam a := by
  rcases ha.eq_or_lt with h | h
  · simp [← h,saddleZ]
  · simp only [saddleZ,ite_eq_right h.ne']
    exact mul_lt_mul_of_pos_left (saddleRadius_spec lam h).1 h

lemma saddleZ_gap_pos (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) (i : ι) :
    0 < saddleZ lam a-a*lam i := by
  have h := mul_le_mul_of_nonneg_left (le_spectralTop lam i) ha
  linarith [saddleZ_pos_gap lam ha]

lemma saddleZ_reciprocal_sum (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ∑ i, (saddleZ lam a-a*lam i)⁻¹ = Fintype.card ι := by
  rcases ha.eq_or_lt with h | h
  · simp [← h,saddleZ]
  · have heq := (saddleRadius_spec lam h).2
    unfold spectralStieltjes at heq
    have hs : ∑ i, (saddleRadius lam a-lam i)⁻¹ = (Fintype.card ι : ℝ)*a := by
      have hN : (Fintype.card ι : ℝ) ≠ 0 := cardinal_pos_real.ne'
      exact (inv_mul_eq_iff_eq_mul₀ hN).mp heq
    simp only [saddleZ,ite_eq_right h.ne',← mul_sub,_root_.mul_inv_rev]
    rw [← Finset.sum_mul, hs]
    field_simp

lemma saddleObjective_min (lam : ι → ℝ) {a z : ℝ} (ha : 0 ≤ a)
    (hz : a*spectralTop lam < z) :
    saddleObjective lam a (saddleZ lam a) ≤ saddleObjective lam a z := by
  have hzpos (i : ι) : 0 < z-a*lam i := by
    have h := mul_le_mul_of_nonneg_left (le_spectralTop lam i) ha
    linarith
  have hl (i : ι) : Real.log (z-a*lam i)-Real.log (saddleZ lam a-a*lam i) ≤
      (z-saddleZ lam a)*(saddleZ lam a-a*lam i)⁻¹ := by
    rw [← Real.log_div (hzpos i).ne' (saddleZ_gap_pos lam ha i).ne']
    have hh := Real.log_le_sub_one_of_pos (div_pos (hzpos i) (saddleZ_gap_pos lam ha i))
    convert hh using 1
    field_simp [(saddleZ_gap_pos lam ha i).ne']
    ring
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hl i)
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,saddleZ_reciprocal_sum lam ha] at hs
  have hN : (0:ℝ) < Fintype.card ι := cardinal_pos_real
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (2*(Fintype.card ι : ℝ))⁻¹ by positivity)
  unfold saddleObjective
  have he : (2*(Fintype.card ι : ℝ))⁻¹ * ((z-saddleZ lam a)*(Fintype.card ι : ℝ)) =
      (z-saddleZ lam a)/2 := by field_simp
  rw [he] at hm
  linarith

lemma sphericalVariational_eq (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    sphericalVariational lam a = saddleObjective lam a (saddleZ lam a) := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨saddleZ lam a,saddleZ_pos_gap lam ha,rfl⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact saddleObjective_min lam ha hz

lemma sphericalVariational_zero (lam : ι → ℝ) : sphericalVariational lam 0 = 0 := by
  rw [sphericalVariational_eq lam (le_refl 0)]
  simp [saddleObjective,saddleZ]

lemma sphericalVariational_radius_expr (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    sphericalVariational lam a = (a*saddleRadius lam a-1)/2-Real.log a/2 -
      (2*(Fintype.card ι : ℝ))⁻¹ * ∑ i, Real.log (saddleRadius lam a-lam i) := by
  rw [sphericalVariational_eq lam ha.le]
  simp only [saddleObjective,saddleZ,ite_eq_right ha.ne',← mul_sub]
  have hr := (saddleRadius_spec lam ha).1
  have he (i : ι) := Real.log_mul ha.ne' (ne_of_gt (show 0 < saddleRadius lam a-lam i by linarith [le_spectralTop lam i]))
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hN : (Fintype.card ι : ℝ) ≠ 0 := cardinal_pos_real.ne'
  field_simp
  ring

lemma sphericalVariational_hasDerivAt (lam : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (sphericalVariational lam) ((saddleRadius lam a-a⁻¹)/2) a := by
  let r := saddleRadius lam
  let d := (spectralStieltjesSlope lam (r a))⁻¹
  have hr : HasDerivAt r d a := (saddleRadius_hasStrictDerivAt lam ha).hasDerivAt
  have hpos (i : ι) : 0 < r a-lam i := by
    have hs := (saddleRadius_spec lam ha).1
    dsimp [r]
    linarith [le_spectralTop lam i]
  have hlog (i : ι) := (hr.sub_const (lam i)).log (hpos i).ne'
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ => hlog i)
  have hd := (((hasDerivAt_id a).mul hr).sub_const 1).div_const 2
  have hd := (hd.sub ((hasDerivAt_log ha.ne').div_const 2)).sub
    (hsum.const_mul (2*(Fintype.card ι : ℝ))⁻¹)
  have heq : ∀ᶠ b in 𝓝 a, sphericalVariational lam b =
      (b*r b-1)/2-Real.log b/2 - (2*(Fintype.card ι : ℝ))⁻¹*∑ i, Real.log (r b-lam i) := by
    filter_upwards [eventually_gt_nhds ha] with b hb
    exact sphericalVariational_radius_expr lam hb
  simp only [Pi.mul_apply, Finset.sum_apply, id_eq] at hd
  have hres := hd.congr_of_eventuallyEq heq
  have hs := (saddleRadius_spec lam ha).2
  unfold spectralStieltjes at hs
  have hN : (Fintype.card ι : ℝ) ≠ 0 := cardinal_pos_real.ne'
  have hs' : ∑ i, (r a-lam i)⁻¹ = (Fintype.card ι : ℝ)*a :=
    (inv_mul_eq_iff_eq_mul₀ hN).mp hs
  convert! hres using 1
  simp only [div_eq_mul_inv,← Finset.mul_sum,hs']
  field_simp
  ring

lemma saddleZ_weighted_identity (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (saddleZ lam a-1)*(Fintype.card ι : ℝ) =
      a*∑ i, lam i*(saddleZ lam a-a*lam i)⁻¹ := by
  have h (i : ι) : saddleZ lam a*(saddleZ lam a-a*lam i)⁻¹ -
      a*(lam i*(saddleZ lam a-a*lam i)⁻¹) = 1 := by
    rw [← mul_assoc,← sub_mul,mul_inv_cancel₀ (saddleZ_gap_pos lam ha i).ne']
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h i)
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,
    saddleZ_reciprocal_sum lam ha,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hs
  linarith

lemma sphericalVariational_slope_bound (lam : ι → ℝ) {a C : ℝ} (ha : 0 < a)
    (hlam : ∀ i, |lam i| ≤ C) : |(saddleRadius lam a-a⁻¹)/2| ≤ C/2 := by
  have hN : (0:ℝ) < Fintype.card ι := cardinal_pos_real
  have hw := saddleZ_weighted_identity lam ha.le
  have hb : |∑ i, lam i*(saddleZ lam a-a*lam i)⁻¹| ≤ C*(Fintype.card ι : ℝ) := by
    calc
      _ ≤ ∑ i, |lam i*(saddleZ lam a-a*lam i)⁻¹| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, C*(saddleZ lam a-a*lam i)⁻¹ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul,abs_of_pos (inv_pos.mpr (saddleZ_gap_pos lam ha.le i))]
        exact mul_le_mul_of_nonneg_right (hlam i) (inv_pos.mpr (saddleZ_gap_pos lam ha.le i)).le
      _ = _ := by rw [← Finset.mul_sum,saddleZ_reciprocal_sum lam ha.le]
  have hwb := congrArg abs hw
  rw [abs_mul,abs_of_pos hN,abs_mul,abs_of_pos ha] at hwb
  have hzbound : |saddleZ lam a-1| ≤ a*C := by nlinarith
  have heq : (saddleRadius lam a-a⁻¹)/2 = (saddleZ lam a-1)/(2*a) := by
    simp only [saddleZ,ite_eq_right ha.ne']
    field_simp
  rw [heq,abs_div,abs_of_pos (by positivity : 0 < 2*a)]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

lemma sphericalVariational_abs_le (lam : ι → ℝ) {a C : ℝ} (ha : 0 ≤ a)
    (hlam : ∀ i, |lam i| ≤ C) : |sphericalVariational lam a| ≤ a*C/2 := by
  have hN : (0:ℝ) < Fintype.card ι := cardinal_pos_real
  have htop : spectralTop lam ≤ C := by
    obtain ⟨i,hi⟩ := spectralTop_attained lam
    rw [← hi]
    exact (abs_le.mp (hlam i)).2
  have hz : a*spectralTop lam < 1+a*C := by nlinarith [mul_le_mul_of_nonneg_left htop ha]
  have hu := saddleObjective_min lam ha hz
  have hlogs : 0 ≤ ∑ i, Real.log (1+a*C-a*lam i) := by
    apply Finset.sum_nonneg
    intro i _
    apply Real.log_nonneg
    nlinarith [mul_le_mul_of_nonneg_left (abs_le.mp (hlam i)).2 ha]
  have hlo := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Real.log_le_sub_one_of_pos (saddleZ_gap_pos lam ha i))
  have hsumlow : -(C*(Fintype.card ι : ℝ)) ≤ ∑ i, lam i := by
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (abs_le.mp (hlam i)).1)
    simpa [Finset.sum_const,Finset.card_univ,mul_comm] using hs
  rw [sphericalVariational_eq lam ha,abs_le]
  constructor
  · unfold saddleObjective
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      ← Finset.mul_sum,mul_one] at hlo
    have hl := mul_le_mul_of_nonneg_left hsumlow ha
    have hb : ∑ i, Real.log (saddleZ lam a-a*lam i) ≤
        (Fintype.card ι : ℝ)*(saddleZ lam a-1+a*C) := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ (2*(Fintype.card ι : ℝ))⁻¹ by positivity)
    have he : (2*(Fintype.card ι : ℝ))⁻¹ *((Fintype.card ι : ℝ)*(saddleZ lam a-1+a*C)) =
        (saddleZ lam a-1+a*C)/2 := by field_simp
    rw [he] at hh
    linarith
  · unfold saddleObjective at hu ⊢
    have hh : 0 ≤ (2*(Fintype.card ι : ℝ))⁻¹ * ∑ i, Real.log (1+a*C-a*lam i) := mul_nonneg (by positivity) hlogs
    linarith

lemma sphericalVariational_continuousOn (lam : ι → ℝ) :
    ContinuousOn (sphericalVariational lam) (Ici 0) := by
  intro a ha
  change 0 ≤ a at ha
  rcases ha.eq_or_lt with h | h
  · subst a
    let C := Finset.univ.sup' Finset.univ_nonempty (fun i => |lam i|)
    have hC (i : ι) : |lam i| ≤ C := Finset.le_sup' (fun i => |lam i|) (Finset.mem_univ i)
    rw [ContinuousWithinAt]
    rw [sphericalVariational_zero]
    apply squeeze_zero_norm' (f := sphericalVariational lam) (a := fun a : ℝ => a*C/2)
    · filter_upwards [self_mem_nhdsWithin] with a ha
      simpa only [norm_eq_abs] using sphericalVariational_abs_le lam ha hC
    · simpa using (((continuousAt_id.mul_const C).div_const 2).tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (fun a : ℝ => a*C/2) (𝓝[Ici 0] 0) (𝓝 (0*C/2)))
  · exact (sphericalVariational_hasDerivAt lam h).continuousAt.continuousWithinAt

end

section

open Set

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma gaussianPiPrefactor_log {v : ι → ℝ≥0} (hv : ∀ i, v i ≠ 0) :
    Real.log (gaussianPiPrefactor v) = -(∑ i, Real.log (2*Real.pi*(v i:ℝ)))/2 := by
  unfold gaussianPiPrefactor
  rw [Real.log_prod (fun i _ => inv_ne_zero (Real.sqrt_ne_zero'.mpr (by
    have hi : 0 < (v i : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (hv i))
    positivity)))]
  have hs (i : ι) : Real.log (Real.sqrt (2*Real.pi*(v i:ℝ))) = Real.log (2*Real.pi*(v i:ℝ))/2 :=
    Real.log_sqrt (by positivity)
  simp_rw [Real.log_inv,hs]
  simp only [Finset.sum_neg_distrib,← Finset.sum_div,neg_div]

omit [Nonempty ι] in
lemma gaussianPiPrefactor_log_ratio {v : ι → ℝ≥0} (hv : ∀ i, v i ≠ 0) :
    Real.log (gaussianPiPrefactor v / gaussianPiPrefactor (fun _ : ι => 1)) =
      (∑ i, Real.log ((v i : ℝ)⁻¹))/2 := by
  rw [Real.log_div (gaussianPiPrefactor_pos hv).ne'
    (gaussianPiPrefactor_pos (v := fun _ : ι => 1) (by simp)).ne',
    gaussianPiPrefactor_log hv,gaussianPiPrefactor_log (v := fun _ : ι => 1) (by simp)]
  have hlog (i : ι) : Real.log (2*Real.pi*(v i:ℝ)) = Real.log (2*Real.pi)+Real.log (v i) :=
    Real.log_mul (by positivity) (NNReal.coe_ne_zero.mpr (hv i))
  simp_rw [hlog,NNReal.coe_one,mul_one,Real.log_inv]
  rw [Finset.sum_add_distrib,Finset.sum_neg_distrib]
  ring

lemma spherical_gaussian_identity {lam : ι → ℝ} {v : ι → ℝ≥0} {z a : ℝ}
    (hv : ∀ i, v i ≠ 0) (hq : ∀ i, (v i : ℝ)⁻¹ = z-a*lam i) :
    spherePartition lam a (Real.sqrt (Fintype.card ι)) =
      Real.exp ((Fintype.card ι : ℝ)*saddleObjective lam a z) *
        (diagonalSquareDensity v (Fintype.card ι) /
          diagonalSquareDensity (fun _ : ι => 1) (Fintype.card ι)) := by
  have hN : (0:ℝ) < Fintype.card ι := cardinal_pos_real
  have hs := Real.sqrt_pos.mpr hN
  have hr := spherical_radial_ratio hq hs
  have hp := gaussianPiPrefactor_log_ratio hv
  simp_rw [hq] at hp
  have he : gaussianPiPrefactor v / gaussianPiPrefactor (fun _ : ι => 1) *
      Real.exp (-(z-1)*(Real.sqrt (Fintype.card ι))^2/2) =
      Real.exp (-((Fintype.card ι : ℝ)*saddleObjective lam a z)) := by
    rw [← Real.exp_log (div_pos (gaussianPiPrefactor_pos hv) (gaussianPiPrefactor_pos (by simp))),
      ← Real.exp_add,hp,Real.sq_sqrt hN.le]
    congr 1
    unfold saddleObjective
    field_simp
    ring
  rw [he] at hr
  have hd : diagonalSquareDensity v (Fintype.card ι) /
      diagonalSquareDensity (fun _ : ι => 1) (Fintype.card ι) =
      radialDensity volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF v x) (Real.sqrt (Fintype.card ι)) /
        radialDensity volume (fun x : EuclideanSpace ℝ ι => gaussianPiPDF (fun _ => 1) x) (Real.sqrt (Fintype.card ι)) := by
    unfold diagonalSquareDensity
    rw [div_div_div_cancel_right₀ (mul_ne_zero two_ne_zero hs.ne')]
  rw [hd,hr,Real.exp_neg]
  field_simp

lemma saddleZ_le_bound (lam : ι → ℝ) {a C : ℝ} (ha : 0 ≤ a) (hlam : ∀ i, lam i ≤ C) :
    saddleZ lam a ≤ 1+a*C := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hlam i) (inv_pos.mpr (saddleZ_gap_pos lam ha i)).le)
  rw [← Finset.mul_sum,saddleZ_reciprocal_sum lam ha] at hs
  have hh := mul_le_mul_of_nonneg_left hs ha
  rw [← saddleZ_weighted_identity lam ha] at hh
  have hN : (0:ℝ) < Fintype.card ι := cardinal_pos_real
  nlinarith

def saddleVariance (lam : ι → ℝ) (a : ℝ) (i : ι) : ℝ≥0 :=
  Real.toNNReal ((saddleZ lam a-a*lam i)⁻¹)

lemma saddleVariance_coe (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) (i : ι) :
    (saddleVariance lam a i : ℝ) = (saddleZ lam a-a*lam i)⁻¹ :=
  Real.coe_toNNReal _ (inv_pos.mpr (saddleZ_gap_pos lam ha i)).le

lemma saddleVariance_pos (lam : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) (i : ι) :
    0 < saddleVariance lam a i := by
  rw [← NNReal.coe_pos,saddleVariance_coe lam ha]
  exact inv_pos.mpr (saddleZ_gap_pos lam ha i)

lemma saddleVariance_lower (lam : ι → ℝ) {a : ℝ} (ha : a ∈ Icc 0 2)
    (hlam : ∀ i, |lam i| ≤ 3) (i : ι) : (1:ℝ)/13 ≤ saddleVariance lam a i := by
  rw [saddleVariance_coe lam ha.1]
  have hz := saddleZ_le_bound lam ha.1 (fun i => (abs_le.mp (hlam i)).2)
  have hi := (abs_le.mp (hlam i)).1
  have hm := mul_le_mul_of_nonneg_left hi ha.1
  have hg : saddleZ lam a-a*lam i ≤ 13 := by nlinarith [ha.2]
  simpa using inv_anti₀ (saddleZ_gap_pos lam ha.1 i) hg

variable (n : ℕ)

end

section

open Set

variable {n : ℕ}

lemma diagonalSquareDensity_standard_upper :
    diagonalSquareDensity (fun _ : Fin (n+2) => 1) (n+2) ≤ 1/2 := by
  have hh := diagonalSquareDensity_upper (fun _ : Fin (n+2) => 1) (by simp)
    (by positivity : (0:ℝ) < n+2)
  have he : Real.pi*gaussianPairPrefactor 1 1 = 1/2 := by
    unfold gaussianPairPrefactor
    norm_num only [NNReal.coe_one,mul_one]
    rw [← sq,Real.sq_sqrt (by positivity)]
    field_simp
  rwa [he] at hh

end

def fixedBulkDeficit {n : ℕ} (lam : Fin (n+2) → ℝ) (s : ℝ) : ℝ :=
  (n+2)-(∑ i : Fin n, (fixedEdgeVariance lam s i.succ.succ:ℝ))

lemma fixedBulkDeficit_bounds {n : ℕ} {lam : Fin (n+2) → ℝ} {h s : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hs1 : s ≤ 1)
    (hcost : traceCost (n+1) h s ≤ 1/100) (hlam : lam ∈ spectralGood (n+1) h s)
    (hspace : 32768 ≤ (n+2:ℝ)*s*Real.sqrt s) :
    0 < fixedBulkDeficit lam s ∧ fixedBulkDeficit lam s/(1/(2*s)) ≤ 6*((n+2:ℝ)*s*Real.sqrt s) ∧
    128*(∑ i : Fin n, (fixedEdgeVariance lam s i.succ.succ:ℝ)^2) ≤ (fixedBulkDeficit lam s)^2 := by
  have hi := spectralGood_fixed_bulk hh hs hs1 hcost hlam hspace
  change _ ≤ fixedBulkDeficit lam s ∧ fixedBulkDeficit lam s ≤ _ ∧ _ at hi
  refine ⟨lt_of_lt_of_le (by positivity) hi.1,?_,hi.2.2⟩
  have ht := mul_le_mul_of_nonneg_right hi.2.1 (by positivity : 0 ≤ 2*s)
  simpa only [div_div_eq_mul_div,div_one] using ht.trans_eq (show 3*(n+2:ℝ)*Real.sqrt s*(2*s) = 6*((n+2:ℝ)*s*Real.sqrt s) by ring)

end CriticalSK

end

end OAI
