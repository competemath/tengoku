import Tengoku.OpenaiMath.OAI.Analysis.LpDimension.ConvexRepresentation
import Tengoku.OpenaiMath.OAI.Analysis.LpDimension.GridObstruction

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
universe u uE uI uΩ

namespace SubpolynomialLp

def PairIndex (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}
instance (n : ℕ) : Fintype (PairIndex n) := inferInstanceAs (Fintype {ij : Fin n × Fin n // ij.1 < ij.2})

lemma pairIndex_card (n : ℕ) : Fintype.card (PairIndex n) = n.choose 2 := by
  classical
  change Fintype.card {ij : Fin n × Fin n // ij.1 < ij.2} = _
  rw [Fintype.card_subtype, ← Finset.univ_product_univ, Finset.card_product_filter_lt]
  simp

def pairPower (p : ℝ) {n : ℕ} (z : Fin n → ℝ) : PairIndex n → ℝ :=
  fun e => |z e.val.1 - z e.val.2| ^ p

lemma pairPower_nonneg (p : ℝ) {n : ℕ} (z : Fin n → ℝ) (e : PairIndex n) :
    0 ≤ pairPower p z e := Real.rpow_nonneg (abs_nonneg _) _

lemma pairPower_continuous (p : ℝ) (hp : 0 < p) (n : ℕ) : Continuous (pairPower (n := n) p) := by
  apply continuous_pi
  intro e
  unfold pairPower
  exact ((continuous_apply e.val.1).sub (continuous_apply e.val.2)).abs.rpow_const
    (fun _ => Or.inr hp.le)

lemma pairPower_pair_le_sum (p : ℝ) {n : ℕ} (z : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    |z i-z j|^p ≤ ∑ e, pairPower p z e := by
  classical
  rcases lt_or_gt_of_ne hij with h | h
  · exact Finset.single_le_sum (fun e _ => pairPower_nonneg p z e) (Finset.mem_univ ⟨(i,j),h⟩)
  · rw [abs_sub_comm]
    exact Finset.single_le_sum (fun e _ => pairPower_nonneg p z e) (Finset.mem_univ ⟨(j,i),h⟩)

lemma pairPower_sum_bound (p : ℝ) (hp : 0 < p) {n : ℕ} (z : Fin n → ℝ)
    (i₀ : Fin n) (hz : z i₀ = 0) (hs : ∑ e, pairPower p z e = 1) :
    ∀ i, |z i| ≤ 1 := by
  intro i
  by_cases hi : i = i₀
  · simp [hi,hz]
  have h := pairPower_pair_le_sum p z i i₀ hi
  rw [hs, hz, sub_zero] at h
  apply (Real.rpow_le_rpow_iff (abs_nonneg _) zero_le_one hp).mp
  simpa using h

def normalizedLabels (p : ℝ) {n : ℕ} (i₀ : Fin n) : Set (Fin n → ℝ) :=
  {z | z i₀ = 0 ∧ ∑ e, pairPower p z e = 1}

def normalizedPowers (p : ℝ) {n : ℕ} (i₀ : Fin n) : Set (PairIndex n → ℝ) :=
  pairPower p '' normalizedLabels p i₀

lemma normalizedLabels_compact (p : ℝ) (hp : 0 < p) {n : ℕ} (i₀ : Fin n) :
    IsCompact (normalizedLabels p i₀) := by
  have hc : IsClosed (normalizedLabels p i₀) :=
    (isClosed_eq (continuous_apply i₀) continuous_const).inter
      (isClosed_eq (continuous_finsetSum _ (fun e _ =>
        (continuous_apply e).comp (pairPower_continuous p hp n))) continuous_const)
  apply isCompact_Icc.of_isClosed_subset hc
  intro z hz
  have h := pairPower_sum_bound p hp z i₀ hz.1 hz.2
  exact ⟨fun i => (abs_le.mp (h i)).1, fun i => (abs_le.mp (h i)).2⟩

lemma normalizedPowers_compact (p : ℝ) (hp : 0 < p) {n : ℕ} (i₀ : Fin n) :
    IsCompact (normalizedPowers p i₀) :=
  (normalizedLabels_compact p hp i₀).image (pairPower_continuous p hp n)

lemma normalizedPowers_sum (p : ℝ) {n : ℕ} (i₀ : Fin n) {v : PairIndex n → ℝ}
    (hv : v ∈ normalizedPowers p i₀) : ∑ e, v e = 1 := by
  obtain ⟨z, hz, rfl⟩ := hv
  exact hz.2

lemma pairPower_smul_sub (p : ℝ) {n : ℕ} (z : Fin n → ℝ) (a b : ℝ) :
    pairPower p (fun i => a * (z i-b)) = |a|^p • pairPower p z := by
  ext e
  simp only [pairPower, Pi.smul_apply, smul_eq_mul]
  rw [show a*(z e.val.1-b)-a*(z e.val.2-b) = a*(z e.val.1-z e.val.2) by ring,
    abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]

lemma pairPower_normalize (p : ℝ) (hp : 0 < p) {n : ℕ} (i₀ : Fin n) (z : Fin n → ℝ)
    (hs : 0 < ∑ e, pairPower p z e) :
    (∑ e, pairPower p z e)⁻¹ • pairPower p z ∈ normalizedPowers p i₀ := by
  let s := ∑ e, pairPower p z e
  let a := (s⁻¹)^(1/p)
  have ha : 0 < a := Real.rpow_pos_of_pos (inv_pos.mpr hs) _
  have hap : |a|^p = s⁻¹ := by
    rw [abs_of_pos ha]
    dsimp [a]
    rw [one_div]
    exact (Real.rpow_inv_rpow (inv_nonneg.mpr hs.le) hp.ne' :
      (s⁻¹^p⁻¹)^p = s⁻¹)
  refine ⟨(fun i => a*(z i-z i₀)), ⟨by simp, ?_⟩, ?_⟩
  · rw [pairPower_smul_sub, hap]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  · rw [pairPower_smul_sub, hap]

lemma lpDifference_integrable (p : ℝ) (hp : 0 < p) {Ω : Type uΩ} [MeasurableSpace Ω]
    {μ : Measure Ω} (f g : Lp ℝ (ENNReal.ofReal p) μ) :
    Integrable (fun t => |f t-g t|^p) μ := by
  have h := ((Lp.memLp f).sub (Lp.memLp g)).norm_rpow
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
  rw [memLp_one_iff_integrable] at h
  simpa only [Real.norm_eq_abs, Pi.sub_apply, ENNReal.toReal_ofReal hp.le] using h

lemma pad_coordinates {I : Type uI} (p : ℝ) (hp : 0 < p) {k d : ℕ} (hk : k ≤ d)
    (y : I → Fin k → ℝ) : ∃ Y : I → Fin d → ℝ, ∀ i j,
      (∑ a, |Y i a-Y j a|^p) = ∑ a, |y i a-y j a|^p := by
  induction d, hk using Nat.le_induction with
  | base => exact ⟨y, fun _ _ => rfl⟩
  | succ d hd ih =>
    obtain ⟨Y,hY⟩ := ih
    refine ⟨fun i => Fin.snoc (Y i) 0, ?_⟩
    intro i j
    simpa [Fin.sum_univ_castSucc, Real.zero_rpow hp.ne'] using hY i j

end SubpolynomialLp

end

end OAI
