import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A polar Hadamard extension lemma

If `f` is differentiable at the origin and vanishes there, then its first
difference quotient along a continuously varying direction has a continuous
extension across polar radius zero.  No compactness or finite-dimensionality
assumption is needed: continuity of the direction supplies the local
boundedness used to turn the derivative remainder `o(‖x‖)` into `o(|r|)`.
-/

noncomputable section

open Filter Function
open scoped Topology

namespace Submission

set_option autoImplicit false

/-- The first polar quotient, filled in by the derivative at radius zero.-/
def polarFirstQuotient
    {E F T : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (D : E →L[ℝ] F) (v : T → E)
    (q : ℝ × T) : F :=
  if q.1 = 0 then D (v q.2)
  else q.1⁻¹ • f (q.1 • v q.2)

/-- Away from no point at all (including radius zero), the filled polar
quotient is the derivative in the varying direction plus the rescaled
derivative remainder.-/
theorem polarFirstQuotient_eq_linear_add_remainder
    {E F T : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (D : E →L[ℝ] F) (v : T → E)
    (hf0 : f 0 = 0) (q : ℝ × T) :
    polarFirstQuotient f D v q =
      D (v q.2) + q.1⁻¹ • (f (q.1 • v q.2) - D (q.1 • v q.2)) := by
  by_cases hr : q.1 = 0
  · simp [polarFirstQuotient, hr, hf0]
  · rw [polarFirstQuotient, ite_eq_right hr]
    calc
      q.1⁻¹ • f (q.1 • v q.2) =
          q.1⁻¹ • (D (q.1 • v q.2) +
            (f (q.1 • v q.2) - D (q.1 • v q.2))) := by
              congr 1
              abel
      _ = q.1⁻¹ • D (q.1 • v q.2) +
          q.1⁻¹ • (f (q.1 • v q.2) - D (q.1 • v q.2)) := by
            rw [smul_add]
      _ = D (v q.2) +
          q.1⁻¹ • (f (q.1 • v q.2) - D (q.1 • v q.2)) := by
            rw [D.map_smul]
            simp [hr]

/-- The derivative remainder divided by the polar radius tends to zero,
uniformly for a direction parameter tending to `t₀`.-/
theorem tendsto_polarFirstRemainder_div
    {E F T : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace T]
    (f : E → F) (D : E →L[ℝ] F) (v : T → E) (t₀ : T)
    (hf : HasFDerivAt f D 0) (hf0 : f 0 = 0)
    (hv : ContinuousAt v t₀) :
    Tendsto
      (fun q : ℝ × T =>
        q.1⁻¹ • (f (q.1 • v q.2) - D (q.1 • v q.2)))
      (nhds (0, t₀)) (nhds 0) := by
  let x : ℝ × T → E := fun q => q.1 • v q.2
  let r : ℝ × T → ℝ := fun q => q.1
  have hv_snd :
      ContinuousAt (fun q : ℝ × T => v q.2) (0, t₀) := by
    change ContinuousAt (v ∘ Prod.snd) (0, t₀)
    exact hv.comp continuousAt_snd
  have hx_tendsto : Tendsto x (nhds (0, t₀)) (nhds 0) := by
    have hr_fst :
        ContinuousAt (fun q : ℝ × T => q.1) (0, t₀) :=
      continuousAt_fst
    have h := hr_fst.smul hv_snd
    have h' :
        Tendsto (fun q : ℝ × T => q.1 • v q.2)
          (nhds (0, t₀)) (nhds ((0 : ℝ) • v t₀)) := by
      refine h.congr' ?_
      exact Eventually.of_forall fun _q => rfl
    simpa [x] using h'
  have hrem : (fun y : E => f y - D y) =o[nhds 0] (fun y => y) := by
    simpa [hf0] using (hasFDerivAt_iff_isLittleO_nhds_zero.mp hf)
  have hrem_comp :
      (fun q : ℝ × T => f (x q) - D (x q)) =o[nhds (0, t₀)] x := by
    simpa [Function.comp_def] using hrem.comp_tendsto hx_tendsto
  have hv_tendsto :
      Tendsto (fun q : ℝ × T => v q.2) (nhds (0, t₀)) (nhds (v t₀)) :=
    hv_snd
  have hv_bigO :
      (fun q : ℝ × T => v q.2) =O[nhds (0, t₀)]
        (fun _q : ℝ × T => (1 : ℝ)) :=
    hv_tendsto.isBigO_one ℝ
  obtain ⟨c, hc⟩ := hv_bigO.bound
  have hx_bigO : x =O[nhds (0, t₀)] r := by
    apply Asymptotics.IsBigO.of_bound c
    filter_upwards [hc] with q hq
    have hmul := mul_le_mul_of_nonneg_left hq (norm_nonneg q.1)
    simpa [x, r, norm_smul, mul_comm] using hmul
  have hrem_radius :
      (fun q : ℝ × T => f (x q) - D (x q)) =o[nhds (0, t₀)] r :=
    hrem_comp.trans_isBigO hx_bigO
  simpa [x, r] using hrem_radius.tendsto_inv_smul_nhds_zero

/-- A Hadamard-style extension theorem for the first polar quotient.-/
theorem continuousAt_polarFirstQuotient
    {E F T : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace T]
    (f : E → F) (D : E →L[ℝ] F) (v : T → E) (t₀ : T)
    (hf : HasFDerivAt f D 0) (hf0 : f 0 = 0)
    (hv : ContinuousAt v t₀) :
    ContinuousAt (polarFirstQuotient f D v) (0, t₀) := by
  have hv_snd :
      ContinuousAt (fun q : ℝ × T => v q.2) (0, t₀) := by
    change ContinuousAt (v ∘ Prod.snd) (0, t₀)
    exact hv.comp continuousAt_snd
  have hlinear :
      Tendsto (fun q : ℝ × T => D (v q.2))
        (nhds (0, t₀)) (nhds (D (v t₀))) := by
    have hD : ContinuousAt D (v t₀) := D.continuous.continuousAt
    simpa [Function.comp_def] using
      (Filter.Tendsto.comp (f := fun q : ℝ × T => v q.2) (g := D)
        hD hv_snd)
  have hremainder := tendsto_polarFirstRemainder_div f D v t₀ hf hf0 hv
  have hsum :
      Tendsto
        (fun q : ℝ × T =>
          D (v q.2) +
            q.1⁻¹ • (f (q.1 • v q.2) - D (q.1 • v q.2)))
        (nhds (0, t₀)) (nhds (D (v t₀))) := by
    simpa using hlinear.add hremainder
  have heq :
      polarFirstQuotient f D v = fun q : ℝ × T =>
        D (v q.2) +
          q.1⁻¹ • (f (q.1 • v q.2) - D (q.1 • v q.2)) := by
    funext q
    exact polarFirstQuotient_eq_linear_add_remainder f D v hf0 q
  rw [heq]
  simpa only [ContinuousAt, Prod.fst, Prod.snd, inv_zero, zero_smul,
    add_zero] using hsum

end Submission
