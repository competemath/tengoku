import Tengoku.OpenaiMath.OAI.Geometry.HarmonicGrowth.PulseODE
import Tengoku.OpenaiMath.OAI.Geometry.HarmonicGrowth.SmoothWord

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open MeasureTheory
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

lemma orthogonalMatrix_injective (b : OrthonormalBasis ι ℝ E) :
    Function.Injective (orthogonalMatrix b) := by
  intro T U h
  ext x
  apply b.repr.injective
  apply PiLp.ext
  intro i
  have hT := congrFun (orthogonalMatrix_mulVec b T x) i
  have hU := congrFun (orthogonalMatrix_mulVec b U x) i
  rw [h] at hT
  exact hT.symm.trans hU

/-- A fixed coordinate norm constant, chosen independently of the pulse,
its duration, its history and its parameters. -/
theorem orthogonalMatrix_norm_bound (b : OrthonormalBasis ι ℝ E) :
    ∃ C : ℝ,0 < C ∧ ∀ T : E →L[ℝ] E,‖T‖ ≤ C*‖orthogonalMatrix b T‖ := by
  obtain ⟨C,hC,h⟩ := (orthogonalMatrix b).toLinearMap.injective_iff_antilipschitz.1
    (orthogonalMatrix_injective b)
  exact ⟨C,by exact_mod_cast hC,fun T => ZeroHomClass.bound_of_antilipschitz (orthogonalMatrix b) h T⟩

lemma integrated_matrix_error_to_operator {a b C : ℝ} (hab : a ≤ b)
    (basis : OrthonormalBasis ι ℝ E)
    (hbound : ∀ T : E →L[ℝ] E,‖T‖ ≤ C*‖orthogonalMatrix basis T‖)
    {P Q : ℝ → E →L[ℝ] E} (hP : ContinuousOn P (Set.Icc a b))
    (hQ : ContinuousOn Q (Set.Icc a b)) :
    (∫ t in a..b,‖P t-Q t‖) ≤ C*(∫ t in a..b,‖orthogonalMatrix basis (P t)-orthogonalMatrix basis (Q t)‖) := by
  have hc := ((orthogonalMatrix basis).continuous.comp_continuousOn (hP.sub hQ)).norm
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) hab
  calc
    _ ≤ ∫ t in a..b,C*‖orthogonalMatrix basis (P t-Q t)‖ :=
      intervalIntegral.integral_mono_on hab ((hP.sub hQ).norm.intervalIntegrable_of_Icc hab)
        (hi.const_mul C) (fun t _ => hbound (P t-Q t))
    _ = C*(∫ t in a..b,‖orthogonalMatrix basis (P t)-orthogonalMatrix basis (Q t)‖) := by
      rw [intervalIntegral.integral_const_mul]
      simp only [map_sub]

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set MeasureTheory

/-- The bounded exact positive scalar from local attainment has a UNIFORM
logarithm cost. It cannot become exponentially small along histories. -/
lemma bounded_target_log {c : ℝ} (hc : c ∈ Ioo (1/2:ℝ) (3/2)) :
    |Real.log c| ≤ Real.log 2 := by
  have hc₀ : 0 < c := by linarith [hc.1]
  rw [abs_le]
  constructor
  · have h := Real.log_le_log (by norm_num : (0:ℝ) < 1/2) hc.1.le
    rw [Real.log_div one_ne_zero (by norm_num),Real.log_one,zero_sub] at h
    exact h
  · exact Real.log_le_log hc₀ (by linarith [hc.2])

/-- Undoing exactly the scalar baseline normalizer preserves an exact positive
scalar-permutation endpoint and adds only the genuine baseline integral to its
logarithm. This is an equality of actual operators, not a weighted model. -/
lemma undo_scalar_normalization {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    {Y perm : R} {I c : ℝ} (he : Real.exp (-I) • Y=c • perm) :
    Y=(Real.exp I*c) • perm := by
  have hh := congrArg (fun X : R => Real.exp I • X) he
  rw [smul_smul,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul,smul_smul] at hh
  exact hh

lemma lifted_target_log {I c V T : ℝ} (hc : c ∈ Ioo (1/2:ℝ) (3/2))
    (hI : |I| ≤ V*T) :
    0 < Real.exp I*c ∧ |Real.log (Real.exp I*c)| ≤ V*T+Real.log 2 := by
  have hc₀ : 0 < c := by linarith [hc.1]
  refine ⟨mul_pos (Real.exp_pos _) hc₀,?_⟩
  rw [Real.log_mul (Real.exp_ne_zero _) hc₀.ne',Real.log_exp]
  exact (abs_add_le _ _).trans (add_le_add hI (bounded_target_log hc))

/-- Actual scalar PB baseline integrated log cost. The constant precedes all
pulse histories and lengths; no value of an unproved scalar ODE is supplied. -/
theorem actual_baseline_log_cost {α p : ℝ → ℝ}
    (hα : Continuous α) (hp : Continuous p)
    {M Mp B β p₀ θ γ δ T : ℝ}
    (hM : 0 ≤ M) (hMp : 0 ≤ Mp) (hθ : 0 ≤ θ) (hγ : 0 < γ)
    (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (hαn : ∀ t,|α t| ≤ M) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ α t*B) (hroot : β*B-p₀*θ-θ^2=0)
    (hscale : ∀ t ∈ Icc 0 T,|α t-β| ≤ δ)
    (hpt : ∀ t ∈ Icc 0 T,|p t-p₀| ≤ δ)
    (hpl : ∀ t ∈ Icc 0 T,γ ≤ p t) :
    |∫ t in (0:ℝ)..T,scalarBaseline (fun s => α s*B) p θ t| ≤
      (θ+((|B|+|θ|)/γ)*δ)*T := by
  let v := scalarBaseline (fun s => α s*B) p θ
  have hn (s : ℝ) : |α s*B| ≤ M*|B| := by rw [abs_mul];gcongr;exact hαn s
  have hvc : ContinuousOn v (Icc 0 T) := fun t ht =>
    (actual_scalar_baseline_deriv (hα.mul continuous_const) hp
      (by positivity) hMp hn hpn hAp hθ ht.1).continuousAt.continuousWithinAt
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) : |v t| ≤ θ+((|B|+|θ|)/γ)*δ := by
    have hv := berger_scalar_baseline_close hα hp hM hMp hθ hγ hδ hαn hpn hAp
      hroot hscale hpt hpl t ht
    have he := abs_add_le (v t-θ) θ
    rw [sub_add_cancel,abs_of_nonneg hθ] at he
    linarith
  have hvi : IntervalIntegrable v volume 0 T := hvc.intervalIntegrable_of_Icc hT
  calc
    _ ≤ ∫ t in (0:ℝ)..T,|v t| := by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (f := v) hT
    _ ≤ ∫ _ in (0:ℝ)..T,θ+((|B|+|θ|)/γ)*δ :=
      intervalIntegral.integral_mono_on hT hvi.norm intervalIntegrable_const hbound
    _ = _ := by rw [intervalIntegral.integral_const];simp only [sub_zero,smul_eq_mul];ring

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
lemma bergerSlowGenerator_eq_smul (r B β p₀ θ z : ℝ) (D : R) :
    bergerSlowGenerator r B β p₀ θ z D=z • bergerSlowGenerator r B β p₀ θ 1 D := by
  simp only [bergerSlowGenerator,mul_one,smul_smul]
  rw [mul_comm z]
end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.FiniteControl.SmoothWord
open HarmonicCounterexample.LinearODE
open Set Filter
open scoped Topology BigOperators
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] {n : ℕ}

/-- Exact representation of the normalized smooth finite-word coefficient
and its time derivative by the selected Berger angular generator. -/
theorem unitBergerPacket_selected (a : Fin n → ℝ) (D : Fin n → R)
    (r B β p₀ θ : ℝ) (d : ℝ → Fin n)
    (hd : ∀ t i,i ≠ d t → bump i t=0 ∧ deriv (bump i) t=0) (t : ℝ) :
    unitPacketCoefficient a (fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)) t=
      bergerSlowGenerator r B β p₀ θ (unitPacketScalar a t) (D (d (duration n*t))) ∧
    unitPacketCoefficientD a (fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)) t=
      bergerSlowGenerator r B β p₀ θ (unitPacketScalarD a t) (D (d (duration n*t))) := by
  obtain ⟨h₁,h₂⟩ := unitPacketCoefficient_selected a
    (fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)) d hd t
  exact ⟨h₁.trans (bergerSlowGenerator_eq_smul r B β p₀ θ _ _).symm,
    h₂.trans (bergerSlowGenerator_eq_smul r B β p₀ θ _ _).symm⟩

/-- The normalized selector is locally constant unless every actual scalar
packet vanishes on a neighborhood. Thus angular changes occur on ROUND gaps. -/
theorem exists_unit_round_gap_selector (n : ℕ) [NeZero n] :
    ∃ d : ℝ → Fin n,
      (∀ t i,i ≠ d t → bump i (duration n*t)=0 ∧ deriv (bump i) (duration n*t)=0) ∧
      ∀ t,(∀ᶠ s in 𝓝 t,d s=d t) ∨
        (∀ᶠ s in 𝓝 t,∀ a : Fin n → ℝ,unitPacketScalar a s=0) := by
  obtain ⟨d,hd,he⟩ := exists_round_gap_selector n
  refine ⟨fun t => d (duration n*t),fun t i hi => hd _ i hi,fun t => ?_⟩
  have hc : Tendsto (fun s : ℝ => duration n*s) (𝓝 t) (𝓝 (duration n*t)) :=
    (continuous_const.mul continuous_id).continuousAt
  rcases he (duration n*t) with h|h
  · exact Or.inl (hc.eventually h)
  · right
    filter_upwards [hc.eventually h] with s hs
    intro a
    simp only [unitPacketScalar,packetScalar,hs,mul_zero,Finset.sum_const_zero]

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {E H ι : Type*} {n : ℕ} [NeZero n] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [Fintype ι] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

open HarmonicCounterexample.FiniteControl.SmoothWord

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
open scoped InnerProductSpace
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma norm_integral_mono_upper {F : Type*} [NormedAddCommGroup F]
    {f : ℝ → F} (hf : Continuous f) {s t : ℝ} (_hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ u in (0:ℝ)..s,‖f u‖) ≤ ∫ u in (0:ℝ)..t,‖f u‖ := by
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.norm.intervalIntegrable 0 s) (hf.norm.intervalIntegrable s t)
  have hp : 0 ≤ ∫ u in s..t,‖f u‖ := intervalIntegral.integral_nonneg hst (fun _ _ => norm_nonneg _)
  linarith

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The exact first-jet coefficient on value/parameter-derivative pairs. -/
def jetBlock (A : E →L[ℝ] E) (A' : H →L[ℝ] E →L[ℝ] E) :
    E×(H →L[ℝ] E) →L[ℝ] E×(H →L[ℝ] E) :=
  (A.comp (ContinuousLinearMap.fst ℝ E (H →L[ℝ] E))).prod
    (((ContinuousLinearMap.compL ℝ H E E) A).comp (ContinuousLinearMap.snd ℝ E (H →L[ℝ] E)) +
      A'.flip.comp (ContinuousLinearMap.fst ℝ E (H →L[ℝ] E)))

omit [CompleteSpace E] in
lemma jetBlock_apply (A : E →L[ℝ] E) (A' : H →L[ℝ] E →L[ℝ] E) (v : E×(H →L[ℝ] E)) :
    jetBlock A A' v = (A v.1,A.comp v.2+A'.flip v.1) := rfl

omit [CompleteSpace E] in
lemma jetBlock_continuous (A : ℝ → E →L[ℝ] E)
    (A' : ℝ → H →L[ℝ] E →L[ℝ] E) (hA : Continuous A) (hA' : Continuous A') :
    Continuous (fun t => jetBlock (A t) (A' t)) := by
  unfold jetBlock
  exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := E×(H →L[ℝ] E)) (F := E) (G := H →L[ℝ] E) ℝ).continuous.comp
    ((hA.clm_comp continuous_const).prodMk
    (((ContinuousLinearMap.compL ℝ H E E).continuous.comp hA).clm_comp continuous_const |>.add
      (((ContinuousLinearMap.flipₗᵢ ℝ H E E).continuous.comp hA').clm_comp continuous_const)))

omit [CompleteSpace E] in
lemma jetBlock_norm (A : E →L[ℝ] E) (A' : H →L[ℝ] E →L[ℝ] E) :
    ‖jetBlock A A'‖ ≤ ‖A‖+‖A'‖ := by
  apply (jetBlock A A').opNorm_le_bound (M := ‖A‖+‖A'‖) (add_nonneg (norm_nonneg A) (norm_nonneg A'))
  intro v
  rw [jetBlock_apply,Prod.norm_def]
  apply max_le
  · calc
      ‖A v.1‖ ≤ ‖A‖*‖v.1‖ := A.le_opNorm _
      _ ≤ (‖A‖+‖A'‖)*‖v‖ := by
        rw [Prod.norm_def]
        exact mul_le_mul (le_add_of_nonneg_right (norm_nonneg A')) (le_max_left _ _)
          (norm_nonneg _) (add_nonneg (norm_nonneg A) (norm_nonneg A'))
  · calc
      _ ≤ ‖A.comp v.2‖+‖A'.flip v.1‖ := norm_add_le _ _
      _ ≤ ‖A‖*‖v.2‖+‖A'‖*‖v.1‖ := by
        apply add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
        simpa only [ContinuousLinearMap.opNorm_flip] using A'.flip.le_opNorm v.1
      _ ≤ (‖A‖+‖A'‖)*‖v‖ := by
        rw [Prod.norm_def,add_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg A'))

/-- The actual parameter jet is itself the actual constructed linear flow. -/
lemma flow_jet (A : H → ℝ → E →L[ℝ] E) (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (hA : ∀ p,Continuous (A p)) (hA' : ∀ p,Continuous (A' p))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ p s,‖A p s‖ ≤ M) (hb' : ∀ p s,‖A' p s‖ ≤ M)
    (x : E) (p : H) (t : ℝ) :
    (flow (A p) x t,flowD A A' x p t) =
      flow (fun s => jetBlock (A p s) (A' p s)) (x,0) t := by
  have hJ := jetBlock_continuous (A p) (A' p) (hA p) (hA' p)
  have hJb (s : ℝ) : ‖jetBlock (A p s) (A' p s)‖ ≤ 2*M :=
    (jetBlock_norm _ _).trans (by linarith [hb p s,hb' p s])
  have hd (s : ℝ) : HasDerivAt (fun u => (flow (A p) x u,flowD A A' x p u))
      (jetBlock (A p s) (A' p s) (flow (A p) x s,flowD A A' x p s)) s :=
    (flow_hasDerivAt (hA p) hM (hb p) x s).prodMk (flowD_hasDerivAt A A' hA hA' hM hb hb' x p s)
  have he := solution_unique (by positivity : 0 ≤ 2*M) hJb hd
    (flow_hasDerivAt hJ (by positivity) hJb (x,0)) (t₀ := 0)
    (by simp only [flow_initial,flowD_initial])
  exact congrFun he t

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open MeasureTheory
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Rescaling an integrated error introduces NO pulse-duration factor. -/
lemma slow_time_integral_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : ℝ → F) (a : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ τ in (0:ℝ)..1,‖T • X (a+T*τ)‖)=(∫ t in a..a+T,‖X t‖) := by
  simp_rw [norm_smul,Real.norm_eq_abs,abs_of_pos hT]
  rw [intervalIntegral.integral_const_mul]
  have he := intervalIntegral.integral_comp_add_mul (f := fun t => ‖X t‖)
    (a := (0:ℝ)) (b := 1) hT.ne' a
  rw [he]
  simp only [mul_zero,add_zero,mul_one,smul_eq_mul]
  field_simp

omit [CompleteSpace E] in
lemma jetBlock_integral_le {A : ℝ → E →L[ℝ] E}
    {A' : ℝ → H →L[ℝ] E →L[ℝ] E}
    (hA : Continuous A) (hA' : Continuous A') {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0:ℝ)..t,‖jetBlock (A s) (A' s)‖) ≤
      (∫ s in (0:ℝ)..t,‖A s‖)+(∫ s in (0:ℝ)..t,‖A' s‖) := by
  have hc := jetBlock_continuous A A' hA hA'
  have hnc := Continuous.norm (E := E×(H →L[ℝ] E) →L[ℝ] E×(H →L[ℝ] E)) hc
  calc
    _ ≤ ∫ s in (0:ℝ)..t,‖A s‖+‖A' s‖ :=
      intervalIntegral.integral_mono_on (f := fun s => ‖jetBlock (A s) (A' s)‖) ht
        (hnc.intervalIntegrable 0 t)
        ((hA.norm.add (Continuous.norm (E := H →L[ℝ] E →L[ℝ] E) hA')).intervalIntegrable 0 t) (fun _ _ => jetBlock_norm _ _)
    _ = _ := intervalIntegral.integral_add (hA.norm.intervalIntegrable 0 t)
      ((Continuous.norm (E := H →L[ℝ] E →L[ℝ] E) hA').intervalIntegrable 0 t)

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
variable {H F ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

/-- Finite-direction estimates control the genuine derivative operator norm.
No interchange of supremum and integral is used. -/
lemma opNorm_le_sum_basis (b : OrthonormalBasis ι ℝ H) (L : H →L[ℝ] F) :
    ‖L‖ ≤ ∑ i,‖L (b i)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _) 
  intro x
  calc
    ‖L x‖ = ‖∑ i,⟪b i,x⟫_ℝ • L (b i)‖ := by
      conv_lhs => rw [← b.sum_repr' x]
      rw [map_sum]; simp only [map_smul]
    _ ≤ ∑ i,‖⟪b i,x⟫_ℝ • L (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ i,‖x‖*‖L (b i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      have h : ‖⟪b i,x⟫_ℝ‖ ≤ ‖x‖ := by
        simpa only [b.norm_eq_one i,one_mul] using (norm_inner_le_norm (𝕜 := ℝ) (b i) x)
      exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = (∑ i,‖L (b i)‖)*‖x‖ := by rw [← Finset.mul_sum, mul_comm]

/-- Turning the integrated raywise Riccati-jet estimates into the C1 operator
estimate costs only the FIXED parameter dimension, never the pulse duration. -/
theorem integrated_opNorm_le_basis_sum (b : OrthonormalBasis ι ℝ H)
    {L : ℝ → H →L[ℝ] F} {a z C : ℝ} (haz : a ≤ z)
    (hL : ContinuousOn L (Set.Icc a z))
    (hI : ∀ i,(∫ t in a..z,‖L t (b i)‖) ≤ C) :
    (∫ t in a..z,‖L t‖) ≤ (Fintype.card ι:ℝ)*C := by
  have hc (i : ι) : ContinuousOn (fun t => ‖L t (b i)‖) (Set.Icc a z) :=
    (hL.clm_apply continuousOn_const).norm
  calc
    _ ≤ ∫ t in a..z,∑ i,‖L t (b i)‖ :=
      intervalIntegral.integral_mono_on haz (hL.norm.intervalIntegrable_of_Icc haz)
        ((continuousOn_finsetSum _ (fun i _ => hc i)).intervalIntegrable_of_Icc haz)
        (fun _ _ => opNorm_le_sum_basis b _)
    _ = ∑ i,∫ t in a..z,‖L t (b i)‖ := by
      rw [intervalIntegral.integral_finsetSum]
      intro i _;exact (hc i).intervalIntegrable_of_Icc haz
    _ ≤ ∑ _i : ι,C := Finset.sum_le_sum fun i _ => hI i
    _ = _ := by simp

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {E H ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype κ]

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open MeasureTheory
variable {E H V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup V] [NormedSpace ℝ V]

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {E H F ι κ : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype κ]

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {E H ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype κ]

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
/-- Exterior extension is by constant coefficients, never by altering the
actual solution on the pulse. -/
def clip01 (t : ℝ) : ℝ := min 1 (max 0 t)
lemma clip01_continuous : Continuous clip01 :=
  continuous_const.min (continuous_const.max continuous_id)
lemma clip01_mem (t : ℝ) : clip01 t ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_min zero_le_one (le_max_left _ _),min_le_left _ _⟩
lemma clip01_eq {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : clip01 t=t := by
  rw [clip01,max_eq_right ht.1,min_eq_right ht.2]
lemma integral_clip01 (f : ℝ → ℝ) :
    (∫ t in (0:ℝ)..1,f (clip01 t))=∫ t in (0:ℝ)..1,f t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
  change f (clip01 t)=f t
  rw [clip01_eq ht]
end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {E H ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype κ]

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- PB iteration uses only coefficient values on the actual elapsed interval. -/
lemma term_congr_interval {A B : ℝ → E →L[ℝ] E} {b : ℝ}
    (hAB : EqOn A B (Icc 0 b)) (x : E) (n : ℕ) :
    ∀ t ∈ Icc 0 b,term A x n t=term B x n t := by
  induction n with
  | zero => intro t ht; rfl
  | succ n ih =>
    intro t ht
    simp only [term]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hsb : s ∈ Icc 0 b := ⟨hs.1,hs.2.trans ht.2⟩
    change A s (term A x n s)=B s (term B x n s)
    rw [hAB hsb,ih s hsb]

/-- Exact identity, not an endpoint estimate, under exterior coefficient
extension; this also identifies genuine parameter derivatives by congruence. -/
lemma flow_congr_interval {A B : ℝ → E →L[ℝ] E} {b : ℝ}
    (hAB : EqOn A B (Icc 0 b)) (x : E) {t : ℝ} (ht : t ∈ Icc 0 b) :
    flow A x t=flow B x t := by
  unfold flow
  apply tsum_congr
  intro n
  exact term_congr_interval hAB x n t ht

lemma flow_clip01_endpoint (A : ℝ → E →L[ℝ] E) (x : E) :
    flow (fun t => A (clip01 t)) x 1=flow A x 1 :=
  flow_congr_interval (fun t ht => congrArg A (clip01_eq ht)) x ⟨by norm_num,le_rfl⟩

/-- The Frobenius integrated error of the normalized coefficient is EXACTLY
that of the actual physical-time Riccati comparison. No factor T is lost. -/
lemma normalized_matrix_integral {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (P S : ℝ → F) (v : ℝ → ℝ) (I : F) (a : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ u in (0:ℝ)..1,‖L (T • (P (a+T*u)-v (a+T*u) • I))-L (S u)‖)=
    ∫ t in a..a+T,‖L (P t)-L (v t • I+T⁻¹ • S (T⁻¹*(t-a)))‖ := by
  let X : ℝ → G := fun t => L (P t)-L (v t • I+T⁻¹ • S (T⁻¹*(t-a)))
  have he (u : ℝ) :
      L (T • (P (a+T*u)-v (a+T*u) • I))-L (S u)=T • X (a+T*u) := by
    have hu : T⁻¹*(a+T*u-a)=u := by field_simp;ring
    dsimp [X]
    rw [hu]
    simp only [map_smul,map_sub,map_add,smul_sub,smul_add,smul_smul,mul_inv_cancel₀ hT.ne',one_smul]
    module
  calc
    _ = ∫ u in (0:ℝ)..1,‖T • X (a+T*u)‖ := by
      apply intervalIntegral.integral_congr
      intro u _
      exact congrArg norm (he u)
    _ = _ := slow_time_integral_norm X a hT

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [CompleteSpace E] in
/-- Peano--Baker construction is causal on the positive half line, before any
existence/summability assumption is imposed. -/
lemma term_history_eq {A B : ℝ → E →L[ℝ] E} {T : ℝ}
    (h : Set.EqOn A B (Set.Icc 0 T)) (x : E) (n : ℕ) :
    Set.EqOn (term A x n) (term B x n) (Set.Icc 0 T) := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    intro t ht
    simp only [term]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht.1] at hs
    have hsT : s ∈ Set.Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
    change A s (term A x n s)=B s (term B x n s)
    rw [h hsT,ih hsT]

omit [CompleteSpace E] in
lemma flow_history_eq {A B : ℝ → E →L[ℝ] E} {T : ℝ}
    (h : Set.EqOn A B (Set.Icc 0 T)) (x : E) :
    Set.EqOn (flow A x) (flow B x) (Set.Icc 0 T) := by
  intro t ht
  exact tsum_congr (fun n => term_history_eq h x n ht)

omit [CompleteSpace E] in
/-- A control parameter not used in the incoming history has identically zero
actual variational flow throughout that history. -/
lemma termD_history_zero {A : H → ℝ → E →L[ℝ] E}
    {A' : H → ℝ → H →L[ℝ] E →L[ℝ] E} {p : H} {T : ℝ}
    (h : ∀ t ∈ Set.Icc 0 T,A' p t=0) (x : E) (n : ℕ) :
    ∀ t ∈ Set.Icc 0 T,termD A A' x p n t=0 := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    intro t ht
    simp only [termD]
    have hz : (∫ s in (0:ℝ)..t,
        (A p s).comp (termD A A' x p n s)+(A' p s).flip (term (A p) x n s)) =
        ∫ _ in (0:ℝ)..t,(0:H →L[ℝ] E) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le ht.1] at hs
      have hsT : s ∈ Set.Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
      simp only [h s hsT,ih s hsT,ContinuousLinearMap.comp_zero,
        ContinuousLinearMap.flip_zero,zero_apply,add_zero]
    simpa only [intervalIntegral.integral_zero] using hz

omit [CompleteSpace E] in
lemma flowD_history_zero {A : H → ℝ → E →L[ℝ] E}
    {A' : H → ℝ → H →L[ℝ] E →L[ℝ] E} {p : H} {T : ℝ}
    (h : ∀ t ∈ Set.Icc 0 T,A' p t=0) (x : E) :
    ∀ t ∈ Set.Icc 0 T,flowD A A' x p t=0 := by
  intro t ht
  unfold flowD
  simp only [termD_history_zero h x _ t ht,tsum_zero]

omit [CompleteSpace E] in
/-- Exact restart, independent of earlier coefficients, follows from interval
ODE uniqueness with the actual incoming value, not an artificially reset value. -/
lemma solution_unique_on_Icc {A : ℝ → E →L[ℝ] E} {M a b : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t ∈ Set.Ico a b,‖A t‖ ≤ M) {f g : ℝ → E}
    (hfc : ContinuousOn f (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b))
    (hf : ∀ t ∈ Set.Ico a b,HasDerivAt f (A t (f t)) t)
    (hg : ∀ t ∈ Set.Ico a b,HasDerivAt g (A t (g t)) t)
    (he : f a=g a) : Set.EqOn f g (Set.Icc a b) := by
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => Set.univ) (K := ⟨M,hM⟩)
    (fun t ht => ((A t).lipschitzWith.weaken (hb t ht)).lipschitzOnWith)
    hfc (fun t ht => (hf t ht).hasDerivWithinAt) (fun _ _ => Set.mem_univ _)
    hgc (fun t ht => (hg t ht).hasDerivWithinAt) (fun _ _ => Set.mem_univ _) he

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def scalarNormalized (v : ℝ → ℝ) (a : ℝ) (f : ℝ → E) (t : ℝ) : E :=
  Real.exp (-(∫ s in a..t,v s)) • f t

omit [CompleteSpace E] in
/-- Removing the exact scalar baseline, rather than its frozen limit, from an
actual solution is an exact differentiable identity. -/
lemma scalarNormalized_deriv {v : ℝ → ℝ} (hv : Continuous v)
    {P : ℝ → E →L[ℝ] E} {f : ℝ → E} {a t : ℝ}
    (hf : HasDerivAt f (P t (f t)) t) :
    HasDerivAt (scalarNormalized v a f)
      ((P t-v t • ContinuousLinearMap.id ℝ E) (scalarNormalized v a f t)) t := by
  have hi := intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable a t)
    hv.stronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt
  have he := hi.neg.exp
  have hd := he.smul hf
  apply hd.congr_deriv
  simp only [sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,map_smul,scalarNormalized]
  module

omit [CompleteSpace E] in
lemma scalarNormalized_initial (v : ℝ → ℝ) (a : ℝ) (f : ℝ → E) :
    scalarNormalized v a f a=f a := by simp [scalarNormalized]

omit [CompleteSpace E] in
/-- Exact passage to slow pulse time. The factor T belongs inside the
coefficient; scalar phase may grow with T but causes no error amplification. -/
lemma scalarNormalized_rescaled_deriv {v : ℝ → ℝ} (hv : Continuous v)
    {P : ℝ → E →L[ℝ] E} {f : ℝ → E} {a T τ : ℝ}
    (hf : HasDerivAt f (P (a+T*τ) (f (a+T*τ))) (a+T*τ)) :
    HasDerivAt (fun u => scalarNormalized v a f (a+T*u))
      ((T • (P (a+T*τ)-v (a+T*τ) • ContinuousLinearMap.id ℝ E))
        (scalarNormalized v a f (a+T*τ))) τ := by
  have hc : HasDerivAt (fun u : ℝ => a+T*u) T τ := by
    simpa only [mul_one,id_eq] using ((hasDerivAt_id τ).const_mul T).const_add a
  simpa only [Function.comp_def,smul_apply] using
    (scalarNormalized_deriv (a := a) hv hf).scomp τ hc

/-- The normalized ACTUAL solution equals the actual constructed first-order
flow on the entire pulse. The incoming value is not replaced or estimated. -/
theorem scalarNormalized_eq_flow {v : ℝ → ℝ} (hv : Continuous v)
    {P : ℝ → E →L[ℝ] E} {f : ℝ → E} {a T : ℝ}
    (hf : ∀ t,HasDerivAt f (P t (f t)) t)
    {C : ℝ → E →L[ℝ] E}
    (hC : Continuous C) {M : ℝ} (hM : 0 ≤ M) (hCb : ∀ t,‖C t‖ ≤ M)
    (hCe : ∀ τ ∈ Set.Icc (0:ℝ) 1,
      C τ=T • (P (a+T*τ)-v (a+T*τ) • ContinuousLinearMap.id ℝ E)) :
    ∀ τ ∈ Set.Icc (0:ℝ) 1,
      scalarNormalized v a f (a+T*τ)=flow C (f a) τ := by
  have hd (τ : ℝ) := scalarNormalized_rescaled_deriv hv (a := a) (T := T) (hf (a+T*τ))
  apply solution_unique_on_Icc hM (fun t _ => hCb t)
    ((continuous_iff_continuousAt.2 fun τ => (hd τ).continuousAt).continuousOn)
    ((continuous_iff_continuousAt.2 fun τ => (flow_hasDerivAt hC hM hCb (f a) τ).continuousAt).continuousOn)
    (fun τ hτ => by rw [hCe τ ⟨hτ.1,hτ.2.le⟩]; exact hd τ)
    (fun τ _ => flow_hasDerivAt hC hM hCb (f a) τ)
  simp only [mul_zero,add_zero,scalarNormalized_initial,flow_initial]

omit [CompleteSpace E] in
/-- The scalar baseline is independent of the current control parameter, so
normalization commutes exactly with its Frechet derivative. -/
lemma scalarNormalized_hasFDerivAt_parameter {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : H → ℝ → E} {f' : H →L[ℝ] E} {p : H} {v : ℝ → ℝ} {a t : ℝ}
    (hf : HasFDerivAt (fun q => f q t) f' p) :
    HasFDerivAt (fun q => scalarNormalized v a (f q) t)
      (Real.exp (-(∫ s in a..t,v s)) • f') p := hf.const_smul _

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Local normalization: only integrability from a to t and continuity at t
are required of the scalar baseline. Irrelevant pre-pulse poles are allowed. -/
lemma scalarNormalized_deriv_local {v : ℝ → ℝ} {a t : ℝ}
    (hvint : IntervalIntegrable v volume a t) (hvmeas : StronglyMeasurableAtFilter v (𝓝 t))
    (hv : ContinuousAt v t) {P : ℝ → E →L[ℝ] E} {f : ℝ → E}
    (hf : HasDerivAt f (P t (f t)) t) :
    HasDerivAt (scalarNormalized v a f)
      ((P t-v t • ContinuousLinearMap.id ℝ E) (scalarNormalized v a f t)) t := by
  have hi := intervalIntegral.integral_hasDerivAt_right hvint hvmeas hv
  have hd := hi.neg.exp.smul hf
  apply hd.congr_deriv
  simp only [sub_apply,smul_apply,ContinuousLinearMap.id_apply,map_smul,scalarNormalized]
  module

omit [CompleteSpace E] in
lemma scalarNormalized_rescaled_deriv_local {v : ℝ → ℝ} {a T τ : ℝ}
    (hvint : IntervalIntegrable v volume a (a+T*τ))
    (hvmeas : StronglyMeasurableAtFilter v (𝓝 (a+T*τ)))
    (hv : ContinuousAt v (a+T*τ)) {P : ℝ → E →L[ℝ] E} {f : ℝ → E}
    (hf : HasDerivAt f (P (a+T*τ) (f (a+T*τ))) (a+T*τ)) :
    HasDerivAt (fun u => scalarNormalized v a f (a+T*u))
      ((T • (P (a+T*τ)-v (a+T*τ) • ContinuousLinearMap.id ℝ E))
        (scalarNormalized v a f (a+T*τ))) τ := by
  have hc : HasDerivAt (fun u : ℝ => a+T*u) T τ := by
    simpa only [mul_one,id_eq] using ((hasDerivAt_id τ).const_mul T).const_add a
  simpa only [Function.comp_def,smul_apply] using
    (scalarNormalized_deriv_local hvint hvmeas hv hf).scomp τ hc

/-- Exact identification of the normalized actual solution with PB flow,
using derivatives only on the pulse. The exterior extension is applied only
to its coefficient, never to the unknown solution or its derivative. -/
theorem scalarNormalized_eq_flow_on {v : ℝ → ℝ} {a T : ℝ}
    (hT : 0 ≤ T) (hvc : ∀ t ∈ Icc a (a+T),ContinuousAt v t)
    (hvm : StronglyMeasurable v)
    {P : ℝ → E →L[ℝ] E} {f : ℝ → E}
    (hf : ∀ t ∈ Icc a (a+T),HasDerivAt f (P t (f t)) t)
    {C : ℝ → E →L[ℝ] E}
    (hC : Continuous C) {M : ℝ} (hM : 0 ≤ M) (hCb : ∀ t,‖C t‖ ≤ M)
    (hCe : ∀ τ ∈ Icc (0:ℝ) 1,
      C τ=T • (P (a+T*τ)-v (a+T*τ) • ContinuousLinearMap.id ℝ E)) :
    ∀ τ ∈ Icc (0:ℝ) 1,
      scalarNormalized v a f (a+T*τ)=flow C (f a) τ := by
  have hvcOn : ContinuousOn v (Icc a (a+T)) := fun t ht => (hvc t ht).continuousWithinAt
  have hτt (τ : ℝ) (hτ : τ ∈ Icc (0:ℝ) 1) : a+T*τ ∈ Icc a (a+T) := by
    constructor <;> nlinarith [mul_nonneg hT hτ.1,mul_le_mul_of_nonneg_left hτ.2 hT]
  have hd (τ : ℝ) (hτ : τ ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun u => scalarNormalized v a f (a+T*u))
        (C τ (scalarNormalized v a f (a+T*τ))) τ := by
    rw [hCe τ hτ]
    have ht := hτt τ hτ
    apply scalarNormalized_rescaled_deriv_local _ hvm.stronglyMeasurableAtFilter (hvc _ ht) (hf _ ht)
    exact (hvcOn.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  apply solution_unique_on_Icc hM (fun t _ => hCb t)
    (fun τ hτ => (hd τ hτ).continuousAt.continuousWithinAt)
    ((continuous_iff_continuousAt.2 fun τ => (flow_hasDerivAt hC hM hCb (f a) τ).continuousAt).continuousOn)
    (fun τ hτ => hd τ ⟨hτ.1,hτ.2.le⟩)
    (fun τ _ => flow_hasDerivAt hC hM hCb (f a) τ)
  simp only [mul_zero,add_zero,scalarNormalized_initial,flow_initial]

/-- Constant exterior extension of a pulse coefficient. Its boundedness
follows from genuine continuity on the compact pulse, rather than global
invertibility of an irrelevant scalar comparison. -/
def clippedPulse (C : ℝ → E →L[ℝ] E) : ℝ → E →L[ℝ] E :=
  IccExtend (by norm_num : (0:ℝ) ≤ 1) (fun s : Icc (0:ℝ) 1 => C s)

omit [CompleteSpace E] in
lemma clippedPulse_eq (C : ℝ → E →L[ℝ] E) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    clippedPulse C t=C t := IccExtend_of_mem _ _ ht

omit [CompleteSpace E] in
lemma clippedPulse_continuous {C : ℝ → E →L[ℝ] E} (hC : ContinuousOn C (Icc (0:ℝ) 1)) :
    Continuous (clippedPulse C) :=
  continuous_IccExtend_iff.2 (continuousOn_iff_continuous_domRestrict.1 hC)

omit [CompleteSpace E] in
lemma clippedPulse_bounded {C : ℝ → E →L[ℝ] E} (hC : ContinuousOn C (Icc (0:ℝ) 1)) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ t,‖clippedPulse C t‖ ≤ M := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hC
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro t
  exact (hM _ (projIcc _ _ (by norm_num : (0:ℝ) ≤ 1) t).property).trans (le_max_left _ _)

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A coarse finite-time bound used ONLY to justify local parameter
 differentiation; it is not the uniform-history C1 error constant. -/
lemma flowD_norm_bound_pointwise
    (A : H → ℝ → E →L[ℝ] E) (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    {p : H} (hA : Continuous (A p)) (hA' : Continuous (A' p))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ s,‖A p s‖ ≤ M) (hb' : ∀ s,‖A' p s‖ ≤ M)
    (x : E) (t : ℝ) : ‖flowD A A' x p t‖ ≤ ‖x‖*Real.exp (2*M*|t|) := by
  unfold flowD
  apply tsum_of_norm_bounded
    (show HasSum (fun n : ℕ => ‖x‖*((2*M*|t|)^n/(n.factorial:ℝ)))
      (‖x‖*Real.exp (2*M*|t|)) from by
        simpa only [← Real.exp_eq_exp_ℝ] using
          (NormedSpace.expSeries_div_hasSum_exp (2*M*|t|)).mul_left ‖x‖)
  intro n
  simpa only [mul_pow,mul_div_assoc,mul_assoc] using
    termD_bound_at_parameter A A' hA hA' hM hb hb' x n t

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
open scoped InnerProductSpace
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
open scoped InnerProductSpace
variable {E H ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [Fintype ι] [Fintype κ] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
open scoped InnerProductSpace
variable {E H ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [Fintype ι] [Fintype κ] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.LinearODE

end

end OAI
