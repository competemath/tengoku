import Tengoku.OpenaiMath.OAI.Geometry.HarmonicGrowth.ScalarODE
import Tengoku.OpenaiMath.OAI.Geometry.HarmonicGrowth.Taylor

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.LinearODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- Exact scalar-baseline cancellation. Keeping v exact removes a term of
size (a-a_*) times the long pulse duration. -/
lemma slow_residual_identity (A₀ p p₀ v θ τ : ℝ) (S Sdot Err : R) :
    (A₀ • (1:R)+((p₀+2*θ)*τ) • S+Err)-
      p • (v • (1:R)+τ • S)-(v • (1:R)+τ • S)*(v • (1:R)+τ • S)-
      ((A₀-p*v-v^2) • (1:R)+(τ^2) • Sdot) =
      Err+((p₀+2*θ-p-2*v)*τ) • S-(τ^2) • (S*S+Sdot) := by
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,smul_smul,smul_add]
  module

/-- Exact first parameter derivative of that residual. The scalar baseline and
p are independent of the CURRENT control parameter. -/
lemma slow_residual_jet_identity (p p₀ v θ τ : ℝ) (S Sh Shdot Errh : R) :
    (((p₀+2*θ)*τ) • Sh+Errh)-p • (τ • Sh)-
      (τ • Sh)*(v • (1:R)+τ • S)-(v • (1:R)+τ • S)*(τ • Sh)-
      (τ^2) • Shdot =
      Errh+((p₀+2*θ-p-2*v)*τ) • Sh-(τ^2) • (Sh*S+S*Sh+Shdot) := by
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,smul_smul,smul_add]
  module

/-- A uniform slow-pulse residual bound with completely explicit constants. -/
lemma slow_residual_bound {Err S Sdot : R} {C δ τ ε : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ)
    (he : ‖Err‖ ≤ C*(δ*τ+τ^2)) (hε : |ε| ≤ 3*C*δ)
    (hS : ‖S‖ ≤ C) (hSd : ‖Sdot‖ ≤ C) :
    ‖Err+(ε*τ) • S-(τ^2) • (S*S+Sdot)‖ ≤
      (3*C^2+2*C)*(δ*τ+τ^2) := by
  have hn : ‖S*S+Sdot‖ ≤ C^2+C := by
    calc
      _ ≤ ‖S*S‖+‖Sdot‖ := norm_add_le _ _
      _ ≤ ‖S‖*‖S‖+C := add_le_add (norm_mul_le _ _) hSd
      _ ≤ C*C+C := by nlinarith [mul_self_le_mul_self (norm_nonneg S) hS]
      _ = _ := by ring
  calc
    _ ≤ ‖Err‖+‖(ε*τ) • S‖+‖(τ^2) • (S*S+Sdot)‖ :=
      (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ = ‖Err‖+|ε| *τ*‖S‖+τ^2*‖S*S+Sdot‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hτ,abs_of_nonneg (sq_nonneg τ),mul_assoc]
    _ ≤ C*(δ*τ+τ^2)+(3*C*δ)*τ*C+τ^2*(C^2+C) := by
      gcongr
    _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg C) (sq_nonneg τ),mul_nonneg hC (mul_nonneg hδ hτ)]

lemma slow_residual_jet_bound {Errh S Sh Shdot : R} {C δ τ ε : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ)
    (he : ‖Errh‖ ≤ C*(δ*τ+τ^2)) (hε : |ε| ≤ 3*C*δ)
    (hS : ‖S‖ ≤ C) (hSh : ‖Sh‖ ≤ C) (hShd : ‖Shdot‖ ≤ C) :
    ‖Errh+(ε*τ) • Sh-(τ^2) • (Sh*S+S*Sh+Shdot)‖ ≤
      (3*C^2+2*C)*(δ*τ+τ^2) := by
  have hn : ‖Sh*S+S*Sh+Shdot‖ ≤ 2*C^2+C := by
    calc
      _ ≤ ‖Sh*S+S*Sh‖+‖Shdot‖ := norm_add_le _ _
      _ ≤ (‖Sh*S‖+‖S*Sh‖)+C := add_le_add (norm_add_le _ _) hShd
      _ ≤ (‖Sh‖*‖S‖+‖S‖*‖Sh‖)+C := by gcongr <;> exact norm_mul_le _ _
      _ ≤ (C*C+C*C)+C := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ‖Errh‖+‖(ε*τ) • Sh‖+‖(τ^2) • (Sh*S+S*Sh+Shdot)‖ :=
      (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ = ‖Errh‖+|ε| *τ*‖Sh‖+τ^2*‖Sh*S+S*Sh+Shdot‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hτ,abs_of_nonneg (sq_nonneg τ),mul_assoc]
    _ ≤ C*(δ*τ+τ^2)+(3*C*δ)*τ*C+τ^2*(2*C^2+C) := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg C) (sq_nonneg τ),mul_nonneg hC (mul_nonneg hδ hτ)]

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

namespace HarmonicCounterexample.LinearODE
open HarmonicCounterexample.PulseTaylor
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- The source's first-order slow generator, including its precise
Riccati denominator. The angular infinitesimal is r B Id+D. -/
def bergerSlowGenerator (r B β p₀ θ z : ℝ) (D : R) : R :=
  (β/(p₀+2*θ)*z) • (r • (B • (1:R))+D)

/-- Uniform residual AND true parameter-direction residual estimates for the
exact Berger comparison. The constant is chosen before the scalar history,
small deviation, duration, pulse position and parameters. All nonlinear
angular remainders are proved, not hypotheses. -/
theorem berger_comparison_residuals (r B β p₀ θ : ℝ) (D : R)
    {M Z K : ℝ} (hM : 0 ≤ M) (hZ : 0 ≤ Z) (hK : 0 ≤ K)
    (hc : p₀+2*θ ≠ 0) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ α p v δ τ z zd zh zhd : ℝ,
      0 ≤ δ → 0 ≤ τ → |α| ≤ M → |α-β| ≤ δ → |p-p₀| ≤ δ → |v-θ| ≤ K*δ →
      |z| ≤ Z → |zd| ≤ Z → |zh| ≤ Z → |zhd| ≤ Z →
      1+τ*z ∈ Set.Icc (1/2:ℝ) (3/2) →
      let S := bergerSlowGenerator r B β p₀ θ z D
      let Sd := bergerSlowGenerator r B β p₀ θ zd D
      let Sh := bergerSlowGenerator r B β p₀ θ zh D
      let Shd := bergerSlowGenerator r B β p₀ θ zhd D
      let Q := v • (1:R)+τ • S
      ‖α • angular r (B • (1:R)) D (1+τ*z)-p • Q-Q*Q-
        ((α*B-p*v-v^2) • (1:R)+(τ^2) • Sd)‖ ≤ C*(δ*τ+τ^2) ∧
      ‖(τ*zh) • (α • angularD r (B • (1:R)) D (1+τ*z))-
        p • (τ • Sh)-(τ • Sh)*Q-Q*(τ • Sh)-(τ^2) • Shd‖ ≤ C*(δ*τ+τ^2) := by
  obtain ⟨C₀,hC₀,hrem⟩ := berger_slow_pulse_remainders r (B • (1:R)) D hM hZ
  let L := r • (B • (1:R))+D
  let A := |β/(p₀+2*θ)| *Z*‖L‖
  let C₁ := C₀+A+K+1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁];linarith
  have h₀ : C₀ ≤ C₁ := by dsimp [C₁];linarith
  have h₁ : A ≤ C₁ := by dsimp [C₁];linarith
  have h₂ : K ≤ C₁ := by dsimp [C₁];linarith
  have h₃ : 1 ≤ C₁ := by dsimp [C₁];linarith
  refine ⟨3*C₁^2+2*C₁,by positivity,?_⟩
  intro α p v δ τ z zd zh zhd hδ hτ hα hscale hp hv hz hzd hzh hzhd hq
  dsimp only
  have hSn (x : ℝ) (hx : |x| ≤ Z) : ‖bergerSlowGenerator r B β p₀ θ x D‖ ≤ C₁ := by
    calc
      _ = |β/(p₀+2*θ)| *|x| *‖L‖ := by simp only [bergerSlowGenerator,norm_smul,Real.norm_eq_abs,abs_mul,L]
      _ ≤ A := by dsimp [A];gcongr
      _ ≤ C₁ := h₁
  have hε : |p₀+2*θ-p-2*v| ≤ 3*C₁*δ := by
    have he : p₀+2*θ-p-2*v= -(p-p₀)-2*(v-θ) := by ring
    rw [he]
    calc
      _ ≤ |-(p-p₀)|+|2*(v-θ)| := abs_sub _ _
      _ = |p-p₀|+2*|v-θ| := by rw [abs_neg,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ δ+2*(K*δ) := by gcongr
      _ ≤ 3*C₁*δ := by nlinarith [mul_le_mul_of_nonneg_right h₂ hδ,mul_le_mul_of_nonneg_right h₃ hδ]
  obtain ⟨he,hej⟩ := hrem α β δ τ z zh hδ hτ hα hscale hz hzh hq
  have hfac (x : ℝ) : ((p₀+2*θ)*τ) • bergerSlowGenerator r B β p₀ θ x D=
      (β*τ*x) • L := by
    rw [bergerSlowGenerator,smul_smul]
    change (((p₀+2*θ)*τ)*(β/(p₀+2*θ)*x)) • L=(β*τ*x) • L
    congr 1
    field_simp
  let Err := α • angular r (B • (1:R)) D (1+τ*z)-α • (B • (1:R))-(β*τ*z) • L
  let Errh := (τ*zh) • (α • angularD r (B • (1:R)) D (1+τ*z)-β • L)
  have he' : ‖Err‖ ≤ C₁*(δ*τ+τ^2) := he.trans (mul_le_mul_of_nonneg_right h₀ (by positivity))
  have hej' : ‖Errh‖ ≤ C₁*(δ*τ+τ^2) := hej.trans (mul_le_mul_of_nonneg_right h₀ (by positivity))
  have hvId : (α*B) • (1:R)+((p₀+2*θ)*τ) • bergerSlowGenerator r B β p₀ θ z D+Err=
      α • angular r (B • (1:R)) D (1+τ*z) := by
    rw [hfac]
    dsimp only [Err]
    simp only [smul_smul]
    abel
  have hjId : ((p₀+2*θ)*τ) • bergerSlowGenerator r B β p₀ θ zh D+Errh=
      (τ*zh) • (α • angularD r (B • (1:R)) D (1+τ*z)) := by
    rw [hfac]
    dsimp only [Errh]
    simp only [smul_sub,smul_smul]
    rw [show τ*zh*β=β*τ*zh by ring]
    abel
  constructor
  · rw [← hvId,slow_residual_identity]
    exact slow_residual_bound hC₁ hδ hτ he' hε (hSn z hz) (hSn zd hzd)
  · rw [← hjId,slow_residual_jet_identity]
    exact slow_residual_jet_bound hC₁ hδ hτ hej' hε (hSn z hz) (hSn zh hzh) (hSn zhd hzhd)

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

namespace HarmonicCounterexample.LinearODE
open Set

/-- The exact source scalar baseline, forced by B/a(t)^2, deviates from
its limiting root by O(delta), uniformly in the pulse length. -/
theorem berger_scalar_baseline_close {α p : ℝ → ℝ}
    (hα : Continuous α) (hp : Continuous p)
    {M Mp B β p₀ θ γ δ T : ℝ}
    (hM : 0 ≤ M) (hMp : 0 ≤ Mp) (hθ : 0 ≤ θ) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (hαn : ∀ t,|α t| ≤ M) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ α t*B) (hroot : β*B-p₀*θ-θ^2=0)
    (hscale : ∀ t ∈ Icc 0 T,|α t-β| ≤ δ)
    (hpt : ∀ t ∈ Icc 0 T,|p t-p₀| ≤ δ)
    (hpl : ∀ t ∈ Icc 0 T,γ ≤ p t) :
    ∀ t ∈ Icc 0 T,|scalarBaseline (fun s => α s*B) p θ t-θ| ≤
      ((|B|+|θ|)/γ)*δ := by
  have hAB (t : ℝ) : |α t*B| ≤ M*|B| := by rw [abs_mul];gcongr;exact hαn t
  have hF (t : ℝ) (ht : t ∈ Icc 0 T) :
      |α t*B-p t*θ-θ^2| ≤ (|B|+|θ|)*δ := by
    have he : α t*B-p t*θ-θ^2=(α t-β)*B-(p t-p₀)*θ := by nlinarith [hroot]
    rw [he]
    calc
      _ ≤ |(α t-β)*B|+|(p t-p₀)*θ| := abs_sub _ _
      _ = |α t-β| *|B|+|p t-p₀| *|θ| := by rw [abs_mul,abs_mul]
      _ ≤ δ*|B|+δ*|θ| := by gcongr;exact hscale t ht;exact hpt t ht
      _ = _ := by ring
  have hh := actual_scalar_baseline_close (hα.mul continuous_const) hp
    (show 0 ≤ M*|B| by positivity) hMp hAB hpn hAp hθ hγ
    (show 0 ≤ (|B|+|θ|)*δ by positivity) hpl hF
  intro t ht
  exact (hh t ht).trans_eq (by ring)

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- Model-specific residuals with the actual scalar PB baseline substituted.
The resulting C is fixed BEFORE all histories, scalar coefficient functions,
period lengths, pulse positions and control parameters. This is the analytic
uniformity required for recursive attainment, not a compactness claim about
an unspecified incoming Riccati matrix. -/
theorem actual_berger_comparison_residuals (r B β p₀ θ γ : ℝ) (D : R)
    {M Z : ℝ} (hM : 0 ≤ M) (hZ : 0 ≤ Z) (hθ : 0 ≤ θ) (hγ : 0 < γ)
    (hc : p₀+2*θ ≠ 0) (hroot : β*B-p₀*θ-θ^2=0) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (α p : ℝ → ℝ) (Mp δ T τ : ℝ),
      Continuous α → Continuous p → 0 ≤ Mp → 0 ≤ δ → 0 ≤ τ →
      (∀ t,|α t| ≤ M) → (∀ t,|p t| ≤ Mp) →
      (∀ t,0 ≤ t → 0 ≤ α t*B) →
      (∀ t ∈ Icc 0 T,|α t-β| ≤ δ) →
      (∀ t ∈ Icc 0 T,|p t-p₀| ≤ δ) →
      (∀ t ∈ Icc 0 T,γ ≤ p t) →
      ∀ t ∈ Icc 0 T,∀ z zd zh zhd : ℝ,
        |z| ≤ Z → |zd| ≤ Z → |zh| ≤ Z → |zhd| ≤ Z →
        1+τ*z ∈ Icc (1/2:ℝ) (3/2) →
        let v := scalarBaseline (fun s => α s*B) p θ t
        let S := bergerSlowGenerator r B β p₀ θ z D
        let Sd := bergerSlowGenerator r B β p₀ θ zd D
        let Sh := bergerSlowGenerator r B β p₀ θ zh D
        let Shd := bergerSlowGenerator r B β p₀ θ zhd D
        let Q := v • (1:R)+τ • S
        ‖α t • PulseTaylor.angular r (B • (1:R)) D (1+τ*z)-p t • Q-Q*Q-
          ((α t*B-p t*v-v^2) • (1:R)+(τ^2) • Sd)‖ ≤ C*(δ*τ+τ^2) ∧
        ‖(τ*zh) • (α t • PulseTaylor.angularD r (B • (1:R)) D (1+τ*z))-
          p t • (τ • Sh)-(τ • Sh)*Q-Q*(τ • Sh)-(τ^2) • Shd‖ ≤ C*(δ*τ+τ^2) := by
  obtain ⟨C,hC,hres⟩ := berger_comparison_residuals r B β p₀ θ D hM hZ
    (show 0 ≤ (|B|+|θ|)/γ by positivity) hc
  refine ⟨C,hC,?_⟩
  intro α p Mp δ T τ hα hp hMp hδ hτ hαn hpn hAp hscale hpt hpl t ht z zd zh zhd hz hzd hzh hzhd hq
  exact hres (α t) (p t) (scalarBaseline (fun s => α s*B) p θ t) δ τ z zd zh zhd
    hδ hτ (hαn t) (hscale t ht) (hpt t ht)
    (berger_scalar_baseline_close hα hp hM hMp hθ hγ hδ hαn hpn hAp hroot hscale hpt hpl t ht)
    hz hzd hzh hzhd hq

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

namespace HarmonicCounterexample.LinearODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

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

namespace HarmonicCounterexample.LinearODE
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positivity of the comparison follows from a small pulse and the actual
positive scalar baseline. Symmetry is not used or silently assumed here. -/
lemma scalar_plus_small_positive {S : E →L[ℝ] E} {v τ C : ℝ}
    (hτ : 0 ≤ τ) (hSn : ‖S‖ ≤ C) (hgap : τ*C ≤ v) :
    ∀ x : E,0 ≤ inner ℝ x ((v • (1:E →L[ℝ] E)+τ • S) x) := by
  intro x
  have hn := S.le_opNorm x
  have hb : ‖S x‖ ≤ C*‖x‖ := hn.trans (mul_le_mul_of_nonneg_right hSn (norm_nonneg x))
  have hh := neg_le_of_abs_le (abs_real_inner_le_norm x (S x))
  have he := mul_le_mul_of_nonneg_left hb (norm_nonneg x)
  have hτh := mul_le_mul_of_nonneg_left hh hτ
  have ht := mul_le_mul_of_nonneg_left he hτ
  have hv := mul_le_mul_of_nonneg_right hgap (sq_nonneg ‖x‖)
  simp only [add_apply,smul_apply,
    one_apply_eq_self,inner_add_right,inner_smul_right, real_inner_self_eq_norm_sq]
  nlinarith

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

namespace HarmonicCounterexample.LinearODE
open MeasureTheory Set

/-- Global measurability of the genuine quotient holds even at irrelevant
negative-time zeros. No global nonvanishing hypothesis is needed for FTC. -/
lemma scalarBaseline_stronglyMeasurable {A p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p) {MA Mp : ℝ}
    (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp) (hAn : ∀ t,|A t| ≤ MA)
    (hpn : ∀ t,|p t| ≤ Mp) (θ : ℝ) :
    StronglyMeasurable (scalarBaseline A p θ) := by
  have hy : Continuous (fun t => (scalarPhase A p 1 θ t).1) :=
    continuous_iff_continuousAt.2 fun t =>
      (scalarPhase_value_deriv hA hp hMA hMp hAn hpn 1 θ t).continuousAt
  have hv : Continuous (fun t => (scalarPhase A p 1 θ t).2) :=
    continuous_iff_continuousAt.2 fun t =>
      (scalarPhase_velocity_deriv hA hp hMA hMp hAn hpn 1 θ t).continuousAt
  exact (hv.measurable.div hy.measurable).stronglyMeasurable

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- The actual comparison used in the slow pulse: the scalar part is built
from PB flow, not chosen as an unproved solution of a Riccati equation. -/
def actualBergerComparison (α p : ℝ → ℝ) (r B β p₀ θ τ : ℝ) (D : R)
    (z : ℝ → ℝ) (t : ℝ) : R :=
  scalarBaseline (fun s => α s*B) p θ t • (1:R)+
    τ • bergerSlowGenerator r B β p₀ θ (z (τ*t)) D

lemma actualBergerComparison_initial (α p : ℝ → ℝ) (r B β p₀ θ τ : ℝ) (D : R)
    {z : ℝ → ℝ} (hz : z 0=0) :
    actualBergerComparison α p r B β p₀ θ τ D z 0=θ • (1:R) := by
  simp only [actualBergerComparison,scalarBaseline_init,mul_zero,hz,bergerSlowGenerator,
    zero_smul,smul_zero,add_zero]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

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

namespace HarmonicCounterexample.LinearODE
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma scalar_plus_small_coercive {S : E →L[ℝ] E} {v τ C : ℝ}
    (hτ : 0 ≤ τ) (hSn : ‖S‖ ≤ C) :
    ∀ x : E,(v-τ*C)*‖x‖^2 ≤ inner ℝ x ((v • (1:E →L[ℝ] E)+τ • S) x) := by
  intro x
  have hb : ‖S x‖ ≤ C*‖x‖ := (S.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hSn (norm_nonneg x))
  have hh := neg_le_of_abs_le (abs_real_inner_le_norm x (S x))
  have he := mul_le_mul_of_nonneg_left hb (norm_nonneg x)
  have hτh := mul_le_mul_of_nonneg_left hh hτ
  have ht := mul_le_mul_of_nonneg_left he hτ
  simp only [add_apply,smul_apply,one_apply_eq_self,inner_add_right,inner_smul_right,
    real_inner_self_eq_norm_sq]
  nlinarith

/-- Uniform positivity of the actual comparison is derived from the actual
baseline estimate and smallness conditions, not assumed for the Riccati bound. -/
lemma actualBergerComparison_coercive {α p : ℝ → ℝ}
    (hα : Continuous α) (hp : Continuous p) {M Mp B β p₀ θ γ δ T τ r Z : ℝ}
    (hM : 0 ≤ M) (hMp : 0 ≤ Mp) (hθ : 0 ≤ θ) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (hτ : 0 ≤ τ) (hαn : ∀ t,|α t| ≤ M) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ α t*B) (hroot : β*B-p₀*θ-θ^2=0)
    (hscale : ∀ t ∈ Set.Icc 0 T,|α t-β| ≤ δ)
    (hpt : ∀ t ∈ Set.Icc 0 T,|p t-p₀| ≤ δ)
    (hpl : ∀ t ∈ Set.Icc 0 T,γ ≤ p t)
    (D : E →L[ℝ] E) {z : ℝ → ℝ}
    (hz : ∀ t ∈ Set.Icc 0 T,|z (τ*t)| ≤ Z)
    (hsmall : ((|B|+|θ|)/γ)*δ+
      τ*(|β/(p₀+2*θ)| * Z * ‖r • (B • (1:E →L[ℝ] E))+D‖) ≤ θ/2) :
    ∀ t ∈ Set.Icc 0 T,∀ x : E,
      (θ/2)*‖x‖^2 ≤ inner ℝ x (actualBergerComparison α p r B β p₀ θ τ D z t x) := by
  intro t ht x
  have hv := neg_le_of_abs_le
    (berger_scalar_baseline_close hα hp hM hMp hθ hγ hδ hαn hpn hAp hroot hscale hpt hpl t ht)
  have hn : ‖bergerSlowGenerator r B β p₀ θ (z (τ*t)) D‖ ≤
      |β/(p₀+2*θ)| * Z * ‖r • (B • (1:E →L[ℝ] E))+D‖ := by
    simp only [bergerSlowGenerator,norm_smul,Real.norm_eq_abs,abs_mul]
    gcongr
    exact hz t ht
  have hh := scalar_plus_small_coercive
    (v := scalarBaseline (fun s => α s*B) p θ t) hτ hn x
  have hnum : θ/2 ≤ scalarBaseline (fun s => α s*B) p θ t-
      τ*(|β/(p₀+2*θ)| * Z * ‖r • (B • (1:E →L[ℝ] E))+D‖) := by linarith
  exact (mul_le_mul_of_nonneg_right hnum (sq_nonneg ‖x‖)).trans hh

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

namespace HarmonicCounterexample.LinearODE
open Set Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {E H ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

namespace HarmonicCounterexample.LinearODE
open Set Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {E H ι κ : Type*} [Fintype κ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

end HarmonicCounterexample.LinearODE

end

end OAI
