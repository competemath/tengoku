import Tengoku.OpenaiMath.OAI.Geometry.HarmonicGrowth.PulseSystem
import Tengoku.OpenaiMath.OAI.Geometry.HarmonicGrowth.AngularStream

namespace OAI

noncomputable section

namespace HarmonicCounterexample.LinearODE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open scoped InnerProductSpace

lemma symmetric_norm_bound {S : E →L[ℝ] E} {C : ℝ} (hC : 0 ≤ C)
    (hs : S.IsSymmetric) (hpos : ∀ v, 0 ≤ ⟪v,S v⟫_ℝ)
    (hb : ∀ v, ⟪v,S v⟫_ℝ ≤ C*‖v‖^2) : ‖S‖ ≤ C := by
  rw [S.norm_eq_iSup_rayleighQuotient hs]
  apply ciSup_le
  intro v
  by_cases hv : v = 0
  · simp [hv,hC]
  · have hn : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.2 hv)
    have hp := hpos v
    have hupper := hb v
    change |⟪S v,v⟫_ℝ / ‖v‖^2| ≤ C
    rw [real_inner_comm v (S v),abs_of_nonneg (div_nonneg hp hn.le)]
    exact (div_le_iff₀ hn).2 hupper

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace

/-- Primitive radial coefficients and fixed angular operators. All fields are
scalar/asymptotic or pointwise geometric facts; no transmission/reset/growth
conclusion is part of this data. -/
structure HistoryGeometry (S : PulseSystem E ι κ) where
  D₀ : ∀ b,E b →L[ℝ] E b
  D₀nonpos : ∀ b v,inner ℝ v (D₀ b v) ≤ 0
  BD₀ : ∀ b v,-(S.B b*‖v‖^2) ≤ inner ℝ v (D₀ b v)
  D₀symm : ∀ b x y,inner ℝ (D₀ b x) y=inner ℝ x (D₀ b y)
  Dsymm : ∀ b j x y,inner ℝ (S.D b j x) y=inner ℝ x (S.D b j y)
  qstar : ℝ
  qstar_ge : 1 ≤ qstar
  l : ξ → ℝ
  lpos : ∀ b,0 < l b
  B₀ : ℝ
  B_eq : ∀ b,S.B b=l b*(l b+B₀)
  α : ℝ → ℝ
  drift : ℝ → ℝ
  Mp : ℝ
  Mpnonneg : 0 ≤ Mp
  αsmooth : ContDiff ℝ ∞ α
  driftContinuous : Continuous drift
  αbound : ∀ t,|α t| ≤ S.M
  αnonneg : ∀ t,0 ≤ α t
  driftBound : ∀ t,|drift t| ≤ Mp
  αcenter : ∀ t ≤ 0,α t=1
  driftCenter : ∀ t ≤ 0,drift t=B₀
  αlimit : ∀ b,Tendsto α atTop (𝓝 (S.β b))
  driftLimit : Tendsto drift atTop (𝓝 S.p₀)
  driftLower : ∀ᶠ t in atTop,S.γ ≤ drift t

variable {S : PulseSystem E ι κ} (G : HistoryGeometry S) {n : ℕ} [NeZero n] (slot : Fin n → κ)

def HistoryGeometry.coefficient (s : ℕ → Fin n → ℝ) (j0 : ℕ) (b : ξ) (t : ℝ) : E b →L[ℝ] E b :=
  G.α t • angular S.r (S.B b • (1:E b →L[ℝ] E b)) (G.D₀ b) (fun i => S.D b (slot i)) s G.qstar j0 t

def HistoryGeometry.bound (b : ξ) : ℝ := S.M *
  (angular_uniform_bound S.r (S.B b • (1:E b →L[ℝ] E b)) (G.D₀ b)
    (fun i => S.D b (slot i)) G.qstar_ge).choose

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma HistoryGeometry.bound_nonneg (b : ξ) : 0 ≤ G.bound slot b :=
  mul_nonneg S.hM (angular_uniform_bound S.r (S.B b • (1:E b →L[ℝ] E b)) (G.D₀ b)
    (fun i => S.D b (slot i)) G.qstar_ge).choose_spec.1

variable (s : ℕ → Fin n → ℝ) (j0 : ℕ)
  (hpos : ∀ j,j0 ≤ j → ∀ t i,packetStretch (s j) (pulse j) t i ∈ Icc (1/2:ℝ) (3/2))

include hpos

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] [NeZero n] in
lemma HistoryGeometry.coefficient_smooth (b : ξ) : ContDiff ℝ ∞ (G.coefficient slot s j0 b) :=
  G.αsmooth.smul (angular_smooth S.r _ _ _ s G.qstar_ge j0
    (fun j hj t i => by linarith [(hpos j hj t i).1]))

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma HistoryGeometry.coefficient_bound (b : ξ) (t : ℝ) :
    ‖G.coefficient slot s j0 b t‖ ≤ G.bound slot b := by
  rw [HistoryGeometry.coefficient,norm_smul,Real.norm_eq_abs]
  apply mul_le_mul (G.αbound t)
    ((angular_uniform_bound S.r (S.B b • (1:E b →L[ℝ] E b)) (G.D₀ b)
      (fun i => S.D b (slot i)) G.qstar_ge).choose_spec.2 s j0 hpos t)
    (norm_nonneg _) S.hM

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma HistoryGeometry.coefficient_nonnegative (b : ξ) (t : ℝ) (x : E b) :
    0 ≤ inner ℝ x (G.coefficient slot s j0 b t x) := by
  simp only [HistoryGeometry.coefficient,smul_apply,inner_smul_right]
  apply mul_nonneg (G.αnonneg t)
  apply angular_nonnegative S.r (S.B b) (G.D₀ b) (fun i => S.D b (slot i)) s G.qstar_ge j0 hpos
  · intro d x;cases d with
    | none => exact G.D₀nonpos b x
    | some i => exact S.hD b (slot i) x
  · intro d x;cases d with
    | none => exact G.BD₀ b x
    | some i => exact S.hBD b (slot i) x

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma HistoryGeometry.coefficient_symmetric (b : ξ) (t : ℝ) (x y : E b) :
    inner ℝ (G.coefficient slot s j0 b t x) y=inner ℝ x (G.coefficient slot s j0 b t y) := by
  simp only [HistoryGeometry.coefficient,smul_apply,real_inner_smul_left,inner_smul_right]
  congr 1
  apply angular_symmetric S.r (S.B b) (G.D₀ b) (fun i => S.D b (slot i)) s G.qstar_ge j0 hpos
  intro d x y;cases d with
  | none => exact G.D₀symm b x y
  | some i => exact G.Dsymm b (slot i) x y

omit hpos [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] [NeZero n] in
lemma HistoryGeometry.coefficient_center (b : ξ) (t : ℝ) (ht : t ≤ 0) (x : E b) :
    G.coefficient slot s j0 b t x=(G.l b*(G.l b+G.B₀)) • x := by
  rw [HistoryGeometry.coefficient,angular_initial S.r _ _ _ s (ht.trans (time_pos j0).le),
    G.αcenter t ht,one_smul,G.B_eq b]
  rfl

omit hpos [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] [NeZero n] in
lemma HistoryGeometry.coefficient_round (b : ξ) {j : ℕ} (hj : j0 ≤ j) (hz : s j=0)
    (t : ℝ) (ht : t ∈ Icc (time j) (time j+pulse j)) :
    G.coefficient slot s j0 b t=G.α t • (S.B b • (1:E b →L[ℝ] E b)) := by
  rw [HistoryGeometry.coefficient,angular_zero_pulse S.r _ _ _ s hj hz ht.1 ht.2]

omit hpos [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] [NeZero n] in
lemma HistoryGeometry.coefficient_rest (b : ξ) (j : ℕ)
    (t : ℝ) (ht : t ∈ Icc (time j+3*pulse j+dwell j) (time (j+1))) :
    G.coefficient slot s j0 b t=G.α t • (S.B b • (1:E b →L[ℝ] E b)) := by
  rw [HistoryGeometry.coefficient,angular_rest S.r _ _ _ s ht.1 ht.2]

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace
variable {S : PulseSystem E ι κ} (G : HistoryGeometry S) {n : ℕ} [NeZero n] (slot : Fin n → κ)

omit [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma HistoryGeometry.uniform_radial_tail {δ : ℝ} (hδ : 0 < δ) :
    ∃ J : ℕ,∀ j,J ≤ j → ∀ t,time j ≤ t →
      (∀ b,|G.α t-S.β b| ≤ δ) ∧ |G.drift t-S.p₀| ≤ δ ∧ S.γ ≤ G.drift t := by
  have hα : ∀ᶠ t in atTop,∀ b,|G.α t-S.β b| ≤ δ := by
    apply Filter.eventually_all.2
    intro b
    have hh : Tendsto (fun t => |G.α t-S.β b|) atTop (𝓝 0) := by
      simpa only [sub_self,abs_zero] using ((G.αlimit b).sub_const (S.β b)).abs
    exact (hh.eventually (gt_mem_nhds hδ)).mono (fun _ h => h.le)
  have hp : Tendsto (fun t => |G.drift t-S.p₀|) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero] using (G.driftLimit.sub_const S.p₀).abs
  obtain ⟨a,ha⟩ := eventually_atTop.1 (hα.and ((hp.eventually (gt_mem_nhds hδ)).and G.driftLower))
  obtain ⟨J,hJ⟩ := eventually_atTop.1 (time_atTop.eventually_ge_atTop a)
  exact ⟨J,fun j hj t ht => ⟨(ha t ((hJ j hj).trans ht)).1,
    (ha t ((hJ j hj).trans ht)).2.1.le,(ha t ((hJ j hj).trans ht)).2.2⟩⟩

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl HarmonicCounterexample.FiniteControl.SmoothWord
open HarmonicCounterexample.FiniteControl.Frobenius HarmonicCounterexample.Transmission
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace
local instance (d : ℕ) : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] MatrixProduct ι) := ContinuousLinearMap.toNormedAddCommGroup
local instance (d : ℕ) : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] MatrixProduct ι) := ContinuousLinearMap.toNormedSpace

omit [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma PhysicalWord.ideal_factor (S : PulseSystem E ι κ) (w : PhysicalWord κ) :
    (fun x b => orthogonalMatrix (S.basis b) (flow (fun t => ContinuousLinearMap.mul ℝ (E b →L[ℝ] E b)
        (unitPacketCoefficient (fun j => w.amps j x) (fun j => bergerSlowGenerator S.r (S.B b) (S.β b) S.p₀ (S.θ b) 1 (S.D b (w.slot j))) t)) 1 1))=w.ideal S := by
  funext x b
  rw [orthogonalMatrix_packet]
  exact (actual_packet_apply (fun j => w.amps j x) (S.generator ∘ w.slot) b).symm

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma PhysicalWord.value_factor (S : PulseSystem E ι κ) (w : PhysicalWord κ) (H : PulseHistory S) :
    (fun x b => orthogonalMatrix (S.basis b) (Real.exp (-(∫ t in H.a..H.a+H.T,
      scalarBaseline (fun s => H.α (H.a+s)*S.B b) (fun s => H.drift (H.a+s)) (S.θ b) (max 0 (t-H.a)))) •
        (operatorValue (insertWord (H.history b) H.α S.r (S.B b • (1:E b →L[ℝ] E b))
          (fun j => S.D b (w.slot j)) (fun j => w.amps j x) H.a H.T) H.drift (H.l b) (H.a+H.T)*
        Ring.inverse (operatorValue (insertWord (H.history b) H.α S.r (S.B b • (1:E b →L[ℝ] E b))
          (fun j => S.D b (w.slot j)) (fun j => w.amps j x) H.a H.T) H.drift (H.l b) H.a)))) = w.value S H := rfl

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma PhysicalWord.defect_factor (S : PulseSystem E ι κ) (w : PhysicalWord κ) (H : PulseHistory S) :
    (fun x b => orthogonalMatrix (S.basis b) (slope (insertWord (H.history b) H.α S.r
      (S.B b • (1:E b →L[ℝ] E b)) (fun j => S.D b (w.slot j)) (fun j => w.amps j x) H.a H.T)
      H.drift (H.l b) (H.a+H.T))-S.θ b • (1:Matrix (ι b) (ι b) ℝ)) = w.defect S H := rfl

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl HarmonicCounterexample.FiniteControl.SmoothWord
open HarmonicCounterexample.FiniteControl.Frobenius HarmonicCounterexample.Transmission
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace
local instance (d : ℕ) : NormedAddCommGroup (EuclideanSpace ℝ (Fin d) →L[ℝ] MatrixProduct ι) := ContinuousLinearMap.toNormedAddCommGroup
local instance (d : ℕ) : NormedSpace ℝ (EuclideanSpace ℝ (Fin d) →L[ℝ] MatrixProduct ι) := ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses FiniteControl.SmoothWord
open scoped Topology ContDiff BigOperators
variable {κ : Type*} (w : PhysicalWord κ)

/-- Zero belongs to the admissible control space as a genuinely absent pulse,
not as the generally nonzero word at parameter zero. -/
def PhysicalWord.admissible : Set (Fin w.n → ℝ) :=
  {a | a=0 ∨ ∃ x ∈ w.ball,a=(fun i => w.amps i x)}

lemma PhysicalWord.zero_admissible : (0:Fin w.n → ℝ) ∈ w.admissible := Or.inl rfl

lemma PhysicalWord.amplitudes_admissible {x : w.Parameter} (hx : x ∈ w.ball) :
    (fun i => w.amps i x) ∈ w.admissible := Or.inr ⟨x,hx,rfl⟩

lemma PhysicalWord.admissible_uniform_bound : ∃ U : ℝ,0 ≤ U ∧
    ∀ a ∈ w.admissible,∀ i,|a i| ≤ U := by
  classical
  choose C hC using fun i : Fin w.n => (isCompact_closedBall (0:w.Parameter) w.radius).exists_bound_of_continuousOn
    (f:=w.amps i) ((w.smooth i).continuous.continuousOn : ContinuousOn (w.amps i) w.ball)
  let U := ∑ i : Fin w.n,max (C i) 0
  have hU : 0 ≤ U := Finset.sum_nonneg (fun i _ => le_max_right _ _)
  refine ⟨U,hU,fun a ha i => ?_⟩
  rcases ha with rfl | ⟨x,hx,rfl⟩
  · simpa using hU
  · exact (hC i x hx).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun j _ => le_max_right (C j) 0) (Finset.mem_univ i)))

/-- The same compact parameter ball works in every later pulse, with a
threshold independent of histories or later parameter choices. -/
theorem PhysicalWord.admissible_stretch_threshold : ∃ J : ℕ,∀ j,J ≤ j →
    ∀ a ∈ w.admissible,∀ t i,packetStretch a (pulse j) t i ∈ Icc (1/2:ℝ) (3/2) := by
  obtain ⟨U,hU,hbound⟩ := w.admissible_uniform_bound
  obtain ⟨C,hC,hpos⟩ := packetStretch_uniform_positive w.n
  obtain ⟨J,hJ⟩ := eventually_atTop.1 (pulse_atTop_limit.eventually_ge_atTop (2*C*U))
  exact ⟨J,fun j hj a ha => hpos a U (pulse j) hU (hbound a ha) (pulse_pos j) (hJ j hj)⟩

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open HarmonicCounterexample.Transmission HarmonicCounterexample.FiniteControl HarmonicCounterexample.FiniteControl.Frobenius
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace
variable {S : PulseSystem E ι κ} (G : HistoryGeometry S) {n : ℕ} [NeZero n] (slot : Fin n → κ)

def HistoryGeometry.baseline (j : ℕ) (b : ξ) (t : ℝ) : ℝ :=
  scalarBaseline (fun s => G.α (time j+s)*S.B b) (fun s => G.drift (time j+s))
    (S.θ b) (max 0 (t-time j))

def HistoryGeometry.packet (s : ℕ → Fin n → ℝ) (j0 j : ℕ) : MatrixProduct ι := fun b =>
  orthogonalMatrix (S.basis b) (Real.exp (-(∫ t in time j..time j+pulse j,G.baseline j b t)) •
    (operatorValue (G.coefficient slot s j0 b) G.drift (G.l b) (time j+pulse j)*
      Ring.inverse (operatorValue (G.coefficient slot s j0 b) G.drift (G.l b) (time j))))

def HistoryGeometry.defect (s : ℕ → Fin n → ℝ) (j0 j : ℕ) : MatrixProduct ι := fun b =>
  orthogonalMatrix (S.basis b) (slope (G.coefficient slot s j0 b) G.drift (G.l b) (time j+pulse j))-
    S.θ b • (1:Matrix (ι b) (ι b) ℝ)

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] [NeZero n] in
lemma HistoryGeometry.coefficient_causal {s u : ℕ → Fin n → ℝ} {j0 j : ℕ}
    (he : ∀ i < j,s i=u i) {t : ℝ} (ht : t ≤ time j) (b : ξ) :
    G.coefficient slot s j0 b t=G.coefficient slot u j0 b t := by
  dsimp [HistoryGeometry.coefficient]
  rw [angular_causal S.r _ _ _ G.qstar j0 he ht]

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] [NeZero n] in
lemma HistoryGeometry.packet_causal {s u : ℕ → Fin n → ℝ} {j0 j : ℕ}
    (he : ∀ i < j+1,s i=u i) :
    G.packet slot s j0 j=G.packet slot u j0 j ∧ G.defect slot s j0 j=G.defect slot u j0 j := by
  have ht1 : time j ∈ Icc 0 (time (j+1)) :=
    ⟨(time_pos j).le,time_strictMono.monotone (by omega)⟩
  have ht2 : time j+pulse j ∈ Icc 0 (time (j+1)) := by
    constructor
    · linarith [time_pos j,pulse_pos j]
    · rw [time_succ];linarith [dwell_pos j,pulse_pos j]
  have hcoeff (b : ξ) : EqOn (G.coefficient slot s j0 b) (G.coefficient slot u j0 b)
      (Icc 0 (time (j+1))) := fun t ht => G.coefficient_causal slot he ht.2 b
  constructor
  · funext b
    simp only [HistoryGeometry.packet,(operator_history_eq (hcoeff b) G.drift (G.l b) ht1).1,
      (operator_history_eq (hcoeff b) G.drift (G.l b) ht2).1]
  · funext b
    simp only [HistoryGeometry.defect,slope_history_eq (hcoeff b) G.drift (G.l b) ht2]

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open HarmonicCounterexample.Transmission HarmonicCounterexample.FiniteControl
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace
variable {S : PulseSystem E ι κ} (G : HistoryGeometry S) {n : ℕ} [NeZero n] (slot : Fin n → κ)
variable (s : ℕ → Fin n → ℝ) (j0 j : ℕ) (δ ε : ℝ)
  (hpos : ∀ k,j0 ≤ k → ∀ t i,packetStretch (s k) (pulse k) t i ∈ Icc (1/2:ℝ) (3/2))
  (hj : j0 ≤ j) (hz : s j=0) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
  (hr : ∀ t,time j ≤ t → (∀ b,|G.α t-S.β b| ≤ δ) ∧ |G.drift t-S.p₀| ≤ δ ∧ S.γ ≤ G.drift t)
  (hi : ∀ b,‖orthogonalMatrix (S.basis b) (slope (G.coefficient slot s j0 b) G.drift (G.l b) (time j))-
    S.θ b • (1:Matrix (ι b) (ι b) ℝ)‖ ≤ ε)

/-- This is a constructor from the actual stream. All nontrivial input facts
are supplied by the single history-independent threshold theorem. -/
def HistoryGeometry.pulseHistory : PulseHistory S where
  history := G.coefficient slot s j0
  α := G.α
  drift := G.drift
  MH := G.bound slot
  Mb := G.Mp
  l := G.l
  B₀ := G.B₀
  a := time j
  T := pulse j
  δ := δ
  ε := ε
  smooth := G.coefficient_smooth slot s j0 hpos
  αsmooth := G.αsmooth
  driftContinuous := G.driftContinuous
  MHnonneg := G.bound_nonneg slot
  Mbnonneg := G.Mpnonneg
  αbound := G.αbound
  αnonneg := G.αnonneg
  driftBound := G.driftBound
  bound := G.coefficient_bound slot s j0 hpos
  nonneg := G.coefficient_nonnegative slot s j0 hpos
  round := fun b t ht => G.coefficient_round slot s j0 b hj hz t ht
  lpos := G.lpos
  center := G.coefficient_center slot s j0
  driftCenter := G.driftCenter
  apos := (time_pos j).le
  δnonneg := hδ
  εnonneg := hε
  αclose := fun b t ht => (hr t ht.1).1 b
  driftClose := fun t ht => (hr t ht.1).2.1
  driftLower := fun t ht => (hr t ht.1).2.2
  incoming := hi

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open HarmonicCounterexample.Transmission HarmonicCounterexample.FiniteControl
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.Frobenius
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.Transmission
open Set
open scoped Matrix.Norms.Frobenius
variable {β : Type*} [Fintype β] {ι : β → Type*}
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)]

omit [Fintype β] in
/-- Block-dependent Riccati roots are kept in the complete-leg identity. -/
lemma blockwise_whole_period_exact_leg
    {U V P B : ∀ b,Matrix (ι b) (ι b) ℝ} (θ : β → ℝ)
    (D M : ∀ b,(Matrix (ι b) (ι b) ℝ)ˣ)
    (hD : ∀ b,(D b:Matrix (ι b) (ι b) ℝ)=U b+θ b • V b)
    (hatt : ∀ b,∃ c : ℝ,c ∈ Ioo (1/2:ℝ) (3/2) ∧
      wholePeriod ((↑(D b)⁻¹:Matrix (ι b) (ι b) ℝ)*V b) (P b-θ b • 1) (B b)=
        c • (M b:Matrix (ι b) (ι b) ℝ)) :
    ∀ b,∃ c : ℝ,c ∈ Ioo (1/2:ℝ) (3/2) ∧
      (U b+V b*P b)*B b=c • ((D b:Matrix (ι b) (ι b) ℝ)*(M b:Matrix (ι b) (ι b) ℝ)) := by
  intro b
  obtain ⟨c,hc,he⟩ := hatt b
  refine ⟨c,hc,?_⟩
  have hf := full_leg_factor (U b) (V b) (P b) (B b) (θ b) (D b) (hD b)
  change (↑(D b)⁻¹:Matrix (ι b) (ι b) ℝ)*((U b+V b*P b)*B b)=
    wholePeriod ((↑(D b)⁻¹:Matrix (ι b) (ι b) ℝ)*V b) (P b-θ b • 1) (B b) at hf
  have hh := congrArg (fun X => (D b:Matrix (ι b) (ι b) ℝ)*X) hf
  rw [← mul_assoc,Units.mul_inv,one_mul,he,Matrix.mul_smul] at hh
  exact hh

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- Undo ONLY the harmless scalar pulse normalization. The scalar logarithmic
cost is separated from the genuine diagonal factor of the entire leg. -/
lemma unnormalize_whole_leg {Fa Fc Fd U V P D M : R} {I c : ℝ}
    (hvalue : Fd=(U+V*P)*Fc)
    (htune : (U+V*P)*(Real.exp (-I) • (Fc*Fa))=c • (D*M)) :
    Fd*Fa=(Real.exp I*c) • (D*M) := by
  have he := congrArg (fun X : R => Real.exp I • X) htune
  rw [mul_smul_comm,smul_smul,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul] at he
  rw [hvalue,mul_assoc]
  simpa only [smul_smul] using he

end HarmonicCounterexample.Transmission

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open HarmonicCounterexample.Transmission HarmonicCounterexample.FiniteControl
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace
local instance (b : ξ) : NormedAddCommGroup ((E b →L[ℝ] E b) →L[ℝ] Matrix (ι b) (ι b) ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ ((E b →L[ℝ] E b) →L[ℝ] Matrix (ι b) (ι b) ℝ) := ContinuousLinearMap.toNormedSpace

local instance (b : ξ) : NormedAddCommGroup (Matrix (ι b) (ι b) ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (Matrix (ι b) (ι b) ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance (b : ξ) : NormedAddCommGroup ((ι b → ℝ) →L[ℝ] Matrix (ι b) (ι b) ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ ((ι b → ℝ) →L[ℝ] Matrix (ι b) (ι b) ℝ) := ContinuousLinearMap.toNormedSpace

variable {S : PulseSystem E ι κ} (G : HistoryGeometry S) {n : ℕ} [NeZero n]

omit [NeZero n] in
lemma zero_stretch (j : ℕ) (t : ℝ) (i : Fin n) :
    packetStretch (0:Fin n → ℝ) (pulse j) t i ∈ Icc (1/2:ℝ) (3/2) := by
  norm_num [packetStretch]

/-- Background diagonal coefficient, independent of all control choices. -/
def HistoryGeometry.baseCoefficient (j0 : ℕ) (b : ξ) (t : ℝ) : E b →L[ℝ] E b :=
  G.α t • PulseTaylor.angular S.r (S.B b • (1:E b →L[ℝ] E b)) (G.D₀ b) (base G.qstar j0 t)

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] [NeZero n] in
lemma HistoryGeometry.baseCoefficient_eq (slot : Fin n → κ) (j0 : ℕ) (b : ξ) :
    G.baseCoefficient j0 b=G.coefficient slot 0 j0 b := by
  funext t
  unfold HistoryGeometry.baseCoefficient HistoryGeometry.coefficient angular
  have he : (fun j => activeIncrement S.r (S.B b • (1:E b →L[ℝ] E b))
      (fun i => S.D b (slot i)) 0 j0 j t)=fun _ => (0:E b →L[ℝ] E b) := by
    funext j
    dsimp [activeIncrement]
    split_ifs
    · exact increment_zero S.r _ _ rfl t
    · rfl
  rw [he,tsum_zero,add_zero]

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma HistoryGeometry.baseCoefficient_diagonal (d₀ : ∀ b,ι b → ℝ)
    (hd₀ : ∀ b,orthogonalMatrix (S.basis b) (G.D₀ b)=Matrix.diagonal (d₀ b))
    (j0 : ℕ) (b : ξ) (t : ℝ) :
    orthogonalMatrix (S.basis b) (G.baseCoefficient j0 b t)=Matrix.diagonal (fun i =>
      G.α t*((base G.qstar j0 t)^S.r*S.B b+
        ((base G.qstar j0 t)^S.r-(base G.qstar j0 t)^(S.r-1))*d₀ b i)) := by
  simp only [HistoryGeometry.baseCoefficient,PulseTaylor.angular,map_smul,map_add,
    orthogonalMatrix_one,hd₀]
  ext i j
  by_cases h : i=j
  · subst j;simp [Matrix.diagonal_apply_eq,smul_eq_mul]
  · simp [h,smul_eq_mul]

/-- The genuine fixed diagonal scalar coefficient. -/
def HistoryGeometry.legLambda (d₀ : ∀ b,ι b → ℝ) (j0 : ℕ) (b : ξ) (i : ι b) (t : ℝ) : ℝ :=
  G.α t*((base G.qstar j0 t)^S.r*S.B b+
    ((base G.qstar j0 t)^S.r-(base G.qstar j0 t)^(S.r-1))*d₀ b i)

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma HistoryGeometry.legLambda_properties (slot : Fin n → κ) (d₀ : ∀ b,ι b → ℝ)
    (hd₀ : ∀ b,orthogonalMatrix (S.basis b) (G.D₀ b)=Matrix.diagonal (d₀ b)) (j0 : ℕ) (b : ξ) :
    ∃ N : ι b → ℝ,(∀ i,0 ≤ N i) ∧
      (∀ i,Continuous (G.legLambda d₀ j0 b i)) ∧
      (∀ i t,|G.legLambda d₀ j0 b i t| ≤ N i) ∧
      (∀ i t,0 ≤ G.legLambda d₀ j0 b i t) := by
  have hp : ∀ j,j0 ≤ j → ∀ t i,packetStretch ((0:ℕ → Fin n → ℝ) j) (pulse j) t i ∈ Icc (1/2:ℝ) (3/2) :=
    fun j _ t i => zero_stretch j t i
  have hbc := G.baseCoefficient_eq slot j0 b
  have hc : Continuous (G.baseCoefficient j0 b) := by
    rw [hbc];exact (G.coefficient_smooth slot 0 j0 hp b).continuous
  have he (i : ι b) (t : ℝ) : G.legLambda d₀ j0 b i t=
      matrixEntry i i (orthogonalMatrix (S.basis b) (G.baseCoefficient j0 b t)) := by
    rw [matrixEntry_apply,G.baseCoefficient_diagonal d₀ hd₀,Matrix.diagonal_apply_eq]
    rfl
  let N : ι b → ℝ := fun i => ‖matrixEntry i i‖*‖orthogonalMatrix (S.basis b)‖*G.bound slot b
  refine ⟨N,fun i => mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (G.bound_nonneg slot b),?_,?_,?_⟩
  · intro i
    have hf : G.legLambda d₀ j0 b i=fun t => matrixEntry i i (orthogonalMatrix (S.basis b) (G.baseCoefficient j0 b t)) := funext (he i)
    rw [hf];exact (matrixEntry i i).continuous.comp ((orthogonalMatrix (S.basis b)).continuous.comp hc)
  · intro i t
    rw [he i t,← Real.norm_eq_abs]
    calc
      _ ≤ ‖matrixEntry i i‖*‖orthogonalMatrix (S.basis b) (G.baseCoefficient j0 b t)‖ := (matrixEntry i i).le_opNorm _
      _ ≤ ‖matrixEntry i i‖*(‖orthogonalMatrix (S.basis b)‖*‖G.baseCoefficient j0 b t‖) :=
        mul_le_mul_of_nonneg_left ((orthogonalMatrix (S.basis b)).le_opNorm _) (norm_nonneg _)
      _ ≤ N i := by
        dsimp [N];rw [mul_assoc,hbc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (G.coefficient_bound slot 0 j0 hp b t) (norm_nonneg _)) (norm_nonneg _)
  · intro i t
    rw [he i t,matrixEntry_apply,orthogonalMatrix_apply,OrthonormalBasis.repr_apply_apply,hbc]
    exact G.coefficient_nonnegative slot 0 j0 hp b t (S.basis b i)

/-- ACTUAL complete-leg columns with the physical schedule. -/
def HistoryGeometry.legU (d₀ : ∀ b,ι b → ℝ) (j0 j : ℕ) (b : ξ) : Matrix (ι b) (ι b) ℝ :=
  Matrix.diagonal (fun i => scalarU (fun t => G.legLambda d₀ j0 b i (time j+pulse j+t))
    (fun t => G.drift (time j+pulse j+t)) (time (j+1)-(time j+pulse j)))
def HistoryGeometry.legV (d₀ : ∀ b,ι b → ℝ) (j0 j : ℕ) (b : ξ) : Matrix (ι b) (ι b) ℝ :=
  Matrix.diagonal (fun i => scalarV (fun t => G.legLambda d₀ j0 b i (time j+pulse j+t))
    (fun t => G.drift (time j+pulse j+t)) (time (j+1)-(time j+pulse j)))

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b, Nontrivial (ι b)] in
lemma HistoryGeometry.leg_normalizer (slot : Fin n → κ) (d₀ : ∀ b,ι b → ℝ)
    (hd₀ : ∀ b,orthogonalMatrix (S.basis b) (G.D₀ b)=Matrix.diagonal (d₀ b)) (j0 j : ℕ) (b : ξ) :
    ∃ D : (Matrix (ι b) (ι b) ℝ)ˣ,
      (D:Matrix (ι b) (ι b) ℝ)=G.legU d₀ j0 j b+S.θ b • G.legV d₀ j0 j b ∧
      (∀ i,0 < (D:Matrix (ι b) (ι b) ℝ) i i) ∧
      ‖(↑D⁻¹:Matrix (ι b) (ι b) ℝ)*G.legV d₀ j0 j b‖ ≤
        ‖diagonalL (ι:=ι b)‖*(S.θ b)⁻¹ := by
  obtain ⟨N,hN,hc,hb,hp⟩ := G.legLambda_properties slot d₀ hd₀ j0 b
  apply actual_diagonal_normalizer (fun i => (hc i).comp (continuous_const.add continuous_id))
    (G.driftContinuous.comp (continuous_const.add continuous_id)) N hN G.Mpnonneg
    (fun i t => hb i _) (fun t => G.driftBound _) (fun i t _ => hp i _) ?_ (S.hθ b)
  rw [time_succ];linarith [pulse_pos j,dwell_pos j]

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open HarmonicCounterexample.Transmission HarmonicCounterexample.FiniteControl
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ (E b →L[ℝ] E b) := ContinuousLinearMap.toNormedSpace
variable {S : PulseSystem E ι κ} (G : HistoryGeometry S) {n : ℕ} [NeZero n] (slot : Fin n → κ)

/-- Actual center-regular value transmission, including the complete diagonal
leg and with no pulse scalar normalization. -/
def HistoryGeometry.transmission (s : ℕ → Fin n → ℝ) (j0 j : ℕ) (b : ξ) : Matrix (ι b) (ι b) ℝ :=
  orthogonalMatrix (S.basis b)
    (operatorValue (G.coefficient slot s j0 b) G.drift (G.l b) (time (j+1))*
      Ring.inverse (operatorValue (G.coefficient slot s j0 b) G.drift (G.l b) (time j)))

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open HarmonicCounterexample.Transmission HarmonicCounterexample.FiniteControl
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
attribute [local instance 100] LieRing.ofAssociativeRing
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
local instance (b : ξ) : NormedAddCommGroup ((ι b → ℝ) →L[ℝ] Matrix (ι b) (ι b) ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance (b : ξ) : NormedSpace ℝ ((ι b → ℝ) →L[ℝ] Matrix (ι b) (ι b) ℝ) := ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.LinearODE

end

end OAI
