import Tengoku.OpenaiMath.OAI.Geometry.HarmonicGrowth.InsertedWord

namespace OAI

noncomputable section

namespace HarmonicCounterexample.PulseTaylor
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniform value and derivative bounds on the fixed positive stretch interval.
These are bounds for the actual nonlinear Berger formula. -/
theorem angular_uniform_bounds (r : ℝ) (b D : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ Icc (1/2:ℝ) (3/2),
      ‖angular r b D q-b‖ ≤ C*|q-1| ∧ ‖angularD r b D q‖ ≤ C := by
  obtain ⟨C,hC,hest⟩ := angular_remainder r b D
  refine ⟨C+‖r • b+D‖,add_nonneg hC (norm_nonneg _),?_⟩
  intro q hq
  have hq₁ : |q-1| ≤ 1 := (abs_le.2 ⟨by linarith [hq.1],by linarith [hq.2]⟩)
  have hq₂ : (q-1)^2 ≤ |q-1| := by
    nlinarith [sq_abs (q-1),mul_le_mul_of_nonneg_left hq₁ (abs_nonneg (q-1))]
  obtain ⟨hv,hd⟩ := hest q hq
  constructor
  · calc
      ‖angular r b D q-b‖ ≤ ‖angular r b D q-b-(q-1) • (r • b+D)‖+
          ‖(q-1) • (r • b+D)‖ := norm_le_norm_sub_add _ _
      _ ≤ C*(q-1)^2+|q-1| *‖r • b+D‖ := by
        simpa only [norm_smul,Real.norm_eq_abs] using add_le_add hv (le_refl ‖(q-1) • (r • b+D)‖)
      _ ≤ (C+‖r • b+D‖)*|q-1| := by nlinarith [mul_le_mul_of_nonneg_left hq₂ hC]
  · calc
      ‖angularD r b D q‖ ≤ ‖angularD r b D q-(r • b+D)‖+‖r • b+D‖ := norm_le_norm_sub_add _ _
      _ ≤ C*|q-1|+‖r • b+D‖ := add_le_add hd le_rfl
      _ ≤ C+‖r • b+D‖ := by nlinarith [mul_le_mul_of_nonneg_left hq₁ hC]

end HarmonicCounterexample.PulseTaylor

end

noncomputable section

namespace HarmonicCounterexample.FiniteControl.SmoothWord
open Set
open scoped BigOperators
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}

/-- The finite C1 amplitude family has one bound on its compact parameter set;
no incoming metric or regular-solution history occurs in this choice. -/
lemma compact_amplitude_jet_bound {K : Set H} (hK : IsCompact K)
    (amps : Fin n → H → ℝ) (amps' : Fin n → H → H →L[ℝ] ℝ)
    (hc : ∀ j,ContinuousOn (amps j) K) (hd : ∀ j,ContinuousOn (amps' j) K) :
    ∃ U : ℝ,0 ≤ U ∧ ∀ x ∈ K,∀ j,|amps j x| ≤ U ∧ ‖amps' j x‖ ≤ U := by
  classical
  choose C hC using fun j => hK.exists_bound_of_continuousOn (hc j)
  choose D hD using fun j => hK.exists_bound_of_continuousOn (hd j)
  let U := ∑ j : Fin n,max (max (C j) (D j)) 0
  have hU : 0 ≤ U := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  refine ⟨U,hU,?_⟩
  intro x hx j
  have hj : max (max (C j) (D j)) 0 ≤ U :=
    Finset.single_le_sum (f := fun j : Fin n => max (max (C j) (D j)) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ j)
  have hac : |amps j x| ≤ C j := by simpa only [Real.norm_eq_abs] using hC j x hx
  exact ⟨hac.trans
      ((le_max_left _ _).trans ((le_max_left _ _).trans hj)),
    (hD j x hx).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hj))⟩

/-- Quantitative compact-ball-ready C1 bounds for the nonlinear word on ALL
of the time axis. The constants precede amplitudes, parameter jets, and duration. -/
theorem nonlinearBergerWord_uniform_C1_bound (r : ℝ) (b : E) (D : Fin n → E) :
    ∃ C₀ C : ℝ,0 ≤ C₀ ∧ 0 ≤ C ∧
      ∀ (amps : Fin n → ℝ) (jets : Fin n → H →L[ℝ] ℝ) (U T : ℝ),
        0 ≤ U → (∀ j,|amps j| ≤ U) → (∀ j,‖jets j‖ ≤ U) →
        0 < T → 2*C₀*U ≤ T → ∀ t,
        ‖nonlinearBergerWord r b D amps T t-b‖ ≤ C*U/T ∧
        ‖∑ j : Fin n,((T⁻¹*duration n*bump j (duration n*t)) • jets j).smulRight
          (PulseTaylor.angularD r b (D j) (packetStretch amps T t j))‖ ≤ C*U/T := by
  classical
  obtain ⟨C₀,hC₀,hpos⟩ := packetStretch_uniform_positive n
  choose B hB hb using fun j : Fin n => packet_functions_bounded j
  choose K hK hk using fun j : Fin n => PulseTaylor.angular_uniform_bounds r b (D j)
  let C := ∑ j : Fin n,duration n*B j*K j
  have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (duration_pos n).le (hB j)) (hK j))
  refine ⟨C₀,C,hC₀,hC,?_⟩
  intro amps jets U T hU ha hj hT hlong t
  have hq (j : Fin n) := hpos amps U T hU ha hT hlong t j
  have hsmall (j : Fin n) : |packetStretch amps T t j-1| ≤ duration n*B j*U/T := by
    calc
      _ = duration n*|bump j (duration n*t)| *|amps j|/T := by
        simp only [packetStretch,add_sub_cancel_left,abs_mul,abs_inv,
          abs_of_pos hT,abs_of_pos (duration_pos n)]
        ring
      _ ≤ duration n*B j*U/T := by
        apply div_le_div_of_nonneg_right _ hT.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hb j _).1 (duration_pos n).le)
          (ha j) (abs_nonneg _) (mul_nonneg (duration_pos n).le (hB j))
  have hend : (∑ j : Fin n,(duration n*B j*K j)*U/T)=C*U/T := by
    rw [← Finset.sum_div,← Finset.sum_mul]
  constructor
  · have he : nonlinearBergerWord r b D amps T t-b =
        ∑ j : Fin n,(PulseTaylor.angular r b (D j) (packetStretch amps T t j)-b) := by
      simp only [nonlinearBergerWord,nonlinearPacket,add_sub_cancel_left]
    rw [he]
    calc
      _ ≤ ∑ j : Fin n,‖PulseTaylor.angular r b (D j) (packetStretch amps T t j)-b‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n,(duration n*B j*K j)*U/T := by
        apply Finset.sum_le_sum
        intro j _
        calc
          _ ≤ K j*|packetStretch amps T t j-1| := (hk j _ (hq j)).1
          _ ≤ K j*(duration n*B j*U/T) := mul_le_mul_of_nonneg_left (hsmall j) (hK j)
          _ = (duration n*B j*K j)*U/T := by ring
      _ = C*U/T := hend
  · calc
      _ ≤ ∑ j : Fin n,‖((T⁻¹*duration n*bump j (duration n*t)) • jets j).smulRight
          (PulseTaylor.angularD r b (D j) (packetStretch amps T t j))‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n,(duration n*B j*K j)*U/T := by
        apply Finset.sum_le_sum
        intro j _
        rw [ContinuousLinearMap.norm_smulRight_apply,norm_smul,Real.norm_eq_abs,
          abs_mul,abs_mul,abs_inv,abs_of_pos hT,abs_of_pos (duration_pos n)]
        have hw : T⁻¹*duration n*|bump j (duration n*t)| *‖jets j‖ ≤
            T⁻¹*duration n*B j*U :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hb j _).1 (mul_nonneg (inv_nonneg.2 hT.le) (duration_pos n).le))
            (hj j) (norm_nonneg _) (mul_nonneg (mul_nonneg (inv_nonneg.2 hT.le) (duration_pos n).le) (hB j))
        calc
          _ ≤ (T⁻¹*duration n*B j*U)*K j :=
            mul_le_mul hw (hk j _ (hq j)).2 (norm_nonneg _) (mul_nonneg
              (mul_nonneg (mul_nonneg (inv_nonneg.2 hT.le) (duration_pos n).le) (hB j)) hU)
          _ = (duration n*B j*K j)*U/T := by ring
      _ = C*U/T := hend

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section

namespace HarmonicCounterexample.FiniteControl.SmoothWord
open Set
open scoped BigOperators
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}

/-- One parameter-ball bound for the actual inserted coefficient and its actual
Frechet derivative. Both constants are fixed before ALL histories and time shifts. -/
theorem insertWord_compact_C1_bound {K : Set H} (hK : IsCompact K)
    (r : ℝ) (b : E) (D : Fin n → E)
    (amps : Fin n → H → ℝ) (amps' : Fin n → H → H →L[ℝ] ℝ)
    (ha : ∀ x ∈ K,∀ j,HasFDerivAt (amps j) (amps' j x) x)
    (hc : ∀ j,ContinuousOn (amps j) K) (hd : ∀ j,ContinuousOn (amps' j) K) :
    ∃ T₀ C : ℝ,1 ≤ T₀ ∧ 0 ≤ C ∧ ∀ T ≥ T₀,∀ x ∈ K,
      (∀ j t,packetStretch (fun i => amps i x) T t j ∈ Icc (1/2:ℝ) (3/2)) ∧
      ∀ (history : ℝ → E) (α : ℝ → ℝ) (M a : ℝ),0 ≤ M →
        (∀ t,|α t| ≤ M) → ∀ t,
        ‖insertWord history α r b D (fun i => amps i x) a T t-history t‖ ≤ M*C/T ∧
        ‖fderiv ℝ (fun y => insertWord history α r b D (fun i => amps i y) a T t) x‖ ≤ M*C/T := by
  obtain ⟨U,hU,hbound⟩ := compact_amplitude_jet_bound hK amps amps' hc hd
  obtain ⟨C₀,C,hC₀,hC,hest⟩ := nonlinearBergerWord_uniform_C1_bound (H := H) r b D
  obtain ⟨P,hP,hpos⟩ := packetStretch_uniform_positive n
  let T₀ := max 1 (max (2*C₀*U) (2*P*U))
  refine ⟨T₀,C*U,le_max_left _ _,mul_nonneg hC hU,?_⟩
  intro T hT x hx
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hT)
  have hl₀ : 2*C₀*U ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hl₁ : 2*P*U ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have has (j : Fin n) := (hbound x hx j).1
  have hjs (j : Fin n) := (hbound x hx j).2
  have hq (j : Fin n) (t : ℝ) := hpos (fun i => amps i x) U T hU has hTpos hl₁ t j
  refine ⟨hq,?_⟩
  intro history α M a hM hα t
  have he := hest (fun i => amps i x) (fun i => amps' i x) U T hU has hjs hTpos hl₀ ((t-a)/T)
  have hne (j : Fin n) : packetStretch (fun i => amps i x) T ((t-a)/T) j ≠ 0 := by
    have := (hq j ((t-a)/T)).1
    linarith
  constructor
  · change ‖history t+α t • (nonlinearBergerWord r b D (fun i => amps i x) T ((t-a)/T)-b)-history t‖ ≤ _
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ M*(C*U/T) := mul_le_mul (hα t) he.1 (norm_nonneg _) hM
      _ = M*(C*U)/T := by ring
  · rw [(insertWord_hasFDerivAt history α r b D amps (fun i => amps' i x)
      (ha x hx) a T t hne).fderiv,norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ M*(C*U/T) := mul_le_mul (hα t) he.2 (norm_nonneg _) hM
      _ = M*(C*U)/T := by ring

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open scoped ContDiff
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

/-- Fixed continuous linear injection from angular coefficients to the
lower-left phase block. It does not depend on histories or parameters. -/
def phaseCoefficientInjection : (E →L[ℝ] E) →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E :=
  (ContinuousLinearMap.compL ℝ (OperatorPhase E) (E →L[ℝ] E) (OperatorPhase E)
      (ContinuousLinearMap.inr ℝ (E →L[ℝ] E) (E →L[ℝ] E))).comp
    (((ContinuousLinearMap.compL ℝ (OperatorPhase E) (E →L[ℝ] E) (E →L[ℝ] E)).flip
      (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) (E →L[ℝ] E))).comp
        (ContinuousLinearMap.mul ℝ (E →L[ℝ] E)))

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ} [NeZero n]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter
open scoped Topology

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

namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {E H ι : Type*} {n : ℕ} [NeZero n]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [Fintype ι] [DecidableEq ι]
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

namespace HarmonicCounterexample.FiniteControl.SmoothWord
open Set MeasureTheory
open scoped ContDiff BigOperators
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}
local instance : NormedAddCommGroup (H →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

/-- The actual Frechet derivative of the ideal packet, retained as a continuous
linear map rather than only its finitely many rays. -/
def unitPacketJet (a' : Fin n → H →L[ℝ] ℝ) (X : Fin n → E) (t : ℝ) : H →L[ℝ] E :=
  duration n • (∑ j,(a' j).smulRight (bump j (duration n*t) • X j))

lemma unitPacketJet_smooth (a' : Fin n → H →L[ℝ] ℝ) (X : Fin n → E) :
    ContDiff ℝ ∞ (unitPacketJet a' X) := by
  unfold unitPacketJet
  apply (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => duration n)).smul
  apply ContDiff.sum
  intro j _
  have he : (fun t => (a' j).smulRight (bump j (duration n*t) • X j))=
      (fun t => bump j (duration n*t) • (a' j).smulRight (X j)) := by
    ext t z
    simp only [ContinuousLinearMap.smulRight_apply,smul_apply]
    exact smul_comm _ _ _
  rw [he]
  exact ((bump_smooth j).comp (contDiff_const.mul contDiff_id)).smul contDiff_const

/-- A single value-and-operator-jet bound on a compact parameter set, chosen
before any physical history, duration or radial coefficients. -/
theorem compact_ideal_packet_bound {K : Set H} (hK : IsCompact K)
    (amps : Fin n → H → ℝ) (amps' : Fin n → H → H →L[ℝ] ℝ)
    (hc : ∀ j,ContinuousOn (amps j) K) (hd : ∀ j,ContinuousOn (amps' j) K)
    (X : Fin n → E) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ x ∈ K,
      (∀ t,‖unitPacketCoefficient (fun j => amps j x) X t‖ ≤ C) ∧
      (∀ t,‖unitPacketJet (fun j => amps' j x) X t‖ ≤ C) ∧
      (∫ t in (0:ℝ)..1,‖unitPacketCoefficient (fun j => amps j x) X t‖)+
        (∫ t in (0:ℝ)..1,‖unitPacketJet (fun j => amps' j x) X t‖) ≤ 2*C := by
  classical
  obtain ⟨U,hU,hbound⟩ := compact_amplitude_jet_bound hK amps amps' hc hd
  choose B hB hb using fun j : Fin n => packet_functions_bounded j
  let C := duration n * ∑ j : Fin n,U*B j*‖X j‖
  have hC : 0 ≤ C := mul_nonneg (duration_pos n).le (Finset.sum_nonneg (fun j _ => mul_nonneg (mul_nonneg hU (hB j)) (norm_nonneg _)))
  refine ⟨C,hC,?_⟩
  intro x hx
  have hv (t : ℝ) : ‖unitPacketCoefficient (fun j => amps j x) X t‖ ≤ C := by
    rw [unitPacketCoefficient,norm_smul,Real.norm_eq_abs,abs_of_pos (duration_pos n)]
    apply mul_le_mul_of_nonneg_left _ (duration_pos n).le
    calc
      ‖packetCoefficient (fun j => amps j x) X (duration n*t)‖ ≤
          ∑ j : Fin n,‖(amps j x*bump j (duration n*t)) • X j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n,U*B j*‖X j‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul,Real.norm_eq_abs,abs_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (hbound x hx j).1 (hb j _).1 (abs_nonneg _) hU) (norm_nonneg _)
  have hj (t : ℝ) : ‖unitPacketJet (fun j => amps' j x) X t‖ ≤ C := by
    rw [unitPacketJet,norm_smul,Real.norm_eq_abs,abs_of_pos (duration_pos n)]
    apply mul_le_mul_of_nonneg_left _ (duration_pos n).le
    calc
      _ ≤ ∑ j : Fin n,‖(amps' j x).smulRight (bump j (duration n*t) • X j)‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n,U*B j*‖X j‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [ContinuousLinearMap.norm_smulRight_apply,norm_smul,Real.norm_eq_abs,← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (hbound x hx j).2 (hb j _).1 (abs_nonneg _) hU) (norm_nonneg _)
  refine ⟨hv,hj,?_⟩
  have hvI := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    ((unitPacketCoefficient_smooth (fun j => amps j x) X).continuous.norm.intervalIntegrable 0 1)
    (intervalIntegrable_const (c := C)) (fun t _ => hv t)
  have hjI := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    ((unitPacketJet_smooth (fun j => amps' j x) X).continuous.norm.intervalIntegrable 0 1)
    (intervalIntegrable_const (c := C)) (fun t _ => hj t)
  simp only [intervalIntegral.integral_const,sub_zero,one_smul] at hvI hjI
  linarith

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set

/-- Positive-time scalar baseline with a continuous global extension. This
avoids making a false global nonsingularity claim at negative time. -/
lemma clipped_scalarBaseline_continuous {A p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ A t) {θ : ℝ} (hθ : 0 ≤ θ) (a : ℝ) :
    Continuous (fun t => scalarBaseline A p θ (max 0 (t-a))) := by
  have hc : ContinuousOn (scalarBaseline A p θ) (Ici 0) := by
    intro t ht
    exact (actual_scalar_baseline_deriv hA hp hMA hMp hAn hpn hAp hθ ht).continuousAt.continuousWithinAt
  exact hc.comp_continuous (continuous_const.max (continuous_id.sub continuous_const))
    (fun t => show 0 ≤ max 0 (t-a) from le_max_left _ _)

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {E H ι κ : Type*} {n : ℕ} [NeZero n]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [Fintype ι] [DecidableEq ι] [Fintype κ]
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

namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ} [NeZero n]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {E H ι : Type*} {n : ℕ} [NeZero n]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [Fintype ι] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup (H →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff
variable {H A : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] {n : ℕ}
lemma leftWord_differentiableAt (X : ℕ → H → A) {x : H}
    (hX : ∀ j,DifferentiableAt ℝ (X j) x) (m : ℕ) :
    DifferentiableAt ℝ (fun y => leftWord (fun j => X j y) m) x := by
  induction m with
  | zero => exact differentiableAt_const _
  | succ m ih =>
    exact (((contDiff_iff_contDiffAt.2 (fun z => (NormedSpace.exp_analytic (𝕂:=ℝ) z).contDiffAt) : ContDiff ℝ ∞ (NormedSpace.exp : A → A)) : ContDiff ℝ ∞ (NormedSpace.exp : A → A)).differentiable (by simp)).differentiableAt.comp x (hX m) |>.mul ih

lemma actual_packet_differentiableAt (amps : Fin n → H → ℝ) (X : Fin n → A)
    {x : H} (ha : ∀ j,DifferentiableAt ℝ (amps j) x) :
    DifferentiableAt ℝ (fun y => LinearODE.flow (fun t => ContinuousLinearMap.mul ℝ A
      (unitPacketCoefficient (fun j => amps j y) X t)) 1 1) x := by
  simp_rw [actual_packet_endpoint]
  apply leftWord_differentiableAt
  intro j
  by_cases hj : j < n
  · simpa only [extendWord,dite_eq_left hj,Pi.smul_apply,Pi.smul_apply',smul_eq_mul] using (ha ⟨j,hj⟩).smul_const (X ⟨j,hj⟩)
  · simpa only [extendWord,dite_eq_right hj] using (differentiableAt_const (0:A) : DifferentiableAt ℝ (fun _ : H => (0:A)) x)

lemma leftWord_contDiff (X : ℕ → H → A) (hX : ∀ j,ContDiff ℝ ∞ (X j)) (m : ℕ) :
    ContDiff ℝ ∞ (fun y => leftWord (fun j => X j y) m) := by
  induction m with
  | zero => exact contDiff_const
  | succ m ih => exact ((contDiff_iff_contDiffAt.2 (fun z => (NormedSpace.exp_analytic (𝕂:=ℝ) z).contDiffAt) : ContDiff ℝ ∞ (NormedSpace.exp : A → A)).comp (hX m)).mul ih

lemma actual_packet_contDiff (amps : Fin n → H → ℝ) (X : Fin n → A)
    (ha : ∀ j,ContDiff ℝ ∞ (amps j)) :
    ContDiff ℝ ∞ (fun y => LinearODE.flow (fun t => ContinuousLinearMap.mul ℝ A
      (unitPacketCoefficient (fun j => amps j y) X t)) 1 1) := by
  simp_rw [actual_packet_endpoint]
  apply leftWord_contDiff
  intro j
  by_cases hj : j < n
  · simpa only [extendWord,dite_eq_left hj,Pi.smul_apply,Pi.smul_apply',smul_eq_mul] using (ha ⟨j,hj⟩).smul_const (X ⟨j,hj⟩)
  · simpa only [extendWord,dite_eq_right hj] using (contDiff_const : ContDiff ℝ ∞ (fun _ : H => (0:A)))
end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
lemma normalized_transmission_differentiableAt (A : H → ℝ → E →L[ℝ] E)
    (b : ℝ → ℝ) (l a t c : ℝ) {x : H}
    {Da Dt : H →L[ℝ] E →L[ℝ] E}
    (ha : HasFDerivAt (fun y => operatorValue (A y) b l a) Da x)
    (ht : HasFDerivAt (fun y => operatorValue (A y) b l t) Dt x)
    (hu : IsUnit (operatorValue (A x) b l a)) :
    DifferentiableAt ℝ (fun y => c • (operatorValue (A y) b l t*
      Ring.inverse (operatorValue (A y) b l a))) x :=
  (ht.mul' (clm_inverse_fderiv hu ha)).differentiableAt.const_smul c
end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {E H ι κ : Type*} {n : ℕ} [NeZero n]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [Fintype ι] [DecidableEq ι] [Fintype κ]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (H →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

lemma small_radius_bounds {G L F θ d : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hF : 0 ≤ F) (hθ : 0 < θ) (hd : 0 ≤ d)
    (h : d ≤ min (1/(1+G)) (θ/(2*(1+L+F)))) :
    G*d ≤ 1 ∧ (L+F)*d ≤ θ/2 := by
  constructor
  · have hi := (le_div_iff₀ (show 0 < 1+G by linarith)).1 (h.trans (min_le_left _ _))
    nlinarith
  · have hratio : (L+F)/(2*(1+L+F)) ≤ 1/2 :=
      (div_le_iff₀ (show 0 < 2*(1+L+F) by positivity)).2 (by linarith)
    calc
      (L+F)*d ≤ (L+F)*(θ/(2*(1+L+F))) :=
        mul_le_mul_of_nonneg_left (h.trans (min_le_right _ _)) (add_nonneg hL hF)
      _ = ((L+F)/(2*(1+L+F)))*θ := by ring
      _ ≤ (1/2)*θ := mul_le_mul_of_nonneg_right hratio hθ.le
      _ = θ/2 := by ring

lemma source_small_of_total {n : ℕ} (f : Fin n → ℝ) (hf : ∀ j,0 ≤ f j)
    {Z L δ u d θ F : ℝ} (hZ : 0 ≤ Z) (hL : 0 ≤ L) (hfF : (∑ j,f j*Z) ≤ F)
    (hδ : δ ≤ d) (hu : u ≤ d) (hd : 0 ≤ d) (hS : (L+F)*d ≤ θ/2) :
    L*δ+u*(∑ j,f j*Z) ≤ θ/2 := by
  have hz : 0 ≤ ∑ j,f j*Z := Finset.sum_nonneg (fun j _ => mul_nonneg (hf j) hZ)
  calc
    _ ≤ L*d+d*F := add_le_add (mul_le_mul_of_nonneg_left hδ hL) (mul_le_mul hu hfF hz hd)
    _ = (L+F)*d := by ring
    _ ≤ θ/2 := hS

lemma exponential_error_linear {J G d : ℝ} (hJ : 0 ≤ J) (hG : 0 ≤ G)
    (hd : 0 ≤ d) (hGd : G*d ≤ 1) :
    Real.exp (2*J+J*(G*d))*(J*(G*d)) ≤ (Real.exp (3*J)*J*G)*d := by
  calc
    _ ≤ Real.exp (3*J)*(J*(G*d)) := by
      apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hGd hJ]
    _ = _ := by ring

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set
open scoped ContDiff BigOperators Matrix.Norms.Frobenius
variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
local instance : NormedAddCommGroup (H →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (H →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] F) := ContinuousLinearMap.toNormedSpace

lemma linear_C1_error (L : E →L[ℝ] F) {f g : H → E} {x : H} {η : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (he : max ‖f x-g x‖ ‖fderiv ℝ f x-fderiv ℝ g x‖ ≤ η) :
    max ‖L (f x)-L (g x)‖
      ‖fderiv ℝ (fun y => L (f y)) x-fderiv ℝ (fun y => L (g y)) x‖ ≤ ‖L‖*η := by
  apply max_le
  · rw [← map_sub]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans he) (norm_nonneg _))
  · change ‖fderiv ℝ (L ∘ f) x-fderiv ℝ (L ∘ g) x‖ ≤ ‖L‖*η
    rw [(L.hasFDerivAt.comp x hf.hasFDerivAt).fderiv,
      (L.hasFDerivAt.comp x hg.hasFDerivAt).fderiv,← ContinuousLinearMap.comp_sub]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans he) (norm_nonneg _))

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open HarmonicCounterexample.FiniteControl.SmoothWord
open scoped Matrix.Norms.Frobenius
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

def orthogonalMatrixAlgHom (b : OrthonormalBasis ι ℝ E) :
    (E →L[ℝ] E) →ₐ[ℝ] Matrix ι ι ℝ where
  toFun := orthogonalMatrix b
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := orthogonalMatrix_one b
  map_mul' := orthogonalMatrix_mul b
  commutes' c := by simp only [Algebra.algebraMap_eq_smul_one,map_smul,orthogonalMatrix_one]

lemma orthogonalMatrix_exp (b : OrthonormalBasis ι ℝ E) (X : E →L[ℝ] E) :
    orthogonalMatrix b (NormedSpace.exp X)=NormedSpace.exp (orthogonalMatrix b X) := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact NormedSpace.map_exp (orthogonalMatrixAlgHom b) (orthogonalMatrix b).continuous X

lemma orthogonalMatrix_leftWord (b : OrthonormalBasis ι ℝ E) (X : ℕ → E →L[ℝ] E) (n : ℕ) :
    orthogonalMatrix b (leftWord X n)=leftWord (fun j => orthogonalMatrix b (X j)) n := by
  induction n with
  | zero => exact orthogonalMatrix_one b
  | succ n ih =>
    rw [leftWord,orthogonalMatrix_mul,orthogonalMatrix_exp,ih]
    rfl

/-- Orthonormal coordinates of the genuine chronological ideal packet. -/
lemma orthogonalMatrix_packet (b : OrthonormalBasis ι ℝ E) {n : ℕ}
    (a : Fin n → ℝ) (X : Fin n → E →L[ℝ] E) :
    orthogonalMatrix b (flow (fun t => ContinuousLinearMap.mul ℝ (E →L[ℝ] E)
      (unitPacketCoefficient a X t)) 1 1)=
      flow (fun t => ContinuousLinearMap.mul ℝ (Matrix ι ι ℝ)
        (unitPacketCoefficient a (fun j => orthogonalMatrix b (X j)) t)) 1 1 := by
  rw [actual_packet_endpoint,actual_packet_endpoint,orthogonalMatrix_leftWord]
  congr 1
  funext j
  by_cases hj : j < n
  · simp only [extendWord,dite_eq_left hj,map_smul]
  · simp only [extendWord,dite_eq_right hj,map_zero]

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open Set HarmonicCounterexample.FiniteControl.SmoothWord
open scoped ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {E H ι κ : Type*} {n : ℕ} [NeZero n]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [Fintype ι] [DecidableEq ι] [Fintype κ]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (H →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

end HarmonicCounterexample.LinearODE

end

noncomputable section

namespace HarmonicCounterexample.LinearODE
open scoped BigOperators
variable {β H : Type*} [Fintype β] [NormedAddCommGroup H] [NormedSpace ℝ H]
  {F : β → Type*} [∀ i,NormedAddCommGroup (F i)] [∀ i,NormedSpace ℝ (F i)]
local instance : NormedAddCommGroup (H →L[ℝ] ((i : β) → F i)) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (H →L[ℝ] ((i : β) → F i)) := ContinuousLinearMap.toNormedSpace

lemma finite_C1_norm {f : (i : β) → H → F i} {x : H} {η : ℝ}
    (hη : 0 ≤ η) (hf : ∀ i,DifferentiableAt ℝ (f i) x)
    (he : ∀ i,max ‖f i x‖ ‖fderiv ℝ (f i) x‖ ≤ η) :
    DifferentiableAt ℝ (fun y i => f i y) x ∧
      max ‖(fun i => f i x)‖ ‖fderiv ℝ (fun y i => f i y) x‖ ≤ η := by
  have hdf := hasFDerivAt_pi.2 (fun i => (hf i).hasFDerivAt)
  refine ⟨hdf.differentiableAt,max_le ?_ ?_⟩
  · exact (pi_norm_le_iff_of_nonneg hη).2 (fun i => (le_max_left _ _).trans (he i))
  · rw [hdf.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ hη
    intro v
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hη (norm_nonneg v))).2
    intro i
    exact ((fderiv ℝ (f i) x).le_opNorm v).trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (he i)) (norm_nonneg v))

end HarmonicCounterexample.LinearODE

end

end OAI
