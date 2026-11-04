import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.LaurentPicard

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Picard branches driven by a continuous curve of scalar base velocities. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen
noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The same scalar lift, now driven pointwise by a continuous velocity curve.-/
def drivenCurveVectorField {d : ℕ} (f : MultiLaurent d) (a : C(X, ℂ))
    (z : Fin d → C(X, ℂ)) : Fin d → C(X, ℂ) :=
  fun i => a * curveVectorField (laurentRepresentative f) 1 z i

omit [CompactSpace X] in
theorem drivenCurveVectorField_apply {d : ℕ} (f : MultiLaurent d) (a : C(X, ℂ))
    {z : Fin d → C(X, ℂ)} (hz : ∀ t, (fun i => z i t) ∈ laurentRegularDomain f)
    (i : Fin d) (t : X) :
    drivenCurveVectorField f a z i t = laurentVectorField f (a t) (fun j => z j t) i := by
  simp only [drivenCurveVectorField, ContinuousMap.mul_apply,
    curveVectorField_apply (laurentRepresentative f) 1 hz,
    laurentVectorField, polynomialVectorField, scalarLift, one_mul]
  ring

theorem drivenCurveVectorField_contDiffAt {d : ℕ} (f : MultiLaurent d)
    {a : C(X, ℂ)} {z : Fin d → C(X, ℂ)}
    (hz : ∀ t, (fun i => z i t) ∈ laurentRegularDomain f) :
    ContDiffAt ℝ ⊤ (fun az : C(X, ℂ) × (Fin d → C(X, ℂ)) =>
      drivenCurveVectorField f az.1 az.2) (a, z) := by
  have hv : ContDiffAt ℝ ⊤ (fun az : C(X, ℂ) × (Fin d → C(X, ℂ)) =>
      curveVectorField (laurentRepresentative f) 1 az.2) (a, z) :=
    (laurentCurveVectorField_contDiffAt f (a := 1) hz).comp (a, z)
      (contDiffAt_const.prodMk contDiffAt_snd)
  apply contDiffAt_pi.mpr
  intro i
  exact contDiffAt_fst.mul ((contDiffAt_apply ℝ _ i _).comp (a, z) hv)

/-- Evaluation of all coordinate curves at a fixed unit-interval time.-/
def torusCurveEval (d : ℕ) (τ : CurveTime) : TorusCurves d →L[ℝ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi (fun i => (ContinuousMap.evalCLM ℝ τ).comp (ContinuousLinearMap.proj i))

/-- Integration with an arbitrary anchor, allowing local solutions on both
sides of an initial time by anchoring at the middle of the unit interval.-/
def torusCurveIntegralFrom (d : ℕ) (τ : CurveTime) : TorusCurves d →L[ℝ] TorusCurves d :=
  torusCurveIntegral d - (constantTorusCurves d).comp ((torusCurveEval d τ).comp (torusCurveIntegral d))

/-- A regular analytic Picard branch with a continuous velocity curve as a
Banach-space parameter. No time derivative of that curve is assumed.-/
theorem laurent_exists_driven_picard_neighborhood {d : ℕ} (f : MultiLaurent d)
    (τ : CurveTime) (a : C(CurveTime, ℂ)) {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    ∃ (Ψ : ℝ × (C(CurveTime, ℂ) × (Fin d → ℂ)) → TorusCurves d)
      (U : Set (ℝ × (C(CurveTime, ℂ) × (Fin d → ℂ)))),
      IsOpen U ∧ (0, (a, z)) ∈ U ∧ ContDiffOn ℝ ⊤ Ψ U ∧
      Ψ (0, (a, z)) = constantTorusCurves d z ∧
      ∀ q ∈ U, (∀ t, (fun i => Ψ q i t) ∈ laurentRegularDomain f) ∧
        Ψ q = constantTorusCurves d q.2.2 +
          q.1 • torusCurveIntegralFrom d τ (drivenCurveVectorField f q.2.1 (Ψ q)) := by
  let V : C(CurveTime, ℂ) × TorusCurves d → TorusCurves d :=
    fun az => drivenCurveVectorField f az.1 az.2
  have hV : ContDiffAt ℝ ⊤ V (a, constantTorusCurves d z) :=
    drivenCurveVectorField_contDiffAt f (fun _ => hz)
  obtain ⟨Φ, hΦ, hΦ0, heq⟩ := exists_smooth_picard_branch (torusCurveIntegralFrom d τ) V hV
  let j : ℝ × (C(CurveTime, ℂ) × (Fin d → ℂ)) →
      ℝ × (C(CurveTime, ℂ) × TorusCurves d) :=
    fun q => (q.1, (q.2.1, constantTorusCurves d q.2.2))
  have hj : ContDiff ℝ ⊤ j := contDiff_fst.prodMk
    (contDiff_snd.fst.prodMk ((constantTorusCurves d).contDiff.comp contDiff_snd.snd))
  have hs : ContDiffAt ℝ ⊤ (Φ ∘ j) (0, (a, z)) := hΦ.comp (0, (a, z)) hj.contDiffAt
  have hzero : (Φ ∘ j) (0, (a, z)) = constantTorusCurves d z := hΦ0
  have hreg : ∀ᶠ q in 𝓝 (0, (a, z)),
      ∀ t, (fun i => (Φ ∘ j) q i t) ∈ laurentRegularDomain f :=
    hs.continuousAt.preimage_mem_nhds ((regularTorusCurves_isOpen f).mem_nhds (by
      rw [hzero]
      exact fun _ => hz))
  have hall := ((hs.eventually (by simp)).and hreg).and
    (hj.continuous.continuousAt.tendsto.eventually heq)
  obtain ⟨U, hU, hopen, hbase⟩ := mem_nhds_iff.mp hall
  exact ⟨Φ ∘ j, U, hopen, hbase, fun q hq => (hU hq).1.1.contDiffWithinAt,
    hzero, fun q hq => ⟨(hU hq).1.2, (hU hq).2⟩⟩

/-- A driven Picard solution yields an actual nonautonomous ODE trajectory,
with full derivatives at both ends of the unit interval.-/
theorem laurent_driven_picard_equation_solves_ode {d : ℕ} (f : MultiLaurent d)
    (τ : CurveTime) (a : C(CurveTime, ℂ)) (δ : ℝ) (z : Fin d → ℂ) (u : TorusCurves d)
    (hu : ∀ t, (fun i => u i t) ∈ laurentRegularDomain f)
    (he : u = constantTorusCurves d z +
      δ • torusCurveIntegralFrom d τ (drivenCurveVectorField f a u)) :
    ∃ γ : ℝ → Fin d → ℂ, γ τ.val = z ∧
      (∀ t : CurveTime, γ t.val = fun i => u i t) ∧
      ∀ t : CurveTime, γ t.val ∈ laurentRegularDomain f ∧
        HasDerivAt γ (δ • laurentVectorField f (a t) (γ t.val)) t.val := by
  let w := drivenCurveVectorField f a u
  let γ : ℝ → Fin d → ℂ := fun t i => z i + δ • ((∫ s in (0 : ℝ)..t, extendCurve (w i) s) -
    ∫ s in (0 : ℝ)..τ.val, extendCurve (w i) s)
  have hγ : ∀ t : CurveTime, γ t.val = fun i => u i t := by
    intro t
    funext i
    have hi := congrArg (fun v : TorusCurves d => v i t) he
    change u i t = z i + δ • ((∫ s in (0 : ℝ)..t.val, extendCurve (w i) s) -
      ∫ s in (0 : ℝ)..τ.val, extendCurve (w i) s) at hi
    exact hi.symm
  refine ⟨γ, ?_, hγ, ?_⟩
  · ext i
    simp [γ]
  · intro t
    refine ⟨(hγ t) ▸ hu t, hasDerivAt_pi.mpr (fun i => ?_)⟩
    have hd := (((curvePrimitive_hasDerivAt (w i) t).sub_const
      (∫ s in (0 : ℝ)..τ.val, extendCurve (w i) s)).const_smul δ).const_add (z i)
    change HasDerivAt (fun t => γ t i) (δ • w i t) t.val at hd
    simpa only [w, drivenCurveVectorField_apply f a hu, hγ t, Pi.smul_apply] using hd

/-- A continuous driving velocity restricted to an oriented time segment.-/
def rescaledVelocity (a : ℝ → ℂ) (ha : Continuous a) (τ : CurveTime) (p : ℝ × ℝ) : C(CurveTime, ℂ) :=
  ⟨fun t => a (p.1 + p.2 * (t.val - τ.val)), ha.comp (continuous_const.add
    (continuous_const.mul (continuous_subtype_val.sub continuous_const)))⟩

theorem rescaledVelocity_continuous (a : ℝ → ℂ) (ha : Continuous a) (τ : CurveTime) :
    Continuous (rescaledVelocity a ha τ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact ha.comp (continuous_fst.fst.add (continuous_fst.snd.mul
    ((continuous_subtype_val.comp continuous_snd).sub continuous_const)))

@[simp] theorem rescaledVelocity_zero (a : ℝ → ℂ) (ha : Continuous a) (τ : CurveTime) (s : ℝ) :
    rescaledVelocity a ha τ (s, 0) = ContinuousMap.const CurveTime (a s) := by
  ext t
  simp [rescaledVelocity]

/-- Around every time and regular initial point, continuous driving velocities
admit regular scaled Picard solutions. The solutions depend continuously on all
parameters and analytically on the initial point for fixed start time and scale.-/
theorem laurent_driven_local_family {d : ℕ} (f : MultiLaurent d)
    (τ : CurveTime) (a : ℝ → ℂ) (ha : Continuous a) (s : ℝ)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    ∃ (Ψ : ℝ × (ℝ × (Fin d → ℂ)) → TorusCurves d)
      (Ω : Set (ℝ × (ℝ × (Fin d → ℂ)))),
      IsOpen Ω ∧ (s, (0, z)) ∈ Ω ∧ ContinuousOn Ψ Ω ∧
      (∀ t δ, ContDiffOn ℝ ⊤ (fun y => Ψ (t, (δ, y))) {y | (t, (δ, y)) ∈ Ω}) ∧
      ∀ q ∈ Ω, (∀ t, (fun i => Ψ q i t) ∈ laurentRegularDomain f) ∧
        Ψ q = constantTorusCurves d q.2.2 + q.2.1 • torusCurveIntegralFrom d τ
          (drivenCurveVectorField f (rescaledVelocity a ha τ (q.1, q.2.1)) (Ψ q)) := by
  obtain ⟨Φ, U, hU, hbase, hΦ, hzero, heq⟩ :=
    laurent_exists_driven_picard_neighborhood f τ (ContinuousMap.const CurveTime (a s)) hz
  let j : ℝ × (ℝ × (Fin d → ℂ)) → ℝ × (C(CurveTime, ℂ) × (Fin d → ℂ)) :=
    fun q => (q.2.1, (rescaledVelocity a ha τ (q.1, q.2.1), q.2.2))
  have hj : Continuous j := continuous_snd.fst.prodMk
    (((rescaledVelocity_continuous a ha τ).comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
      continuous_snd.snd)
  refine ⟨Φ ∘ j, j ⁻¹' U, hU.preimage hj, ?_,
    hΦ.continuousOn.comp hj.continuousOn (mapsTo_preimage j U), ?_, ?_⟩
  · simpa only [mem_preimage, j, rescaledVelocity_zero] using hbase
  · intro t δ
    have hj' : ContDiff ℝ ⊤ (fun y : Fin d → ℂ => j (t, (δ, y))) := by
      dsimp only [j]
      exact contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
    exact hΦ.comp hj'.contDiffOn (fun y hy => hy)
  · intro q hq
    exact heq (j q) hq

end
end DuistermaatVanDerKallen
