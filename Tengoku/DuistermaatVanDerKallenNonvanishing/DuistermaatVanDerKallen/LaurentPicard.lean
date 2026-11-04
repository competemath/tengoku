import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.CurveField
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.CurveIntegral
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.PicardImplicit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A local implicit Picard branch for the actual Laurent vector field, with
joint dependence on time scale, base velocity, and the initial torus point. -/

open Set
open scoped Topology

namespace DuistermaatVanDerKallen

noncomputable section

abbrev TorusCurves (d : ℕ) := Fin d → C(CurveTime, ℂ)

/-- Constant torus-coordinate curves, bounded real-linearly in the initial point.-/
def constantTorusCurves (d : ℕ) : (Fin d → ℂ) →L[ℝ] TorusCurves d :=
  ContinuousLinearMap.pi (fun i =>
    (ContinuousLinearMap.const ℝ CurveTime).comp (ContinuousLinearMap.proj i))

/-- Coordinatewise integration on the fixed unit interval.-/
def torusCurveIntegral (d : ℕ) : TorusCurves d →L[ℝ] TorusCurves d :=
  ContinuousLinearMap.pi (fun i => curvePrimitiveCLM.comp (ContinuousLinearMap.proj i))

/-- Regrouping coordinate curves as a curve in coordinate space is continuous.
@isnad1 id=continuo.0h1v.s8.a04bb76c8899 from=translated src=- shape=be6121fc vocab=ef04a7bf
-/
theorem continuous_torusCurves_pi (d : ℕ) :
    Continuous (ContinuousMap.pi : TorusCurves d → C(CurveTime, Fin d → ℂ)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply continuous_pi
  intro i
  exact continuous_eval.comp ((continuous_apply i |>.comp continuous_fst).prodMk continuous_snd)

/-- Curves entirely contained in the regular ODE domain form an open set.
@isnad1 id=isopen.0h2v.s7.4556a34ea828 from=translated src=- shape=630aaba9 vocab=96e96e4e
-/
theorem regularTorusCurves_isOpen {d : ℕ} (f : MultiLaurent d) :
    IsOpen {u : TorusCurves d | ∀ t, (fun i => u i t) ∈ laurentRegularDomain f} := by
  have hopen := ContinuousMap.isOpen_setOfPred_range_subset (X := CurveTime)
    (polynomialRegularDomain_isOpen (laurentRepresentative f))
  convert hopen.preimage (continuous_torusCurves_pi d) using 1
  ext u
  simp only [mem_preimage, mem_ofPred_eq, range_subset_iff, ContinuousMap.pi_eval]
  rfl

/-- Clamping and then evaluating the lifted field gives exactly the actual
Laurent field of the clamped coordinate curves.
@isnad1 id=eq.1h6v.s7.2a169a319355 from=translated src=- shape=71b568f2 vocab=38dc2277
-/
theorem extendCurve_vectorField {d : ℕ} (f : MultiLaurent d) (a : ℂ)
    {u : TorusCurves d} (hu : ∀ t, (fun i => u i t) ∈ laurentRegularDomain f)
    (i : Fin d) (s : ℝ) :
    extendCurve (curveVectorField (laurentRepresentative f) a u i) s =
      laurentVectorField f a (fun j => extendCurve (u j) s) i :=
  curveVectorField_apply (laurentRepresentative f) a hu i (projIcc 0 1 (by norm_num) s)

/-- There is a branch of regular curves solving the actual Laurent Picard
integral equation for all sufficiently small parameter changes. The branch is
real smooth at zero time scale, jointly in velocity and the initial point.
This does not yet identify it with the complete chosen transport curves.
@isnad1 id=ex.1h4v.s10.e477a59807dc from=translated src=- shape=87ab19b3 vocab=eb7e50fe
-/
theorem laurent_exists_smooth_picard_branch {d : ℕ} (f : MultiLaurent d)
    {a : ℂ} {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    ∃ Ψ : ℝ × (ℂ × (Fin d → ℂ)) → TorusCurves d,
      ContDiffAt ℝ ⊤ Ψ (0, (a, z)) ∧ Ψ (0, (a, z)) = constantTorusCurves d z ∧
      ∀ᶠ q in 𝓝 (0, (a, z)),
        (∀ t, (fun i => Ψ q i t) ∈ laurentRegularDomain f) ∧
        ∀ i t, Ψ q i t = q.2.2 i + q.1 •
          ∫ s in (0 : ℝ)..t.val,
            laurentVectorField f q.2.1 (fun j => extendCurve (Ψ q j) s) i := by
  let V : ℂ × TorusCurves d → TorusCurves d := fun az =>
    curveVectorField (laurentRepresentative f) az.1 az.2
  have hV : ContDiffAt ℝ ⊤ V (a, constantTorusCurves d z) :=
    laurentCurveVectorField_contDiffAt f (fun _ => hz)
  obtain ⟨Φ, hΦ, hΦ0, heq⟩ := exists_smooth_picard_branch (torusCurveIntegral d) V hV
  let j : ℝ × (ℂ × (Fin d → ℂ)) → ℝ × (ℂ × TorusCurves d) :=
    fun q => (q.1, (q.2.1, constantTorusCurves d q.2.2))
  have hj : ContDiff ℝ ⊤ j := contDiff_fst.prodMk
    (contDiff_snd.fst.prodMk ((constantTorusCurves d).contDiff.comp contDiff_snd.snd))
  have hs : ContDiffAt ℝ ⊤ (Φ ∘ j) (0, (a, z)) := hΦ.comp (0, (a, z)) (f := j) hj.contDiffAt
  have hzero : (Φ ∘ j) (0, (a, z)) = constantTorusCurves d z := hΦ0
  refine ⟨Φ ∘ j, hs, hzero, ?_⟩
  have hreg : ∀ᶠ q in 𝓝 (0, (a, z)),
      ∀ t, (fun i => (Φ ∘ j) q i t) ∈ laurentRegularDomain f :=
    hs.continuousAt.preimage_mem_nhds ((regularTorusCurves_isOpen f).mem_nhds (by
      rw [hzero]
      exact fun _ => hz))
  filter_upwards [hreg, hj.continuous.continuousAt.tendsto.eventually heq] with q hq hqe
  refine ⟨hq, fun i t => ?_⟩
  have he := congrArg (fun u : TorusCurves d => u i t) hqe
  change (Φ ∘ j) q i t = q.2.2 i + q.1 •
    ∫ s in (0 : ℝ)..t.val,
      extendCurve (curveVectorField (laurentRepresentative f) q.2.1 ((Φ ∘ j) q) i) s at he
  simpa only [extendCurve_vectorField f q.2.1 hq] using he

/-- The differentiability order `⊤` is mathlib's analytic order. Consequently
one open parameter neighborhood carries an analytic regular Picard branch,
including nearby nonzero time scales.
@isnad1 id=ex.1h4v.s10.0970b1b9b278 from=translated src=- shape=cb5ba80d vocab=5ba9d163
-/
theorem laurent_exists_analytic_picard_neighborhood {d : ℕ} (f : MultiLaurent d)
    {a : ℂ} {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    ∃ (Ψ : ℝ × (ℂ × (Fin d → ℂ)) → TorusCurves d)
      (U : Set (ℝ × (ℂ × (Fin d → ℂ)))),
      IsOpen U ∧ (0, (a, z)) ∈ U ∧ ContDiffOn ℝ ⊤ Ψ U ∧
      Ψ (0, (a, z)) = constantTorusCurves d z ∧
      ∀ q ∈ U, (∀ t, (fun i => Ψ q i t) ∈ laurentRegularDomain f) ∧
        ∀ i t, Ψ q i t = q.2.2 i + q.1 •
          ∫ s in (0 : ℝ)..t.val,
            laurentVectorField f q.2.1 (fun j => extendCurve (Ψ q j) s) i := by
  obtain ⟨Ψ, hs, hzero, heq⟩ := laurent_exists_smooth_picard_branch f (a := a) hz
  have hall := (hs.eventually (by simp)).and heq
  obtain ⟨U, hU, hopen, hbase⟩ := mem_nhds_iff.mp hall
  exact ⟨Ψ, U, hopen, hbase, fun q hq => (hU hq).1.contDiffWithinAt,
    hzero, fun q hq => (hU hq).2⟩

/-- A regular solution of the actual Picard equation gives an ODE trajectory
with the asserted derivative even at the endpoints of the unit interval.
@isnad1 id=ex.2h6v.s9.854ec4425e56 from=translated src=- shape=452cfcad vocab=d1d75efc
-/
theorem laurent_picard_equation_solves_ode {d : ℕ} (f : MultiLaurent d)
    (a : ℂ) (δ : ℝ) (z : Fin d → ℂ) (u : TorusCurves d)
    (hu : ∀ t, (fun i => u i t) ∈ laurentRegularDomain f)
    (he : ∀ i t, u i t = z i + δ • ∫ s in (0 : ℝ)..t.val,
      laurentVectorField f a (fun j => extendCurve (u j) s) i) :
    ∃ γ : ℝ → Fin d → ℂ, γ 0 = z ∧
      (∀ t : CurveTime, γ t.val = fun i => u i t) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ laurentRegularDomain f ∧
        HasDerivAt γ (δ • laurentVectorField f a (γ t)) t := by
  let w := curveVectorField (laurentRepresentative f) a u
  let γ : ℝ → Fin d → ℂ := fun t i => z i + δ • ∫ s in (0 : ℝ)..t, extendCurve (w i) s
  have hγ : ∀ t : CurveTime, γ t.val = fun i => u i t := by
    intro t
    funext i
    change z i + δ • (∫ s in (0 : ℝ)..t.val,
      extendCurve (curveVectorField (laurentRepresentative f) a u i) s) = u i t
    simpa only [extendCurve_vectorField f a hu] using (he i t).symm
  refine ⟨γ, ?_, hγ, ?_⟩
  · ext i
    simp [γ]
  · intro t ht
    have heval := hγ ⟨t, ht⟩
    refine ⟨heval ▸ hu ⟨t, ht⟩, hasDerivAt_pi.2 (fun i => ?_)⟩
    have hd := ((curvePrimitive_hasDerivAt (w i) ⟨t, ht⟩).const_smul δ).const_add (z i)
    change HasDerivAt (fun t => γ t i) (δ • w i ⟨t, ht⟩) t at hd
    simpa only [w, curveVectorField_apply (laurentRepresentative f) a hu,
      laurentVectorField, heval, Pi.smul_apply] using hd

end

end DuistermaatVanDerKallen
