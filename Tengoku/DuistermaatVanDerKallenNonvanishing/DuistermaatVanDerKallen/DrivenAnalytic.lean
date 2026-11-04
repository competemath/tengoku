import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.DrivenContinuation
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.AnalyticTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Analytic dependence on initial data for continuous scalar driving paths. -/

open Set Filter
open scoped Topology

namespace DuistermaatVanDerKallen
noncomputable section

/-- Rescaling an oriented subinterval retains the same driven equation.
@isnad1 id=and.4h7v.s9.673e5b245a54 from=translated src=- shape=081198e8 vocab=89e57a04
-/
theorem laurent_rescale_driven_segment {d : ℕ} (f : MultiLaurent d) (v : ℝ → ℂ)
    {γ : ℝ → Fin d → ℂ}
    (hγ : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ laurentRegularDomain f ∧
      HasDerivAt γ (laurentVectorField f (v r) (γ r)) r)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ r ∈ Icc (0 : ℝ) 1, γ (s + (t - s) * r) ∈ laurentRegularDomain f ∧
      HasDerivAt (fun u => γ (s + (t - s) * u))
        (laurentVectorField f ((t - s) • v (s + (t - s) * r))
          (γ (s + (t - s) * r))) r := by
  intro r hr
  have hrt : s + (t - s) * r ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hr.2),
      mul_nonneg ht.1 hr.1, mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hr.2),
      mul_nonneg (sub_nonneg.mpr ht.2) hr.1]
  refine ⟨(hγ _ hrt).1, ?_⟩
  rw [laurentVectorField_real_smul]
  simpa only [Function.comp_def, id_eq, mul_one] using
    (hγ _ hrt).2.scomp r (((hasDerivAt_id r).const_mul (t - s)).const_add s)

/-- Local endpoint maps are analytic in the initial position even when the
prescribed scalar velocity is only continuous in time.
@isnad1 id=ex.2h5v.s9.f5f665e7c49e from=translated src=- shape=7465a609 vocab=03453f49
-/
theorem laurent_driven_local_analytic_endpoint {d : ℕ} (f : MultiLaurent d)
    (v : ℝ → ℂ) (hv : Continuous v) (s : ℝ)
    {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    ∃ (F : ℝ × (ℝ × (Fin d → ℂ)) → Fin d → ℂ)
      (U : Set (ℝ × (ℝ × (Fin d → ℂ)))),
      IsOpen U ∧ (s, (0, z)) ∈ U ∧ ContinuousOn F U ∧
      (∀ t δ, ContDiffOn ℝ ⊤ (fun y => F (t, (δ, y))) {y | (t, (δ, y)) ∈ U}) ∧
      ∀ q ∈ U, ∀ γ : ℝ → Fin d → ℂ, γ 0 = q.2.2 →
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ laurentRegularDomain f ∧
          HasDerivAt γ (laurentVectorField f (q.2.1 • v (q.1 + q.2.1 * t)) (γ t)) t) →
        F q = γ 1 := by
  let τ : CurveTime := ⟨0, by simp⟩
  obtain ⟨Ψ, U, hU, hbase, hcont, hΨ, hspec⟩ :=
    laurent_driven_local_family f τ v hv s hz
  let F : ℝ × (ℝ × (Fin d → ℂ)) → Fin d → ℂ := fun q i => Ψ q i ⟨1, by simp⟩
  have hF : ∀ t δ, ContDiffOn ℝ ⊤ (fun y => F (t, (δ, y))) {y | (t, (δ, y)) ∈ U} := by
    intro t δ
    apply contDiffOn_pi.2
    intro i
    exact (ContinuousMap.evalCLM ℝ ⟨1, by simp⟩).contDiff.comp_contDiffOn
      ((contDiff_apply ℝ _ i).comp_contDiffOn (hΨ t δ))
  have hcF : ContinuousOn F U := by
    apply continuousOn_pi.mpr
    intro i
    exact (ContinuousMap.evalCLM ℝ ⟨1, by simp⟩).continuous.comp_continuousOn
      ((continuous_apply i).comp_continuousOn hcont)
  refine ⟨F, U, hU, hbase, hcF, hF, ?_⟩
  intro q hq γ hγ0 hγ
  obtain ⟨η, hη0, hηcurve, hη⟩ := laurent_driven_picard_equation_solves_ode f τ
    (rescaledVelocity v hv τ (q.1, q.2.1)) q.2.1 q.2.2 (Ψ q)
    (hspec q hq).1 (hspec q hq).2
  have hη' : ∀ t ∈ Icc (0 : ℝ) 1, η t ∈ laurentRegularDomain f ∧
      HasDerivAt η (laurentVectorField f (q.2.1 • v (q.1 + q.2.1 * t)) (η t)) t := by
    intro t ht
    have h := hη ⟨t, ht⟩
    change η t ∈ laurentRegularDomain f ∧
      HasDerivAt η (q.2.1 • laurentVectorField f (v (q.1 + q.2.1 * (t - 0))) (η t)) t at h
    simpa only [sub_zero, laurentVectorField_real_smul] using h
  have hw : Continuous (fun t => q.2.1 • v (q.1 + q.2.1 * t)) := by fun_prop
  have he := laurent_driven_unique_on_closed_interval f _ hw
    (fun t ht => (hγ t ht).2.continuousAt.continuousWithinAt)
    (fun t ht => (hη' t ht).2.continuousAt.continuousWithinAt)
    (fun t ht => (hγ t (Ico_subset_Icc_self ht)).2)
    (fun t ht => (hη' t (Ico_subset_Icc_self ht)).2)
    (fun t ht => (hγ t ht).1) (fun t ht => (hη' t ht).1)
    (hγ0.trans hη0.symm)
  exact (hηcurve ⟨1, by simp⟩).symm.trans (he (by simp)).symm

section Families
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Initial-point analyticity propagates across a driven local endpoint map.
@isnad1 id=contdiff.9h11v.s10.b14292fa8bf4 from=translated src=- shape=a2e4100a vocab=337b33b8
-/
theorem laurent_driven_family_analytic_step {d : ℕ} (f : MultiLaurent d) (v : ℝ → ℂ)
    {S : Set P} {p₀ : P} (hp₀ : p₀ ∈ S) {Γ : P → ℝ → Fin d → ℂ}
    (hΓ : ∀ p ∈ S, ∀ r ∈ Icc (0 : ℝ) 1, Γ p r ∈ laurentRegularDomain f ∧
      HasDerivAt (Γ p) (laurentVectorField f (v r) (Γ p r)) r)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    {F : ℝ × (ℝ × (Fin d → ℂ)) → Fin d → ℂ}
    {U : Set (ℝ × (ℝ × (Fin d → ℂ)))} (hU : IsOpen U)
    (hF : ∀ t δ, ContDiffOn ℝ ⊤ (fun y => F (t, (δ, y))) {y | (t, (δ, y)) ∈ U})
    (hspec : ∀ q ∈ U, ∀ γ : ℝ → Fin d → ℂ, γ 0 = q.2.2 →
      (∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ laurentRegularDomain f ∧
        HasDerivAt γ (laurentVectorField f (q.2.1 • v (q.1 + q.2.1 * r)) (γ r)) r) → F q = γ 1)
    (hq : (s, (t - s, Γ p₀ s)) ∈ U)
    (hstart : ContDiffWithinAt ℝ ⊤ (fun p => Γ p s) S p₀) :
    ContDiffWithinAt ℝ ⊤ (fun p => Γ p t) S p₀ := by
  have hslice : IsOpen {y : Fin d → ℂ | (s, (t - s, y)) ∈ U} :=
    hU.preimage (by fun_prop)
  have hcomp : ContDiffWithinAt ℝ ⊤ (fun p => F (s, (t - s, Γ p s))) S p₀ :=
    ((hF s (t - s)).contDiffAt (hslice.mem_nhds hq)).comp_contDiffWithinAt p₀
      (g := fun y => F (s, (t - s, y))) (f := fun p => Γ p s) hstart
  apply hcomp.congr_of_eventuallyEq_of_mem _ hp₀
  have hnear : ∀ᶠ p in 𝓝[S] p₀, (s, (t - s, Γ p s)) ∈ U :=
    hstart.continuousWithinAt.preimage_mem_nhdsWithin (hslice.mem_nhds hq)
  filter_upwards [hnear, self_mem_nhdsWithin] with p hp hpS
  have he := hspec (s, (t - s, Γ p s)) hp (fun r => Γ p (s + (t - s) * r)) (by simp)
    (laurent_rescale_driven_segment f v (hΓ p hpS) hs ht)
  simpa using he.symm

/-- Every existing family of regular driven trajectories inherits analytic
initial-data dependence at every fixed time. No advance continuity assumption
on the family of chosen solutions is needed.
@isnad1 id=contdiff.5h8v.s8.bca45eb97b4d from=translated src=- shape=d889b2ab vocab=9a93637c
-/
theorem laurent_driven_family_analytic {d : ℕ} (f : MultiLaurent d)
    (v : ℝ → ℂ) (hv : Continuous v)
    {S : Set P} {p₀ : P} (hp₀ : p₀ ∈ S) {Γ : P → ℝ → Fin d → ℂ}
    (hΓ : ∀ p ∈ S, ∀ r ∈ Icc (0 : ℝ) 1, Γ p r ∈ laurentRegularDomain f ∧
      HasDerivAt (Γ p) (laurentVectorField f (v r) (Γ p r)) r)
    (hinit : ContDiffWithinAt ℝ ⊤ (fun p => Γ p 0) S p₀) :
    ∀ t ∈ Icc (0 : ℝ) 1, ContDiffWithinAt ℝ ⊤ (fun p => Γ p t) S p₀ := by
  let Q : ℝ → Prop := fun t => ContDiffWithinAt ℝ ⊤ (fun p => Γ p t) S p₀
  have hcont : ContinuousOn (Γ p₀) (Icc (0 : ℝ) 1) :=
    fun t ht => (hΓ p₀ hp₀ t ht).2.continuousAt.continuousWithinAt
  have hlocal : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] t,
      (Q t → Q s) ∧ (Q s → Q t) := by
    intro t ht
    obtain ⟨F, U, hU, hbase, _, hF, hspec⟩ :=
      laurent_driven_local_analytic_endpoint f v hv t (hΓ p₀ hp₀ t ht).1
    have hfwd : ContinuousWithinAt (fun s : ℝ => (t, (s - t, Γ p₀ t)))
        (Icc (0 : ℝ) 1) t := by fun_prop
    have hbwd : ContinuousWithinAt (fun s : ℝ => (s, (t - s, Γ p₀ s)))
        (Icc (0 : ℝ) 1) t :=
      continuousWithinAt_id.prodMk
        ((continuousWithinAt_const.sub continuousWithinAt_id).prodMk (hcont t ht))
    have hfmem : ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] t, (t, (s - t, Γ p₀ t)) ∈ U :=
      hfwd.preimage_mem_nhdsWithin (by simpa using hU.mem_nhds hbase)
    have hbmem : ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] t, (s, (t - s, Γ p₀ s)) ∈ U :=
      hbwd.preimage_mem_nhdsWithin (by simpa using hU.mem_nhds hbase)
    filter_upwards [hfmem, hbmem, self_mem_nhdsWithin] with s hfs hbs hs
    exact ⟨laurent_driven_family_analytic_step f v hp₀ hΓ ht hs hU hF hspec hfs,
      laurent_driven_family_analytic_step f v hp₀ hΓ hs ht hU hF hspec hbs⟩
  intro t ht
  exact isPreconnected_Icc.induction₂' (fun s t => Q s → Q t) hlocal
    (fun _ _ _ _ _ _ hst htu => htu ∘ hst) (by simp) ht hinit

/-- The velocity needs to be continuous only on the closed time interval.
@isnad1 id=contdiff.5h8v.s8.ba47b31672d3 from=translated src=- shape=7aa27270 vocab=79ee15b0
-/
theorem laurent_driven_family_analytic_on {d : ℕ} (f : MultiLaurent d)
    (v : ℝ → ℂ) (hv : ContinuousOn v (Icc (0 : ℝ) 1))
    {S : Set P} {p₀ : P} (hp₀ : p₀ ∈ S) {Γ : P → ℝ → Fin d → ℂ}
    (hΓ : ∀ p ∈ S, ∀ r ∈ Icc (0 : ℝ) 1, Γ p r ∈ laurentRegularDomain f ∧
      HasDerivAt (Γ p) (laurentVectorField f (v r) (Γ p r)) r)
    (hinit : ContDiffWithinAt ℝ ⊤ (fun p => Γ p 0) S p₀) :
    ∀ t ∈ Icc (0 : ℝ) 1, ContDiffWithinAt ℝ ⊤ (fun p => Γ p t) S p₀ := by
  let vC : C(CurveTime, ℂ) := ⟨fun t => v t.val, continuousOn_iff_continuous_domRestrict.mp hv⟩
  apply laurent_driven_family_analytic f (extendCurve vC) (extendCurve vC).continuous hp₀ _ hinit
  intro p hp t ht
  have he : extendCurve vC t = v t := extendCurve_apply vC ⟨t, ht⟩
  simpa only [he] using hΓ p hp t ht

end Families

/-- Uniqueness on unit time uses no extension premise on the velocity.
@isnad1 id=eqon.4h5v.s8.35496c5048b3 from=translated src=- shape=c94b235f vocab=1aa058b4
-/
theorem laurent_driven_unit_unique {d : ℕ} (f : MultiLaurent d)
    (v : ℝ → ℂ) (hv : ContinuousOn v (Icc (0 : ℝ) 1))
    {γ η : ℝ → Fin d → ℂ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ laurentRegularDomain f ∧
      HasDerivAt γ (laurentVectorField f (v t) (γ t)) t)
    (hη : ∀ t ∈ Icc (0 : ℝ) 1, η t ∈ laurentRegularDomain f ∧
      HasDerivAt η (laurentVectorField f (v t) (η t)) t)
    (heq : γ 0 = η 0) : EqOn γ η (Icc (0 : ℝ) 1) := by
  let vC : C(CurveTime, ℂ) := ⟨fun t => v t.val, continuousOn_iff_continuous_domRestrict.mp hv⟩
  have he : ∀ t ∈ Icc (0 : ℝ) 1, extendCurve vC t = v t :=
    fun t ht => extendCurve_apply vC ⟨t, ht⟩
  apply laurent_driven_unique_on_closed_interval f (extendCurve vC) (extendCurve vC).continuous
    (fun t ht => (hγ t ht).2.continuousAt.continuousWithinAt)
    (fun t ht => (hη t ht).2.continuousAt.continuousWithinAt) _ _
    (fun t ht => (hγ t ht).1) (fun t ht => (hη t ht).1) heq
  · intro t ht
    simpa only [he t (Ico_subset_Icc_self ht)] using (hγ t (Ico_subset_Icc_self ht)).2
  · intro t ht
    simpa only [he t (Ico_subset_Icc_self ht)] using (hη t (Ico_subset_Icc_self ht)).2

end
end DuistermaatVanDerKallen
