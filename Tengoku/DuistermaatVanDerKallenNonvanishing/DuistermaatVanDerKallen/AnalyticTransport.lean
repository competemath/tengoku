import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.LaurentPicard
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.FiberTransport
import Tengoku.Seed.Topology.Connected.Clopen

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Identification of the local analytic Picard branch with actual transport,
and propagation of parameter dependence along existing complete trajectories. -/

open Set Filter
open scoped Topology

namespace DuistermaatVanDerKallen

noncomputable section

/-- Real scaling of the base velocity scales the explicit normalized lift.-/
theorem laurentVectorField_real_smul {d : ℕ} (f : MultiLaurent d)
    (r : ℝ) (a : ℂ) (z : Fin d → ℂ) :
    laurentVectorField f (r • a) z = r • laurentVectorField f a z := by
  ext i
  simp only [laurentVectorField, polynomialVectorField, scalarLift, Pi.smul_apply,
    Complex.real_smul]
  ring

/-- Any oriented subsegment of a trajectory can be rescaled to unit time.-/
theorem laurent_rescale_segment {d : ℕ} (f : MultiLaurent d) (a : ℂ)
    {γ : ℝ → Fin d → ℂ}
    (hγ : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ laurentRegularDomain f ∧
      HasDerivAt γ (laurentVectorField f a (γ r)) r)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ r ∈ Icc (0 : ℝ) 1, γ (s + (t - s) * r) ∈ laurentRegularDomain f ∧
      HasDerivAt (fun u => γ (s + (t - s) * u))
        (laurentVectorField f ((t - s) • a) (γ (s + (t - s) * r))) r := by
  intro r hr
  have hrt : s + (t - s) * r ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hr.2),
      mul_nonneg ht.1 hr.1, mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hr.2),
      mul_nonneg (sub_nonneg.mpr ht.2) hr.1]
  refine ⟨(hγ _ hrt).1, ?_⟩
  rw [laurentVectorField_real_smul]
  simpa only [Function.comp_def, id_eq, mul_one] using
    (hγ _ hrt).2.scomp r (((hasDerivAt_id r).const_mul (t - s)).const_add s)

/-- A local analytic endpoint map agrees with every regular solution of the
scaled ODE with the same initial value.-/
theorem laurent_local_analytic_endpoint {d : ℕ} (f : MultiLaurent d)
    {a : ℂ} {z : Fin d → ℂ} (hz : z ∈ laurentRegularDomain f) :
    ∃ (F : ℝ × (ℂ × (Fin d → ℂ)) → Fin d → ℂ)
      (U : Set (ℝ × (ℂ × (Fin d → ℂ)))),
      IsOpen U ∧ (0, (a, z)) ∈ U ∧ ContDiffOn ℝ ⊤ F U ∧
      ∀ q ∈ U, ∀ γ : ℝ → Fin d → ℂ, γ 0 = q.2.2 →
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ laurentRegularDomain f ∧
          HasDerivAt γ (laurentVectorField f (q.1 • q.2.1) (γ t)) t) →
        F q = γ 1 := by
  obtain ⟨Ψ, U, hU, hbase, hΨ, hzero, hspec⟩ :=
    laurent_exists_analytic_picard_neighborhood f (a := a) hz
  let F : ℝ × (ℂ × (Fin d → ℂ)) → Fin d → ℂ := fun q i => Ψ q i ⟨1, by simp⟩
  have hF : ContDiffOn ℝ ⊤ F U := by
    apply contDiffOn_pi.2
    intro i
    exact (ContinuousMap.evalCLM ℝ ⟨1, by simp⟩).contDiff.comp_contDiffOn
      ((contDiff_apply ℝ _ i).comp_contDiffOn hΨ)
  refine ⟨F, U, hU, hbase, hF, ?_⟩
  intro q hq γ hγ0 hγ
  obtain ⟨η, hη0, hηcurve, hη⟩ := laurent_picard_equation_solves_ode f q.2.1 q.1 q.2.2
    (Ψ q) (hspec q hq).1 (hspec q hq).2
  have he := laurent_segment_unique f (q.1 • q.2.1) hγ
    (fun t ht => ⟨(hη t ht).1, by simpa only [laurentVectorField_real_smul] using (hη t ht).2⟩)
    (hγ0.trans hη0.symm)
  exact (hηcurve ⟨1, by simp⟩).symm.trans (he (by simp)).symm

section Families

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Analytic dependence propagates across any subsegment represented by one
local analytic endpoint map. No regularity of the chosen solutions in their
parameters is assumed in advance.-/
theorem laurent_family_analytic_step {d : ℕ} (f : MultiLaurent d)
    {S : Set P} {p₀ : P} (hp₀ : p₀ ∈ S) {a : P → ℂ}
    {Γ : P → ℝ → Fin d → ℂ}
    (ha : ContDiffWithinAt ℝ ⊤ a S p₀)
    (hΓ : ∀ p ∈ S, ∀ r ∈ Icc (0 : ℝ) 1, Γ p r ∈ laurentRegularDomain f ∧
      HasDerivAt (Γ p) (laurentVectorField f (a p) (Γ p r)) r)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    {F : ℝ × (ℂ × (Fin d → ℂ)) → Fin d → ℂ}
    {U : Set (ℝ × (ℂ × (Fin d → ℂ)))} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ⊤ F U)
    (hspec : ∀ q ∈ U, ∀ γ : ℝ → Fin d → ℂ, γ 0 = q.2.2 →
      (∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ laurentRegularDomain f ∧
        HasDerivAt γ (laurentVectorField f (q.1 • q.2.1) (γ r)) r) → F q = γ 1)
    (hq : (t - s, (a p₀, Γ p₀ s)) ∈ U)
    (hstart : ContDiffWithinAt ℝ ⊤ (fun p => Γ p s) S p₀) :
    ContDiffWithinAt ℝ ⊤ (fun p => Γ p t) S p₀ := by
  let j : P → ℝ × (ℂ × (Fin d → ℂ)) := fun p => (t - s, (a p, Γ p s))
  have hj : ContDiffWithinAt ℝ ⊤ j S p₀ := contDiffWithinAt_const.prodMk (ha.prodMk hstart)
  have hcomp : ContDiffWithinAt ℝ ⊤ (F ∘ j) S p₀ :=
    (hF.contDiffAt (hU.mem_nhds hq)).comp_contDiffWithinAt p₀ hj
  apply hcomp.congr_of_eventuallyEq_of_mem _ hp₀
  have hnear : ∀ᶠ p in 𝓝[S] p₀, j p ∈ U :=
    hj.continuousWithinAt.preimage_mem_nhdsWithin (hU.mem_nhds hq)
  filter_upwards [hnear, self_mem_nhdsWithin] with p hp hpS
  have he := hspec (j p) hp (fun r => Γ p (s + (t - s) * r)) (by simp [j])
    (laurent_rescale_segment f (a p) (hΓ p hpS) hs ht)
  simpa [j, Function.comp_def] using he.symm

/-- Real analytic parameter dependence of every existing family of complete
regular segment solutions. This follows from local Picard analyticity and
uniqueness along the whole connected time interval, not from an assumed smooth
flow. The parameter set may be a fiber or any other subset of a normed space.-/
theorem laurent_family_analytic {d : ℕ} (f : MultiLaurent d)
    {S : Set P} {p₀ : P} (hp₀ : p₀ ∈ S) {a : P → ℂ}
    {Γ : P → ℝ → Fin d → ℂ}
    (ha : ContDiffWithinAt ℝ ⊤ a S p₀)
    (hΓ : ∀ p ∈ S, ∀ r ∈ Icc (0 : ℝ) 1, Γ p r ∈ laurentRegularDomain f ∧
      HasDerivAt (Γ p) (laurentVectorField f (a p) (Γ p r)) r)
    (hinit : ContDiffWithinAt ℝ ⊤ (fun p => Γ p 0) S p₀) :
    ∀ t ∈ Icc (0 : ℝ) 1, ContDiffWithinAt ℝ ⊤ (fun p => Γ p t) S p₀ := by
  let Q : ℝ → Prop := fun t => ContDiffWithinAt ℝ ⊤ (fun p => Γ p t) S p₀
  have hcont : ContinuousOn (Γ p₀) (Icc (0 : ℝ) 1) :=
    fun t ht => (hΓ p₀ hp₀ t ht).2.continuousAt.continuousWithinAt
  have hlocal : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] t,
      (Q t → Q s) ∧ (Q s → Q t) := by
    intro t ht
    obtain ⟨F, U, hU, hbase, hF, hspec⟩ :=
      laurent_local_analytic_endpoint f (a := a p₀) (hΓ p₀ hp₀ t ht).1
    have hfwd : ContinuousWithinAt (fun s : ℝ => (s - t, (a p₀, Γ p₀ t)))
        (Icc (0 : ℝ) 1) t := by fun_prop
    have hbwd : ContinuousWithinAt (fun s : ℝ => (t - s, (a p₀, Γ p₀ s)))
        (Icc (0 : ℝ) 1) t :=
      (continuousWithinAt_const.sub continuousWithinAt_id).prodMk
        (continuousWithinAt_const.prodMk (hcont t ht))
    have hfmem : ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] t, (s - t, (a p₀, Γ p₀ t)) ∈ U :=
      hfwd.preimage_mem_nhdsWithin (by simpa using hU.mem_nhds hbase)
    have hbmem : ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] t, (t - s, (a p₀, Γ p₀ s)) ∈ U :=
      hbwd.preimage_mem_nhdsWithin (by simpa using hU.mem_nhds hbase)
    filter_upwards [hfmem, hbmem, self_mem_nhdsWithin] with s hfs hbs hs
    exact ⟨laurent_family_analytic_step f hp₀ ha hΓ ht hs hU hF hspec hfs,
      laurent_family_analytic_step f hp₀ ha hΓ hs ht hU hF hspec hbs⟩
  intro t ht
  exact isPreconnected_Icc.induction₂' (fun s t => Q s → Q t) hlocal
    (fun _ _ _ _ _ _ hst htu => htu ∘ hst) (by simp) ht hinit

/-- Joint analytic dependence on the trajectory parameters and time, including
both endpoints, by rescaling each requested time to a unit segment.-/
theorem laurent_family_joint_analytic {d : ℕ} (f : MultiLaurent d)
    {S : Set P} {p₀ : P} (hp₀ : p₀ ∈ S) {a : P → ℂ}
    {Γ : P → ℝ → Fin d → ℂ}
    (ha : ContDiffWithinAt ℝ ⊤ a S p₀)
    (hΓ : ∀ p ∈ S, ∀ r ∈ Icc (0 : ℝ) 1, Γ p r ∈ laurentRegularDomain f ∧
      HasDerivAt (Γ p) (laurentVectorField f (a p) (Γ p r)) r)
    (hinit : ContDiffWithinAt ℝ ⊤ (fun p => Γ p 0) S p₀)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContDiffWithinAt ℝ ⊤ (fun q : P × ℝ => Γ q.1 q.2)
      (S ×ˢ Icc (0 : ℝ) 1) (p₀, t) := by
  let b : P × ℝ → ℂ := fun q => q.2 • a q.1
  let Δ : (P × ℝ) → ℝ → Fin d → ℂ := fun q r => Γ q.1 (q.2 * r)
  have hb : ContDiffWithinAt ℝ ⊤ b (S ×ˢ Icc (0 : ℝ) 1) (p₀, t) :=
    contDiffWithinAt_snd.smul (ha.comp (p₀, t) contDiffWithinAt_fst (fun _ h => h.1))
  have hΔ : ∀ q ∈ S ×ˢ Icc (0 : ℝ) 1, ∀ r ∈ Icc (0 : ℝ) 1,
      Δ q r ∈ laurentRegularDomain f ∧
        HasDerivAt (Δ q) (laurentVectorField f (b q) (Δ q r)) r := by
    intro q hq
    simpa only [Δ, b, sub_zero, zero_add] using
      laurent_rescale_segment f (a q.1) (hΓ q.1 hq.1) (by simp : (0 : ℝ) ∈ Icc 0 1) hq.2
  have hΔ0 : ContDiffWithinAt ℝ ⊤ (fun q => Δ q 0) (S ×ˢ Icc (0 : ℝ) 1) (p₀, t) := by
    simpa only [Δ, mul_zero, Function.comp_def] using
      hinit.comp (p₀, t) contDiffWithinAt_fst (fun _ h => h.1)
  simpa only [Δ, mul_one] using
    laurent_family_analytic f (S := S ×ˢ Icc (0 : ℝ) 1) (p₀ := (p₀, t))
      (a := b) (Γ := Δ) ⟨hp₀, ht⟩ hb hΔ hΔ0 1 (by simp)

end Families

end

end DuistermaatVanDerKallen
