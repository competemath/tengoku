import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.DrivenAnalytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Joint continuity for the complete time-dependent scalar transport. -/

open Set Filter
open scoped Topology

namespace DuistermaatVanDerKallen
noncomputable section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Joint continuity in the initial parameter and time for the complete driven
family, obtained from the local Picard endpoint and ODE uniqueness.-/
theorem laurent_driven_family_joint_continuous {d : ℕ} (f : MultiLaurent d)
    (v : ℝ → ℂ) (hv : Continuous v)
    {S : Set P} {p₀ : P} (hp₀ : p₀ ∈ S) {Γ : P → ℝ → Fin d → ℂ}
    (hΓ : ∀ p ∈ S, ∀ r ∈ Icc (0 : ℝ) 1, Γ p r ∈ laurentRegularDomain f ∧
      HasDerivAt (Γ p) (laurentVectorField f (v r) (Γ p r)) r)
    (hinit : ContDiffWithinAt ℝ ⊤ (fun p => Γ p 0) S p₀)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousWithinAt (fun q : P × ℝ => Γ q.1 q.2)
      (S ×ˢ Icc (0 : ℝ) 1) (p₀, t) := by
  obtain ⟨F, U, hU, hbase, hF, _, hspec⟩ :=
    laurent_driven_local_analytic_endpoint f v hv t (hΓ p₀ hp₀ t ht).1
  have hs := (laurent_driven_family_analytic f v hv hp₀ hΓ hinit t ht).continuousWithinAt
  let j : P × ℝ → ℝ × (ℝ × (Fin d → ℂ)) := fun q => (t, (q.2 - t, Γ q.1 t))
  have hj : ContinuousWithinAt j (S ×ˢ Icc (0 : ℝ) 1) (p₀, t) :=
    continuousWithinAt_const.prodMk ((continuousWithinAt_snd.sub continuousWithinAt_const).prodMk
      (hs.comp (x := (p₀, t)) (g := fun p => Γ p t) (f := Prod.fst) (s := S ×ˢ Icc (0 : ℝ) 1)
        continuousWithinAt_fst (fun _ h => h.1)))
  have hq : j (p₀, t) ∈ U := by simpa only [j, sub_self] using hbase
  have hc := (hF.continuousAt (hU.mem_nhds hq)).comp_continuousWithinAt hj
  apply hc.congr_of_eventuallyEq_of_mem _ ⟨hp₀, ht⟩
  have hnear : ∀ᶠ q in 𝓝[S ×ˢ Icc (0 : ℝ) 1] (p₀, t), j q ∈ U :=
    hj.preimage_mem_nhdsWithin (hU.mem_nhds hq)
  filter_upwards [hnear, self_mem_nhdsWithin] with q hq hqS
  have he := hspec (j q) hq (fun r => Γ q.1 (t + (q.2 - t) * r)) (by simp [j])
    (laurent_rescale_driven_segment f v (hΓ q.1 hqS.1) ht hqS.2)
  simpa [j, Function.comp_def] using he.symm

/-- Joint dependence needs velocity continuity only on the time interval.-/
theorem laurent_driven_family_joint_continuous_on {d : ℕ} (f : MultiLaurent d)
    (v : ℝ → ℂ) (hv : ContinuousOn v (Icc (0 : ℝ) 1))
    {S : Set P} {p₀ : P} (hp₀ : p₀ ∈ S) {Γ : P → ℝ → Fin d → ℂ}
    (hΓ : ∀ p ∈ S, ∀ r ∈ Icc (0 : ℝ) 1, Γ p r ∈ laurentRegularDomain f ∧
      HasDerivAt (Γ p) (laurentVectorField f (v r) (Γ p r)) r)
    (hinit : ContDiffWithinAt ℝ ⊤ (fun p => Γ p 0) S p₀)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousWithinAt (fun q : P × ℝ => Γ q.1 q.2)
      (S ×ˢ Icc (0 : ℝ) 1) (p₀, t) := by
  let vC : C(CurveTime, ℂ) := ⟨fun t => v t.val, continuousOn_iff_continuous_domRestrict.mp hv⟩
  apply laurent_driven_family_joint_continuous f (extendCurve vC) (extendCurve vC).continuous
    hp₀ _ hinit ht
  intro p hp t ht
  have he : extendCurve vC t = v t := extendCurve_apply vC ⟨t, ht⟩
  simpa only [he] using hΓ p hp t ht

end
end DuistermaatVanDerKallen
