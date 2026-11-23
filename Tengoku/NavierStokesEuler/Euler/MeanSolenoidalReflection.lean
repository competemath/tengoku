import Tengoku.NavierStokesEuler.Euler.MeanSolenoidalTranslation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Actual spatial reflection on ordinary R³ L².  Reflection preserves the
closed gradient and solenoidal spaces and commutes with the genuine Helmholtz
projection.  The scalar test is reflected with a minus sign so its gradient
has the same pullback as an ordinary vector field.
-/

noncomputable section

namespace EulerMeanSolenoidal

open MeasureTheory InnerProductSpace EulerSmoothLimit
open scoped ContDiff

/--
@isnad1 id=measurep.0h0v.s9.3771ec8e5b98 from=translated src=- shape=03e42864 vocab=dca83712
-/
theorem measurePreserving_reflection :
    MeasurePreserving (fun x : Space => -x) (volume : Measure Space) volume :=
  Measure.measurePreserving_neg volume

def reflection : L2 →ₗᵢ[ℝ] L2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : Space => -x) measurePreserving_reflection

/--
@isnad1 id=eventual.0h1v.s15.204b2ce908d0 from=translated src=- shape=3789228c vocab=88c67cbb
-/
theorem reflection_ae (u : L2) : reflection u =ᵐ[volume] fun x => u (-x) :=
  Lp.coeFn_compMeasurePreserving u measurePreserving_reflection

/--
@isnad1 id=eq.0h1v.s16.f457c736dd58 from=translated src=- shape=978e2a7a vocab=bf624953
-/
@[simp] theorem reflection_involutive (u : L2) : reflection (reflection u) = u := by
  apply Lp.ext
  filter_upwards [reflection_ae (reflection u),
    measurePreserving_reflection.quasiMeasurePreserving.ae (reflection_ae u)] with x hx hy
  rw [hx, hy, neg_neg]

/--
@isnad1 id=eq.0h1v.s15.48795aba3b48 from=translated src=- shape=57502ff7 vocab=20caf2a1
-/
theorem reflection_norm (u : L2) : ‖reflection u‖ = ‖u‖ := reflection.norm_map u

/--
@isnad1 id=eq.0h2v.s16.7ee945498017 from=translated src=- shape=1b017697 vocab=07253dd5
-/
theorem reflection_inner_shift (u v : L2) : ⟪reflection u, v⟫_ℝ = ⟪u, reflection v⟫_ℝ := by
  calc
    _ = ⟪reflection u, reflection (reflection v)⟫_ℝ := by rw [reflection_involutive]
    _ = _ := reflection.inner_map_map u (reflection v)

/-- The two signs in the derivative of `-f(-x)` cancel.
@isnad1 id=eq.1h3v.s10.5505a1ef8ed7 from=translated src=- shape=22e045ea vocab=ed841162
-/
theorem fderiv_neg_reflect {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) (hf : Differentiable ℝ f) (x : Space) :
    fderiv ℝ (fun y => -f (-y)) x = fderiv ℝ f (-x) := by
  have hd : HasFDerivAt f (fderiv ℝ f (-x)) ((-id) x) := (hf (-x)).hasFDerivAt
  have hh := (hd.comp x (hasFDerivAt_id (𝕜 := ℝ) x).neg).neg
  have he : -((fderiv ℝ f (-x)).comp (-(ContinuousLinearMap.id ℝ Space))) =
      fderiv ℝ f (-x) := by
    ext v
    simp
  rw [he] at hh
  exact hh.fderiv

/--
@isnad1 id=eq.1h2v.s9.622df4bf64fe from=translated src=- shape=1a607d80 vocab=50c83e1b
-/
theorem gradient_neg_reflect (φ : Space → ℝ) (hφ : Differentiable ℝ φ) (x : Space) :
    gradient (fun y => -φ (-y)) x = gradient φ (-x) := by
  simp only [gradient, fderiv_neg_reflect φ hφ]

/--
@isnad1 id=mem.1h1v.s16.41a28dbb3b99 from=translated src=- shape=ccd9b54f vocab=7a6d9278
-/
theorem reflected_generator {g : L2} (hg : g ∈ gradientGenerators) :
    reflection g ∈ gradientGenerators := by
  obtain ⟨φ, hc, hs, hg⟩ := hg
  refine ⟨fun x => -φ (-x), (hc.comp_homeomorph (Homeomorph.neg Space)).neg,
    (hs.comp contDiff_id.neg).neg, ?_⟩
  filter_upwards [reflection_ae g,
    measurePreserving_reflection.quasiMeasurePreserving.ae hg] with x hx hy
  rw [hx, hy, gradient_neg_reflect φ (hs.differentiable (by simp))]

/--
@isnad1 id=mem.1h1v.s16.ba0980722cbf from=translated src=- shape=0033fa74 vocab=529f2331
-/
theorem reflection_gradient_mem {g : L2} (hg : g ∈ gradientSpace) :
    reflection g ∈ gradientSpace := by
  let ρ := reflection.toContinuousLinearMap
  have hspan : Submodule.span ℝ gradientGenerators ≤ gradientSpace.comap ρ.toLinearMap := by
    apply Submodule.span_le.2
    intro f hf
    exact (Submodule.span ℝ gradientGenerators).le_topologicalClosure
      (Submodule.subset_span (reflected_generator hf))
  exact (Submodule.span ℝ gradientGenerators).topologicalClosure_minimal hspan
    (gradientSpace_closed.preimage ρ.continuous) hg

/--
@isnad1 id=mem.1h1v.s16.11bf1db698d0 from=translated src=- shape=0033fa74 vocab=3ce7a73c
-/
theorem reflection_solenoidal_mem {u : L2} (hu : u ∈ solenoidalSpace) :
    reflection u ∈ solenoidalSpace := by
  intro g hg
  calc
    ⟪g, reflection u⟫_ℝ = ⟪reflection (reflection g), reflection u⟫_ℝ := by
      rw [reflection_involutive]
    _ = ⟪reflection g, u⟫_ℝ := reflection.inner_map_map _ _
    _ = 0 := hu _ (reflection_gradient_mem hg)

/--
@isnad1 id=eq.0h0v.s15.4f00d98cd212 from=translated src=- shape=213f4bda vocab=b702a1e9
-/
theorem solenoidalSpace_map_reflection :
    solenoidalSpace.map reflection.toLinearMap = solenoidalSpace := by
  apply le_antisymm
  · rintro u ⟨v, hv, rfl⟩
    exact reflection_solenoidal_mem hv
  · intro u hu
    exact ⟨reflection u, reflection_solenoidal_mem hu, reflection_involutive u⟩

/-- The actual ordinary Helmholtz projection commutes with reflection.
@isnad1 id=eq.0h1v.s18.71aa3b572616 from=translated src=- shape=aad1c4ca vocab=af014aaa
-/
theorem solenoidalProjection_reflection (u : L2) :
    reflection (solenoidalProjection u) = solenoidalProjection (reflection u) := by
  have hmap := solenoidalSpace_map_reflection
  let : (solenoidalSpace.map reflection.toLinearMap).HasOrthogonalProjection := by
    rw [hmap]
    infer_instance
  simpa only [solenoidalProjection, hmap] using reflection.map_starProjection solenoidalSpace u

/--
@isnad1 id=eq.0h2v.s17.af9b9ae41ced from=translated src=- shape=9a9019ac vocab=672b3e5a
-/
theorem reflection_translation (a : Space) (u : L2) :
    reflection (translation a u) = translation (-a) (reflection u) := by
  apply Lp.ext
  filter_upwards [reflection_ae (translation a u),
    measurePreserving_reflection.quasiMeasurePreserving.ae (translation_ae a u),
    translation_ae (-a) (reflection u),
    (measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving.ae
      (reflection_ae u)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  congr 1
  abel

end EulerMeanSolenoidal
