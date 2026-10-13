/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.Rado.Surface.Harmonic
public import Tengoku.LeanPool.LeanPool.Rado.Complex.Dirichlet
import Tengoku.LeanPool.LeanPool.Rado.Complex.Poisson
public import Tengoku

/-!
# Harmonic replacement and Perron's principle

Step 4 of `Rado/PLAN.md`: `surfaceReplace` (replace a subharmonic function
inside a chart disk by the Dirichlet solution of its boundary values, Anghel–
Stan Remark 4 — Hausdorffness genuinely needed, see the counterexample at
`surfaceReplace_surfaceSubharmonicOn`), Perron families, Harnack's principle
for monotone sequences of harmonic functions, and **Perron's principle**: the
upper envelope of a Perron family is harmonic
(`IsPerronFamily.surfaceHarmonicOn_perronSup`; Anghel–Stan Theorem 6, Hubbard
Prop. 1.2.3).
-/

@[expose] public section

open Set Topology Metric MeasureTheory InnerProductSpace Complex Filter

namespace Rado

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Harmonic replacement and Perron families -/

open Classical in
/-- Replace `g` inside the closed disk `e.symm '' closedBall c r` by the
Dirichlet solution with `g`'s boundary values, read through the chart. -/
noncomputable def surfaceReplace (g : X → ℝ) (e : OpenPartialHomeomorph X ℂ)
    (c : ℂ) (r : ℝ) : X → ℝ := fun x ↦
  if _h : x ∈ e.source ∧ e x ∈ closedBall c r then
    poissonExtension (g ∘ e.symm) c r (e x)
  else g x

section Replace

variable {g : X → ℝ} {s : Set X} {e : OpenPartialHomeomorph X ℂ} {c : ℂ} {r : ℝ}

/-- Data for a legal replacement disk: a maximal-atlas chart and a closed disk
in its target whose preimage lies in `s`. -/
structure IsReplaceDisk (e : OpenPartialHomeomorph X ℂ) (c : ℂ) (r : ℝ) (s : Set X) :
    Prop where
  mem_atlas : e ∈ riemannAtlas X
  r_pos : 0 < r
  closedBall_subset : closedBall c r ⊆ e.target
  preimage_subset : e.symm '' closedBall c r ⊆ s

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem IsReplaceDisk.compact_preimage (hd : IsReplaceDisk e c r s) :
    IsCompact (e.symm '' closedBall c r) :=
  (isCompact_closedBall c r).image_of_continuousOn
    (e.symm.continuousOn.mono (by simpa using hd.closedBall_subset))

omit [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The replacement agrees with `g` off the closed replacement disk. -/
theorem surfaceReplace_eqOn_compl :
    EqOn (surfaceReplace g e c r) g (e.symm '' closedBall c r)ᶜ := by
  intro x hx
  rw [surfaceReplace, dite_eq_right]
  rintro ⟨hxs, hxb⟩
  exact hx ⟨e x, hxb, e.left_inv hxs⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem IsReplaceDisk.closedBall_subset_chartImage (hd : IsReplaceDisk e c r s) :
    closedBall c r ⊆ chartImage e s := fun w hw ↦
  ⟨e.symm w, ⟨hd.preimage_subset ⟨w, hw, rfl⟩, e.map_target (hd.closedBall_subset hw)⟩,
    e.right_inv (hd.closedBall_subset hw)⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem IsReplaceDisk.isOpen_ball_image (hd : IsReplaceDisk e c r s) :
    IsOpen (e.symm '' ball c r) :=
  e.symm.isOpen_image_of_subset_source isOpen_ball
    (by simpa using ball_subset_closedBall.trans hd.closedBall_subset)

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
private theorem IsReplaceDisk.continuousOn_sphere (hd : IsReplaceDisk e c r s)
    (hg : SurfaceSubharmonicOn g s) : ContinuousOn (g ∘ e.symm) (sphere c r) :=
  (continuousOn_comp_chart_symm e hg.continuousOn).mono
    (sphere_subset_closedBall.trans hd.closedBall_subset_chartImage)

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- `g` is dominated by its replacement (comparison principle); helper form. -/
private theorem le_surfaceReplace_aux (hg : SurfaceSubharmonicOn g s)
    (hd : IsReplaceDisk e c r s) : ∀ x ∈ s, g x ≤ surfaceReplace g e c r x := by
  intro x hx
  by_cases hxD : x ∈ e.symm '' closedBall c r
  · obtain ⟨w, hwb, rfl⟩ := hxD
    have hwt : w ∈ e.target := hd.closedBall_subset hwb
    have hxsrc : e.symm w ∈ e.source := e.map_target hwt
    have hew : e (e.symm w) = w := e.right_inv hwt
    have hle := (hg.subMeanOn e hd.mem_atlas).le_poissonExtension_on
      hd.r_pos hd.closedBall_subset_chartImage w hwb
    rw [surfaceReplace, dite_eq_left ⟨hxsrc, by rw [hew]; exact hwb⟩, hew]
    exact hle
  · exact (surfaceReplace_eqOn_compl hxD).ge

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The replacement is harmonic inside the disk; helper form. -/
private theorem surfaceReplace_surfaceHarmonicOn_aux (hg : SurfaceSubharmonicOn g s)
    (hd : IsReplaceDisk e c r s) :
    SurfaceHarmonicOn (surfaceReplace g e c r) (e.symm '' ball c r) := by
  have hbt : ball c r ⊆ e.target := ball_subset_closedBall.trans hd.closedBall_subset
  have hgs : ContinuousOn (g ∘ e.symm) (sphere c r) := hd.continuousOn_sphere hg
  refine SurfaceHarmonicOn.of_chartwise ?_
  rintro x ⟨w, hwb, rfl⟩
  have hwt : w ∈ e.target := hbt hwb
  have hxsrc : e.symm w ∈ e.source := e.map_target hwt
  have hew : e (e.symm w) = w := e.right_inv hwt
  refine ⟨e, hd.mem_atlas, hxsrc, ?_⟩
  rw [hew]
  have hharm := poissonExtension_harmonicOnNhd hd.r_pos hgs w hwb
  refine (harmonicAt_congr_nhds ?_).mpr hharm
  filter_upwards [isOpen_ball.mem_nhds hwb] with w' hw'
  have hwt' : w' ∈ e.target := hbt hw'
  simp only [Function.comp_apply]
  rw [surfaceReplace, dite_eq_left ⟨e.map_target hwt',
    by rw [e.right_inv hwt']; exact ball_subset_closedBall hw'⟩, e.right_inv hwt']

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The replacement is subharmonic (Anghel–Stan Remark 4): with `[T2Space X]`
the compact replacement disk is closed, and the replacement is subharmonic on
`s` — harmonic inside the disk, equal to `g` outside, and the sub-mean
inequality glues across the circle because `g ≤ surfaceReplace g` there.

The Hausdorff hypothesis is genuinely needed: on the plane with doubled
origin, with `g = ‖chart value‖²`, the replacement on the copy-1 unit disk is
`≡ 1` on the shared punctured disk but `0` at the doubled origin, which lies
in the closure of the replacement disk but outside `e.source` — so the
replacement fails to be continuous, let alone subharmonic. -/
theorem surfaceReplace_surfaceSubharmonicOn [T2Space X] (hs : IsOpen s)
    (hg : SurfaceSubharmonicOn g s) (hd : IsReplaceDisk e c r s) :
    SurfaceSubharmonicOn (surfaceReplace g e c r) s := by
  classical
  have hgs : ContinuousOn (g ∘ e.symm) (sphere c r) := hd.continuousOn_sphere hg
  have hrepg : ContinuousOn (g ∘ e.symm) (chartImage e s) :=
    continuousOn_comp_chart_symm e hg.continuousOn
  -- the chart-side glued function is continuous on `chartImage e s`
  have hh : ContinuousOn (fun w ↦ if w ∈ closedBall c r
      then poissonExtension (g ∘ e.symm) c r w else (g ∘ e.symm) w) (chartImage e s) := by
    refine ContinuousOn.if ?_ ?_ ?_
    · intro a ha
      have h2 := ha.2
      simp only [Set.ofPred_mem_eq] at h2
      rw [frontier_closedBall c hd.r_pos.ne'] at h2
      exact poissonExtension_eqOn_sphere hd.r_pos hgs h2
    · refine (poissonExtension_continuousOn hd.r_pos hgs).mono ?_
      refine inter_subset_right.trans ?_
      simp only [Set.ofPred_mem_eq]
      rw [isClosed_closedBall.closure_eq]
    · exact hrepg.mono inter_subset_left
  -- continuity of the replacement on `s`
  have hcont : ContinuousOn (surfaceReplace g e c r) s := by
    intro x hx
    by_cases hxsrc : x ∈ e.source
    · have hex : e x ∈ chartImage e s := mem_chartImage_of_mem hx hxsrc
      have h1 : ContinuousAt (fun w ↦ if w ∈ closedBall c r
          then poissonExtension (g ∘ e.symm) c r w else (g ∘ e.symm) w) (e x) :=
        hh.continuousAt ((isOpen_chartImage e hs).mem_nhds hex)
      have h2 : ContinuousAt ((fun w ↦ if w ∈ closedBall c r
          then poissonExtension (g ∘ e.symm) c r w else (g ∘ e.symm) w) ∘ e) x :=
        h1.comp (e.continuousAt hxsrc)
      refine (h2.congr ?_).continuousWithinAt
      filter_upwards [e.open_source.mem_nhds hxsrc] with y hy
      by_cases hyb : e y ∈ closedBall c r
      · simp only [Function.comp_apply, ite_eq_left hyb]
        rw [surfaceReplace, dite_eq_left ⟨hy, hyb⟩]
      · simp only [Function.comp_apply, ite_eq_right hyb]
        rw [surfaceReplace, dite_eq_right fun hcon ↦ hyb hcon.2]
        simp only [e.left_inv hy]
    · -- off the chart source: the disk is closed (T2), so the replacement
      -- agrees with `g` on a neighbourhood
      have hxD : x ∉ e.symm '' closedBall c r := by
        rintro ⟨w, hw, rfl⟩
        exact hxsrc (e.map_target (hd.closedBall_subset hw))
      have hDc : IsClosed (e.symm '' closedBall c r) := hd.compact_preimage.isClosed
      have hev : surfaceReplace g e c r =ᶠ[𝓝 x] g := by
        filter_upwards [hDc.isOpen_compl.mem_nhds hxD] with y hy
        exact surfaceReplace_eqOn_compl hy
      exact (hg.continuousOn x hx).congr_of_eventuallyEq
        (hev.filter_mono nhdsWithin_le_nhds) hev.self_of_nhds
  -- the sub-mean inequality in every chart, on small circles
  refine ⟨hcont, fun e' he' ↦ ?_⟩
  refine SubMeanLocalOn.subMeanOn ?_
  refine ⟨continuousOn_comp_chart_symm e' hcont, ?_⟩
  rintro w ⟨x, ⟨hxs, hxe⟩, rfl⟩
  by_cases hxB : x ∈ e.symm '' ball c r
  · -- interior of the disk: harmonic, hence the mean-value equality
    have hharm : HarmonicOnNhd (surfaceReplace g e c r ∘ e'.symm)
        (chartImage e' (e.symm '' ball c r)) :=
      surfaceReplace_surfaceHarmonicOn_aux hg hd e' he'
    have hMeq : MeanEqOn (surfaceReplace g e c r ∘ e'.symm)
        (chartImage e' (e.symm '' ball c r)) :=
      HarmonicOnNhd.meanEqOn hharm
    have hmem : e' x ∈ chartImage e' (e.symm '' ball c r) := mem_chartImage_of_mem hxB hxe
    obtain ⟨ρ, hρ, hball⟩ :=
      Metric.isOpen_iff.mp (isOpen_chartImage e' hd.isOpen_ball_image) _ hmem
    filter_upwards [Ioo_mem_nhdsGT hρ] with r' hr'
    exact (hMeq.mean_eq (e' x) r' hr'.1 ((closedBall_subset_ball hr'.2).trans hball)).ge
  · -- on the circle or outside: the replacement equals `g` at the point and
    -- dominates `g` on the circles
    have hux : surfaceReplace g e c r x = g x := by
      by_cases hxD : x ∈ e.symm '' closedBall c r
      · obtain ⟨w', hw', rfl⟩ := hxD
        have hwt : w' ∈ e.target := hd.closedBall_subset hw'
        have hxsrc : e.symm w' ∈ e.source := e.map_target hwt
        have hew : e (e.symm w') = w' := e.right_inv hwt
        have hsph : w' ∈ sphere c r := by
          rw [mem_sphere]
          rcases lt_or_eq_of_le (mem_closedBall.mp hw') with hlt | heq'
          · exact absurd ⟨w', mem_ball.mpr hlt, rfl⟩ hxB
          · exact heq'
        rw [surfaceReplace, dite_eq_left ⟨hxsrc, by rw [hew]; exact hw'⟩, hew,
          poissonExtension_eqOn_sphere hd.r_pos hgs hsph]
        simp
      · exact surfaceReplace_eqOn_compl hxD
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp (isOpen_chartImage e' hs) _
      (mem_chartImage_of_mem hxs hxe)
    filter_upwards [Ioo_mem_nhdsGT hρ] with r' hr'
    have hcb : closedBall (e' x) r' ⊆ chartImage e' s :=
      (closedBall_subset_ball hr'.2).trans hball
    have hsph_sub : sphere (e' x) r' ⊆ chartImage e' s := sphere_subset_closedBall.trans hcb
    have hig : CircleIntegrable (g ∘ e'.symm) (e' x) r' :=
      ((hg.subMeanOn e' he').continuousOn.mono hsph_sub).circleIntegrable hr'.1.le
    have hiu : CircleIntegrable (surfaceReplace g e c r ∘ e'.symm) (e' x) r' :=
      ((continuousOn_comp_chart_symm e' hcont).mono hsph_sub).circleIntegrable hr'.1.le
    have hle1 : (g ∘ e'.symm) (e' x) ≤ Real.circleAverage (g ∘ e'.symm) (e' x) r' :=
      (hg.subMeanOn e' he').submean (e' x) r' hr'.1 hcb
    have hle2 : Real.circleAverage (g ∘ e'.symm) (e' x) r'
        ≤ Real.circleAverage (surfaceReplace g e c r ∘ e'.symm) (e' x) r' := by
      refine Real.circleAverage_mono hig hiu ?_
      intro z hz
      rw [abs_of_pos hr'.1] at hz
      obtain ⟨y, ⟨hys, hye⟩, rfl⟩ := hsph_sub hz
      simp only [Function.comp_apply]
      rw [e'.left_inv hye]
      exact le_surfaceReplace_aux hg hd y hys
    have hval : (surfaceReplace g e c r ∘ e'.symm) (e' x) = (g ∘ e'.symm) (e' x) := by
      simp only [Function.comp_apply, e'.left_inv hxe, hux]
    rw [hval]
    exact hle1.trans hle2

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- The replacement stays in `[0,1]` if `g` does (on `s`). -/
theorem surfaceReplace_mem_Icc (hg : SurfaceSubharmonicOn g s)
    (hd : IsReplaceDisk e c r s) (hb : ∀ x ∈ s, g x ∈ Icc (0 : ℝ) 1) :
    ∀ x ∈ s, surfaceReplace g e c r x ∈ Icc (0 : ℝ) 1 := by
  intro x hx
  by_cases hxD : x ∈ e.symm '' closedBall c r
  · obtain ⟨w, hwb, rfl⟩ := hxD
    have hwt : w ∈ e.target := hd.closedBall_subset hwb
    have hxsrc : e.symm w ∈ e.source := e.map_target hwt
    have hew : e (e.symm w) = w := e.right_inv hwt
    have hbd : ∀ z ∈ sphere c r, (g ∘ e.symm) z ∈ Icc (0:ℝ) 1 := fun z hz ↦
      hb _ (hd.preimage_subset ⟨z, sphere_subset_closedBall hz, rfl⟩)
    have hval := poissonExtension_mem_Icc hd.r_pos (hd.continuousOn_sphere hg) hbd w hwb
    rw [surfaceReplace, dite_eq_left ⟨hxsrc, by rw [hew]; exact hwb⟩, hew]
    exact hval
  · rw [surfaceReplace_eqOn_compl hxD]
    exact hb x hx

end Replace

/-- A Perron family on `s`: a nonempty set of `[0,1]`-valued subharmonic
functions, closed under pairwise `max` and under harmonic replacement on disks
inside `s` (Anghel–Stan Definition 5, with the `[0,1]` normalization that
suffices for Radó). -/
structure IsPerronFamily (𝓕 : Set (X → ℝ)) (s : Set X) : Prop where
  nonempty : 𝓕.Nonempty
  subharmonic : ∀ g ∈ 𝓕, SurfaceSubharmonicOn g s
  bounds : ∀ g ∈ 𝓕, ∀ x ∈ s, g x ∈ Icc (0 : ℝ) 1
  max_mem : ∀ g₁ ∈ 𝓕, ∀ g₂ ∈ 𝓕, (fun x ↦ Max.max (g₁ x) (g₂ x)) ∈ 𝓕
  replace_mem : ∀ g ∈ 𝓕, ∀ e c r, IsReplaceDisk e c r s → surfaceReplace g e c r ∈ 𝓕

/-- The upper envelope of a family of functions. -/
noncomputable def perronSup (𝓕 : Set (X → ℝ)) : X → ℝ := fun x ↦
  sSup ((fun g ↦ g x) '' 𝓕)

/-! ### Harnack's principle for monotone sequences of harmonic functions -/

/-! ### The Perron approximation sequence -/

/-- Pointwise maximum of the first `j + 1` members of a sequence of
functions. -/
private def maxUpTo (f : ℕ → X → ℝ) : ℕ → X → ℝ
  | 0 => f 0
  | j + 1 => fun y ↦ Max.max (maxUpTo f j y) (f (j + 1) y)

/-- The recursive Perron approximation sequence: harmonic replacements of the
running maxima of a given sequence of family members. -/
private noncomputable def perronSeq (e : OpenPartialHomeomorph X ℂ) (c : ℂ) (r : ℝ)
    (b : ℕ → X → ℝ) : ℕ → X → ℝ
  | 0 => surfaceReplace (b 0) e c r
  | n + 1 => surfaceReplace
      (fun y ↦ Max.max (perronSeq e c r b n y) (b (n + 1) y)) e c r

section PerronSeq

variable {𝓕 : Set (X → ℝ)} {s : Set X} {e : OpenPartialHomeomorph X ℂ} {c : ℂ} {r : ℝ}
  {b : ℕ → X → ℝ}

end PerronSeq

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem IsPerronFamily.le_perronSup {𝓕 : Set (X → ℝ)} {s : Set X}
    (h𝓕 : IsPerronFamily 𝓕 s) {g : X → ℝ} (hg : g ∈ 𝓕) :
    ∀ x ∈ s, g x ≤ perronSup 𝓕 x := fun x hx ↦
  le_csSup ⟨1, fun _ ⟨g', hg', hgx⟩ ↦ hgx ▸ (h𝓕.bounds g' hg' x hx).2⟩ ⟨g, hg, rfl⟩

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
theorem IsPerronFamily.perronSup_le {𝓕 : Set (X → ℝ)} {s : Set X}
    (h𝓕 : IsPerronFamily 𝓕 s) {M : ℝ} {x : X}
    (hM : ∀ g ∈ 𝓕, g x ≤ M) : perronSup 𝓕 x ≤ M :=
  csSup_le (h𝓕.nonempty.image _) fun _ ⟨g, hg, hgx⟩ ↦ hgx ▸ hM g hg

/-- `SubMeanOn` transfers along equality on the domain. -/
theorem subMeanOn_congr {g₁ g₂ : ℂ → ℝ} {s : Set ℂ} (hg : SubMeanOn g₁ s)
    (h : EqOn g₂ g₁ s) : SubMeanOn g₂ s := by
  refine ⟨hg.continuousOn.congr h, fun c r hr hsub ↦ ?_⟩
  have havg : Real.circleAverage g₂ c r = Real.circleAverage g₁ c r := by
    refine Real.circleAverage_congr_sphere fun z hz ↦ ?_
    rw [abs_of_pos hr] at hz
    exact h (hsub (sphere_subset_closedBall hz))
  rw [h (hsub (mem_closedBall_self hr.le)), havg]
  exact hg.submean c r hr hsub

omit [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] in
/-- `SurfaceSubharmonicOn` transfers along equality on the domain. -/
theorem surfaceSubharmonicOn_congr {g₁ g₂ : X → ℝ} {s : Set X}
    (hg : SurfaceSubharmonicOn g₁ s) (h : EqOn g₂ g₁ s) : SurfaceSubharmonicOn g₂ s := by
  refine ⟨hg.continuousOn.congr h, fun e' he' ↦ ?_⟩
  refine subMeanOn_congr (hg.subMeanOn e' he') ?_
  rintro w ⟨x, ⟨hxs, hxe⟩, rfl⟩
  simp only [Function.comp_apply]
  rw [e'.left_inv hxe]
  exact h hxs

end Rado
