import Tengoku
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SardPrelim
import Tengoku.LeanEvalPiSuccSphereNMulequivZmodTwo.Submission.SardTaylor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sard's theorem, Steps 1 and 2 of Milnor's induction

* `Submission.step2_local` — near a point of `C_i \ C_{i+1}` (`i ≥ 1`), the
  image `f (C_i ∩ V)` is null, assuming the inductive hypothesis in dimension
  `n` (with the same target dimension).  The set `C_i` locally lies on a smooth
  graph over `ℝ^n`, and all its points are critical for the restriction of `f`
  to that graph.

* `Submission.step1_local` — near a critical point where `df ≠ 0`, the image
  `f (C ∩ V)` is null, assuming the inductive hypothesis in dimension `n` with
  target dimension one less.  Here `f` is locally conjugated (by a chart given
  by the inverse function theorem) to a map `(t, z) ↦ (t, ĝ(t, z))`, and
  Fubini reduces the claim to the slice maps `ĝ(t, ·)`.
-/

namespace Submission

noncomputable section

open Function MeasureTheory Metric Set Filter
open scoped ContDiff Topology

variable {n q : ℕ}

/-! ## Smoothness of iterated derivatives on an open set -/

/--
@isnad1 id=contdiff.2h5v.s11.31806e738680 from=translated src=- shape=e92f5f4a vocab=1fdc4f4b
-/
theorem contDiffOn_iteratedFDeriv_of_isOpen {U : Set (Fin (n + 1) → ℝ)}
    (hU : IsOpen U) {f : (Fin (n + 1) → ℝ) → Fin (q + 1) → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (i : ℕ) :
    ContDiffOn ℝ ∞ (iteratedFDeriv ℝ i f) U := by
  intro x hx
  have h1 : ContDiffAt ℝ ∞ f x := hf.contDiffAt (hU.mem_nhds hx)
  have h2 : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ i f) x :=
    h1.iteratedFDeriv_right (by exact_mod_cast le_top)
  exact h2.contDiffWithinAt

/-! ## Step 2 -/

/-- **Milnor's Step 2, local version.**  Let `x₀ ∈ C_i \ C_{i+1}` with `i ≥ 1`.
Assuming Sard's theorem in dimension `n` (same target), some neighbourhood `V`
of `x₀` satisfies `volume (f '' (C_i ∩ V)) = 0`.
@isnad1 id=ex.6h6v.s10.d369527ff7a8 from=translated src=- shape=49af0e28 vocab=0d0ba891
-/
theorem step2_local {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U)
    {f : (Fin (n + 1) → ℝ) → Fin (q + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    {i : ℕ} (hi : 1 ≤ i)
    (IH : ∀ (U' : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Fin (q + 1) → ℝ),
      IsOpen U' → ContDiffOn ℝ ∞ g U' → volume (g '' critSet U' g) = 0)
    {x₀ : Fin (n + 1) → ℝ} (hx₀ : x₀ ∈ vanishSet U f i)
    (hx₀' : x₀ ∉ vanishSet U f (i + 1)) :
    ∃ V ∈ 𝓝 x₀, volume (f '' (vanishSet U f i ∩ V)) = 0 := by
  classical
  have hx₀U : x₀ ∈ U := hx₀.1
  -- some `(i+1)`-st derivative does not vanish at `x₀`
  have hne : iteratedFDeriv ℝ (i + 1) f x₀ ≠ 0 := by
    intro hzero
    apply hx₀'
    refine ⟨hx₀U, fun j h1 h2 => ?_⟩
    rcases eq_or_lt_of_le h2 with rfl | hlt
    · exact hzero
    · exact hx₀.2 j h1 (by omega)
  have hm : ∃ m : Fin (i + 1) → (Fin (n + 1) → ℝ),
      iteratedFDeriv ℝ (i + 1) f x₀ m ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hne (ContinuousMultilinearMap.ext hall)
  obtain ⟨m, hm⟩ := hm
  obtain ⟨r₀, hr₀⟩ : ∃ r₀, iteratedFDeriv ℝ (i + 1) f x₀ m r₀ ≠ 0 :=
    Function.ne_iff.1 hm
  -- the scalar function `w` vanishing on `C_i` with `dw(x₀) ≠ 0`
  set Λ : ((Fin (n + 1) → ℝ) [×i]→L[ℝ] (Fin (q + 1) → ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj r₀).comp
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => Fin (n + 1) → ℝ)
        (Fin (q + 1) → ℝ) (Fin.tail m)) with hΛdef
  set w : (Fin (n + 1) → ℝ) → ℝ := fun y => Λ (iteratedFDeriv ℝ i f y)
    with hwdef
  have hAsm : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ i f) U :=
    contDiffOn_iteratedFDeriv_of_isOpen hU hf i
  have hwsm : ContDiffOn ℝ ∞ w U := Λ.contDiff.comp_contDiffOn hAsm
  have hwvanish : ∀ y ∈ vanishSet U f i, w y = 0 := by
    intro y hy
    rw [hwdef]
    simp only [hy.2 i hi le_rfl, map_zero]
  -- `dw(x₀) ≠ 0`
  have hAdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ i f) x₀ :=
    (hAsm.contDiffAt (hU.mem_nhds hx₀U)).differentiableAt infty_ne_zero
  have hwderiv : HasFDerivAt w
      (Λ.comp (fderiv ℝ (iteratedFDeriv ℝ i f) x₀)) x₀ :=
    Λ.hasFDerivAt.comp x₀ hAdiff.hasFDerivAt
  have hdm0 : (Λ.comp (fderiv ℝ (iteratedFDeriv ℝ i f) x₀)) (m 0) ≠ 0 := by
    have h1 : (Λ.comp (fderiv ℝ (iteratedFDeriv ℝ i f) x₀)) (m 0)
        = iteratedFDeriv ℝ (i + 1) f x₀ m r₀ := by
      rw [ContinuousLinearMap.comp_apply, hΛdef,
        ContinuousLinearMap.comp_apply]
      congr 1
    rw [h1]
    exact hr₀
  obtain ⟨s, hs⟩ := exists_apply_single_ne_zero hdm0
  have hd : fderiv ℝ w x₀ (Pi.single s 1) ≠ 0 := by
    rw [hwderiv.fderiv]
    exact hs
  -- the chart
  obtain ⟨V, W, h', hVopen, hWopen, hx₀V, hVU, h'sm, hmapsVW, hleft, hmapsWV,
    hright⟩ := exists_chart hU hwsm hx₀U hd
  refine ⟨V, hVopen.mem_nhds hx₀V, ?_⟩
  -- the graph map and the restricted function
  set φ : (Fin n → ℝ) → Fin (n + 1) → ℝ := fun z => Fin.insertNth s 0 z
    with hφdef
  have hφsm : ContDiff ℝ ∞ φ := by
    have h1 : φ = fun z => (splitCLE n s).symm ((0 : ℝ), z) := by
      funext z
      rw [hφdef, splitCLE_symm_apply]
    rw [h1]
    exact (splitCLE n s).symm.contDiff.comp (contDiff_const.prodMk contDiff_id)
  set Ω₀ : Set (Fin n → ℝ) := φ ⁻¹' W with hΩ₀def
  have hΩ₀open : IsOpen Ω₀ := hWopen.preimage hφsm.continuous
  set g : (Fin n → ℝ) → Fin (q + 1) → ℝ := fun z => f (h' (φ z)) with hgdef
  have hgsm : ContDiffOn ℝ ∞ g Ω₀ := by
    have h1 : ContDiffOn ℝ ∞ (f ∘ h') W :=
      hf.comp h'sm fun w hw => hmapsWV w hw |> hVU
    have h2 : ContDiffOn ℝ ∞ ((f ∘ h') ∘ φ) Ω₀ :=
      h1.comp (hφsm.contDiffOn) fun z hz => hz
    exact h2
  -- the inclusion of images
  have hincl : f '' (vanishSet U f i ∩ V) ⊆ g '' critSet Ω₀ g := by
    rintro _ ⟨y, ⟨hyK, hyV⟩, rfl⟩
    have hyU : y ∈ U := hVU hyV
    have hwy : w y = 0 := hwvanish y hyK
    have hhy : Function.update y s (w y) ∈ W := hmapsVW y hyV
    rw [hwy] at hhy
    set z : Fin n → ℝ := Fin.removeNth s (Function.update y s (0 : ℝ))
      with hzdef
    have hφz : φ z = Function.update y s (0 : ℝ) := by
      rw [hφdef]
      have h1 : (Function.update y s (0 : ℝ)) s = 0 := Function.update_self ..
      calc Fin.insertNth s 0 z
          = Fin.insertNth s ((Function.update y s (0 : ℝ)) s)
            (Fin.removeNth s (Function.update y s (0 : ℝ))) := by rw [h1]
        _ = Function.update y s (0 : ℝ) := Fin.insertNth_self_removeNth ..
    have hzΩ : z ∈ Ω₀ := by
      rw [hΩ₀def, mem_preimage, hφz]
      exact hhy
    have hh'φz : h' (φ z) = y := by
      rw [hφz, ← hwy]
      exact hleft y hyV
    have hgz : g z = f y := by rw [hgdef]; simp only [hh'φz]
    refine ⟨z, ⟨hzΩ, ?_⟩, hgz⟩
    -- `z` is critical for `g`: the derivative of `g` at `z` vanishes
    have hfy0 : fderiv ℝ f y = 0 := fderiv_eq_zero_of_mem_vanishSet hi hyK
    have hfydiff : HasFDerivAt f (0 : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (q + 1) → ℝ)) y := by
      have h1 : DifferentiableAt ℝ f y :=
        (hf.contDiffAt (hU.mem_nhds hyU)).differentiableAt infty_ne_zero
      have h2 := h1.hasFDerivAt
      rwa [hfy0] at h2
    have hh'diff : DifferentiableAt ℝ h' (φ z) := by
      have := (h'sm.contDiffAt (hWopen.mem_nhds hzΩ)).differentiableAt
        infty_ne_zero
      exact this
    have hφdiff : DifferentiableAt ℝ φ z :=
      hφsm.differentiable infty_ne_zero |>.differentiableAt
    have hcomp1 : HasFDerivAt (f ∘ h')
        ((0 : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (q + 1) → ℝ)).comp
          (fderiv ℝ h' (φ z))) (φ z) := by
      rw [← hh'φz] at hfydiff
      exact hfydiff.comp _ hh'diff.hasFDerivAt
    have hcomp2 : HasFDerivAt ((f ∘ h') ∘ φ)
        (((0 : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (q + 1) → ℝ)).comp
          (fderiv ℝ h' (φ z))).comp (fderiv ℝ φ z)) z :=
      hcomp1.comp z hφdiff.hasFDerivAt
    have hzero : (((0 : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (q + 1) → ℝ)).comp
        (fderiv ℝ h' (φ z))).comp (fderiv ℝ φ z)) = 0 := by
      rw [ContinuousLinearMap.zero_comp, ContinuousLinearMap.zero_comp]
    rw [hzero] at hcomp2
    have hgderiv : fderiv ℝ g z = 0 := hcomp2.fderiv
    rw [hgderiv]
    exact not_surjective_zero
  exact measure_mono_null hincl (IH Ω₀ g hΩ₀open hgsm)

/-! ## Step 1 -/

/-- **Milnor's Step 1, local version.**  Let `x₀` be a point of `U` where
`df(x₀) ≠ 0`.  Assuming Sard's theorem in dimension `n` with target dimension
`q`, some neighbourhood `V` of `x₀` satisfies
`volume (f '' (critSet U f ∩ V)) = 0`.
@isnad1 id=ex.5h5v.s11.3c21a97214cb from=translated src=- shape=40a817b7 vocab=cad09af1
-/
theorem step1_local {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U)
    {f : (Fin (n + 1) → ℝ) → Fin (q + 1) → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (IH : ∀ (U' : Set (Fin n → ℝ)) (g : (Fin n → ℝ) → Fin q → ℝ),
      IsOpen U' → ContDiffOn ℝ ∞ g U' → volume (g '' critSet U' g) = 0)
    {x₀ : Fin (n + 1) → ℝ} (hx₀U : x₀ ∈ U) (hfd0 : fderiv ℝ f x₀ ≠ 0) :
    ∃ V ∈ 𝓝 x₀, volume (f '' (critSet U f ∩ V)) = 0 := by
  classical
  -- choose target coordinate `r` and domain coordinate `s`
  have hv : ∃ v, fderiv ℝ f x₀ v ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hfd0 (ContinuousLinearMap.ext hall)
  obtain ⟨v, hv⟩ := hv
  obtain ⟨r, hr⟩ : ∃ r, fderiv ℝ f x₀ v r ≠ 0 := Function.ne_iff.1 hv
  set σ : (Fin (n + 1) → ℝ) → ℝ := fun y => f y r with hσdef
  have hσsm : ContDiffOn ℝ ∞ σ U :=
    (ContinuousLinearMap.proj r :
      (Fin (q + 1) → ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn hf
  have hfdiffx₀ : DifferentiableAt ℝ f x₀ :=
    (hf.contDiffAt (hU.mem_nhds hx₀U)).differentiableAt infty_ne_zero
  have hσderiv : HasFDerivAt σ
      ((ContinuousLinearMap.proj r :
        (Fin (q + 1) → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ f x₀)) x₀ :=
    (ContinuousLinearMap.proj r :
      (Fin (q + 1) → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp x₀ hfdiffx₀.hasFDerivAt
  have hξv : ((ContinuousLinearMap.proj r :
      (Fin (q + 1) → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ f x₀)) v ≠ 0 := by
    simpa using hr
  obtain ⟨s, hs⟩ := exists_apply_single_ne_zero hξv
  have hd : fderiv ℝ σ x₀ (Pi.single s 1) ≠ 0 := by
    rw [hσderiv.fderiv]
    exact hs
  -- the chart
  obtain ⟨V, W, h', hVopen, hWopen, hx₀V, hVU, h'sm, hmapsVW, hleft, hmapsWV,
    hright⟩ := exists_chart hU hσsm hx₀U hd
  -- the conjugated map `g` on `W`
  set g : (Fin (n + 1) → ℝ) → Fin (q + 1) → ℝ := fun w => f (h' w) with hgdef
  have hgsm : ContDiffOn ℝ ∞ g W :=
    hf.comp h'sm fun w hw => hVU (hmapsWV w hw)
  -- key identity: the `r`-th component of `g w` is the `s`-th coordinate of `w`
  have hkey : ∀ w ∈ W, g w r = w s := by
    intro w hw
    have h1 := congrFun (hright w hw) s
    rw [Function.update_self] at h1
    exact h1
  -- a compact ball around `x₀` inside `V`
  obtain ⟨ρ, hρ, hballV⟩ : ∃ ρ > 0, closedBall x₀ ρ ⊆ V :=
    Metric.nhds_basis_closedBall.mem_iff.1 (hVopen.mem_nhds hx₀V)
  refine ⟨closedBall x₀ ρ, Metric.closedBall_mem_nhds x₀ hρ, ?_⟩
  set K₀ : Set (Fin (n + 1) → ℝ) := critSet U f ∩ closedBall x₀ ρ with hK₀def
  have hK₀U : K₀ ⊆ U := fun y hy => hVU (hballV hy.2)
  have hK₀V : K₀ ⊆ V := fun y hy => hballV hy.2
  have hK₀cpt : IsCompact K₀ :=
    isCompact_critSet_inter hU hf (isCompact_closedBall x₀ ρ)
      fun y hy => hVU (hballV hy)
  -- the chart map `h`
  set h : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
    fun y => Function.update y s (σ y) with hhdef
  have hhsm : ContDiffOn ℝ ∞ h U := by
    have h1 : h = fun y => y + (σ y - y s) • Pi.single s 1 := by
      funext y
      exact update_eq_add_smul_single y s (σ y)
    rw [h1]
    exact contDiffOn_id.add ((hσsm.sub ((ContinuousLinearMap.proj s :
      (Fin (n + 1) → ℝ) →L[ℝ] ℝ).contDiff.contDiffOn)).smul contDiffOn_const)
  set S : Set (Fin (n + 1) → ℝ) := h '' K₀ with hSdef
  have hScpt : IsCompact S :=
    hK₀cpt.image_of_continuousOn (hhsm.continuousOn.mono hK₀U)
  have hSW : S ⊆ W := by
    rintro _ ⟨y, hy, rfl⟩
    exact hmapsVW y (hK₀V hy)
  have hgh : ∀ y ∈ V, g (h y) = f y := by
    intro y hy
    rw [hgdef]
    show f (h' (Function.update y s (σ y))) = f y
    rw [hleft y hy]
  have himg : f '' K₀ = g '' S := by
    rw [hSdef, ← image_comp]
    exact image_congr fun y hy => (hgh y (hK₀V hy)).symm
  -- the product-side compact set
  set A' : Set (ℝ × (Fin q → ℝ)) := (fun w => splitCLE q r (g w)) '' S
    with hA'def
  have hA'cpt : IsCompact A' :=
    hScpt.image_of_continuousOn
      ((splitCLE q r).continuous.comp_continuousOn (hgsm.continuousOn.mono hSW))
  -- slices of `A'` are null, by the inductive hypothesis
  have hslice : ∀ t : ℝ, volume (Prod.mk t ⁻¹' A') = 0 := by
    intro t
    set Ωt : Set (Fin n → ℝ) := {z | (splitCLE n s).symm (t, z) ∈ W}
      with hΩtdef
    have hΩtopen : IsOpen Ωt := by
      have hcont : Continuous fun z : Fin n → ℝ =>
          (splitCLE n s).symm (t, z) :=
        (splitCLE n s).symm.continuous.comp (continuous_const.prodMk
          continuous_id)
      exact hWopen.preimage hcont
    set gt : (Fin n → ℝ) → Fin q → ℝ :=
      fun z => Fin.removeNth r (g ((splitCLE n s).symm (t, z))) with hgtdef
    have hgtsm : ContDiffOn ℝ ∞ gt Ωt := by
      have h1 : ContDiffOn ℝ ∞
          (fun z : Fin n → ℝ => g ((splitCLE n s).symm (t, z))) Ωt :=
        hgsm.comp (((splitCLE n s).symm.contDiff.comp
          (contDiff_const.prodMk contDiff_id)).contDiffOn) fun z hz => hz
      have h2 : ContDiff ℝ ∞ fun w : Fin (q + 1) → ℝ => Fin.removeNth r w := by
        have h3 : (fun w : Fin (q + 1) → ℝ => Fin.removeNth r w)
            = fun w => (splitCLE q r w).2 := rfl
        rw [h3]
        exact contDiff_snd.comp (splitCLE q r).contDiff
      exact h2.comp_contDiffOn h1
    have hincl : Prod.mk t ⁻¹' A' ⊆ gt '' critSet Ωt gt := by
      intro y' hy'
      obtain ⟨w, hwS, hweq⟩ := hy'
      obtain ⟨y₁, hy₁K, rfl⟩ := hwS
      have hwW : h y₁ ∈ W := hSW ⟨y₁, hy₁K, rfl⟩
      have hy₁V : y₁ ∈ V := hK₀V hy₁K
      have hy₁U : y₁ ∈ U := hVU hy₁V
      have hgwr : g (h y₁) r = (h y₁) s := hkey _ hwW
      have ht' : g (h y₁) r = t := congrArg Prod.fst hweq
      have hy'eq : Fin.removeNth r (g (h y₁)) = y' := congrArg Prod.snd hweq
      set z : Fin n → ℝ := Fin.removeNth s (h y₁) with hzdef
      have hφz : (splitCLE n s).symm (t, z) = h y₁ := by
        rw [splitCLE_symm_apply]
        show Fin.insertNth s t (Fin.removeNth s (h y₁)) = h y₁
        rw [← ht', hgwr]
        exact Fin.insertNth_self_removeNth ..
      have hzΩt : z ∈ Ωt := by
        rw [hΩtdef, mem_ofPred_eq, hφz]
        exact hwW
      have hgtz : gt z = y' := by
        rw [hgtdef]
        show Fin.removeNth r (g ((splitCLE n s).symm (t, z))) = y'
        rw [hφz]
        exact hy'eq
      refine ⟨z, ⟨hzΩt, ?_⟩, hgtz⟩
      -- criticality of `z` for the slice map
      intro hsurj
      apply hy₁K.1.2
      -- differentiability bookkeeping
      have hgdiffw : DifferentiableAt ℝ g (h y₁) :=
        (hgsm.contDiffAt (hWopen.mem_nhds hwW)).differentiableAt infty_ne_zero
      have hh'diffw : DifferentiableAt ℝ h' (h y₁) :=
        (h'sm.contDiffAt (hWopen.mem_nhds hwW)).differentiableAt infty_ne_zero
      have hfdiffy : DifferentiableAt ℝ f y₁ :=
        (hf.contDiffAt (hU.mem_nhds hy₁U)).differentiableAt infty_ne_zero
      -- the conjugated product map `G` and its derivative `D` at `(t, z)`
      set G : ℝ × (Fin n → ℝ) → ℝ × (Fin q → ℝ) :=
        fun p => splitCLE q r (g ((splitCLE n s).symm p)) with hGdef
      set D : (ℝ × (Fin n → ℝ)) →L[ℝ] ℝ × (Fin q → ℝ) :=
        ((splitCLE q r : (Fin (q + 1) → ℝ) →L[ℝ] ℝ × (Fin q → ℝ)).comp
          ((fderiv ℝ g (h y₁)).comp
            ((splitCLE n s).symm : ℝ × (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))))
        with hDdef
      have hD : HasFDerivAt G D (t, z) := by
        have h1 : HasFDerivAt (splitCLE n s).symm
            ((splitCLE n s).symm : ℝ × (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ))
            (t, z) := (splitCLE n s).symm.hasFDerivAt
        have h2 : HasFDerivAt g (fderiv ℝ g (h y₁))
            ((splitCLE n s).symm (t, z)) := by
          rw [hφz]
          exact hgdiffw.hasFDerivAt
        have h3 := h2.comp (t, z) h1
        have h4 : HasFDerivAt (splitCLE q r)
            (splitCLE q r : (Fin (q + 1) → ℝ) →L[ℝ] ℝ × (Fin q → ℝ))
            (g ((splitCLE n s).symm (t, z))) := (splitCLE q r).hasFDerivAt
        exact h4.comp (t, z) h3
      -- first component of `D` is the first coordinate
      have hfstD : ∀ ξ : ℝ × (Fin n → ℝ), (D ξ).1 = ξ.1 := by
        have hmem : (splitCLE n s).symm ⁻¹' W ∈ 𝓝 ((t, z) : ℝ × (Fin n → ℝ)) := by
          refine (hWopen.preimage (splitCLE n s).symm.continuous).mem_nhds ?_
          rw [mem_preimage, hφz]
          exact hwW
        have hev : (fun p : ℝ × (Fin n → ℝ) => (G p).1)
            =ᶠ[𝓝 ((t, z) : ℝ × (Fin n → ℝ))] fun p => p.1 := by
          filter_upwards [hmem] with p hp
          have h5 : (G p).1 = g ((splitCLE n s).symm p) r := rfl
          rw [h5, hkey _ hp, splitCLE_symm_apply]
          exact Fin.insertNth_apply_same ..
        have h6 : HasFDerivAt (fun p : ℝ × (Fin n → ℝ) => (G p).1)
            ((ContinuousLinearMap.fst ℝ ℝ (Fin q → ℝ)).comp D) (t, z) :=
          (ContinuousLinearMap.fst ℝ ℝ (Fin q → ℝ)).hasFDerivAt.comp (t, z) hD
        have h7 : HasFDerivAt (fun p : ℝ × (Fin n → ℝ) => (G p).1)
            (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)) (t, z) :=
          (hasFDerivAt_fst).congr_of_eventuallyEq hev
        have h8 := h6.unique h7
        intro ξ
        have h9 := congrArg (fun L => L ξ) h8
        exact h9
      -- the derivative of the slice map
      have hgtderiv : HasFDerivAt gt
          (((ContinuousLinearMap.snd ℝ ℝ (Fin q → ℝ)).comp D).comp
            (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ))) z := by
        have h10 : HasFDerivAt (fun p : ℝ × (Fin n → ℝ) => (G p).2)
            ((ContinuousLinearMap.snd ℝ ℝ (Fin q → ℝ)).comp D) (t, z) :=
          (ContinuousLinearMap.snd ℝ ℝ (Fin q → ℝ)).hasFDerivAt.comp (t, z) hD
        exact h10.comp z (hasFDerivAt_prodMk_right t z)
      -- surjectivity transfer: slice ⟹ product map
      have hDsurj : Surjective D := by
        rintro ⟨a, b⟩
        obtain ⟨ζ, hζ⟩ := hsurj (b - (D (a, 0)).2)
        refine ⟨(a, ζ), ?_⟩
        have hsplitp : ((a, ζ) : ℝ × (Fin n → ℝ)) = (a, 0) + (0, ζ) := by
          simp
        rw [hsplitp, map_add]
        have h11 : (D ((0 : ℝ), ζ)).2 = fderiv ℝ gt z ζ := by
          rw [hgtderiv.fderiv]
          rfl
        have h12 : fderiv ℝ gt z ζ = b - (D (a, 0)).2 := hζ
        refine Prod.ext ?_ ?_
        · have ha1 : (D ((a : ℝ), (0 : Fin n → ℝ))).1 = a := hfstD (a, 0)
          have ha2 : (D ((0 : ℝ), ζ)).1 = 0 := hfstD (0, ζ)
          simp [ha1, ha2]
        · simp only [Prod.snd_add, h11, h12]
          abel
      -- surjectivity transfer: product map ⟹ `g` at `h y₁`
      have hgsurj : Surjective (fderiv ℝ g (h y₁)) := by
        intro c
        obtain ⟨ξ, hξ⟩ := hDsurj (splitCLE q r c)
        refine ⟨(splitCLE n s).symm ξ, ?_⟩
        have h13 : D ξ = splitCLE q r
            (fderiv ℝ g (h y₁) ((splitCLE n s).symm ξ)) := rfl
        rw [h13] at hξ
        exact (splitCLE q r).injective hξ
      -- surjectivity transfer: `g` ⟹ `f` at `y₁`
      have hh'w : h' (h y₁) = y₁ := hleft y₁ hy₁V
      have hcomp : fderiv ℝ g (h y₁)
          = (fderiv ℝ f y₁).comp (fderiv ℝ h' (h y₁)) := by
        have h14 : HasFDerivAt f (fderiv ℝ f y₁) (h' (h y₁)) := by
          rw [hh'w]
          exact hfdiffy.hasFDerivAt
        exact (h14.comp (h y₁) hh'diffw.hasFDerivAt).fderiv
      rw [hcomp] at hgsurj
      have h15 : ⇑((fderiv ℝ f y₁).comp (fderiv ℝ h' (h y₁)))
          = ⇑(fderiv ℝ f y₁) ∘ ⇑(fderiv ℝ h' (h y₁)) := rfl
      rw [h15] at hgsurj
      exact hgsurj.of_comp
    exact measure_mono_null hincl (IH Ωt gt hΩtopen hgtsm)
  -- assemble via Fubini
  have hprod : volume A' = 0 := by
    rw [Measure.volume_eq_prod]
    rw [Measure.measure_prod_null hA'cpt.measurableSet]
    exact Filter.Eventually.of_forall hslice
  have hgS : volume (g '' S) = 0 := by
    refine splitCLE_image_null r ?_ hprod
    rw [hA'def, ← image_comp]
    exact Subset.rfl
  show volume (f '' K₀) = 0
  rw [himg]
  exact hgS

end

end Submission
