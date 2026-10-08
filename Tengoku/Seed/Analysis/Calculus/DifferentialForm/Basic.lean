/-
Copyright (c) 2025 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Sam Lindauer
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Normed.Module.Alternating.Uncurry.Fin
public import Tengoku.Seed.Analysis.Calculus.FDeriv.Symmetric
public import Tengoku.Seed.Analysis.Calculus.FDeriv.CompCLM
public import Tengoku.Seed.Analysis.Calculus.FDeriv.ContinuousAlternatingMap

/-!
# Exterior derivative of a differential form on a normed space

In this file we define the exterior derivative of a differential form on a normed space.
Under certain smoothness assumptions, we prove that this operation is linear in the form
and the second exterior derivative of a form is zero.

We represent a differential `n`-form on `E` taking values in `F` as `E → E [⋀^Fin n]→L[𝕜] F`.

## Implementation notes

There are a few competing definitions of the exterior derivative of a differential form
that differ from each other by a normalization factor.
We use the following one:

$$
dω(x; v_0, \dots, v_n) = \sum_{i=0}^n (-1)^i D_x ω(x; v_0, \dots, \widehat{v_i}, \dots, v_n) · v_i
$$

where $\widehat{v_i}$ means that we omit this element of the tuple, see `extDeriv_apply`.

## TODO

- Introduce notation for:
  - an unbundled `n`-form on a normed space;
  - a bundled `C^r`-smooth `n`-form on a normed space;
  - same for manifolds (not defined yet).
- Introduce bundled `C^r`-smooth `n`-forms on normed spaces and manifolds.
  - Discuss the future API and the use cases that need to be covered on Zulip.
  - Introduce new types & notation, copy the API.
- Add shorter and more readable definitions (or abbreviations?)
  for `0`-forms (`constOfIsEmpty`) and `1`-forms (`ofSubsingleton`),
  sync with the API for `ContinuousMultilinearMap`.
-/

@[expose] public section

open Filter ContinuousAlternatingMap Set
open scoped Topology

variable {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n m : ℕ} {r : WithTop ℕ∞}
  {ω ω₁ ω₂ : E → E [⋀^Fin n]→L[𝕜] F} {s t : Set E} {x : E}

/-- Exterior derivative of a differential form.

There are a few competing definitions of the exterior derivative of a differential form
that differ from each other by a normalization factor.
We use the following one:

$$
dω(x; v_0, \dots, v_n) = \sum_{i=0}^n (-1)^i D_x ω(x; v_0, \dots, \widehat{v_i}, \dots, v_n) · v_i
$$

where $\widehat{v_i}$ means that we omit this element of the tuple, see `extDeriv_apply`.
-/
noncomputable def extDeriv (ω : E → E [⋀^Fin n]→L[𝕜] F) (x : E) : E [⋀^Fin (n + 1)]→L[𝕜] F :=
  .alternatizeUncurryFin (fderiv 𝕜 ω x)

/-- Exterior derivative of a differential form within a set.

There are a few competing definitions of the exterior derivative of a differential form
that differ from each other by a normalization factor.
We use the following one:

$$
dω(x; v_0, \dots, v_n) = \sum_{i=0}^n (-1)^i D_x ω(x; v_0, \dots, \widehat{v_i}, \dots, v_n) · v_i
$$

where $\widehat{v_i}$ means that we omit this element of the tuple, see `extDerivWithin_apply`.
-/
noncomputable def extDerivWithin (ω : E → E [⋀^Fin n]→L[𝕜] F) (s : Set E) (x : E) :
    E [⋀^Fin (n + 1)]→L[𝕜] F :=
  .alternatizeUncurryFin (fderivWithin 𝕜 ω s x)

/--
@isnad1 id=eq.0h5v.s7.f9dbbbc7c0a3 from=seed src=0 shape=47cb5f1c vocab=d9ebf0f1
-/
@[simp]
theorem extDerivWithin_univ (ω : E → E [⋀^Fin n]→L[𝕜] F) :
    extDerivWithin ω univ = extDeriv ω := by
  ext1 x
  rw [extDerivWithin, extDeriv, fderivWithin_univ]

/--
@isnad1 id=eq.3h8v.s10.e7625b2f867f from=seed src=0 shape=c773ffad vocab=fbce15fe
-/
theorem extDerivWithin_add (hsx : UniqueDiffWithinAt 𝕜 s x)
    (hω₁ : DifferentiableWithinAt 𝕜 ω₁ s x) (hω₂ : DifferentiableWithinAt 𝕜 ω₂ s x) :
    extDerivWithin (ω₁ + ω₂) s x = extDerivWithin ω₁ s x + extDerivWithin ω₂ s x := by
  simp [extDerivWithin, fderivWithin_add hsx hω₁ hω₂, alternatizeUncurryFin_add]

/--
@isnad1 id=eq.3h8v.s10.94aae55d8856 from=seed src=0 shape=1ca2ed3f vocab=fbce15fe
-/
theorem extDerivWithin_fun_add (hsx : UniqueDiffWithinAt 𝕜 s x)
    (hω₁ : DifferentiableWithinAt 𝕜 ω₁ s x) (hω₂ : DifferentiableWithinAt 𝕜 ω₂ s x) :
    extDerivWithin (fun x ↦ ω₁ x + ω₂ x) s x = extDerivWithin ω₁ s x + extDerivWithin ω₂ s x :=
  extDerivWithin_add hsx hω₁ hω₂

/--
@isnad1 id=eq.2h7v.s10.b307868a3c50 from=seed src=0 shape=66a18fde vocab=0faa2db8
-/
theorem extDeriv_add (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜 ω₂ x) :
    extDeriv (ω₁ + ω₂) x = extDeriv ω₁ x + extDeriv ω₂ x := by
  simp [← extDerivWithin_univ, extDerivWithin_add, *, DifferentiableAt.differentiableWithinAt]

/--
@isnad1 id=eq.2h7v.s10.4c5ec53a90bb from=seed src=0 shape=19ed6cba vocab=0faa2db8
-/
theorem extDeriv_fun_add (hω₁ : DifferentiableAt 𝕜 ω₁ x) (hω₂ : DifferentiableAt 𝕜 ω₂ x) :
    extDeriv (fun x ↦ ω₁ x + ω₂ x) x = extDeriv ω₁ x + extDeriv ω₂ x :=
  extDeriv_add hω₁ hω₂

/--
@isnad1 id=eq.1h8v.s9.023aa9af3d94 from=seed src=0 shape=cbf512be vocab=71448e79
-/
theorem extDerivWithin_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F) (hsx : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin (c • ω) s x = c • extDerivWithin ω s x := by
  simp [extDerivWithin, fderivWithin_const_smul_field, hsx, alternatizeUncurryFin_smul]

/--
@isnad1 id=eq.1h8v.s9.b3b2e06e8f3f from=seed src=0 shape=7afa07c3 vocab=71448e79
-/
theorem extDerivWithin_fun_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F)
    (hsx : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin (fun x ↦ c • ω x) s x = c • extDerivWithin ω s x :=
  extDerivWithin_smul c ω hsx

/--
@isnad1 id=eq.0h7v.s9.7fd2f3416d21 from=seed src=0 shape=8abc81ad vocab=628ce73d
-/
theorem extDeriv_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F) :
    extDeriv (c • ω) x = c • extDeriv ω x := by
  simp [← extDerivWithin_univ, extDerivWithin_smul]

/--
@isnad1 id=eq.0h7v.s9.7fd2f3416d21 from=seed src=0 shape=8abc81ad vocab=628ce73d
-/
theorem extDeriv_fun_smul (c : 𝕜) (ω : E → E [⋀^Fin n]→L[𝕜] F) :
    extDeriv (c • ω) x = c • extDeriv ω x :=
  extDeriv_smul c ω

/-- The exterior derivative of a `0`-form given by a function `f` within a set
is the 1-form given by the derivative of `f` within the set.
@isnad1 id=eq.1h6v.s10.62aa09f4670c from=seed src=0 shape=75c2c490 vocab=de754853
-/
theorem extDerivWithin_constOfIsEmpty (f : E → F) (hs : UniqueDiffWithinAt 𝕜 s x) :
    extDerivWithin (fun x ↦ constOfIsEmpty 𝕜 E (Fin 0) (f x)) s x =
      .ofSubsingleton _ _ _ (0 : Fin 1) (fderivWithin 𝕜 f s x) := by
  simp only [extDerivWithin, ← constOfIsEmptyLIE_apply, ← Function.comp_def _ f,
    (constOfIsEmptyLIE 𝕜 E F (Fin 0)).comp_fderivWithin hs,
    alternatizeUncurryFin_constOfIsEmptyLIE_comp]

/-- The exterior derivative of a `0`-form given by a function `f`
is the 1-form given by the derivative of `f`.
@isnad1 id=eq.0h5v.s10.29f97f29c722 from=seed src=0 shape=551dea7c vocab=6087ef9b
-/
theorem extDeriv_constOfIsEmpty (f : E → F) (x : E) :
    extDeriv (fun x ↦ constOfIsEmpty 𝕜 E (Fin 0) (f x)) x =
      .ofSubsingleton _ _ _ (0 : Fin 1) (fderiv 𝕜 f x) := by
  simp [← extDerivWithin_univ, extDerivWithin_constOfIsEmpty, fderivWithin_univ]

/--
@isnad1 id=eq.2h8v.s8.2168a25c6a94 from=seed src=0 shape=e43aa27b vocab=df5fb4ac
-/
theorem Filter.EventuallyEq.extDerivWithin_eq (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x := by
  simp only [extDerivWithin, alternatizeUncurryFin, hs.fderivWithin_eq hx]

/--
@isnad1 id=eq.2h8v.s8.970da9b32355 from=seed src=0 shape=e6d005b2 vocab=329ef5bc
-/
theorem Filter.EventuallyEq.extDerivWithin_eq_of_mem (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : x ∈ s) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  hs.extDerivWithin_eq (mem_of_mem_nhdsWithin hx hs :)

/--
@isnad1 id=eq.1h8v.s8.6189ee2b9880 from=seed src=0 shape=7afe8017 vocab=d6acbbbf
-/
theorem Filter.EventuallyEq.extDerivWithin_eq_of_insert (hs : ω₁ =ᶠ[𝓝[insert x s] x] ω₂) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x := by
  apply Filter.EventuallyEq.extDerivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
  exact (mem_of_mem_nhdsWithin (mem_insert x s) hs :)

/--
@isnad1 id=eventual.2h9v.s8.362da33134dd from=seed src=0 shape=8f9cf6db vocab=c8e518da
-/
theorem Filter.EventuallyEq.extDerivWithin' (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (ht : t ⊆ s) :
    extDerivWithin ω₁ t =ᶠ[𝓝[s] x] extDerivWithin ω₂ t :=
  (eventually_eventually_nhdsWithin.2 hs).mp <| eventually_mem_nhdsWithin.mono fun _y hys hs =>
    EventuallyEq.extDerivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)

/--
@isnad1 id=eventual.1h8v.s8.26f3f4ca6902 from=seed src=0 shape=1d392917 vocab=df5fb4ac
-/
protected theorem Filter.EventuallyEq.extDerivWithin (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) :
    extDerivWithin ω₁ s =ᶠ[𝓝[s] x] extDerivWithin ω₂ s :=
  hs.extDerivWithin' .rfl

/--
@isnad1 id=eq.1h8v.s8.76d0ed968f92 from=seed src=0 shape=4c7b46f0 vocab=7c57badc
-/
theorem Filter.EventuallyEq.extDerivWithin_eq_nhds (h : ω₁ =ᶠ[𝓝 x] ω₂) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  (h.filter_mono nhdsWithin_le_nhds).extDerivWithin_eq h.self_of_nhds

/--
@isnad1 id=eq.2h8v.s8.0f6cbad3e84b from=seed src=0 shape=739ed8d4 vocab=c827c753
-/
theorem extDerivWithin_congr (hs : EqOn ω₁ ω₂ s) (hx : ω₁ x = ω₂ x) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).extDerivWithin_eq hx

/--
@isnad1 id=eq.2h8v.s8.fba8b658c309 from=seed src=0 shape=b4b2bb0c vocab=ce1a5b96
-/
theorem extDerivWithin_congr' (hs : EqOn ω₁ ω₂ s) (hx : x ∈ s) :
    extDerivWithin ω₁ s x = extDerivWithin ω₂ s x :=
  extDerivWithin_congr hs (hs hx)

/--
@isnad1 id=eventual.1h7v.s8.ff063aa60462 from=seed src=0 shape=795ea972 vocab=99834cca
-/
protected theorem Filter.EventuallyEq.extDeriv (h : ω₁ =ᶠ[𝓝 x] ω₂) :
    extDeriv ω₁ =ᶠ[𝓝 x] extDeriv ω₂ := by
  simp only [← nhdsWithin_univ, ← extDerivWithin_univ] at *
  exact h.extDerivWithin

/--
@isnad1 id=eq.1h7v.s8.0390bc83cd7a from=seed src=0 shape=13d4503c vocab=99834cca
-/
theorem Filter.EventuallyEq.extDeriv_eq (h : ω₁ =ᶠ[𝓝 x] ω₂) : extDeriv ω₁ x = extDeriv ω₂ x :=
  h.extDeriv.self_of_nhds

/--
@isnad1 id=eq.2h8v.s10.65cbc00d33fb from=seed src=0 shape=2bfc8b1a vocab=24bb6c83
-/
theorem extDerivWithin_apply (h : DifferentiableWithinAt 𝕜 ω s x) (hs : UniqueDiffWithinAt 𝕜 s x)
    (v : Fin (n + 1) → E) :
    extDerivWithin ω s x v =
      ∑ i, (-1) ^ i.val • fderivWithin 𝕜 (ω · (i.removeNth v)) s x (v i) := by
  simp [extDerivWithin, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    fderivWithin_continuousAlternatingMap_apply_const_apply, *]

/--
@isnad1 id=eq.1h7v.s10.058db2a08c79 from=seed src=0 shape=85251b4d vocab=dabcf047
-/
theorem extDeriv_apply (h : DifferentiableAt 𝕜 ω x) (v : Fin (n + 1) → E) :
    extDeriv ω x v = ∑ i, (-1) ^ i.val • fderiv 𝕜 (ω · (i.removeNth v)) x (v i) := by
  simp [← extDerivWithin_univ, extDerivWithin_apply h.differentiableWithinAt]

/-- The second exterior derivative of a sufficiently smooth differential form is zero.
@isnad1 id=eq.5h8v.s9.339856e6d57a from=seed src=0 shape=5e0d5d48 vocab=14e38e72
-/
theorem extDerivWithin_extDerivWithin_apply (hω : ContDiffWithinAt 𝕜 r ω s x)
    (hr : minSmoothness 𝕜 2 ≤ r) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ closure (interior s))
    (h'x : x ∈ s) : extDerivWithin (extDerivWithin ω s) s x = 0 := calc
  extDerivWithin (extDerivWithin ω s) s x
    = alternatizeUncurryFin (fderivWithin 𝕜 (fun y ↦
        alternatizeUncurryFin (fderivWithin 𝕜 ω s y)) s x) := rfl
  _ = alternatizeUncurryFin (alternatizeUncurryFinCLM _ _ _ ∘L
        fderivWithin 𝕜 (fderivWithin 𝕜 ω s) s x) := by
    congr 1
    have : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 ω s) s x := by
      refine (hω.fderivWithin_right hs ?_ h'x).differentiableWithinAt one_ne_zero
      exact le_minSmoothness.trans hr
    exact alternatizeUncurryFinCLM _ _ _ |>.hasFDerivAt.comp_hasFDerivWithinAt x
      this.hasFDerivWithinAt |>.fderivWithin (hs.uniqueDiffWithinAt h'x)
  _ = 0 := alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric <|
    hω.isSymmSndFDerivWithinAt hr hs hx h'x

/-- The second exterior derivative of a sufficiently smooth differential form is zero.
@isnad1 id=eqon.3h7v.s9.a2fba0524c76 from=seed src=0 shape=94394787 vocab=7dd7e142
-/
theorem extDerivWithin_extDerivWithin_eqOn (hω : ContDiffOn 𝕜 r ω s) (hr : minSmoothness 𝕜 2 ≤ r)
    (hs : UniqueDiffOn 𝕜 s) :
    EqOn (extDerivWithin (extDerivWithin ω s) s) 0 (s ∩ closure (interior s)) := by
  rintro x ⟨h'x, hx⟩
  exact extDerivWithin_extDerivWithin_apply (hω.contDiffWithinAt h'x) hr hs hx h'x

/-- The second exterior derivative of a sufficiently smooth differential form is zero.
@isnad1 id=eq.2h7v.s9.ccc8900205b3 from=seed src=0 shape=b34ad7e5 vocab=0f9b8e7a
-/
theorem extDeriv_extDeriv_apply (hω : ContDiffAt 𝕜 r ω x) (hr : minSmoothness 𝕜 2 ≤ r) :
    extDeriv (extDeriv ω) x = 0 := by
  simp only [← extDerivWithin_univ]
  apply extDerivWithin_extDerivWithin_apply (s := univ) hω.contDiffWithinAt hr <;> simp

/-- The second exterior derivative of a sufficiently smooth differential form is zero.
@isnad1 id=eq.2h6v.s9.558770efedf7 from=seed src=0 shape=3fef022e vocab=8e5864dc
-/
theorem extDeriv_extDeriv (h : ContDiff 𝕜 r ω) (hr : minSmoothness 𝕜 2 ≤ r) :
    extDeriv (extDeriv ω) = 0 :=
  funext fun _ ↦ extDeriv_extDeriv_apply h.contDiffAt hr

/-- Exterior derivative within a set commutes with pullback.
@isnad1 id=eq.7h11v.s9.67c1504e30f2 from=seed src=0 shape=8b04de42 vocab=3e9b1759
-/
theorem extDerivWithin_pullback {ω : F → F [⋀^Fin n]→L[𝕜] G} {f : E → F} {t : Set F}
    (hω : DifferentiableWithinAt 𝕜 ω t (f x)) (hf : ContDiffWithinAt 𝕜 r f s x)
    (hr : minSmoothness 𝕜 2 ≤ r) (hs : UniqueDiffOn 𝕜 s)
    (hxc : x ∈ closure (interior s)) (hxs : x ∈ s) (hst : MapsTo f s t) :
    extDerivWithin (fun x ↦ (ω (f x)).compContinuousLinearMap (fderivWithin 𝕜 f s x)) s x =
      (extDerivWithin ω t (f x)).compContinuousLinearMap (fderivWithin 𝕜 f s x) := by
  have hdf : DifferentiableWithinAt 𝕜 f s x :=
    hf.differentiableWithinAt <| (two_pos.trans_le <| le_minSmoothness.trans hr).ne'
  have hd2f : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 f s) s x :=
    (hf.fderivWithin_right hs (le_minSmoothness.trans hr) hxs).differentiableWithinAt one_ne_zero
  rw [extDerivWithin,
    fderivWithin_continuousAlternatingMapCompContinuousLinearMap (by exact hω.comp x hdf hst) hd2f
      (hs x hxs),
    alternatizeUncurryFin_add, fderivWithin_fun_comp _ hω hdf hst (hs x hxs), extDerivWithin,
    alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero, add_zero]
  · ext v
    simp +unfoldPartialApp [alternatizeUncurryFin_apply, Fin.removeNth, Function.comp_def]
  · apply hf.isSymmSndFDerivWithinAt <;> assumption

/-- Exterior derivative commutes with pullback.
@isnad1 id=eq.3h9v.s9.c781361063fb from=seed src=0 shape=ea374601 vocab=85418ec2
-/
theorem extDeriv_pullback {ω : F → F [⋀^Fin n]→L[𝕜] G} {f : E → F}
    (hω : DifferentiableAt 𝕜 ω (f x)) (hf : ContDiffAt 𝕜 r f x) (hr : minSmoothness 𝕜 2 ≤ r) :
    extDeriv (fun x ↦ (ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x)) x =
      (extDeriv ω (f x)).compContinuousLinearMap (fderiv 𝕜 f x) := by
  simp only [← differentiableWithinAt_univ, ← extDerivWithin_univ, ← contDiffWithinAt_univ,
    ← fderivWithin_univ] at *
  apply extDerivWithin_pullback (r := r) <;> simp [*]
