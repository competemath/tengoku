/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.DolbeaultComparison.GlueForm01
public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Cech.Refinement
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.Bridges
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.RealSmooth
public import Tengoku

/-!
# PoU splitting of a Čech `0`-cocycle (`Jacobian/DolbeaultComparison/Splitting.lean`)

Unit: dolbeault-comparison (`docs/design/dolbeault-comparison.md` §4.3/§6.2/§6.3). Builds the
Forster 12.6 "smooth splitting" of a `D = 0` Čech cocycle by a partition of unity, and packages
each splitting's PDE data as a `DbarGlueData` (via `GlueForm01.lean`), whose glued form
`dolbForm h𝒰 f` is independent of the chosen splitting modulo `range dbar` — the input to
`Comparison.lean`'s Čech → Dolbeault map.

* `Z1.repr`: pointwise holomorphic representatives of a `D = 0` cocycle's components.
* `Z1.repr_cocycle`/`Z1.repr_add`/`Z1.repr_smul`: pointwise algebraic identities on pair-meets.
* `SmoothSplitting`, `exists_smoothSplitting` (D5 formula, via `RS.exists_smoothPartitionOfUnity`).
* `SmoothSplitting.glueData`, `dolbForm`.
* Independence lemmas, all reducing to `DbarGlueData.form_unique`
  (`sub_mem_range_dbar_of_splittings`, `dolbForm_add_sub_mem`, `dolbForm_smul_sub_mem`,
  `dolbForm_mem_range_of_mem_B1`, `dolbForm_res_sub_mem`).
-/

@[expose] public section

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech

namespace RS.Dolb

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `Z1.repr`: pointwise holomorphic representatives -/

/-- Pointwise holomorphic representative of a component of a `D = 0` cocycle. -/
noncomputable def Z1.repr {𝒰 : FinCover (⊤ : Opens X)} (f : Z1 (0 : RS.Divisor X) 𝒰)
    (p : Fin 𝒰.n × Fin 𝒰.n) : X → ℂ :=
  RS.MeroGermOn.holoRepr
    ((f : C1 (0 : RS.Divisor X) 𝒰) p : RS.MeroGermOn X (𝒰.U p.1 ⊓ 𝒰.U p.2 : Set X))

/-! ### Extension-by-zero smul lemma -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Extension-by-zero workhorse: `ψ` globally smooth with `tsupport ψ ⊆ W`, `F` smooth on
`W ⊓ U` ⇒ `fun x => ψ x • F x` is smooth on `U` (values off `W` are junk-irrelevant: `ψ`
vanishes there). -/
theorem contMDiffOn_smul_of_tsupport_subset {ψ : X → ℝ} {F : X → ℂ} {W U : Opens X}
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ ψ) (hsupp : tsupport ψ ⊆ (W : Set X))
    (hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ F (W ⊓ U : Set X)) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun x => ψ x • F x) (U : Set X) := by
  intro x hx
  by_cases hxW : x ∈ (W : Set X)
  · have hxWU : x ∈ (W ⊓ U : Opens X) := ⟨hxW, hx⟩
    exact ((hψ x).smul (hF.contMDiffAt ((W ⊓ U).isOpen.mem_nhds hxWU))).contMDiffWithinAt
  · have hzero : ψ =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      have hnhds : (tsupport ψ)ᶜ ∈ nhds x :=
        (isClosed_tsupport ψ).isOpen_compl.mem_nhds (fun hmem => hxW (hsupp hmem))
      filter_upwards [hnhds] with y hy
      by_contra hne
      exact hy (subset_tsupport ψ hne)
    have heq : (fun x => ψ x • F x) =ᶠ[nhds x] (fun _ => (0 : ℂ)) := by
      filter_upwards [hzero] with y hy
      show ψ y • F y = 0
      rw [hy]; simp
    exact (contMDiffAt_const.congr_of_eventuallyEq heq).contMDiffWithinAt

/-! ### `SmoothSplitting` and its existence -/

/-- A smooth splitting of a `D = 0` cocycle (Forster 12.6 output, D5's frozen sign
convention). -/
structure SmoothSplitting (𝒰 : FinCover (⊤ : Opens X)) (f : Z1 (0 : RS.Divisor X) 𝒰) where
  /-- The member-wise functions realizing the splitting. -/
  g : Fin 𝒰.n → X → ℂ
  smoothOn : ∀ i, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (g i) (𝒰.U i : Set X)
  split : ∀ i j, ∀ x ∈ (𝒰.U i ⊓ 𝒰.U j : Opens X), Z1.repr f (i, j) x = g j x - g i x

/-! ### `SmoothSplitting.glueData`, `dolbForm` -/

/-! ### Compat: `IsDbarOn.add`/`IsDbarOn.congr` -/

/-! ### Independence lemmas: everything reduces to `DbarGlueData.form_unique` -/

end RS.Dolb
