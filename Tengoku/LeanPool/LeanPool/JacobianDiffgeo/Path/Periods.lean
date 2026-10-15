/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Path.Continuation
public import Tengoku
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Path.HomotopySquare

/-!
# Periods of a holomorphic 1-form along a loop (CC6)

Unit: paths-and-integrals (`docs/design/paths-and-integrals.md` §6). Carrier decision (CC9
alignment): based loops `Path x x`, with descent to `Path.Homotopic.Quotient x x` available via
`pathIntegralQ`. This unit does not define the period subgroup (jacobian-construction's job); it
exports the loop-algebra lemmas that make `AddSubgroup.closure (Set.range (periodVector b))`
well-behaved.

Main declarations:
* `RS.period γ η` — abbreviation for `pathIntegral γ η` on a based loop.
* `RS.period_trans/symm/refl/congr_homotopic/conj`.
* `RS.periodVector b γ` — the period vector w.r.t. a basis `b` of `Form1 X`, with
  `periodVector_trans/symm/refl`.
-/

@[expose] public section

open scoped ContDiff Manifold
open IsManifold Module

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {x x' : X}

/-- The period of a 1-form along a loop. -/
noncomputable abbrev period (γ : Path x x) (η : Form1 X) : ℂ := pathIntegral γ η

/--
@isnad1 id=eq.0h5v.s7.7218031cdbd6 from=translated src=- shape=8caf5531 vocab=2b0884aa
-/
theorem period_trans (γ γ' : Path x x) (η : Form1 X) :
    period (γ.trans γ') η = period γ η + period γ' η := pathIntegral_trans γ γ' η

/--
@isnad1 id=eq.0h4v.s6.f570e5370e19 from=translated src=- shape=bc29392a vocab=8ec7e7fd
-/
theorem period_symm (γ : Path x x) (η : Form1 X) : period γ.symm η = -period γ η :=
  pathIntegral_symm γ η

/--
@isnad1 id=eq.0h3v.s6.0bb7e8f9cfe1 from=translated src=- shape=a2bdc9fb vocab=f1664ae7
-/
theorem period_refl (η : Form1 X) : period (Path.refl x) η = 0 := pathIntegral_refl x η

/--
@isnad1 id=eq.1h5v.s6.efc42ed64bd6 from=translated src=- shape=39f98225 vocab=cd122812
-/
theorem period_congr_homotopic {γ γ' : Path x x} (h : γ.Homotopic γ') (η : Form1 X) :
    period γ η = period γ' η := pathIntegral_congr_homotopic h η

/-- Conjugation invariance: periods are basepoint-independent along a connecting path.
@isnad1 id=eq.0h6v.s7.21388f229b27 from=translated src=- shape=9d0b75f2 vocab=1acd147d
-/
theorem period_conj (σ : Path x' x) (γ : Path x x) (η : Form1 X) :
    period ((σ.trans γ).trans σ.symm) η = period γ η := by
  change pathIntegral ((σ.trans γ).trans σ.symm) η = pathIntegral γ η
  rw [pathIntegral_trans, pathIntegral_trans, pathIntegral_symm]
  ring

/-- Period vector w.r.t. a basis of `Form1 X` (CC9 feed). -/
noncomputable def periodVector {n : ℕ} (b : Basis (Fin n) ℂ (Form1 X)) (γ : Path x x) :
    Fin n → ℂ := fun i => period γ (b i)

/--
@isnad1 id=eq.0h6v.s12.20d74cbc255a from=translated src=- shape=248ef3d1 vocab=09c07d29
-/
theorem periodVector_trans {n : ℕ} (b : Basis (Fin n) ℂ (Form1 X)) (γ γ' : Path x x) :
    periodVector b (γ.trans γ') = periodVector b γ + periodVector b γ' := by
  funext i
  change period (γ.trans γ') (b i) = period γ (b i) + period γ' (b i)
  exact period_trans γ γ' (b i)

/--
@isnad1 id=eq.0h5v.s12.c32ed6ada2d0 from=translated src=- shape=d2a47f0b vocab=5244a534
-/
theorem periodVector_symm {n : ℕ} (b : Basis (Fin n) ℂ (Form1 X)) (γ : Path x x) :
    periodVector b γ.symm = -periodVector b γ := by
  funext i
  change period γ.symm (b i) = -period γ (b i)
  exact period_symm γ (b i)

/--
@isnad1 id=eq.0h4v.s11.d8e933f0824c from=translated src=- shape=3b6fc283 vocab=66254061
-/
@[simp] theorem periodVector_refl {n : ℕ} (b : Basis (Fin n) ℂ (Form1 X)) :
    periodVector b (Path.refl x) = 0 := by
  funext i
  change period (Path.refl x) (b i) = 0
  exact period_refl (b i)

end RS

end
