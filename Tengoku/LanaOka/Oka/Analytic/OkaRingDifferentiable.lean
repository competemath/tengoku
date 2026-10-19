/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Analysis.Calculus.FDeriv.Analytic
import Tengoku.LanaOka.Oka.StructureSheaf

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Holomorphic functions on open subsets of `ℂⁿ` are complex differentiable

`OkaRing.differentiableOn_toGlobalFun`: the extension by zero of an element of `OkaRing U` is
complex differentiable on `U`. This is the bridge from `OkaRing` to the `DifferentiableOn`
vocabulary of Mathlib's complex analysis.
-/

open TopologicalSpace

variable {ι : Type*} [Fintype ι]

/-- Elements of `OkaRing U` are holomorphic on `U`. -/
lemma OkaRing.differentiableOn_toGlobalFun {U : Opens (ι → ℂ)} (f : OkaRing U) :
    DifferentiableOn ℂ (f.toGlobalFun _) U := fun x hx ↦
  ((okaAnalytic_iff _).1 f.2 x hx).differentiableAt.differentiableWithinAt
