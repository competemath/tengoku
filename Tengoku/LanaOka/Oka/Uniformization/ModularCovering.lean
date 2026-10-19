/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku
import Tengoku.Seed.NumberTheory.Modular
import Tengoku.Seed.NumberTheory.ModularForms.ProperlyDiscontinuous
import Tengoku.LanaOka.Oka.Uniformization.CoveringLift
import Tengoku.LanaOka.Oka.Uniformization.Holomorphic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The modular `j`-function off its branch values

`Heights.modularJ : ℍ → ℂ` is holomorphic and its fibres are exactly the `SL(2, ℤ)`-orbits
(`Heights.exists_smul_eq_of_modularJ_eq`). A point of `ℍ` with a nontrivial stabiliser (other than
`±1`) lies in the orbit of `i` or of `ρ` (Mathlib's `ModularGroup.stabilizer_of_ne`), so its
`j`-value lies in `jBranch = {j(i), j(ρ)}`. Off `jBranch`, `SL(2, ℤ)` acts with trivial stabilisers,
proper discontinuity makes `j` locally injective, and the inverse function theorem together with
transitivity on fibres gives continuous sections of `j` through every point over small discs
(`exists_section_jC`). This is the covering of `ℂ ∖ jBranch` by an open subset of `ℍ` from which the
uniformisation of `ℂ ∖ Λ` starts.

We work with `jC : ℂ → ℂ`, equal to `j` on `ℍ` and to `j(i) ∈ jBranch` elsewhere.
-/

open UpperHalfPlane ModularGroup Set Filter Topology Metric Matrix

open scoped MatrixGroups

namespace Uniformization

/-- The Möbius action of `γ ∈ SL(2, ℤ)` as a function on `ℂ` (zero off `ℍ`). -/
noncomputable def smulC (γ : SL(2, ℤ)) (z : ℂ) : ℂ := by
  classical
  exact if h : 0 < z.im then ((γ • (⟨z, h⟩ : ℍ) : ℍ) : ℂ) else 0

end Uniformization
