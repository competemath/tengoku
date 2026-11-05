/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Config.Multiplication
import Tengoku.AclGeom.AclGeom.Transfer.Lift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lifting and reflecting configurations along `ι : K →ₐ[k] Ω`

The configuration predicates `IsPartialQuadrangle`, `Ψ`, `QGeom`, `MulDiagram` and `Q′Geom` along
the lift of points `liftPoint` of `AclGeom.Transfer.Lift`, over a base `K₀` of elements algebraic
over `k`.

* **Lift** (`K/k → Ω/K₀`; preserved from the independently checked point-descent draft):
  `IsPartialQuadrangle.lift`, `QWitness.lift`, `QWitness.PsiCore.lift`,
  `QWitness.Psi.lift`, `QGeom.lift`,
  `MulDiagram.lift`, `Q'Geom.lift`.
* **Reflection** (`Ω/K₀ → K/k`, for configurations of lifted points): `IsPartialQuadrangle.of_lift`,
  `MulDiagram.of_lift`, `QWitness.Psi.of_lift` (with explicitly lifted clause-(vi) witnesses) and
  `QGeom.of_lift_witness`. These provide explicit-instance reflection for the #25
  `Counterexamples.QDescent` consumer, with the clause-(vi) witnesses supplied over `K`.

The module needs only the lift of `AclGeom.Transfer.Lift` and the configuration language; no
completeness hypothesis (`JAssembly`) enters.

**Status:** the listed lifts and explicit-instance reflections are proved.
`Counterexamples.QDescent` uses them in the concrete #25 refutations, proved in
`Counterexamples.QRefutation`.
`Transfer.JCorrectness` proves the source's four-way `J` theorem, and
`Transfer.ProjectedConfigurations` proves corrected projected `Q`/`Q′` equivalences.
No separate general raw existential-witness descent theorem is stated in the source.
That exploratory question is unresolved; none is asserted here.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra k K]
  [Algebra k Ω] {K₀ : IntermediateField k Ω}
  (halg : ∀ y ∈ K₀, IsAlgebraic k y) (ι : K →ₐ[k] Ω)

include halg

namespace QWitness

/-- The lift of a `Q`-witness: all twenty-one points lifted.-/
def lift (w : QWitness k K) : QWitness (↥K₀) Ω where
  A₁ := liftPoint halg ι w.A₁
  A₂ := liftPoint halg ι w.A₂
  B₁ := liftPoint halg ι w.B₁
  B₂ := liftPoint halg ι w.B₂
  C₁ := liftPoint halg ι w.C₁
  C₂ := liftPoint halg ι w.C₂
  D := liftPoint halg ι w.D
  E := liftPoint halg ι w.E
  F := liftPoint halg ι w.F
  G := liftPoint halg ι w.G
  H := liftPoint halg ι w.H
  I := liftPoint halg ι w.I
  P := liftPoint halg ι w.P
  Q := liftPoint halg ι w.Q
  R := liftPoint halg ι w.R
  S := liftPoint halg ι w.S
  T := liftPoint halg ι w.T
  U := liftPoint halg ι w.U
  X := liftPoint halg ι w.X
  Y := liftPoint halg ι w.Y
  Z := liftPoint halg ι w.Z

variable (w : QWitness k K)

end QWitness

/-! ### Reflection along the lift

The converses of the lifts above, for configurations whose points are all lifts of points of `K/k`.
Rank, order, join and meet clauses reflect because the lift is an order embedding that preserves
joins, meets (for algebraically closed `Ω`) and exact rank.  The universal atom clauses of `Ψ(iv)`
reflect by instantiating the `Ω`-statement at lifted atoms.  The existential clause `Ψ(vi)` is NOT
reflected in general: its partial-quadrangle witnesses must be supplied as lifts (`hq`).  No
general descent of witnesses is claimed. -/

namespace QWitness

end QWitness

end

end AclGeom
