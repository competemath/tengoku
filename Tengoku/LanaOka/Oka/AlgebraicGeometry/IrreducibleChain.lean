/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.AlgebraicGeometry.Noetherian
import Tengoku.LanaOka.Oka.Topology.IrreducibleChain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Chains of irreducible components in locally Noetherian Jacobson schemes

The irreducible components of a locally Noetherian scheme form a locally finite family. Hence in
a connected, locally Noetherian, Jacobson scheme (e.g. a connected scheme locally of finite type
over a field) any two closed points are linked by a chain of closed points in which consecutive
points lie in a common irreducible component.

## Main results

- `AlgebraicGeometry.Scheme.locallyFinite_irreducibleComponents`
- `AlgebraicGeometry.Scheme.reflTransGen_irreducibleComponents`
-/

open TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The irreducible components of a locally Noetherian scheme form a locally finite family. -/
theorem Scheme.locallyFinite_irreducibleComponents [IsLocallyNoetherian X] :
    LocallyFinite (fun Z : irreducibleComponents X ↦ (Z : Set X)) := by
  refine _root_.locallyFinite_irreducibleComponents fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact ⟨U, U.isOpen, hxU, noetherianSpace_of_isAffineOpen U hU⟩

/-- **Chain lemma for schemes.** In a connected, locally Noetherian, Jacobson scheme any two
closed points are linked by a chain of closed points in which consecutive points lie in a common
irreducible component. -/
theorem Scheme.reflTransGen_irreducibleComponents [IsLocallyNoetherian X] [JacobsonSpace X]
    [ConnectedSpace X] {x y : X} (hx : IsClosed {x}) (hy : IsClosed {y}) :
    Relation.ReflTransGen (fun a b : X ↦ IsClosed {a} ∧ IsClosed {b} ∧
      ∃ Z ∈ irreducibleComponents X, a ∈ Z ∧ b ∈ Z) x y :=
  JacobsonSpace.reflTransGen_irreducibleComponents X.locallyFinite_irreducibleComponents hx hy

end AlgebraicGeometry
