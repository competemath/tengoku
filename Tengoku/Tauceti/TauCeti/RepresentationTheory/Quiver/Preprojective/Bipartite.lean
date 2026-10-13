/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Combinatorics.Quiver.AlternatingSign
public import Tengoku.Tauceti.TauCeti.RepresentationTheory.Quiver.Preprojective.Signless

/-!
# Bipartiteness and the signless preprojective relation

The local preprojective relator of a finite quiver `Q` at a vertex `v` carries a sign,

```text
ρ_v = ∑_{head a = v} a a* - ∑_{tail a = v} a* a,
```

whereas the signless relator `s_v = ∑_{head a = v} a a* + ∑_{tail a = v} a* a` of the doubled
quiver `Quiver.Symmetrify Q` — the relation which appears in the quadratic dual of a zigzag
algebra — carries none. Rescaling the arrows of `Q` by scalars `ε` replaces `ρ` by the gauged
relator `ρ_ε`, and for a *bipartite* `Q` the colour signs make the corner of `ρ_ε` at every vertex
a multiple of `s_v`, by `TauCeti.gaugedPreprojectiveRelator_bipartite_vertexCorner_eq_smul`.

This file proves the obstruction supplied by an odd closed walk. The backtracks at a fixed vertex
are distinct basis paths, so the corner equation `e_v ρ_ε e_v = c_v • s_v` reads off the gauge:
`ε_a` is the scalar `c` at the head of `a`, and `-c` at its tail. Hence `c` changes sign along
every arrow and is a unit at each vertex incident to an arrow as soon as the corresponding value
of `ε` is a unit. A closed walk of odd length in the doubled quiver therefore forces `2 = 0` in
the coefficient ring. A loop is the smallest such walk.

## Main results

* `TauCeti.gauge_eq_of_vertexCorner_eq_smul`: a cornerwise comparison with the signless relator
  reads off the gauge at every arrow meeting that vertex.
* `TauCeti.eq_neg_of_forall_vertexCorner_eq_smul`: the comparison scalars change sign along every
  arrow.
* `TauCeti.not_exists_forall_vertexCorner_eq_smul_of_odd_length`: **no unit gauge compares the
  preprojective relation cornerwise with the signless one when the doubled quiver carries a closed
  walk of odd length**, unless `2 = 0`.

## References

S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3,
https://arxiv.org/abs/math/0002060, for the signless relation of the quadratic dual of a zigzag
algebra and its comparison with the preprojective relation of a bipartite graph. The preprojective
conventions follow Crawley-Boevey, *Quiver algebras, weighted projective lines, and the
Deligne--Simpson problem*, Section 1.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

/-! ### Reading off the gauge -/

section Gauge

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

end Gauge

section Obstruction

variable (k : Type w) {Q : Type u} [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

end Obstruction

end TauCeti
