/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Topology.Algebra.Nonarchimedean.Basic
import Tengoku.Tauceti.TauCeti.Topology.Algebra.Nonarchimedean.Pi

/-!
# The module topology on a finite module

Let `M` be a finite module over a topological ring `A`. Choosing a finite spanning family of `M`
presents it as an open quotient of `Aⁿ`, by Mathlib's
`IsModuleTopology.isOpenQuotientMap_of_surjective`, and so three properties of `A` descend to
`moduleTopology A M`: first countability, nonarchimedeanness, and — for the canonical right
uniformity, using Mathlib's completeness of a quotient of a complete first-countable additive
group — completeness.

Each theorem asks of `A` exactly what its proof consumes, and none of them needs `A` to be a
Huber or a Tate ring. Separatedness is different: it is equivalent to closedness of the kernel of
the presentation, which is a genuinely arithmetic condition, and it is proved for a complete
noetherian Tate ring in `TauCeti.RingTheory.Huber.FiniteModuleTopology`.

The topology is kept as the explicit expression `moduleTopology A M` in the statements: these are
theorem constructors for local instances, rather than global instances whose heads would hide the
topology on `M` from typeclass search.

## Main results

* `TauCeti.firstCountableTopology_moduleTopology`: the module topology on a finite module over a
  first-countable topological ring is first countable.
* `TauCeti.nonarchimedeanAddGroup_moduleTopology`: over a nonarchimedean topological ring it makes
  the additive group of the module nonarchimedean.
* `TauCeti.completeSpace_moduleTopology`: over a complete first-countable ring its canonical right
  uniformity is complete.
-/

public section

open Filter Topology
open scoped Uniformity

namespace TauCeti

variable {A : Type*} [Ring A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **The module topology on a finite module over a first-countable topological ring is first
countable.** -/
theorem firstCountableTopology_moduleTopology [TopologicalSpace A]
    [IsTopologicalRing A] [FirstCountableTopology A] :
    @FirstCountableTopology M (moduleTopology A M) := by
  let _ : TopologicalSpace M := moduleTopology A M
  have _ : IsModuleTopology A M := inferInstance
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  have hquot : IsOpenQuotientMap f := IsModuleTopology.isOpenQuotientMap_of_surjective hf
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hf y
  rw [← hquot.map_nhds_eq x]
  infer_instance

end TauCeti

end
