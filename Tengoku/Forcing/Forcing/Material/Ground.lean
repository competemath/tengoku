/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Forcing.Forcing.Material.Semantics

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Material grounds: the model-bearing interface

A `MaterialGround T` is a material carrier that **models the theory `T`** in the membership
language. The theory is an **explicit parameter**, never a stored field and never silently
fixed to ZFC: every downstream theorem then states which axioms it consumes, and the
per-axiom preservation ledger of the later ZFC work is literal rather than rhetorical. This
is the name reserved since the carrier layer was introduced, spent now on exactly the
interface it was held for.

The membership structure is **derived** from the carrier (the scoped instance of
`Forcing/Material/Semantics.lean`), not duplicated here; so is membership itself, through
`SetLike`. Nothing else is stored: no visibility context, no internal names, no forcing
presentation, no countability, no closure operations — each of those is a separate layer
relative to a ground, exactly as the carrier layer intended.

**Model satisfaction does not produce internal codes.** A ground satisfying `T` says that
sentences of `T` are realized; it does *not* by itself hand back Lean-level codes for
conditions, names, assignments, or formulas, nor absoluteness statements about them. Those
require explicit coding and absoluteness theorems, derived from **named axioms** of `T` — and
must never be added here as convenience fields.

Nonemptiness is a case in point, and the first dividend of theory-indexing: it is not a field
and not a typeclass assumption, but an *axiom*. A ground of `memLang.nonemptyTheory` has a
nonempty domain (`nonempty_of_nonemptyTheory`), and grounds of theories not containing it
simply do not.

## Main definitions

* `Forcing.MaterialGround`: a material carrier modelling a theory of the membership language.

## Main results

* `Forcing.MaterialGround.realize_of_mem`: the per-axiom accessor — the ledger tool.
* `Forcing.MaterialGround.mono`: a ground of a theory is a ground of any subtheory.
* `Forcing.MaterialGround.nonempty_of_nonemptyTheory`: nonemptiness as an axiom, not a field.
-/

universe u

namespace Forcing

open FirstOrder

/-- A material carrier modelling the theory `T` of the membership language. `T` is an
explicit parameter: no theory is silently fixed, and each downstream theorem names the axioms
it consumes. The membership structure and membership itself are derived from the carrier.-/
structure MaterialGround (T : memLang.Theory) extends MaterialCarrier.{u} where
  /-- The carrier models `T`.-/
  models : ↥toMaterialCarrier ⊨ T

namespace MaterialGround

variable {T T' : memLang.Theory}

/-- Membership is the carrier's membership — derived, not duplicated.-/
instance : SetLike (MaterialGround.{u} T) ZFSet.{u} where
  coe M := {x | x ∈ M.toMaterialCarrier}
  coe_injective := by
    rintro ⟨M, hM⟩ ⟨N, hN⟩ h
    congr 1
    exact SetLike.coe_injective h

/--
@isnad1 id=iff.0h3v.s5.89b928176cd9 from=translated src=- shape=d8121f0a vocab=e90efae9
-/
@[simp] theorem mem_toMaterialCarrier {M : MaterialGround.{u} T} {x : ZFSet.{u}} :
    x ∈ M.toMaterialCarrier ↔ x ∈ M :=
  Iff.rfl

/--
@isnad1 id=eq.1h3v.s5.c1e9fc2feff7 from=translated src=- shape=76c08729 vocab=4c1f37ab
-/
@[ext] theorem ext {M N : MaterialGround.{u} T} (h : ∀ x, x ∈ M ↔ x ∈ N) : M = N :=
  SetLike.ext h

/-- Transitivity, inherited from the carrier.
@isnad1 id=mem.2h4v.s5.817bf1fba0ae from=translated src=- shape=c3de87c3 vocab=4c1f37ab
-/
theorem mem_trans {M : MaterialGround.{u} T} {x y : ZFSet.{u}} (hxy : x ∈ y) (hyM : y ∈ M) :
    x ∈ M :=
  M.toMaterialCarrier.mem_trans hxy hyM

/-- The satisfaction of `T` is available to instance search wherever the ground is.
@isnad1 id=model.0h2v.s4.657363df0793 from=translated src=- shape=c3628a37 vocab=b8410198
-/
instance instModel (M : MaterialGround.{u} T) : ↥M.toMaterialCarrier ⊨ T :=
  M.models

/-- **The per-axiom accessor**: each axiom of `T` is realized in the ground. The ledger tool —
downstream theorems cite the axioms they consume through this.
@isnad1 id=realize.1h3v.s5.7638f32afec7 from=translated src=- shape=2fa27ab6 vocab=2f0a1006
-/
theorem realize_of_mem (M : MaterialGround.{u} T) {φ : memLang.Sentence} (hφ : φ ∈ T) :
    ↥M.toMaterialCarrier ⊨ φ :=
  Language.Theory.realize_sentence_of_mem T hφ

/-- **Theory weakening**: a ground of `T` is a ground of every subtheory. Consuming fewer
axioms is a weaker hypothesis, and the interface says so.-/
def mono (M : MaterialGround.{u} T) (h : T' ⊆ T) : MaterialGround.{u} T' :=
  ⟨M.toMaterialCarrier, ⟨fun _ hφ ↦ M.realize_of_mem (h hφ)⟩⟩

/--
@isnad1 id=eq.1h3v.s4.3415be94812a from=translated src=- shape=e6231abb vocab=6b551347
-/
@[simp] theorem toMaterialCarrier_mono (M : MaterialGround.{u} T) (h : T' ⊆ T) :
    (M.mono h).toMaterialCarrier = M.toMaterialCarrier :=
  rfl

/-- **Nonemptiness is an axiom, not a field**: a ground of a theory containing
`memLang.nonemptyTheory` has a nonempty domain. The first dividend of theory-indexing.
@isnad1 id=nonempty.1h2v.s5.8fb7758d4a77 from=translated src=- shape=cfca3cf5 vocab=3ddbbe9a
-/
theorem nonempty_of_nonemptyTheory (M : MaterialGround.{u} T)
    (h : memLang.nonemptyTheory ⊆ T) : Nonempty ↥M.toMaterialCarrier :=
  (Language.model_nonemptyTheory_iff memLang).1 ⟨fun _ hφ ↦ M.realize_of_mem (h hφ)⟩

/-!
### Sanity examples

The theory is genuinely a parameter: over the empty theory every carrier is a ground — the
degenerate case is admitted honestly rather than excluded by fiat — while nonemptiness must
be *asked for*, and is then available as a theorem.
-/

end MaterialGround

end Forcing
