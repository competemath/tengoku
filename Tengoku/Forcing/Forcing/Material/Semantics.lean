/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Seed.ModelTheory.Semantics
import Tengoku.Forcing.Forcing.Name.MemLang
import Tengoku.Forcing.Forcing.Material.Extension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Membership semantics on material carriers

The audited carrier semantics of ADR 0003, exposed cleanly: the membership-language structure
on a material carrier (a **scoped** instance — available to everything that opens `Forcing`,
never leaking as a global default), the name-to-extension-value helper (`extVal`), and the
carrier-quantifier bridge (`forall_extensionCarrier_iff_names`) — quantification over the
extension carrier *is* quantification over the internal names, through
`mem_extensionCarrier_iff`.

This module is the `Semantics`-side counterpart of the Syntax-only `MemLang`: per the ADR's
normative import boundary, `Mathlib.ModelTheory.Semantics` enters here and nowhere below the
truth layer.

## Main definitions

* the scoped `memLang.Structure` instance on material carriers;
* `Forcing.InternalNamePresentation.extVal`: a name's value as a carrier element.

## Main results

* `Forcing.InternalNamePresentation.realize_term_extVal`: term realization is `extVal` of
  `evalTerm`.
* `Forcing.InternalNamePresentation.forall_extensionCarrier_iff_names`: the
  carrier-quantifier bridge.
* `Forcing.realize_unorderedPairDef`, `Forcing.realize_pairDef`, `Forcing.realize_pairMemDef`:
  the pair-builder laws.
* `Forcing.realize_emptyDef`, `Forcing.realize_successorDef`, `Forcing.realize_sUnionDef`,
  `Forcing.realize_transitiveDef`: the set-operation laws. All hypothesis-free and axiom-free
  — every quantifier bridge is carrier transitivity.
-/

universe u v

namespace Forcing

open FirstOrder PName

/-- Membership semantics on a material carrier: the single relation is `ZFSet` membership of
the underlying elements. Scoped, so it never becomes a global default.-/
scoped instance (M : MaterialCarrier.{u}) : memLang.Structure M where
  funMap f _ := f.elim
  RelMap := fun r x ↦ match r with | .mem => (x 0 : ZFSet) ∈ (x 1 : ZFSet)

/-- The membership relation is interpreted as `ZFSet` membership of the underlying
elements.
@isnad1 id=iff.0h2v.s6.f803e26ed400 from=translated src=- shape=0aab7dae vocab=f5a31b88
-/
@[simp] theorem relMap_mem {M : MaterialCarrier.{u}} {x : Fin 2 → M} :
    Language.Structure.RelMap (L := memLang) memRel.mem x ↔ (x 0 : ZFSet.{u}) ∈ (x 1 : ZFSet.{u}) :=
  Iff.rfl

/-! ### Realization of the pair formulas

The pair builders of the language layer, realized in a material carrier. **No theory axiom is
consumed**: every intermediate set the backward directions need is already a member of a
member of the carrier, so **transitivity** supplies it. Pairing becomes a construction cost
only when an existence proof must build genuinely new sets. -/

section PairRealization

variable {M : MaterialCarrier.{u}} {α : Type v} {n : ℕ} {x y z : memLang.Term (α ⊕ Fin n)}
variable {v : α → M} {xs : Fin n → M}

/--
@isnad1 id=eq.0h7v.s7.14e99131f477 from=translated src=- shape=b2b24f6f vocab=ddd55010
-/
theorem realize_liftTerm (t : memLang.Term (α ⊕ Fin n)) (w : M) :
    Language.Term.realize (Sum.elim v (Fin.snoc xs w)) (liftTerm t) =
      Language.Term.realize (Sum.elim v xs) t := by
  rw [liftTerm, Language.Term.realize_relabel]
  congr 1
  funext i
  cases i with
  | inl a => rfl
  | inr i => simp

/-! ### Set-operation laws

Realization for the function-free vocabulary. All three are **hypothesis-free and axiom-free**:
each quantifier bridge is transitivity of the carrier, since the sets involved are members of
carrier elements. -/

end PairRealization

namespace InternalNamePresentation

variable {M : MaterialCarrier.{u}} {P : Type u} {N : InternalNamePresentation M P}
variable {S : Set P}

/-- A name of the family, as an element of the extension carrier.-/
def extVal (N : InternalNamePresentation M P) (S : Set P) (τ : PName P) (hτ : τ ∈ N.names) :
    N.extensionCarrier S :=
  ⟨zval S τ, N.mem_extensionCarrier_of_mem_of_zval_eq hτ rfl⟩

/--
@isnad1 id=eq.1h5v.s5.e007f2b8da0f from=translated src=- shape=f309cca8 vocab=6f57e479
-/
@[simp] theorem coe_extVal {τ : PName P} (hτ : τ ∈ N.names) :
    (N.extVal S τ hτ : ZFSet.{u}) = zval S τ :=
  rfl

/-- Realization of a function-free term along `extVal`-valued assignments is `extVal` of the
syntactic evaluation.
@isnad1 id=eq.1h7v.s6.097aabdf9e65 from=translated src=- shape=feaef833 vocab=cd2ceaf9
-/
theorem realize_term_extVal {γ : Type v} {a : γ → PName P} (ha : ∀ g, a g ∈ N.names) :
    ∀ t : memLang.Term γ,
      (Language.Term.realize (M := N.extensionCarrier S)
        (fun g ↦ N.extVal S (a g) (ha g)) t) = N.extVal S (evalTerm a t) (evalTerm_mem ha t)
  | .var _ => rfl
  | .func f _ => f.elim

/-- **The carrier-quantifier bridge**: quantification over the extension carrier is
quantification over the internal names — every carrier element is the value of a decoded
name, and every name's value lands in the carrier.
@isnad1 id=iff.0h5v.s6.900572b22449 from=translated src=- shape=9077cd95 vocab=02bc47c0
-/
theorem forall_extensionCarrier_iff_names (Φ : N.extensionCarrier S → Prop) :
    (∀ x, Φ x) ↔ ∀ τ, ∀ hτ : τ ∈ N.names, Φ (N.extVal S τ hτ) := by
  constructor
  · exact fun h τ hτ ↦ h _
  · rintro h ⟨x, hx⟩
    obtain ⟨i, rfl⟩ := N.mem_extensionCarrier_iff.1 hx
    exact h (N.decode i) (N.decode_mem_names i)

end InternalNamePresentation

end Forcing
