/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Forcing.Forcing.Material.Semantics
import Tengoku.Forcing.Forcing.Material.UnionIteration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Union iteration: the approximation formulas

The syntax layer for `Forcing/Material/UnionIteration.lean`, one formula and one realization
law per semantic component. Everything is built on the shared vocabulary — `pairDef`,
`pairMemDef`, `emptyDef`, `successorDef`, `sUnionDef` — so no notion of successor or of
general union is introduced here.

**Every realization law below is hypothesis-free and axiom-free.** Each quantifier bridge is
carrier transitivity: a value reaches the carrier through the pair entry that mentions it, and
the components of a coded pair reach it by descending the Kuratowski coding.

## The successor is quantified, not constructed

`approxStepDef` universally quantifies a candidate successor `s` and *assumes*
`successorDef k s`. It does **not** existentially build one. The difference is what keeps this
component's law standalone: an existential form would have to produce `insert k k` inside the
carrier, which is a closure fact belonging to another component, and the law would stop being
axiom-free.

The universal form costs nothing, because the forward direction instantiates `s` only when an
actual successor entry `⟨insert k k, U⟩ ∈ t` is in hand — and *that* entry supplies
`insert k k` as a carrier element by transitivity through `t`.

The base formula, by contrast, may bind its empty representative existentially: the base pair's
membership in `t` supplies `∅` structurally, for the same reason.

## Deliberately absent

No `ω`, no `MaterialGround`, no scheme instance, and no Infinity, exactly as in the semantic
layer. `IsApprox` is assembled only after all four component laws compile.
-/

universe u v

namespace Forcing

open FirstOrder Language UnionIteration

/-- The bounded-domain condition, as a formula.-/
def inApproxDomainDef {α : Type v} {m : ℕ} (n k : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  memFormula k n ⊔ (k =' n)

/-- **Bounded no-junk support**, as a formula.-/
def approxSupportDef {α : Type v} {m : ℕ} (n t : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  ∀' (memFormula (&(Fin.last m)) (liftTerm t) ⟹
    ∃' ∃' (pairDef (&(Fin.castSucc (Fin.last (m + 1)))) (&(Fin.last (m + 2)))
        (&(Fin.castSucc (Fin.castSucc (Fin.last m)))) ⊓
      inApproxDomainDef (liftTerm (liftTerm (liftTerm n)))
        (&(Fin.castSucc (Fin.last (m + 1))))))

/-- **Totality and functionality**, as a formula.-/
def approxTotalFunctionalDef {α : Type v} {m : ℕ} (n t : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  ∀' (inApproxDomainDef (liftTerm n) (&(Fin.last m)) ⟹
    ∃' (pairMemDef (&(Fin.castSucc (Fin.last m))) (&(Fin.last (m + 1)))
        (liftTerm (liftTerm t)) ⊓
      ∀' (pairMemDef (&(Fin.castSucc (Fin.castSucc (Fin.last m)))) (&(Fin.last (m + 2)))
          (liftTerm (liftTerm (liftTerm t))) ⟹
        (&(Fin.last (m + 2)) =' &(Fin.castSucc (Fin.last (m + 1)))))))

/-- **The base value**, as a formula. The empty representative is bound existentially; the
base pair's membership in `t` supplies it structurally.-/
def approxBaseDef {α : Type v} {m : ℕ} (seed t : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  ∃' (emptyDef (&(Fin.last m)) ⊓
    pairMemDef (&(Fin.last m)) (liftTerm seed) (liftTerm t))

/-- **The recurrence**, as a formula. The candidate successor `s` is **universally quantified
under `successorDef k s`**, never constructed — see the module docstring.-/
def approxStepDef {α : Type v} {m : ℕ} (n t : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  ∀' (memFormula (&(Fin.last m)) (liftTerm n) ⟹
    ∀' (successorDef (&(Fin.castSucc (Fin.last m))) (&(Fin.last (m + 1))) ⟹
      ∀' ∀' (pairMemDef (&(Fin.castSucc (Fin.castSucc (Fin.castSucc (Fin.last m)))))
            (&(Fin.castSucc (Fin.last (m + 2)))) (liftTerm (liftTerm (liftTerm (liftTerm t)))) ⟹
        (pairMemDef (&(Fin.castSucc (Fin.castSucc (Fin.last (m + 1)))))
            (&(Fin.last (m + 3))) (liftTerm (liftTerm (liftTerm (liftTerm t)))) ⟹
          sUnionDef (&(Fin.castSucc (Fin.last (m + 2)))) (&(Fin.last (m + 3)))))))

/-- **An approximation**, as a formula: the conjunction of the four components.-/
def isApproxDef {α : Type v} {m : ℕ} (seed n t : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  approxSupportDef n t ⊓ (approxTotalFunctionalDef n t ⊓
    (approxBaseDef seed t ⊓ approxStepDef n t))

/-- **Prefix agreement**, as a formula: the induction predicate for uniqueness. Parameters are
the final bound, the two traces; the separated variable is the prefix bound.-/
def approxAgreeFormula : memLang.BoundedFormula (Fin 3) 1 :=
  inApproxDomainDef (var (Sum.inl 0)) (&(0 : Fin 1)) ⟹
    ∀' (inApproxDomainDef (liftTerm (&(0 : Fin 1))) (&(Fin.last 1)) ⟹
      ∀' ∀' (pairMemDef (&(Fin.castSucc (Fin.castSucc (Fin.last 1))))
            (&(Fin.castSucc (Fin.last 2)))
            (liftTerm (liftTerm (liftTerm (var (Sum.inl 1))))) ⟹
        (pairMemDef (&(Fin.castSucc (Fin.castSucc (Fin.last 1)))) (&(Fin.last 3))
            (liftTerm (liftTerm (liftTerm (var (Sum.inl 2))))) ⟹
          (&(Fin.castSucc (Fin.last 2)) =' &(Fin.last 3)))))

/-! ### The iteration relation

`UnionIterate` is **carrier-relative by definition**, which is why it lives here rather than
in the Mathlib-only semantic module: the witnessing trace must belong to `M`.

That relativity is not incidental. `unionIterateDef` quantifies only over carrier elements,
and `isApprox_unique` compares *internal* traces; a relation permitting an arbitrary external
trace would make the realization law one-directional, since a formula can never produce a
witness outside the carrier. -/

/-- `S` is the `n`-th union iterate of `seed`, witnessed by a trace **inside `M`**.-/
def UnionIterate (M : MaterialCarrier.{u}) (seed n S : ZFSet.{u}) : Prop :=
  ∃ t, t ∈ M ∧ UnionIteration.IsApprox seed n t ∧ ZFSet.pair n S ∈ t

/-- **The iteration relation**, as a formula: the direct existential. No set of traces is
constructed, so the later gather/filter stage gets an exact, internally meaningful provenance
predicate rather than a family to sift.-/
def unionIterateDef {α : Type v} {m : ℕ} (seed n S : memLang.Term (α ⊕ Fin m)) :
    memLang.BoundedFormula α m :=
  ∃' (isApproxDef (liftTerm seed) (liftTerm n) (&(Fin.last m)) ⊓
    pairMemDef (liftTerm n) (liftTerm S) (&(Fin.last m)))

/-- **Approximation existence**, as a formula: the induction predicate for existence. The seed
is the parameter; the separated variable is the bound.-/
def approxExistsFormula : memLang.BoundedFormula (Fin 1) 1 :=
  ∃' (isApproxDef (liftTerm (var (Sum.inl 0))) (liftTerm (&(0 : Fin 1))) (&(Fin.last 1)))

section Realization

variable {α : Type v} {m : ℕ} {M : MaterialCarrier.{u}} {v : α → M} {xs : Fin m → M}

open MaterialCarrier

end Realization

end Forcing
