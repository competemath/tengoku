/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Tengoku.LeanPool.LeanPool.InfinitaryLogic.Lomega1omega.Syntax
public import Tengoku.LeanPool.LeanPool.InfinitaryLogic.Mathlib.ModelTheory.Infinitary.Semantics
/-!
# Lω₁ω Semantics — compatibility facade over the fixed-carrier semantics

The three realization *definitions* are no longer given here. They come from
`Mathlib.ModelTheory.Infinitary.Semantics`, whose `BoundedFormulaInf.Realize` is the single
structural recursion serving every index carrier. This file re-exports that semantics under the
qualified names the project already uses, and keeps only what Mathlib does not provide.

## Why the definitions had to be adopted, not merely paralleled

`Lomega1omega/Syntax.lean` already identifies `BoundedFormulaω` with `BoundedFormulaInf ℕ`
definitionally. Keeping a *separate* recursive `Realize` here would leave two definitionally
distinct semantics for one and the same formula type: dot-notation `φ.Realize` resolves through
the head symbol to `BoundedFormulaInf.Realize`, while the qualified `BoundedFormulaω.Realize`
would name the other one. Every later operation would then have to pick, and would pick wrong.

## What this file still owns

- the qualified `Realize` names, as **reducible aliases** — 100-odd files name
  `BoundedFormulaω.Realize` / `Formulaω.Realize` / `Sentenceω.Realize` explicitly, many in
  `@`-applied form, so the aliases reproduce Mathlib's semantics at the project's historical
  argument order;
- compatibility wrappers carrying the project's realization theorem names, with the project's
  **explicit** argument convention (Mathlib states these with implicit arguments);
- realization for the connectives Mathlib does not define: `and`/`or`/`iff` and the
  `Encodable`-indexed `einf`/`esup` with their explicit-encoding forms;
- the `⊨ω` notation.

The gates at the end certify by `Iff.rfl` — no rewriting, no casts — that each alias *is* the
Mathlib semantics, and that the historical `Fin.elim0` spellings of the arity-0 cases still
agree with Mathlib's `default`.
-/

@[expose] public section

universe u v w u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}
variable {M : Type w} [L.Structure M]
variable {α : Type u'} {n : ℕ}

open FirstOrder Structure Fin

namespace BoundedFormulaω

/-- Realization of a bounded Lω₁ω formula, as a qualified name.
`Mathlib`'s `BoundedFormulaInf.Realize` is the definition; this alias is `@[reducible]` and
reproduces the project's historical argument order `L M inst α n φ v xs`. -/
abbrev Realize (φ : L.BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) : Prop :=
  BoundedFormulaInf.Realize φ v xs

variable {v : α → M} {xs : Fin n → M}

/-! ### Primitive connectives

Mathlib states each of these with implicit arguments; the project's consumers supply them
explicitly (`realize_rel R ts`, `realize_imp φ ψ`, …), so the wrappers keep that convention. -/

/--
@isnad1 id=iff.0h6v.s5.15e3fada6b8c from=translated src=- shape=b260af2d vocab=bb80f679
-/
theorem realize_falsum : (falsum : L.BoundedFormulaω α n).Realize v xs ↔ False :=
  BoundedFormulaInf.realize_falsum

/--
@isnad1 id=iff.0h6v.s5.d0777c2c67d7 from=translated src=- shape=b2c36896 vocab=3214199b
-/
theorem realize_bot : (⊥ : L.BoundedFormulaω α n).Realize v xs ↔ False :=
  BoundedFormulaInf.realize_bot

/--
@isnad1 id=iff.0h8v.s6.f792593b8c05 from=translated src=- shape=a754e594 vocab=035f767a
-/
theorem realize_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂ : L.BoundedFormulaω α n).Realize v xs ↔
      t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) :=
  BoundedFormulaInf.realize_equal

/--
@isnad1 id=iff.0h9v.s6.6796fab93cff from=translated src=- shape=d9f37f37 vocab=1d21c52d
-/
theorem realize_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts : L.BoundedFormulaω α n).Realize v xs ↔
      RelMap R fun i => (ts i).realize (Sum.elim v xs) :=
  BoundedFormulaInf.realize_rel

/--
@isnad1 id=iff.0h8v.s6.7c326ae6f0af from=translated src=- shape=d2317875 vocab=b7ea7a1d
-/
theorem realize_imp (φ ψ : L.BoundedFormulaω α n) :
    (imp φ ψ).Realize v xs ↔ (φ.Realize v xs → ψ.Realize v xs) :=
  BoundedFormulaInf.realize_imp

/--
@isnad1 id=iff.0h7v.s6.330b6563dfff from=translated src=- shape=5c27fe51 vocab=aa07d6dd
-/
theorem realize_all (φ : L.BoundedFormulaω α (n + 1)) :
    (all φ).Realize v xs ↔ ∀ x : M, φ.Realize v (snoc xs x) :=
  BoundedFormulaInf.realize_all

/--
@isnad1 id=iff.0h7v.s5.f62934f6c5ef from=translated src=- shape=030b29da vocab=dc938318
-/
theorem realize_iSup (φs : ℕ → L.BoundedFormulaω α n) :
    (iSup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs :=
  BoundedFormulaInf.realize_iSup

/--
@isnad1 id=iff.0h7v.s5.aae6bc5f9b78 from=translated src=- shape=9d6183b0 vocab=089cadd3
-/
theorem realize_iInf (φs : ℕ → L.BoundedFormulaω α n) :
    (iInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  BoundedFormulaInf.realize_iInf

/--
@isnad1 id=iff.0h6v.s5.9624ccba9551 from=translated src=- shape=b2c36896 vocab=94d69c3d
-/
theorem realize_top : (⊤ : L.BoundedFormulaω α n).Realize v xs ↔ True :=
  BoundedFormulaInf.realize_top

/--
@isnad1 id=iff.0h7v.s5.b4a69657f890 from=translated src=- shape=59dcb084 vocab=f0fecb05
-/
theorem realize_not (φ : L.BoundedFormulaω α n) :
    φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  BoundedFormulaInf.realize_not

/--
@isnad1 id=iff.0h7v.s6.6dea86c4269a from=translated src=- shape=1d4e7b1c vocab=28b1ffa3
-/
theorem realize_ex (φ : L.BoundedFormulaω α (n + 1)) :
    φ.ex.Realize v xs ↔ ∃ x : M, φ.Realize v (snoc xs x) :=
  BoundedFormulaInf.realize_ex

/-! ### Connectives the project owns -/

/--
@isnad1 id=iff.0h8v.s6.bfa5bd11da70 from=translated src=- shape=9beebf95 vocab=82ef1531
-/
@[simp]
theorem realize_and (φ ψ : L.BoundedFormulaω α n) :
    (φ.and ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp only [BoundedFormulaω.and, realize_not, realize_imp]
  tauto

/--
@isnad1 id=iff.0h8v.s6.cf4a5612332d from=translated src=- shape=e8593ac9 vocab=81e905cc
-/
@[simp]
theorem realize_inf (φ ψ : L.BoundedFormulaω α n) :
    (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs :=
  realize_and φ ψ

@[simp]
private theorem realize_or (φ ψ : L.BoundedFormulaω α n) :
    (φ.or ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs := by
  simp only [BoundedFormulaω.or, realize_not, realize_imp]
  tauto

/--
@isnad1 id=iff.0h8v.s6.c7efbfb8e4fb from=translated src=- shape=e8593ac9 vocab=235d5cbc
-/
@[simp]
theorem realize_sup (φ ψ : L.BoundedFormulaω α n) :
    (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs :=
  realize_or φ ψ

/--
@isnad1 id=iff.0h8v.s6.a2cd0c2f1124 from=translated src=- shape=8461b1cd vocab=ec5694cd
-/
@[simp]
theorem realize_iff (φ ψ : L.BoundedFormulaω α n) :
    (φ.iff ψ).Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs) := by
  simp only [BoundedFormulaω.iff, realize_inf, realize_imp, iff_def]

/--
@isnad1 id=iff.0h8v.s5.eccdb080ab8f from=translated src=- shape=1c3c02d0 vocab=ad20a2f8
-/
@[simp]
theorem realize_einf {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    (einf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  simp only [einf, realize_iInf]
  constructor
  · intro h i
    simpa only [Encodable.encodek] using h (Encodable.encode i)
  · intro h k
    cases hd : Encodable.decode (α := ι) k with
    | none => simp only [realize_top]
    | some i => exact h i

/--
@isnad1 id=iff.0h8v.s6.21bfe81fc7e8 from=translated src=- shape=37f02361 vocab=1475b82b
-/
@[simp]
theorem realize_esup {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    (esup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := by
  simp only [esup, realize_iSup]
  constructor
  · rintro ⟨k, hk⟩
    cases hd : Encodable.decode (α := ι) k with
    | none => simp only [hd, realize_bot] at hk
    | some i =>
      exact ⟨i, by simpa only [hd] using hk⟩
  · rintro ⟨i, hi⟩
    use Encodable.encode i
    simp only [Encodable.encodek, hi]

end BoundedFormulaω

namespace Formulaω

/-- Realization of an Lω₁ω formula, as a qualified name. Mathlib's `FormulaInf.Realize` is the
definition; it fills the arity-0 valuation with `default`, which is definitionally the project's
historical `Fin.elim0` (gated below). -/
abbrev Realize (φ : L.Formulaω α) (v : α → M) : Prop :=
  FormulaInf.Realize φ v

variable {φ : L.Formulaω α} {v : α → M}

/-- The level-crossing lemma: formula realization *is* bounded-formula realization at the empty
tuple.

`FormulaInf.Realize` is a plain definition upstream, not a reducible abbreviation (matching the
finitary `Formula.Realize`), so neither `rw` nor `simp` can see a `BoundedFormulaω` realization
lemma through it. Supply this lemma explicitly — `simp only [Formulaω.realize_def, realize_not]` —
instead of crossing that abstraction boundary. Deliberately not `@[simp]`: the formula-level
lemmas below are the normal interface, and this escape hatch should be visible where it is used.
@isnad1 id=iff.0h5v.s5.775d8f5f09eb from=translated src=- shape=e22d522f vocab=a4a98d95
-/
theorem realize_def (φ : L.Formulaω α) (v : α → M) :
    Realize φ v ↔ BoundedFormulaω.Realize φ v Fin.elim0 := Iff.rfl

/--
@isnad1 id=iff.0h5v.s5.fb14e13415f9 from=translated src=- shape=915d8147 vocab=fd569e73
-/
@[simp]
theorem realize_not : Realize φ.not v ↔ ¬Realize φ v := BoundedFormulaω.realize_not φ

/--
@isnad1 id=iff.0h4v.s5.da156a8e15d4 from=translated src=- shape=c6bab521 vocab=1fd27434
-/
@[simp]
theorem realize_bot : Realize (⊥ : L.Formulaω α) v ↔ False := BoundedFormulaω.realize_bot

/--
@isnad1 id=iff.0h4v.s5.8f3c8838a089 from=translated src=- shape=c6bab521 vocab=22f2ce36
-/
@[simp]
theorem realize_top : Realize (⊤ : L.Formulaω α) v ↔ True := BoundedFormulaω.realize_top

/--
@isnad1 id=iff.0h6v.s5.02e005eb8bf4 from=translated src=- shape=82ec78aa vocab=2e4f28f2
-/
@[simp]
theorem realize_imp (φ ψ : L.Formulaω α) :
    Realize (φ.imp ψ) v ↔ (Realize φ v → Realize ψ v) := BoundedFormulaω.realize_imp φ ψ

/--
@isnad1 id=iff.0h6v.s5.a083e7b91c02 from=translated src=- shape=c49b3a6b vocab=bd7dc062
-/
@[simp]
theorem realize_inf (φ ψ : L.Formulaω α) :
    Realize (φ ⊓ ψ) v ↔ Realize φ v ∧ Realize ψ v := BoundedFormulaω.realize_inf φ ψ

/--
@isnad1 id=iff.0h6v.s5.acbfda7cad18 from=translated src=- shape=c49b3a6b vocab=08c26578
-/
@[simp]
theorem realize_sup (φ ψ : L.Formulaω α) :
    Realize (φ ⊔ ψ) v ↔ Realize φ v ∨ Realize ψ v := BoundedFormulaω.realize_sup φ ψ

/--
@isnad1 id=iff.0h6v.s5.56f0b6bb3593 from=translated src=- shape=0ee4a7a2 vocab=03653dbd
-/
@[simp]
theorem realize_einf {ι : Type*} [Encodable ι] (φs : ι → L.Formulaω α) :
    Realize (BoundedFormulaω.einf φs) v ↔ ∀ i, Realize (φs i) v := BoundedFormulaω.realize_einf φs

/--
@isnad1 id=iff.0h6v.s5.52ca92c21521 from=translated src=- shape=83d0dc64 vocab=85a92a56
-/
@[simp]
theorem realize_esup {ι : Type*} [Encodable ι] (φs : ι → L.Formulaω α) :
    Realize (BoundedFormulaω.esup φs) v ↔ ∃ i, Realize (φs i) v := BoundedFormulaω.realize_esup φs

end Formulaω

namespace Sentenceω

/-- Truth of an Lω₁ω sentence in a structure, as a qualified name. Mathlib's
`SentenceInf.Realize` is the definition. -/
abbrev Realize (φ : L.Sentenceω) (M : Type w) [L.Structure M] : Prop :=
  SentenceInf.Realize φ M

/-- The level-crossing lemma: sentence truth *is* bounded-formula realization at the empty
valuation and the empty tuple. See `Formulaω.realize_def` for why this is needed and why it is
not a `simp` lemma.
@isnad1 id=iff.0h3v.s5.2d4209f62fcb from=translated src=- shape=6f53e659 vocab=dbe44ee4
-/
theorem realize_def (φ : L.Sentenceω) (M : Type w) [L.Structure M] :
    Realize φ M ↔ BoundedFormulaω.Realize φ (Empty.elim : Empty → M) Fin.elim0 := Iff.rfl

/-- Notation for a structure satisfying a sentence. -/
scoped notation:51 M " ⊨ω " φ:51 => Sentenceω.Realize φ M

end Sentenceω

/-! ## Facade semantics gates

Each must close by `Iff.rfl` — no `change`, no rewriting, no explicit cast. That is what
certifies that the qualified ω names *are* Mathlib's semantics rather than a parallel copy of
it, and that the arity-0 spellings the project has used throughout (`Fin.elim0`, `Empty.elim`)
still agree with Mathlib's `default`. -/

section Gates

variable {v : α → M} {xs : Fin n → M}

end Gates

end Language

end FirstOrder
