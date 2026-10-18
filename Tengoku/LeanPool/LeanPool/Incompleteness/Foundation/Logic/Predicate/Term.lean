/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Logic.Predicate.Language
public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Vorspiel.Collection
public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Vorspiel.Vorspiel
public import Tengoku

/-!
# Terms of first-order logic

This file defines the terms of first-order logic.

The bounded variables are denoted by `#x` for `x : Fin n`, and free variables are denoted by `&x`
for `x : ξ`.
`t : Semiterm L ξ n` is a (semi-)term of language `L` with bounded variables of `Fin n` and free
variables of `ξ`.

-/

@[expose] public section
open scoped LO.FirstOrder.Language


namespace LO

namespace FirstOrder

/-- Imported declaration from the Incompleteness formalization. -/
inductive Semiterm (L : Language) (ξ : Type*) (n : ℕ)
  | bvar : Fin n → Semiterm L ξ n
  | fvar : ξ → Semiterm L ξ n
  | func : ∀ {arity}, L.Func arity → (Fin arity → Semiterm L ξ n) → Semiterm L ξ n

/-- Imported declaration from the Incompleteness formalization. -/
scoped prefix:max "&" => Semiterm.fvar
/-- Imported declaration from the Incompleteness formalization. -/
scoped prefix:max "#" => Semiterm.bvar

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Term (L : Language) (ξ : Type*) := Semiterm L ξ 0

/-- Imported declaration from the Incompleteness formalization. -/
abbrev SyntacticSemiterm (L : Language) (n : ℕ) := Semiterm L ℕ n

/-- Imported declaration from the Incompleteness formalization. -/
abbrev SyntacticTerm (L : Language) := SyntacticSemiterm L 0

namespace Semiterm

variable {L L' L₁ L₂ L₃ : Language} {ξ ξ' ξ₁ ξ₂ ξ₃ : Type*} {n n₁ n₂ n₃ : ℕ}

instance [Inhabited ξ] : Inhabited (Semiterm L ξ n) := ⟨&default⟩

section «lp_section_1»

variable [∀ k, ToString (L.Func k)] [ToString ξ]

/-- Imported declaration from the Incompleteness formalization. -/
def toStr : Semiterm L ξ n → String
  | #x                        => "x_{" ++ toString (n - 1 - (x : ℕ)) ++ "}"
  | &x                        => "z_{" ++ toString x ++ "}"
  | func (arity := 0) c _     => toString c
  | func (arity := _ + 1) f v =>
    "{" ++ toString f ++ "} \\left(" ++ String.vecToStr (fun i => toStr (v i)) ++ "\\right)"

instance : Repr (Semiterm L ξ n) := ⟨fun t _ => toStr t⟩

instance : ToString (Semiterm L ξ n) := ⟨toStr⟩

end «lp_section_1»

section «lp_section_2»

variable [∀ k, DecidableEq (L.Func k)] [DecidableEq ξ]

/-- Imported declaration from the Incompleteness formalization. -/
def hasDecEq : (t u : Semiterm L ξ n) → Decidable (Eq t u)
  | #x,                   #y                   => by simp only [bvar.injEq]; exact decEq x y
  | #_,                   &_                   => isFalse (by intro h; cases h)
  | #_,                   func _ _             => isFalse (by intro h; cases h)
  | &_,                   #_                   => isFalse (by intro h; cases h)
  | &x,                   &y                   => by simp only [fvar.injEq]; exact decEq x y
  | &_,                   func _ _             => isFalse (by intro h; cases h)
  | func _ _,             #_                   => isFalse (by intro h; cases h)
  | func _ _,             &_                   => isFalse (by intro h; cases h)
  | @func L ξ _ k₁ r₁ v₁, @func L ξ _ k₂ r₂ v₂ => by
      by_cases e : k₁ = k₂
      · rcases e with rfl
        exact match decEq r₁ r₂ with
        | isTrue h => by
          subst r₂
          simp only [func.injEq, heq_eq_eq, true_and]
          exact Matrix.decVec _ _ (fun i => hasDecEq (v₁ i) (v₂ i))
        | isFalse h => isFalse (by simp[h])
      · exact isFalse (by simp[e])

instance : DecidableEq (Semiterm L ξ n) := hasDecEq

end «lp_section_2»

/-- Imported declaration from the Incompleteness formalization. -/
def complexity : Semiterm L ξ n → ℕ
  | #_       => 0
  | &_       => 0
  | func _ v => Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1

/--
@isnad1 id=eq.0h4v.s4.e915c647819f from=translated src=- shape=13efc257 vocab=8eb76d59
-/
@[simp] lemma complexity_bvar (x : Fin n) : (#x : Semiterm L ξ n).complexity = 0 := rfl

/--
@isnad1 id=eq.0h4v.s4.ac84e9bd9cbd from=translated src=- shape=9668a1ec vocab=5630929a
-/
@[simp] lemma complexity_fvar (x : ξ) : (&x : Semiterm L ξ n).complexity = 0 := rfl

/--
@isnad1 id=eq.0h6v.s6.257bd8929fe5 from=translated src=- shape=e132b45a vocab=a501569f
-/
lemma complexity_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).complexity = Finset.sup Finset.univ (fun i ↦ complexity (v i)) + 1 :=
  rfl

/--
@isnad1 id=lt.0h7v.s5.fe4ee9c948d6 from=translated src=- shape=e13b668a vocab=5c9f5c53
-/
@[simp] lemma complexity_func_lt {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) (i) :
    (v i).complexity < (func f v).complexity := by
  rw [complexity_func]
  exact Nat.lt_succ_of_le <| Finset.le_sup (f := fun i ↦ complexity (v i)) (by simp)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev «func!» (k) (f : L.Func k) (v : Fin k → Semiterm L ξ n) := func f v

/-- Imported declaration from the Incompleteness formalization. -/
def bv : Semiterm L ξ n → Finset (Fin n)
  | #x       => {x}
  | &_       => ∅
  | func _ v => .biUnion .univ fun i ↦ bv (v i)

/--
@isnad1 id=eq.0h4v.s5.7d1b0fb99c90 from=translated src=- shape=d9c983d3 vocab=15d71ae6
-/
@[simp] lemma bv_bvar : (#x : Semiterm L ξ n).bv = {x} := rfl

/--
@isnad1 id=eq.0h4v.s4.42959ebd0e53 from=translated src=- shape=2b054029 vocab=51ad6810
-/
@[simp] lemma bv_fvar : (&x : Semiterm L ξ n).bv = ∅ := rfl

/--
@isnad1 id=eq.0h6v.s5.6a2a6f6cf1af from=translated src=- shape=cd913bc7 vocab=03f07a5e
-/
lemma bv_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).bv = .biUnion .univ fun i ↦ bv (v i) :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.4e6d854bcaf5 from=translated src=- shape=e25db4cf vocab=bedf8518
-/
@[simp] lemma bv_constant (f : L.Func 0) (v : Fin 0 → Semiterm L ξ n) : (func f v).bv = ∅ := rfl

/-- Imported declaration from the Incompleteness formalization. -/
def Positive (t : Semiterm L ξ (n + 1)) : Prop := ∀ x ∈ t.bv, 0 < x

namespace Positive

/--
@isnad1 id=iff.0h4v.s6.0634490aff09 from=translated src=- shape=73e510ad vocab=9e14fac1
-/
@[simp] protected lemma bvar : Positive (#x : Semiterm L ξ (n + 1)) ↔ 0 < x := by simp[Positive]

/--
@isnad1 id=positive.0h4v.s4.5e08a8751c98 from=translated src=- shape=cb82a1ca vocab=cd5f3184
-/
@[simp] protected lemma fvar : Positive (&x : Semiterm L ξ (n + 1)) := by simp[Positive]

/--
@isnad1 id=iff.0h6v.s6.b256ca710a66 from=translated src=- shape=92abe477 vocab=0890a647
-/
@[simp] protected lemma func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ (n + 1)) :
    Positive (func f v) ↔ ∀ i, Positive (v i) := by
  constructor
  · intro h i x hx
    exact h x (by
      rw [bv_func]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
  · intro h x hx
    rw [bv_func] at hx
    rcases Finset.mem_biUnion.mp hx with ⟨i, _, hi⟩
    exact h i x hi

end Positive

/--
@isnad1 id=eq.1h3v.s5.3d6b0bc6461c from=translated src=- shape=e39ecf8c vocab=dbc71e2a
-/
lemma bv_eq_empty_of_positive {t : Semiterm L ξ 1} (ht : t.Positive) : t.bv = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr <| by
    intro x hx
    rw [Fin.eq_zero x] at hx
    exact (Nat.lt_irrefl 0) (ht 0 hx)

section «lp_section_3»

variable [DecidableEq ξ]

/-- Imported declaration from the Incompleteness formalization. -/
def freeVariables : Semiterm L ξ n → Finset ξ
  | #_       => ∅
  | &x       => {x}
  | func _ v => .biUnion .univ fun i ↦ freeVariables (v i)

/--
@isnad1 id=eq.0h4v.s4.29f280720a5f from=translated src=- shape=d642905c vocab=b3b9e9b1
-/
@[simp] lemma freeVariables_bvar : (#x : Semiterm L ξ n).freeVariables = ∅ := rfl

/--
@isnad1 id=eq.0h4v.s4.f05e1e3cd91c from=translated src=- shape=b746f2dd vocab=e7ad7c51
-/
@[simp] lemma freeVariables_fvar : (&x : Semiterm L ξ n).freeVariables = {x} := rfl

/--
@isnad1 id=eq.0h6v.s5.3298f8eef9af from=translated src=- shape=c11c37e9 vocab=ea7f0299
-/
lemma freeVariables_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables := rfl

/--
@isnad1 id=eq.0h5v.s5.c64271935cc8 from=translated src=- shape=fcded73c vocab=8267bceb
-/
@[simp] lemma freeVariables_constant (f : L.Func 0) (v : Fin 0 → Semiterm L ξ n) :
    (func f v).freeVariables = ∅ :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.82c0941ec1dc from=translated src=- shape=e74a6ad1 vocab=1c89eb40
-/
@[simp] lemma freeVariables_empty {ο : Type*} [IsEmpty ο] {t : Semiterm L ο n} :
    t.freeVariables = ∅ := by ext x; exact IsEmpty.elim inferInstance x

/-- Imported declaration from the Incompleteness formalization. -/
abbrev «FVar?» (t : Semiterm L ξ n) (x : ξ) : Prop := x ∈ t.freeVariables

@[simp] lemma «fvar?_bvar» (x z) : ¬(#x : Semiterm L ξ n).FVar? z := by simp [FVar?]

@[simp] lemma «fvar?_fvar» (x z) : (&x : Semiterm L ξ n).FVar? z ↔ x = z := by simp [FVar?, Eq.comm]

@[simp] lemma «fvar?_func» (x) {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    (func f v).FVar? x ↔ ∃ i, (v i).FVar? x := by simp [FVar?, freeVariables_func]

end «lp_section_3»

section «lp_section_4»

variable (Φ : L₁ →ᵥ L₂)

/-- Imported declaration from the Incompleteness formalization. -/
def lMap (Φ : L₁ →ᵥ L₂) : Semiterm L₁ ξ n → Semiterm L₂ ξ n
  | #x       => #x
  | &x       => &x
  | func f v => func (Φ.func f) (fun i => lMap Φ (v i))

/--
@isnad1 id=eq.0h6v.s5.862ce53a59d7 from=translated src=- shape=e3e1843d vocab=29f320a8
-/
@[simp] lemma lMap_bvar (x : Fin n) : (#x : Semiterm L₁ ξ n).lMap Φ = #x := rfl

/--
@isnad1 id=eq.0h6v.s5.2b6a29ab8cb6 from=translated src=- shape=fc8c9dba vocab=84d4993c
-/
@[simp] lemma lMap_fvar (x : ξ) : (&x : Semiterm L₁ ξ n).lMap Φ = &x := rfl

/--
@isnad1 id=eq.0h8v.s6.567aebc1fda3 from=translated src=- shape=ecffcaeb vocab=e85add70
-/
lemma lMap_func {k} (f : L₁.Func k) (v : Fin k → Semiterm L₁ ξ n) :
    (func f v).lMap Φ = func (Φ.func f) (fun i ↦ lMap Φ (v i)) := rfl

/--
@isnad1 id=iff.0h6v.s5.aadcae24f46b from=translated src=- shape=5434031d vocab=7de2f631
-/
@[simp] lemma lMap_positive (t : Semiterm L₁ ξ (n + 1)) : (t.lMap Φ).Positive ↔ t.Positive := by
  induction t <;> simp [lMap_func, *]

/--
@isnad1 id=eq.0h6v.s5.0b10d1eba291 from=translated src=- shape=2e07814e vocab=7c614875
-/
@[simp] lemma freeVariables_lMap [DecidableEq ξ] (Φ : L₁ →ᵥ L₂) (t : Semiterm L₁ ξ n) :
    (Semiterm.lMap Φ t).freeVariables = t.freeVariables := by
  induction t
  case bvar => simp
  case fvar => simp
  case func k f v ih =>
    ext x; simp [lMap_func, freeVariables_func, ih]

end «lp_section_4»

section «lp_section_5»

variable [L.ConstantInhabited]

instance : Inhabited (Semiterm L ξ n) := ⟨func default ![]⟩

/--
@isnad1 id=eq.0h3v.s5.29de8db4ab43 from=translated src=- shape=9bdb9d50 vocab=d997d066
-/
lemma default_def : (default : Semiterm L ξ n) = func default ![] := rfl

end «lp_section_5»

end Semiterm

end FirstOrder

end LO
