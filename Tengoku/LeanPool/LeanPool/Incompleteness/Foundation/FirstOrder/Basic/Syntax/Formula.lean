/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Logic.Predicate.Term
public import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Logic.Predicate.Quantifier
public import Tengoku

/-!
# Formulas of first-order logic

This file defines the formulas of first-order logic.

`φ : Semiformula L ξ n` is a (semi-)formula of language `L` with bounded variables of `Fin n` and
free variables of `ξ`.
The quantification is represented by de Bruijn index.

-/

@[expose] public section

namespace LO

namespace FirstOrder

/-- Imported declaration from the Incompleteness formalization. -/
inductive Semiformula (L : Language) (ξ : Type*) : ℕ → Type _ where
  | verum  {n} : Semiformula L ξ n
  | falsum {n} : Semiformula L ξ n
  | rel    {n} : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  | nrel   {n} : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  | and    {n} : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  | or     {n} : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  | all    {n} : Semiformula L ξ (n + 1) → Semiformula L ξ n
  | ex     {n} : Semiformula L ξ (n + 1) → Semiformula L ξ n

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Formula (L : Language) (ξ : Type*) := Semiformula L ξ 0

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Sentence (L : Language) := Formula L Empty

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Semisentence (L : Language) (n : ℕ) := Semiformula L Empty n

/-- Imported declaration from the Incompleteness formalization. -/
abbrev SyntacticSemiformula (L : Language) (n : ℕ) := Semiformula L ℕ n

/-- Imported declaration from the Incompleteness formalization. -/
abbrev SyntacticFormula (L : Language) := SyntacticSemiformula L 0

namespace Semiformula

variable
  {L : Language} {L₁ : Language} {L₂ : Language} {L₃ : Language}
  {ξ ξ₁ ξ₂ ξ₃ : Type*}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

/-- Imported declaration from the Incompleteness formalization. -/
def neg {n} : Semiformula L ξ n → Semiformula L ξ n
  | verum    => falsum
  | falsum   => verum
  | rel r v  => nrel r v
  | nrel r v => rel r v
  | and φ ψ  => or (neg φ) (neg ψ)
  | or φ ψ   => and (neg φ) (neg ψ)
  | all φ    => ex (neg φ)
  | ex φ     => all (neg φ)

/--
@isnad1 id=eq.0h4v.s4.c752dadc20c7 from=translated src=- shape=5ca92033 vocab=4ff8c232
-/
lemma neg_neg (φ : Semiformula L ξ n) : neg (neg φ) = φ :=
  by induction φ <;> simp[*, neg]

instance : LogicalConnective (Semiformula L ξ n) where
  tilde := neg
  arrow := fun φ ψ => or (neg φ) ψ
  wedge := and
  vee := or
  top := verum
  bot := falsum

instance : DeMorgan (Semiformula L ξ n) where
  verum := rfl
  falsum := rfl
  imply := fun _ _ => rfl
  and := fun _ _ => rfl
  or := fun _ _ => rfl
  neg := neg_neg

instance : Quantifier (Semiformula L ξ) where
  univ := all
  ex := ex

section «lp_section_1»

variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)] [ToString ξ]

/-- Imported declaration from the Incompleteness formalization. -/
def toStr {n} : Semiformula L ξ n → String
  | ⊤                         => "\\top"
  | ⊥                         => "\\bot"
  | rel (arity := 0) r _      => "{" ++ toString r ++ "}"
  | rel (arity := _ + 1) r v  =>
    "{" ++ toString r ++ "} \\left(" ++ String.vecToStr (fun i => toString (v i)) ++ "\\right)"
  | nrel (arity := 0) r _     => "\\lnot {" ++ toString r ++ "}"
  | nrel (arity := _ + 1) r v =>
    "\\lnot {" ++ toString r ++ "} \\left(" ++
      String.vecToStr (fun i => toString (v i)) ++ "\\right)"
  | φ ⋏ ψ                     => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  | φ ⋎ ψ                     => "\\left(" ++ toStr φ ++ " \\lor "  ++ toStr ψ ++ "\\right)"
  | all φ                     => "(\\forall x_{" ++ toString n ++ "}) " ++ toStr φ
  | ex φ                      => "(\\exists x_{" ++ toString n ++ "}) " ++ toStr φ

instance : Repr (Semiformula L ξ n) := ⟨fun t _ => toStr t⟩

instance : ToString (Semiformula L ξ n) := ⟨toStr⟩

end «lp_section_1»

/--
@isnad1 id=eq.0h3v.s5.57ed7fe40150 from=translated src=- shape=e29439d8 vocab=f608d52d
-/
@[simp] lemma neg_top : ∼(⊤ : Semiformula L ξ n) = ⊥ := rfl

/--
@isnad1 id=eq.0h3v.s5.853117c4df55 from=translated src=- shape=e29439d8 vocab=f608d52d
-/
@[simp] lemma neg_bot : ∼(⊥ : Semiformula L ξ n) = ⊤ := rfl

/--
@isnad1 id=eq.0h6v.s5.f01b647dcdec from=translated src=- shape=56bc9305 vocab=3463db10
-/
@[simp] lemma neg_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ∼(rel r v) = nrel r v := rfl

/--
@isnad1 id=eq.0h6v.s5.6fa8bb7a147c from=translated src=- shape=56bc9305 vocab=3463db10
-/
@[simp] lemma neg_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ∼(nrel r v) = rel r v := rfl

/--
@isnad1 id=eq.0h5v.s6.b255ea2aaef8 from=translated src=- shape=566f23b8 vocab=f7ee0fa6
-/
@[simp] lemma neg_and (φ ψ : Semiformula L ξ n) : ∼(φ ⋏ ψ) = ∼φ ⋎ ∼ψ := rfl

/--
@isnad1 id=eq.0h5v.s6.eab1563ecf1a from=translated src=- shape=566f23b8 vocab=f7ee0fa6
-/
@[simp] lemma neg_or (φ ψ : Semiformula L ξ n) : ∼(φ ⋎ ψ) = ∼φ ⋏ ∼ψ := rfl

/--
@isnad1 id=eq.0h4v.s6.5f3db8ce8ea6 from=translated src=- shape=2f3a842e vocab=803e6b01
-/
@[simp 1100] lemma neg_all (φ : Semiformula L ξ (n + 1)) : ∼(∀' φ) = ∃' ∼φ := rfl

/--
@isnad1 id=eq.0h4v.s6.d59d12200c44 from=translated src=- shape=2f3a842e vocab=803e6b01
-/
@[simp] lemma neg_ex (φ : Semiformula L ξ (n + 1)) : ∼(∃' φ) = ∀' ∼φ := rfl

/--
@isnad1 id=eq.0h4v.s5.28fc132c84ec from=translated src=- shape=5c28ce4b vocab=d789c772
-/
@[simp 1100] lemma neg_neg' (φ : Semiformula L ξ n) : ∼∼φ = φ := neg_neg φ

/--
@isnad1 id=iff.0h5v.s5.1377eeef6600 from=translated src=- shape=60b6a162 vocab=d789c772
-/
@[simp] lemma neg_inj (φ ψ : Semiformula L ξ n) : ∼φ = ∼ψ ↔ φ = ψ := by
  constructor
  · intro h; simpa using congr_arg (∼·) h
  · exact congr_arg _

/--
@isnad1 id=eq.0h4v.s6.651fc07a9380 from=translated src=- shape=53a220c8 vocab=7ce4ffd6
-/
@[simp] lemma neg_univClosure (φ : Semiformula L ξ n) : ∼(∀* φ) = ∃* ∼φ := by
  induction n <;> simp [univClosure, exClosure, *]

/--
@isnad1 id=eq.0h4v.s6.a5694d6ec337 from=translated src=- shape=53a220c8 vocab=7ce4ffd6
-/
@[simp] lemma neg_exClosure (φ : Semiformula L ξ n) : ∼(∃* φ) = ∀* ∼φ := by
  induction n <;> simp [univClosure, exClosure, *]

/--
@isnad1 id=eq.0h4v.s5.aef3a475ccf9 from=translated src=- shape=342dc145 vocab=f36a7a9c
-/
lemma neg_eq (φ : Semiformula L ξ n) : ∼φ = neg φ := rfl

/--
@isnad1 id=eq.0h5v.s6.293a349a7635 from=translated src=- shape=d93ed792 vocab=7470f0af
-/
lemma imp_eq (φ ψ : Semiformula L ξ n) : φ ==> ψ = ∼φ ⋎ ψ := rfl

/--
@isnad1 id=eq.0h5v.s6.73cc5cde12b5 from=translated src=- shape=80769566 vocab=19d85142
-/
lemma iff_eq (φ ψ : Semiformula L ξ n) : φ <=> ψ = (∼φ ⋎ ψ) ⋏ (∼ψ ⋎ φ) := rfl

/--
@isnad1 id=eq.0h5v.s7.b87fdc83c484 from=translated src=- shape=75be1100 vocab=247f3cc1
-/
lemma ball_eq (φ ψ : Semiformula L ξ (n + 1)) : (∀[φ] ψ) = ∀' (φ ==> ψ) := rfl

/--
@isnad1 id=eq.0h5v.s7.20a7d44d5888 from=translated src=- shape=75be1100 vocab=32148483
-/
lemma bex_eq (φ ψ : Semiformula L ξ (n + 1)) : (∃[φ] ψ) = ∃' (φ ⋏ ψ) := rfl

/--
@isnad1 id=eq.0h5v.s7.4e0ad1ce35e4 from=translated src=- shape=23ab7546 vocab=c5bc3417
-/
@[simp] lemma neg_ball (φ ψ : Semiformula L ξ (n + 1)) : ∼(∀[φ] ψ) = ∃[φ] ∼ψ := by
  simp [ball, bex, imp_eq]

/--
@isnad1 id=eq.0h5v.s7.9e6cb507fd29 from=translated src=- shape=23ab7546 vocab=c5bc3417
-/
@[simp] lemma neg_bex (φ ψ : Semiformula L ξ (n + 1)) : ∼(∃[φ] ψ) = ∀[φ] ∼ψ := by
  simp [ball, bex, imp_eq]

/--
@isnad1 id=iff.0h7v.s6.f9d26668e58a from=translated src=- shape=aed38246 vocab=0611783c
-/
@[simp] lemma and_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformula L ξ n) : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ :=
by simp [Wedge.wedge]

/--
@isnad1 id=iff.0h7v.s6.e1ce7111ecf8 from=translated src=- shape=aed38246 vocab=83d5c265
-/
@[simp] lemma or_inj (φ₁ ψ₁ φ₂ ψ₂ : Semiformula L ξ n) : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ :=
by simp[Vee.vee]

/--
@isnad1 id=iff.0h5v.s6.6cfa92eee476 from=translated src=- shape=d4e5a281 vocab=04dab56f
-/
@[simp] lemma all_inj (φ ψ : Semiformula L ξ (n + 1)) : ∀' φ = ∀' ψ ↔ φ = ψ :=
  by simp[UnivQuantifier.univ]

/--
@isnad1 id=iff.0h5v.s6.08a90e4e3591 from=translated src=- shape=d4e5a281 vocab=8135a521
-/
@[simp] lemma ex_inj (φ ψ : Semiformula L ξ (n + 1)) : ∃' φ = ∃' ψ ↔ φ = ψ :=
  by simp[ExQuantifier.ex]

/--
@isnad1 id=iff.0h5v.s5.d610c4a4c59a from=translated src=- shape=5e7cc118 vocab=cd9e74ed
-/
@[simp] lemma univClosure_inj (φ ψ : Semiformula L ξ n) : ∀* φ = ∀* ψ ↔ φ = ψ := by
  induction n <;> simp [*, univClosure_succ]

/--
@isnad1 id=iff.0h5v.s5.051a4a9b8629 from=translated src=- shape=5e7cc118 vocab=6dca9da3
-/
@[simp] lemma exClosure_inj (φ ψ : Semiformula L ξ n) : ∃* φ = ∃* ψ ↔ φ = ψ := by
  induction n <;> simp [*, exClosure_succ]

/--
@isnad1 id=iff.0h6v.s6.af82a5da72fa from=translated src=- shape=57e26ebd vocab=9d5df864
-/
@[simp] lemma univItr_inj {k} (φ ψ : Semiformula L ξ (n + k)) : ∀^[k] φ = ∀^[k] ψ ↔ φ = ψ := by
  induction k <;> simp [*, univItr_succ]

/--
@isnad1 id=iff.0h6v.s6.b4d9c7ab0c4e from=translated src=- shape=57e26ebd vocab=5efee5dc
-/
@[simp] lemma exItr_inj {k} (φ ψ : Semiformula L ξ (n + k)) : ∃^[k] φ = ∃^[k] ψ ↔ φ = ψ := by
  induction k <;> simp [*, exItr_succ]

/--
@isnad1 id=iff.0h7v.s6.c5e5612ea088 from=translated src=- shape=d87ed4c8 vocab=5e170707
-/
@[simp] lemma imp_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula L ξ n} :
    φ₁ ==> φ₂ = ψ₁ ==> ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [imp_eq]

/-- Imported declaration from the Incompleteness formalization. -/
abbrev «rel!» (L : Language) (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) := rel r v

/-- Imported declaration from the Incompleteness formalization. -/
abbrev «nrel!» (L : Language) (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) := nrel r v

/-- Imported declaration from the Incompleteness formalization. -/
def complexity {n : ℕ} : Semiformula L ξ n → ℕ
| ⊤        => 0
| ⊥        => 0
| rel _ _  => 0
| nrel _ _ => 0
| φ ⋏ ψ    => max φ.complexity ψ.complexity + 1
| φ ⋎ ψ    => max φ.complexity ψ.complexity + 1
| ∀' φ     => φ.complexity + 1
| ∃' φ     => φ.complexity + 1

/--
@isnad1 id=eq.0h3v.s4.1f51500f3c15 from=translated src=- shape=b336aded vocab=c75f77c2
-/
@[simp] lemma complexity_top : complexity (⊤ : Semiformula L ξ n) = 0 := rfl

/--
@isnad1 id=eq.0h3v.s4.5b766cfd5772 from=translated src=- shape=b336aded vocab=20dd4ab1
-/
@[simp] lemma complexity_bot : complexity (⊥ : Semiformula L ξ n) = 0 := rfl

/--
@isnad1 id=eq.0h6v.s5.aa534ea3c55a from=translated src=- shape=6148e4d1 vocab=3bb61b77
-/
@[simp] lemma complexity_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    complexity (rel r v) = 0 := rfl

/--
@isnad1 id=eq.0h6v.s5.645269e456fc from=translated src=- shape=6148e4d1 vocab=4ca36504
-/
@[simp] lemma complexity_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    complexity (nrel r v) = 0 := rfl

/--
@isnad1 id=eq.0h5v.s5.1f5f6e1a7c6b from=translated src=- shape=5006f494 vocab=df2e9470
-/
@[simp] lemma complexity_and (φ ψ : Semiformula L ξ n) :
    complexity (φ ⋏ ψ) = max φ.complexity ψ.complexity + 1 := rfl
/--
@isnad1 id=eq.0h5v.s5.442bf4ce9eae from=translated src=- shape=ae396491 vocab=c7df2f2d
-/
@[simp] lemma complexity_and' (φ ψ : Semiformula L ξ n) :
    complexity (and φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

/--
@isnad1 id=eq.0h5v.s5.a7360ccf5e99 from=translated src=- shape=5006f494 vocab=e3a3aa77
-/
@[simp] lemma complexity_or (φ ψ : Semiformula L ξ n) :
    complexity (φ ⋎ ψ) = max φ.complexity ψ.complexity + 1 := rfl
/--
@isnad1 id=eq.0h5v.s5.5bf828423267 from=translated src=- shape=ae396491 vocab=be38e467
-/
@[simp] lemma complexity_or' (φ ψ : Semiformula L ξ n) :
    complexity (or φ ψ) = max φ.complexity ψ.complexity + 1 := rfl

/--
@isnad1 id=eq.0h4v.s6.e340d589d586 from=translated src=- shape=ffa43ef9 vocab=a226c620
-/
@[simp] lemma complexity_all (φ : Semiformula L ξ (n + 1)) :
    complexity (∀' φ) = φ.complexity + 1 := rfl
/--
@isnad1 id=eq.0h4v.s5.24bcc51bd105 from=translated src=- shape=d31d1b37 vocab=9a20a712
-/
@[simp] lemma complexity_all' (φ : Semiformula L ξ (n + 1)) :
    complexity (all φ) = φ.complexity + 1 := rfl

/--
@isnad1 id=eq.0h4v.s6.929e6e618eb9 from=translated src=- shape=ffa43ef9 vocab=1a10f9d7
-/
@[simp] lemma complexity_ex (φ : Semiformula L ξ (n + 1)) :
    complexity (∃' φ) = φ.complexity + 1 := rfl
/--
@isnad1 id=eq.0h4v.s5.7dda5b41344c from=translated src=- shape=d31d1b37 vocab=6e168f92
-/
@[simp] lemma complexity_ex' (φ : Semiformula L ξ (n + 1)) :
    complexity (ex φ) = φ.complexity + 1 := rfl

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def cases' {C : ∀ n, Semiformula L ξ n → Sort w}
  (hverum : ∀ {n : ℕ}, C n ⊤)
  (hfalsum : ∀ {n : ℕ}, C n ⊥)
  (hrel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
  (hnrel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
  (hand : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n (φ ⋏ ψ))
  (hor : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n (φ ⋎ ψ))
  (hall : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C n (∀' φ))
  (hex : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C n (∃' φ)) :
    ∀ {n : ℕ} (φ : Semiformula L ξ n), C n φ
  | _, verum    => hverum
  | _, falsum   => hfalsum
  | _, rel r v  => hrel r v
  | _, nrel r v => hnrel r v
  | _, and φ ψ  => hand φ ψ
  | _, or φ ψ   => hor φ ψ
  | _, all φ    => hall φ
  | _, ex φ     => hex φ

/-- Imported declaration from the Incompleteness formalization. -/
@[elab_as_elim]
def rec' {C : ∀ n, Semiformula L ξ n → Sort w}
  (hverum : ∀ {n : ℕ}, C n ⊤)
  (hfalsum : ∀ {n : ℕ}, C n ⊥)
  (hrel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
  (hnrel : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
  (hand : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n φ → C n ψ → C n (φ ⋏ ψ))
  (hor : ∀ {n : ℕ} (φ ψ : Semiformula L ξ n), C n φ → C n ψ → C n (φ ⋎ ψ))
  (hall : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C (n + 1) φ → C n (∀' φ))
  (hex : ∀ {n : ℕ} (φ : Semiformula L ξ (n + 1)), C (n + 1) φ → C n (∃' φ)) :
    ∀ {n : ℕ} (φ : Semiformula L ξ n), C n φ
  | _, verum    => hverum
  | _, falsum   => hfalsum
  | _, rel r v  => hrel r v
  | _, nrel r v => hnrel r v
  | _, and φ ψ  =>
    hand φ ψ (rec' hverum hfalsum hrel hnrel hand hor hall hex φ) (rec' hverum hfalsum hrel hnrel
      hand hor hall hex ψ)
  | _, or φ ψ   =>
    hor φ ψ (rec' hverum hfalsum hrel hnrel hand hor hall hex φ) (rec' hverum hfalsum hrel hnrel
      hand hor hall hex ψ)
  | _, all φ    => hall φ (rec' hverum hfalsum hrel hnrel hand hor hall hex φ)
  | _, ex φ     => hex φ (rec' hverum hfalsum hrel hnrel hand hor hall hex φ)

/--
@isnad1 id=eq.0h4v.s5.d66b470b86d2 from=translated src=- shape=c4687579 vocab=81fd2c7c
-/
@[simp] lemma complexity_neg (φ : Semiformula L ξ n) : complexity (∼φ) = complexity φ :=
  by induction φ using rec' <;> simp[*]

section «lp_section_2»

variable [∀ k, DecidableEq (L.Func k)] [∀ k, DecidableEq (L.Rel k)] [DecidableEq ξ]

/-- Imported declaration from the Incompleteness formalization. -/
def hasDecEq : {n : ℕ} → (φ ψ : Semiformula L ξ n) → Decidable (φ = ψ)
  | _, ⊤,        ψ => by
      cases ψ using cases'
      case hverum => exact isTrue rfl
      all_goals exact isFalse (by intro h; cases h)
  | _, ⊥,        ψ => by
      cases ψ using cases'
      case hfalsum => exact isTrue rfl
      all_goals exact isFalse (by intro h; cases h)
  | _, rel r v,  ψ => by
      cases ψ using cases'
      case hrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h  => by
            rcases h with rfl
            exact match Matrix.decVec _ _ (fun i => decEq (v i) (v₂ i)) with
            | isTrue hv => isTrue (by rw [hv])
            | isFalse hv => isFalse (by intro h; cases h; exact hv rfl)
          | isFalse h => isFalse (by intro hrel; cases hrel; exact h rfl)
        · exact isFalse (by simp[e])
      all_goals exact isFalse (by intro h; cases h)
  | _, nrel r v, ψ => by
      cases ψ using cases'
      case hnrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h  => by
            rcases h with rfl
            exact match Matrix.decVec _ _ (fun i => decEq (v i) (v₂ i)) with
            | isTrue hv => isTrue (by rw [hv])
            | isFalse hv => isFalse (by intro h; cases h; exact hv rfl)
          | isFalse h => isFalse (by intro hnrel; cases hnrel; exact h rfl)
        · exact isFalse (by simp[e])
      all_goals exact isFalse (by intro h; cases h)
  | _, φ ⋏ ψ,    r => by
      cases r using cases'
      case hand φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp[hp, hq])
        | isFalse hp => isFalse (by simp[hp])
      all_goals exact isFalse (by intro h; cases h)
  | _, φ ⋎ ψ,    r => by
      cases r using cases'
      case hor φ' ψ' =>
        exact match hasDecEq φ φ' with
        | isTrue hp =>
          match hasDecEq ψ ψ' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp[hp, hq])
        | isFalse hp => isFalse (by simp[hp])
      all_goals exact isFalse (by intro h; cases h)
  | _, ∀' φ,     ψ => by
      cases ψ using cases'
      case hall φ' =>
        exact match hasDecEq φ φ' with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (by intro e; cases e; exact h rfl)
      all_goals exact isFalse (by intro h; cases h)
  | _, ∃' φ,     ψ => by
      cases ψ using cases'
      case hex φ' =>
        exact match hasDecEq φ φ' with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse (by intro e; cases e; exact h rfl)
      all_goals exact isFalse (by intro h; cases h)

instance : DecidableEq (Semiformula L ξ n) := hasDecEq

end «lp_section_2»

/-! Quantifier Rank -/

section «lp_section_3»

/-- Imported declaration from the Incompleteness formalization. -/
def qr : ∀ {n}, Semiformula L ξ n → ℕ
  | _, ⊤        => 0
  | _, ⊥        => 0
  | _, rel _ _  => 0
  | _, nrel _ _ => 0
  | _, φ ⋏ ψ    => max φ.qr ψ.qr
  | _, φ ⋎ ψ    => max φ.qr ψ.qr
  | _, ∀' φ     => φ.qr + 1
  | _, ∃' φ     => φ.qr + 1

/--
@isnad1 id=eq.0h3v.s4.f46018dd94ed from=translated src=- shape=b336aded vocab=5fce3dd6
-/
@[simp] lemma qr_top : (⊤ : Semiformula L ξ n).qr = 0 := rfl

/--
@isnad1 id=eq.0h3v.s4.a3b8b3fda188 from=translated src=- shape=b336aded vocab=b12bf3fa
-/
@[simp] lemma qr_bot : (⊥ : Semiformula L ξ n).qr = 0 := rfl

/--
@isnad1 id=eq.0h6v.s5.2cc6fa14b774 from=translated src=- shape=6148e4d1 vocab=ba25c0f4
-/
@[simp] lemma qr_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).qr = 0 := rfl

/--
@isnad1 id=eq.0h6v.s5.d4e75873a821 from=translated src=- shape=6148e4d1 vocab=1c784a8f
-/
@[simp] lemma qr_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).qr = 0 := rfl

/--
@isnad1 id=eq.0h5v.s5.04753f4e342b from=translated src=- shape=2d7f46cb vocab=165c3f58
-/
@[simp] lemma qr_and (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ).qr = max φ.qr ψ.qr := rfl

/--
@isnad1 id=eq.0h5v.s5.36309fd95e23 from=translated src=- shape=2d7f46cb vocab=395f89d8
-/
@[simp] lemma qr_or (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ).qr = max φ.qr ψ.qr := rfl

/--
@isnad1 id=eq.0h4v.s6.78c77a284f50 from=translated src=- shape=ffa43ef9 vocab=869a9648
-/
@[simp] lemma qr_all (φ : Semiformula L ξ (n + 1)) : (∀' φ).qr = φ.qr + 1 := rfl

/--
@isnad1 id=eq.0h4v.s6.daeac61b3ad2 from=translated src=- shape=ffa43ef9 vocab=20f60032
-/
@[simp] lemma qr_ex (φ : Semiformula L ξ (n + 1)) : (∃' φ).qr = φ.qr + 1 := rfl

/--
@isnad1 id=eq.0h4v.s5.1ceedece57f0 from=translated src=- shape=c4687579 vocab=9cd9a081
-/
@[simp] lemma qr_neg (φ : Semiformula L ξ n) : (∼φ).qr = φ.qr := by
  induction φ using rec' <;> simp [*]

/--
@isnad1 id=eq.0h5v.s5.15060b8bcd37 from=translated src=- shape=2d7f46cb vocab=5d404910
-/
@[simp] lemma qr_imply (φ ψ : Semiformula L ξ n) : (φ ==> ψ).qr = max φ.qr ψ.qr :=
  by simp[imp_eq]

/--
@isnad1 id=eq.0h5v.s5.647087157af0 from=translated src=- shape=2d7f46cb vocab=729b0617
-/
@[simp] lemma qr_iff (φ ψ : Semiformula L ξ n) : (φ <=> ψ).qr = max φ.qr ψ.qr :=
  by simp[iff_eq, total_of]

end «lp_section_3»

/-! Open (Semi-)Formula -/

section «lp_section_4»

/-- Imported declaration from the Incompleteness formalization. -/
def Open (φ : Semiformula L ξ n) : Prop := φ.qr = 0

/--
@isnad1 id=open.0h3v.s4.93ac6659a59a from=translated src=- shape=7cfc5dc9 vocab=8ea40186
-/
lemma open_top : (⊤ : Semiformula L ξ n).Open := rfl

/--
@isnad1 id=open.0h3v.s4.f8a465e4f13a from=translated src=- shape=7cfc5dc9 vocab=c109e7b2
-/
lemma open_bot : (⊥ : Semiformula L ξ n).Open := rfl

/--
@isnad1 id=open.0h6v.s4.7106f2b054ad from=translated src=- shape=e6bbdf3d vocab=5c6fec1f
-/
lemma open_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).Open := rfl

/--
@isnad1 id=open.0h6v.s4.596d73cff8e8 from=translated src=- shape=e6bbdf3d vocab=4b6f0dd6
-/
lemma open_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).Open := rfl

/--
@isnad1 id=iff.0h5v.s5.acf77664fc85 from=translated src=- shape=45b94e3a vocab=3af07643
-/
@[simp] lemma open_and {φ ψ : Semiformula L ξ n} : (φ ⋏ ψ).Open ↔ φ.Open ∧ ψ.Open := by simp[Open]

/--
@isnad1 id=iff.0h5v.s5.8c3f5b443890 from=translated src=- shape=45b94e3a vocab=64573cca
-/
@[simp] lemma open_or {φ ψ : Semiformula L ξ n} : (φ ⋎ ψ).Open ↔ φ.Open ∧ ψ.Open := by simp[Open]

/--
@isnad1 id=not.0h4v.s5.9e2571508367 from=translated src=- shape=de154d3e vocab=592073bd
-/
@[simp] lemma not_open_all {φ : Semiformula L ξ (n + 1)} : ¬(∀' φ).Open := by simp[Open]

/--
@isnad1 id=not.0h4v.s5.7a4da42ebd37 from=translated src=- shape=de154d3e vocab=719794bd
-/
@[simp] lemma not_open_ex {φ : Semiformula L ξ (n + 1)} : ¬(∃' φ).Open := by simp[Open]

/--
@isnad1 id=iff.0h4v.s5.454607120abc from=translated src=- shape=9be4b2b9 vocab=ca0a38a4
-/
@[simp] lemma open_neg {φ : Semiformula L ξ n} : (∼φ).Open ↔ φ.Open := by simp[Open]

/--
@isnad1 id=iff.0h5v.s5.a1c264073be2 from=translated src=- shape=45b94e3a vocab=6a83041c
-/
@[simp] lemma open_imply {φ ψ : Semiformula L ξ n} : (φ ==> ψ).Open ↔ φ.Open ∧ ψ.Open :=
  by simp[Open]

/--
@isnad1 id=iff.0h5v.s5.caa8db8488d1 from=translated src=- shape=45b94e3a vocab=3dd6c6bd
-/
@[simp] lemma open_iff {φ ψ : Semiformula L ξ n} : (φ <=> ψ).Open ↔ φ.Open ∧ ψ.Open :=
  by simp[Open]

end «lp_section_4»

/-! Free Variables -/

section «lp_section_5»

variable [DecidableEq ξ]

/-- Imported declaration from the Incompleteness formalization. -/
def freeVariables : {n : ℕ} → Semiformula L ξ n → Finset ξ
  | _, rel _ v  => .biUnion .univ fun i ↦ (v i).freeVariables
  | _, nrel _ v => .biUnion .univ fun i ↦ (v i).freeVariables
  | _, ⊤        => ∅
  | _, ⊥        => ∅
  | _, φ ⋏ ψ    => freeVariables φ ∪ freeVariables ψ
  | _, φ ⋎ ψ    => freeVariables φ ∪ freeVariables ψ
  | _, ∀' φ     => freeVariables φ
  | _, ∃' φ     => freeVariables φ

/--
@isnad1 id=eq.0h6v.s5.13b21886ecb2 from=translated src=- shape=92e36f6c vocab=8a08eaa8
-/
lemma freeVariables_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables := rfl

/--
@isnad1 id=eq.0h6v.s5.6a6b6b0deb44 from=translated src=- shape=92e36f6c vocab=8acbd481
-/
lemma freeVariables_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v).freeVariables = .biUnion .univ fun i ↦ (v i).freeVariables := rfl

/--
@isnad1 id=eq.0h3v.s5.d41112b877f0 from=translated src=- shape=3ae29c16 vocab=58760e0d
-/
@[simp] lemma freeVariables_verum : (⊤ : Semiformula L ξ n).freeVariables = ∅ := rfl

/--
@isnad1 id=eq.0h3v.s5.16604624d00a from=translated src=- shape=3ae29c16 vocab=10d4ebca
-/
@[simp] lemma freeVariables_falsum : (⊥ : Semiformula L ξ n).freeVariables = ∅ := rfl

/--
@isnad1 id=eq.0h5v.s5.7bde82dc3f3c from=translated src=- shape=0e90f005 vocab=a48b6fc6
-/
@[simp] lemma freeVariables_and (φ ψ : Semiformula L ξ n) :
    (φ ⋏ ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables := rfl

/--
@isnad1 id=eq.0h5v.s5.3f0a7c704594 from=translated src=- shape=0e90f005 vocab=9f086cb5
-/
@[simp] lemma freeVariables_or (φ ψ : Semiformula L ξ n) :
    (φ ⋎ ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables := rfl

/--
@isnad1 id=eq.0h4v.s6.71b6cff1ecb2 from=translated src=- shape=73abca78 vocab=42e0e37c
-/
@[simp] lemma freeVariables_all (φ : Semiformula L ξ (n + 1)) :
    (∀' φ).freeVariables = φ.freeVariables := rfl

/--
@isnad1 id=eq.0h4v.s6.8b6d18372a8e from=translated src=- shape=73abca78 vocab=455ca244
-/
@[simp] lemma freeVariables_ex (φ : Semiformula L ξ (n + 1)) :
    (∃' φ).freeVariables = φ.freeVariables := rfl

/--
@isnad1 id=eq.0h4v.s5.2a6f282b4b19 from=translated src=- shape=cda7db63 vocab=5e82282f
-/
@[simp] lemma freeVariables_not (φ : Semiformula L ξ n) : (∼φ).freeVariables = φ.freeVariables := by
  induction φ using rec' <;> simp [*, freeVariables_rel, freeVariables_nrel]

/--
@isnad1 id=eq.0h5v.s5.14e06af9bbd7 from=translated src=- shape=0e90f005 vocab=14f992a3
-/
@[simp] lemma freeVariables_imp (φ ψ : Semiformula L ξ n) :
    (φ ==> ψ).freeVariables = φ.freeVariables ∪ ψ.freeVariables := by simp [imp_eq]

/--
@isnad1 id=eq.0h4v.s5.5d5692b1e5f9 from=translated src=- shape=de3ae2f3 vocab=e47da4a8
-/
@[simp] lemma freeVariables_univClosure (φ : Semiformula L ξ n) :
    (∀* φ).freeVariables = φ.freeVariables := by
  induction n <;> simp [univClosure, *]

/--
@isnad1 id=eq.0h4v.s5.f3a2c1e7120d from=translated src=- shape=e74a6ad1 vocab=95a2f83e
-/
@[simp] lemma freeVariables_sentence {ο : Type*} [IsEmpty ο] (φ : Semiformula L ο n) :
    φ.freeVariables = ∅ := by
  ext x; exact IsEmpty.elim inferInstance x

/-- Imported declaration from the Incompleteness formalization. -/
abbrev «FVar?» (φ : Semiformula L ξ n) (x : ξ) : Prop := x ∈ φ.freeVariables

@[simp] lemma «fvar?_rel» {x k} {R : L.Rel k} {v : Fin k → Semiterm L ξ n} :
    (rel R v).FVar? x ↔ ∃ i, (v i).FVar? x := by simp [FVar?, freeVariables_rel]

@[simp] lemma «fvar?_nrel» {x k} {R : L.Rel k} {v : Fin k → Semiterm L ξ n} :
    (nrel R v).FVar? x ↔ ∃ i, (v i).FVar? x := by simp [FVar?, freeVariables_nrel]

@[simp] lemma «fvar?_top» (x) : ¬(⊤ : Semiformula L ξ n).FVar? x := by simp [FVar?]

@[simp] lemma «fvar?_falsum» (x) : ¬(⊥ : Semiformula L ξ n).FVar? x := by simp [FVar?]

@[simp] lemma «fvar?_and» (x) (φ ψ : Semiformula L ξ n) :
    (φ ⋏ ψ).FVar? x ↔ φ.FVar? x ∨ ψ.FVar? x := by simp [FVar?]

@[simp] lemma «fvar?_or» (x) (φ ψ : Semiformula L ξ n) :
    (φ ⋎ ψ).FVar? x ↔ φ.FVar? x ∨ ψ.FVar? x := by simp [FVar?]

@[simp] lemma «fvar?_all» (x) (φ : Semiformula L ξ (n + 1)) :
    (∀' φ).FVar? x ↔ φ.FVar? x := by simp [FVar?]

@[simp] lemma «fvar?_ex» (x) (φ : Semiformula L ξ (n + 1)) :
    (∃' φ).FVar? x ↔ φ.FVar? x := by simp [FVar?]

@[simp] lemma «fvar?_univClosure» (x) (φ : Semiformula L ξ n) :
    (∀* φ).FVar? x ↔ φ.FVar? x := by simp [FVar?]

/-- Imported declaration from the Incompleteness formalization. -/
def fvSup (φ : SyntacticSemiformula L n) : ℕ := (φ.freeVariables.max).recBotCoe 0 .succ

lemma «lt_fvSup_of_fvar?» {φ : SyntacticSemiformula L n} : φ.FVar? m → m < φ.fvSup := by
  unfold fvSup FVar?
  intro hm
  have : ∃ s : ℕ, φ.freeVariables.max = s := Finset.max_of_mem hm
  rcases this with ⟨s, hs⟩
  have : m ≤ s := by
    have : (m : WithBot ℕ) ≤ ↑s := hs ▸ Finset.le_max hm
    exact WithBot.coe_le_coe.mp this
  simpa [hs, WithBot.recBotCoe] using Nat.lt_add_one_of_le this

lemma «not_fvar?_of_lt_fvSup» (φ : SyntacticSemiformula L n) (h : φ.fvSup ≤ m) : ¬φ.FVar? m :=
  fun hm ↦ (lt_self_iff_false _).mp (lt_of_le_of_lt h <| lt_fvSup_of_fvar? hm)

@[simp] lemma «not_fvar?_fvSup» (φ : SyntacticSemiformula L n) : ¬φ.FVar? φ.fvSup :=
  not_fvar?_of_lt_fvSup φ (by simp)

end «lp_section_5»

section «lp_section_6»

variable {α : Type*} [LinearOrder α]

namespace List

end List

end «lp_section_6»

/--
@isnad1 id=ne.1h5v.s5.b605ddfa2f73 from=translated src=- shape=bb6a0092 vocab=13fbda6a
-/
lemma ne_of_ne_complexity {φ ψ : Semiformula L ξ n} (h : φ.complexity ≠ ψ.complexity) : φ ≠ ψ :=
  by rintro rfl; contradiction

/--
@isnad1 id=ne.0h5v.s5.0faecf0ec129 from=translated src=- shape=5aaad54e vocab=83d5c265
-/
@[simp] lemma ne_or_left (φ ψ : Semiformula L ξ n) : φ ≠ φ ⋎ ψ := ne_of_ne_complexity (by simp)

/--
@isnad1 id=ne.0h5v.s5.d5510b7e6132 from=translated src=- shape=0a6d0d74 vocab=83d5c265
-/
@[simp] lemma ne_or_right (φ ψ : Semiformula L ξ n) : ψ ≠ φ ⋎ ψ :=
  ne_of_ne_complexity (Nat.ne_step_max' ψ.complexity φ.complexity)

variable {L : Language} {L₁ : Language} {L₂ : Language} {L₃ : Language} {ξ : Type*} {Φ : L₁ →ᵥ L₂}

/-- Imported declaration from the Incompleteness formalization. -/
def lMapAux (Φ : L₁ →ᵥ L₂) : ∀ {n}, Semiformula L₁ ξ n → Semiformula L₂ ξ n
  | _, ⊤        => ⊤
  | _, ⊥        => ⊥
  | _, rel r v  => rel (Φ.rel r) (Semiterm.lMap Φ ∘ v)
  | _, nrel r v => nrel (Φ.rel r) (Semiterm.lMap Φ ∘ v)
  | _, φ ⋏ ψ    => lMapAux Φ φ ⋏ lMapAux Φ ψ
  | _, φ ⋎ ψ    => lMapAux Φ φ ⋎ lMapAux Φ ψ
  | _, ∀' φ     => ∀' lMapAux Φ φ
  | _, ∃' φ     => ∃' lMapAux Φ φ

/--
@isnad1 id=eq.0h6v.s6.e57f7c708939 from=translated src=- shape=7fc68ebc vocab=c31eab71
-/
lemma lMapAux_neg {n} (φ : Semiformula L₁ ξ n) : (∼φ).lMapAux Φ = ∼φ.lMapAux Φ :=
  by induction φ using Semiformula.rec' <;> simp[*, lMapAux]

/-- Imported declaration from the Incompleteness formalization. -/
def lMap (Φ : L₁ →ᵥ L₂) {n} : Semiformula L₁ ξ n →ˡᶜ Semiformula L₂ ξ n where
  toTr := lMapAux Φ
  map_top' := by simp[lMapAux]
  map_bot' := by simp[lMapAux]
  map_and' := by simp[lMapAux]
  map_or'  := by simp[lMapAux]
  map_neg' := by simp[lMapAux_neg]
  map_imply' := by simp[Semiformula.imp_eq, lMapAux_neg, ←Semiformula.neg_eq, lMapAux]

/--
@isnad1 id=eq.0h8v.s6.b754079bae0d from=translated src=- shape=f825d73f vocab=85e82971
-/
lemma lMap_rel {k} (r : L₁.Rel k) (v : Fin k → Semiterm L₁ ξ n) :
    lMap Φ (rel r v) = rel (Φ.rel r) (fun i => (v i).lMap Φ) := rfl

/--
@isnad1 id=eq.0h7v.s6.f1fce549068f from=translated src=- shape=145bf1f5 vocab=ba720d1d
-/
@[simp] lemma lMap_rel₀ (r : L₁.Rel 0) (v : Fin 0 → Semiterm L₁ ξ n) :
    lMap Φ (rel r v) = rel (Φ.rel r) ![] := by simp[lMap_rel, Matrix.empty_eq]

/--
@isnad1 id=eq.0h7v.s7.8de8d42f0c0f from=translated src=- shape=5e55ad13 vocab=c8d8e0d6
-/
@[simp] lemma lMap_rel₁ (r : L₁.Rel 1) (t : Semiterm L₁ ξ n) :
    lMap Φ (rel r ![t]) = rel (Φ.rel r) ![t.lMap Φ] := by
      simp[lMap_rel, Matrix.constant_eq_singleton]

/--
@isnad1 id=eq.0h8v.s7.8b3a12c57885 from=translated src=- shape=50df1c8f vocab=c8d8e0d6
-/
@[simp] lemma lMap_rel₂ (r : L₁.Rel 2) (t₁ t₂ : Semiterm L₁ ξ n) :
    lMap Φ (rel r ![t₁, t₂]) = rel (Φ.rel r) ![t₁.lMap Φ, t₂.lMap Φ] := by
  rw [lMap_rel]
  congr
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp_all

/--
@isnad1 id=eq.0h8v.s6.afb3bcb2c667 from=translated src=- shape=f825d73f vocab=f46bcded
-/
lemma lMap_nrel {k} (r : L₁.Rel k) (v : Fin k → Semiterm L₁ ξ n) :
    lMap Φ (nrel r v) = nrel (Φ.rel r) (fun i => (v i).lMap Φ) := rfl

/--
@isnad1 id=eq.0h7v.s6.d85b5b656da3 from=translated src=- shape=145bf1f5 vocab=3e51cf5d
-/
@[simp] lemma lMap_nrel₀ (r : L₁.Rel 0) (v : Fin 0 → Semiterm L₁ ξ n) :
    lMap Φ (nrel r v) = nrel (Φ.rel r) ![] := by simp[lMap_nrel, Matrix.empty_eq]

/--
@isnad1 id=eq.0h7v.s7.284cdf0ec139 from=translated src=- shape=5e55ad13 vocab=0b3af98d
-/
@[simp] lemma lMap_nrel₁ (r : L₁.Rel 1) (t : Semiterm L₁ ξ n) :
    lMap Φ (nrel r ![t]) = nrel (Φ.rel r) ![t.lMap Φ] := by
      simp[lMap_nrel, Matrix.constant_eq_singleton]

/--
@isnad1 id=eq.0h8v.s7.a57b326ffe0a from=translated src=- shape=50df1c8f vocab=0b3af98d
-/
@[simp] lemma lMap_nrel₂ (r : L₁.Rel 2) (t₁ t₂ : Semiterm L₁ ξ n) :
    lMap Φ (nrel r ![t₁, t₂]) = nrel (Φ.rel r) ![t₁.lMap Φ, t₂.lMap Φ] := by
  rw [lMap_nrel]
  congr
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp_all

/--
@isnad1 id=eq.0h6v.s8.feed2d0c801a from=translated src=- shape=e414b6c6 vocab=a14c27ae
-/
@[simp] lemma lMap_all (φ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∀' φ) = ∀' lMap Φ φ := rfl

/--
@isnad1 id=eq.0h6v.s8.f3b6a2c13017 from=translated src=- shape=e414b6c6 vocab=c862d04e
-/
@[simp] lemma lMap_ex (φ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∃' φ) = ∃' lMap Φ φ := rfl

/--
@isnad1 id=eq.0h7v.s9.4aa0711e559b from=translated src=- shape=0290dbab vocab=5a99e49b
-/
@[simp] lemma lMap_ball (φ ψ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∀[φ] ψ) = ∀[lMap Φ φ] lMap Φ ψ := by simp [ball]

/--
@isnad1 id=eq.0h7v.s9.aa76eb80a5a9 from=translated src=- shape=0290dbab vocab=3c321e71
-/
@[simp] lemma lMap_bex (φ ψ : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∃[φ] ψ) = ∃[lMap Φ φ] lMap Φ ψ := by simp [bex]

/--
@isnad1 id=eq.0h6v.s7.2e1ec65901ac from=translated src=- shape=f2f8d8f0 vocab=c0aa4e8d
-/
@[simp] lemma lMap_univClosure (φ : Semiformula L₁ ξ n) :
    lMap Φ (∀* φ) = ∀* lMap Φ φ := by induction n <;> simp [*, univClosure_succ]

/--
@isnad1 id=eq.0h6v.s7.3460ec33a40c from=translated src=- shape=f2f8d8f0 vocab=dfaebc06
-/
@[simp] lemma lMap_exClosure (φ : Semiformula L₁ ξ n) :
    lMap Φ (∃* φ) = ∃* lMap Φ φ := by induction n <;> simp [*, exClosure_succ]

/--
@isnad1 id=eq.0h7v.s8.b6899cf7d3eb from=translated src=- shape=351134b6 vocab=0af461cb
-/
@[simp] lemma lMap_univItr {k} (φ : Semiformula L₁ ξ (n + k)) :
    lMap Φ (∀^[k] φ) = ∀^[k] lMap Φ φ := by induction k <;> simp [*, univItr_succ]

/--
@isnad1 id=eq.0h7v.s8.c428be3b2bb1 from=translated src=- shape=351134b6 vocab=b3131ba1
-/
@[simp] lemma lMap_exItr {k} (φ : Semiformula L₁ ξ (n + k)) :
    lMap Φ (∃^[k] φ) = ∃^[k] lMap Φ φ := by induction k <;> simp [*, exItr_succ]

/--
@isnad1 id=eq.0h6v.s6.eabcac0de502 from=translated src=- shape=8b21a6a1 vocab=15cbbe44
-/
@[simp] lemma freeVariables_lMap [DecidableEq ξ] (Φ : L₁ →ᵥ L₂) (φ : Semiformula L₁ ξ n) :
    (Semiformula.lMap Φ φ).freeVariables = φ.freeVariables := by
  induction φ using Semiformula.rec' <;> try simp [lMap_rel, lMap_nrel, freeVariables_rel,
    freeVariables_nrel, *]

end Semiformula

/-- Imported declaration from the Incompleteness formalization. -/
abbrev Theory (L : Language) := Set (SyntacticFormula L)

/-- Imported declaration from the Incompleteness formalization. -/
abbrev ClosedTheory (L : Language) := Set (Sentence L)

instance : Collection (SyntacticFormula L) (Theory L) := inferInstance

instance : Collection (Sentence L) (ClosedTheory L) := inferInstance

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Theory.lMap (Φ : L₁ →ᵥ L₂) (T : Theory L₁) :
    Theory L₂ := Semiformula.lMap Φ '' T

namespace Theory

variable (T U : Theory L)

instance {L : Language} : Add (Theory L) := ⟨(· ∪ ·)⟩

/--
@isnad1 id=eq.0h3v.s5.d63298bc8ab5 from=translated src=- shape=5279f093 vocab=b22922d1
-/
lemma add_def : T + U = T ∪ U := rfl

end Theory

end FirstOrder

end LO
