/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Tengoku

public import Tengoku.LeanPool.LeanPool.PDL.Syntax
public import Tengoku.LeanPool.LeanPool.PDL.General.ListFinset

/-! # Semantics (Section 2.2) -/

@[expose] public section

namespace PDL

/-! ## Models and Truth -/

/-- Kripke Models, also known as Labelled Transition Systems -/
structure KripkeModel (W : Type) : Type where
  /-- The truth assignment for atomic propositions at each world. -/
  val : W → Nat → Prop
  /-- The accessibility relation for each atomic program. -/
  Rel : Nat → W → W → Prop

/-- The syntactic measure used to define formula evaluation and program relations mutually. -/
@[simp]
def complexityOfQuery {W : Type} :
    PSum (Σ' (_ : KripkeModel W) (_ : W), Formula)
         (Σ' (_ : KripkeModel W) (_ : Program) (_ : W), W) → ℕ
  | PSum.inl val => lengthOfFormula val.snd.snd
  | PSum.inr val => lengthOfProgram val.snd.fst

mutual
  /-- Truth of a PDL formula at a world in a Kripke model. -/
  @[simp]
  def evaluate {W : Type} : KripkeModel W → W → Formula → Prop
    | _, _, ⊥ => False
    | M, w, ·c => M.val w c
    | M, w, ~φ => Not (evaluate M w φ)
    | M, w, φ⋀ψ => evaluate M w φ ∧ evaluate M w ψ
    | M, w, ⌈α⌉ φ => ∀ v : W, relate M α w v → evaluate M v φ
  /-- The binary relation denoted by a PDL program in a Kripke model. -/
  @[simp]
  def relate {W : Type} : KripkeModel W → Program → W → W → Prop
    | M, ·c, w, v => M.Rel c w v
    | M, α;'β, w, v => ∃ y, relate M α w y ∧ relate M β y v
    | M, α⋓β, w, v => relate M α w v ∨ relate M β w v
    | M, ∗α, w, v => Relation.ReflTransGen (relate M α) w v
    | M, ?'φ, w, v => w = v ∧ evaluate M w φ
end

-- Reopen namespaces after mutual blocks to keep source-based declaration audits aligned.
end PDL

namespace PDL

theorem evalDis {W M f g} {w : W} : evaluate M w (f⋁g) ↔ evaluate M w f ∨ evaluate M w g :=
  by
  simp
  tauto

/-- Evaluate a formula at a pointed Kripke model. -/
@[simp]
def evaluatePoint {W : Type} : KripkeModel W × W → Formula → Prop
  | (M, w), ϕ => evaluate M w ϕ

/-- Validity of a formula at every world of every Kripke model. -/
def tautology (φ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) w, evaluate M w φ

/-- Falsity of a formula at every world of every Kripke model. -/
def contradiction (φ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) w, ¬evaluate M w φ

/-! ## Satisfiability -/

-- MB: Definition 5, page 9
/-- Types equipped with a notion of semantic satisfiability. -/
class HasSat (α : Type) where
  /-- Existence of a semantic model for an object. -/
  satisfiable : α → Prop
open HasSat
@[simp]
instance formHasSat : HasSat Formula :=
  HasSat.mk fun ϕ => ∃ (W : _) (M : KripkeModel W) (w : _), evaluate M w ϕ
@[simp]
instance setHasSat : HasSat (Finset Formula) :=
  HasSat.mk fun X => ∃ (W : _) (M : KripkeModel W) (w : _), ∀ φ ∈ X, evaluate M w φ
@[simp]
instance listHasSat : HasSat (List Formula) :=
  HasSat.mk fun X => ∃ (W : _) (M : KripkeModel W) (w : _), ∀ φ ∈ X, evaluate M w φ

/-! ## Semantic implication and vDash notation -/

/-- Semantic consequence between finite sets of formulas. -/
def semImpliesSets (X : Finset Formula) (Y : Finset Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w),
    (∀ φ ∈ X, evaluate M w φ) → ∀ ψ ∈ Y, evaluate M w ψ

/-- Semantic consequence between lists of formulas. -/
def semImpliesLists (X : List Formula) (Y : List Formula) :=
  ∀ (W : Type) (M : KripkeModel W) (w),
    (∀ φ ∈ X, evaluate M w φ) → ∀ ψ ∈ Y, evaluate M w ψ

/-- Agreement of two formulas at every pointed Kripke model. -/
def semEquiv (φ ψ : Formula) :=
  ∀ (W : Type) (M : KripkeModel W) w, evaluate M w φ ↔ evaluate M w ψ

/-- Agreement of two program relations in every Kripke model. -/
def relEquiv (α β : Program) :=
  ∀ (W : Type) (M : KripkeModel W) v w, relate M α v w ↔ relate M β v w

/-- An overloaded semantic satisfaction or consequence relation. -/
class vDash (α : Type) (β : Type) where
  /-- The semantic relation for the two specified types. -/
  SemImplies : α → β → Prop

open vDash

instance modelCanSemImplyForm {W : Type} : vDash (KripkeModel W × W) Formula :=
  vDash.mk (@evaluatePoint W)
@[simp]
instance modelCanSemImplyList {W : Type} : vDash (KripkeModel W × W) (List Formula) :=
  vDash.mk (fun ⟨M,w⟩ fs => ∀ f ∈ fs, @evaluate W M w f)
instance modelCanSemImplyAnyFormula {W : Type} : vDash (KripkeModel W × W) AnyFormula :=
  ⟨fun (M,w) ξ => match ξ with
    | (AnyFormula.normal φ) => evaluate M w φ
    | .loaded χ => evaluate M w χ.unload⟩
instance modelCanSemImplyAnyNegFormula {W : Type} : vDash (KripkeModel W × W) AnyNegFormula :=
  vDash.mk (fun ⟨M,w⟩ ⟨ξ⟩ => ¬ SemImplies (M, w) ξ)
instance setCanSemImplySet : vDash (List Formula) (List Formula) := vDash.mk semImpliesLists
instance setCanSemImplyForm : vDash (List Formula) Formula :=
  vDash.mk fun X ψ => semImpliesLists X [ψ]
instance formCanSemImplySet : vDash Formula (List Formula) :=
  vDash.mk fun φ X => semImpliesLists [φ] X
instance formCanSemImplyForm : vDash Formula Formula :=
  vDash.mk fun φ ψ => semImpliesLists [φ] [ψ]

/-- Semantic satisfaction or consequence. -/
scoped infixl:40 " ⊨ " => SemImplies

/-- Semantic equivalence of formulas. -/
scoped infixl:40 " ≡ " => semEquiv

/-- Semantic equivalence of program relations. -/
scoped infixl:40 " ≡ᵣ " => relEquiv

/-- Failure of semantic satisfaction or consequence. -/
scoped infixl:40 " ⊭ " => fun a b => ¬a⊨b

@[simp]
theorem singletonSat_iff_sat : ∀ φ, satisfiable ({φ} : Finset Formula) ↔ satisfiable φ :=
  by
  intro phi
  simp [satisfiable]

@[simp]
theorem vDashSingleton_iff_vDash_formula {M : KripkeModel W} {w : W} :
    ∀ φ, (M, w) ⊨ ([φ] : List Formula) ↔ evaluate M w φ :=
  by
  intro phi
  simp [SemImplies]

-- useful lemmas to connect different ⊨ cases

theorem equiv_iff (φ ψ : Formula) (φ_eq_ψ : φ ≡ ψ) :
    ∀ {W} {M : KripkeModel W} {w : W},
    (M, w) ⊨ φ ↔ (M, w) ⊨ ψ :=
  by
    intro W M w
    constructor
    · intro
      have : evaluate M w φ := by tauto
      rw [φ_eq_ψ] at this
      tauto
    · intro
      have : evaluate M w ψ := by tauto
      rw [← φ_eq_ψ] at this
      tauto

/-- Relational composition of a list of programs, with equality for the empty list. -/
def relateSeq {W} (M : KripkeModel W) (δ : List Program) (w v : W) : Prop :=
  match δ with
  | [] => w = v
  | (α::as) => ∃ u, relate M α w u ∧ relateSeq M as u v

@[simp]
theorem relateSeq_nil {M : KripkeModel W} {w v : W} :
    relateSeq M [] w v ↔ w = v := by
  simp [relateSeq]

@[simp]
theorem relateSeq_singleton {M : KripkeModel W} {α : Program} {w v : W} :
    relateSeq M [α] w v ↔ relate M α w v := by
  simp [relateSeq]

theorem relateSeq_cons {M : KripkeModel W} {d : Program} {δ : List Program} {w v : W} :
    relateSeq M (d :: δ) w v ↔ ∃ u, relate M d w u ∧ relateSeq M δ u v := iff_of_eq rfl

theorem relateSeq_append {M : KripkeModel W} {l1 l2 : List Program} {w v : W} :
    relateSeq M (l1 ++ l2) w v ↔ ∃ u, relateSeq M l1 w u ∧ relateSeq M l2 u v := by
  induction l1 generalizing w v
  · simp [relateSeq]
  case cons l l1 IH =>
    simp [relateSeq]
    aesop

lemma relate_steps_iff_relateSeq (M : KripkeModel W) (δ : List Program) (w v : W) :
    relate M (Program.steps δ) w v ↔ relateSeq M δ w v := by
  induction δ generalizing w v <;> simp_all [relateSeq]

/-- Relating along `Program.unions L` means relating along one of the programs in `L`. -/
lemma relate_unions {W} {M : KripkeModel W} : ∀ (L : List Program) (v u : W),
    relate M (Program.unions L) v u ↔ ∃ a ∈ L, relate M a v u
  | [], v, u => by simp [Program.unions, relate, evaluate]
  | [a], v, u => by simp [Program.unions]
  | a :: b :: L, v, u => by
      simp only [Program.unions, relate, relate_unions (b :: L) v u, List.mem_cons]
      constructor
      · rintro (h | ⟨c, hc, h⟩)
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨c, Or.inr hc, h⟩
      · rintro ⟨c, rfl | hc, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨c, hc, h⟩

theorem evalBoxes (δ : List Program) φ :
    evaluate M w (⌈⌈δ⌉⌉φ) ↔ (∀ v, relateSeq M δ w v → evaluate M v φ) := by
  induction δ generalizing w
  · simp [relateSeq]
  case cons α δ IH =>
    simp only [Formula.boxes_cons]
    constructor
    · intro lhs v v_αδ_w
      simp only [evaluate, relateSeq] at *
      rcases v_αδ_w with ⟨u, w_α_u, u_δ_v⟩
      specialize @IH u
      refine IH.1 ?_ v u_δ_v
      simp_all only [true_iff]
    · intro rhs u w_α_u
      apply IH.2
      intro v u_δ_v
      apply rhs
      simp only [relateSeq]
      use u

@[simp]
theorem evaluate_unload_box {af} :
    evaluate M w (⌊α⌋af).unload ↔ ∀ v, relate M α w v → (M,v) ⊨ af := by
  cases af <;> simp_all [SemImplies]

/-- Semantic induction rule for the Kleene star operator. -/
theorem stepToStar : φ ⊨ (⌈α⌉φ) ⋀ ψ  →  φ ⊨ (⌈∗α⌉ψ) := by
  intro hyp W M w w_φ
  specialize hyp W M
  have : ∀ v, relate M (∗α) w v → evaluate M v φ := by
    intro v w_sta_v
    simp_all only [List.mem_singleton, forall_eq, evaluate, relate]
    induction w_sta_v
    case refl =>
      simp_all
    case tail s t _ s_α_t s_φ =>
      exact (hyp s s_φ).1 t s_α_t
  simp_all

end PDL
