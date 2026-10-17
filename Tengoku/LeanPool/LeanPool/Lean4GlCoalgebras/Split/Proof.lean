/-
Copyright (c) 2026 Madeleine Gignoux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Madeleine Gignoux
-/
module

public import Tengoku.LeanPool.LeanPool.Lean4GlCoalgebras.Logic.Syntax
public import Tengoku

/-! ## Defining GL-split proof systems.

Here we define the GL-split-proof system along with finitization and basic properties. We use the
namespace Split to distinguish from our general GL-proofs.
-/

@[expose] public section
open scoped Lean4GlCoalgebras.Formula


namespace Lean4GlCoalgebras

namespace Split

/-! # Basic components of the GL-split proof system.-/

/-- Rule applications for the GL-split proof system. -/
inductive RuleApp
  | topₗ : (Δ : SplitSequent) → (Sum.inl ⊤) ∈ Δ → RuleApp
  | topᵣ : (Δ : SplitSequent) → (Sum.inr ⊤) ∈ Δ → RuleApp
  | axₗₗ : (Δ : SplitSequent) → (n : Nat) → (Sum.inl (at n) ∈ Δ ∧ Sum.inl (na n) ∈ Δ) → RuleApp
  | axₗᵣ : (Δ : SplitSequent) → (n : Nat) → (Sum.inl (at n) ∈ Δ ∧ Sum.inr (na n) ∈ Δ) → RuleApp
  | axᵣₗ : (Δ : SplitSequent) → (n : Nat) → (Sum.inr (at n) ∈ Δ ∧ Sum.inl (na n) ∈ Δ) → RuleApp
  | axᵣᵣ : (Δ : SplitSequent) → (n : Nat) → (Sum.inr (at n) ∈ Δ ∧ Sum.inr (na n) ∈ Δ) → RuleApp
  | andₗ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inl (A & B) ∈ Δ → RuleApp
  | andᵣ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inr (A & B) ∈ Δ → RuleApp
  | orₗ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inl (A v B) ∈ Δ → RuleApp
  | orᵣ : (Δ : SplitSequent) → (A : Formula) → (B : Formula) → Sum.inr (A v B) ∈ Δ → RuleApp
  | boxₗ : (Δ : SplitSequent) → (A : Formula) → Sum.inl (□ A) ∈ Δ → RuleApp
  | boxᵣ : (Δ : SplitSequent) → (A : Formula) → Sum.inr (□ A) ∈ Δ → RuleApp

/-- Endofunctor for the GL-split proof system. -/
@[simp] def T : (CategoryTheory.Functor Type Type) where
  obj := fun X ↦ (RuleApp × List X)
  map := fun {X Y} f ↦
    TypeCat.ofHom fun x ↦
      match x with
      | (r, A) => (r, A.map (CategoryTheory.ConcreteCategory.hom f))
  map_id := by aesop_cat
  map_comp := by aesop_cat

/-- Given a RuleApp, obtain the principal formulas. -/
def fₚ : RuleApp → SplitSequent
  | RuleApp.topₗ _ _ => {Sum.inl ⊤}
  | RuleApp.topᵣ _ _ => {Sum.inr ⊤}
  | RuleApp.axₗₗ _ n _ => {Sum.inl (at n), Sum.inl (na n)}
  | RuleApp.axₗᵣ _ n _ => {Sum.inl (at n), Sum.inr (na n)}
  | RuleApp.axᵣₗ _ n _ => {Sum.inr (at n), Sum.inl (na n)}
  | RuleApp.axᵣᵣ _ n _ => {Sum.inr (at n), Sum.inr (na n)}
  | RuleApp.andₗ _ A B _ => {Sum.inl (A & B)}
  | RuleApp.andᵣ _ A B _ => {Sum.inr (A & B)}
  | RuleApp.orₗ _ A B _ => {Sum.inl (A v B)}
  | RuleApp.orᵣ _ A B _ => {Sum.inr (A v B)}
  | RuleApp.boxₗ _ A _ => {Sum.inl (□ A)}
  | RuleApp.boxᵣ _ A _ => {Sum.inr (□ A)}

/-- Given a RuleApp, obtain the split sequent. -/
def f : RuleApp → SplitSequent
  | RuleApp.topₗ Δ _ => Δ
  | RuleApp.topᵣ Δ _ => Δ
  | RuleApp.axₗₗ Δ _ _ => Δ
  | RuleApp.axₗᵣ Δ _ _ => Δ
  | RuleApp.axᵣₗ Δ _ _ => Δ
  | RuleApp.axᵣᵣ Δ _ _ => Δ
  | RuleApp.andₗ Δ _ _ _ => Δ
  | RuleApp.andᵣ Δ _ _ _ => Δ
  | RuleApp.orₗ Δ _ _ _ => Δ
  | RuleApp.orᵣ Δ _ _ _ => Δ
  | RuleApp.boxₗ Δ _ _ => Δ
  | RuleApp.boxᵣ Δ _ _ => Δ

/-- Given a RuleApp, obtain the non-principal formulas. -/
def fₙ : RuleApp → SplitSequent := fun Γ ↦ f Γ \ fₚ Γ

/-- Relating principal formulas, non-principal formulas, and the sequent.
@isnad1 id=eq.0h1v.s9.a80025b44682 from=translated src=- shape=0973c4bc vocab=78b8c2b7
-/
lemma fₙ_alternate (r : RuleApp) : fₙ r = match r with
  | RuleApp.topₗ Δ _ => Δ \ {Sum.inl ⊤}
  | RuleApp.topᵣ Δ _ => Δ \ {Sum.inr ⊤}
  | RuleApp.axₗₗ Δ n _ => Δ \ {Sum.inl (at n), Sum.inl (na n)}
  | RuleApp.axₗᵣ Δ n _ => Δ \ {Sum.inl (at n), Sum.inr (na n)}
  | RuleApp.axᵣₗ Δ n _ => Δ \ {Sum.inr (at n), Sum.inl (na n)}
  | RuleApp.axᵣᵣ Δ n _ => Δ \ {Sum.inr (at n), Sum.inr (na n)}
  | RuleApp.andₗ Δ A B _ => Δ \ {Sum.inl (A & B)}
  | RuleApp.andᵣ Δ A B _ => Δ \ {Sum.inr (A & B)}
  | RuleApp.orₗ Δ A B _ => Δ \ {Sum.inl (A v B)}
  | RuleApp.orᵣ Δ A B _ => Δ \ {Sum.inr (A v B)}
  | RuleApp.boxₗ Δ A _ => Δ \ {Sum.inl (□ A)}
  | RuleApp.boxᵣ Δ A _ => Δ \ {Sum.inr (□ A)} := by cases r <;> simp [fₙ, f, fₚ]

/--
@isnad1 id=le.0h1v.s3.02d4d33ae482 from=translated src=- shape=b70c6bb1 vocab=a14aafeb
-/
lemma fₙ_sub_f {r : RuleApp} : fₙ r ⊆ f r := by simp [fₙ]

/-- Auxiliary declaration used in the GL coalgebra development. -/
def RuleApp.isBox : RuleApp → Prop
  | RuleApp.boxₗ _ _ _ => true
  | RuleApp.boxᵣ _ _ _ => true
  | _ => false

/-- Get RuleApp of a node (first projection). -/
def r {X : Type} (α : X → T.obj X) (x : X) := (α x).1

/-- Get premises of a node (second projection). -/
def p {X : Type} (α : X → T.obj X) (x : X) := (α x).2

/-- Edge relation induced by `p`. -/
def edge {X : Type} (α : X → T.obj X) (x y : X) : Prop := y ∈ p α x

/-- Definition of GL-split proof. -/
structure Proof where
  /-- Auxiliary declaration used in the GL coalgebra development. -/
  X : Type
  /-- Auxiliary declaration used in the GL coalgebra development. -/
  α : X → T.obj X
  step : ∀ (x : X), match r α x with
    | RuleApp.topₗ _ _ => p α x = ∅
    | RuleApp.topᵣ _ _ => p α x = ∅
    | RuleApp.axₗₗ _ _ _ => p α x = ∅
    | RuleApp.axₗᵣ _ _ _ => p α x = ∅
    | RuleApp.axᵣₗ _ _ _ => p α x = ∅
    | RuleApp.axᵣᵣ _ _ _ => p α x = ∅
    | RuleApp.andₗ _ A B _ =>
        (p α x).map (fun x ↦ f (r α x)) =
          [(fₙ (r α x)) ∪ {Sum.inl A}, (fₙ (r α x)) ∪ {Sum.inl B}]
    | RuleApp.andᵣ _ A B _ =>
        (p α x).map (fun x ↦ f (r α x)) =
          [(fₙ (r α x)) ∪ {Sum.inr A}, (fₙ (r α x)) ∪ {Sum.inr B}]
    | RuleApp.orₗ _ A B _ =>
        (p α x).map (fun x ↦ f (r α x)) =
          [(fₙ (r α x)) ∪ {Sum.inl A, Sum.inl B}]
    | RuleApp.orᵣ _ A B _ =>
        (p α x).map (fun x ↦ f (r α x)) =
          [(fₙ (r α x)) ∪ {Sum.inr A, Sum.inr B}]
    | RuleApp.boxₗ _ A _ =>
        (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)).D ∪ {Sum.inl A}]
    | RuleApp.boxᵣ _ A _ =>
        (p α x).map (fun x ↦ f (r α x)) = [(fₙ (r α x)).D ∪ {Sum.inr A}]

/-- GL-split proofs are coalgebras. Note: we can do this the other way around, i.e. Proof extends
    CategoryTheory.Endofunctor.Coalgebra T, however I find X and α more explicative than V and str
-/
def Proof.toCoalgebra (𝕏 : Proof) : CategoryTheory.Endofunctor.Coalgebra T where
  V := 𝕏.X
  str := TypeCat.ofHom 𝕏.α

/-- Auxiliary declaration used in the GL coalgebra development. -/
def proves (𝕏 : Proof) (Δ : SplitSequent) : Prop := ∃ x : 𝕏.X, f (r 𝕏.α x) = Δ
/-- Auxiliary declaration used in the GL coalgebra development. -/
def SplitSequent.isTrue (Δ : SplitSequent) : Prop := ∃ (𝕏 : Proof), proves 𝕏 Δ

/-- Auxiliary declaration used in the GL coalgebra development. -/
infixr:6 "⊢" => proves
/-- Auxiliary declaration used in the GL coalgebra development. -/
prefix:40 "⊢" => SplitSequent.isTrue

/-- Auxiliary declaration used in the GL coalgebra development. -/
def equiv (φ : Formula) (ψ : Formula) : Prop :=
  (∃ (𝕏 : Proof), 𝕏 ⊢ {Sum.inl (~ψ), Sum.inr φ}) ∧
    (∃ (𝕏 : Proof), 𝕏 ⊢ {Sum.inr ψ, Sum.inl (~φ)})
/-- Auxiliary declaration used in the GL coalgebra development. -/
scoped infixr:7 "≅" => equiv

/-! # Fischer-Ladner properties of GL-split proofs -/

/-- Every edge is contained in FL closure.
@isnad1 id=le.1h3v.s5.a50190a420a7 from=translated src=- shape=ad21cbb1 vocab=bad8119b
-/
lemma edge_in_FL {𝕏 : Proof} {x y : 𝕏.X} (x_y : (edge 𝕏.α) x y) :
  f (r 𝕏.α y) ⊆ SplitSequent.FL (f (r 𝕏.α x)) := by
  unfold edge at x_y
  have := 𝕏.step x
  cases rule : r 𝕏.α x <;> simp only [rule] at this
  case andₗ Δ φ ψ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_cons, List.not_mem_nil, or_false] at x_y
    rcases x_y with h|h <;> rw [h] <;>
      simp only [SplitSequent.FL, Finset.subset_iff,
        Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion] <;>
      intro χ χ_cases <;>
      rcases χ_cases with h|_ <;> subst_eqs
    · exact ⟨χ, fₙ_sub_f h, SplitFormula.FL_refl⟩
    · exact ⟨Sum.inl (φ & ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
    · exact ⟨χ, fₙ_sub_f h, SplitFormula.FL_refl⟩
    · exact ⟨Sum.inl (φ & ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
  case andᵣ Δ φ ψ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_cons, List.not_mem_nil, or_false] at x_y
    rcases x_y with h|h <;> rw [h] <;>
      simp only [SplitSequent.FL, Finset.subset_iff,
        Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion] <;>
      intro χ χ_cases <;>
      rcases χ_cases with h|_ <;> subst_eqs
    · exact ⟨χ, fₙ_sub_f h, SplitFormula.FL_refl⟩
    · exact ⟨Sum.inr (φ & ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
    · exact ⟨χ, fₙ_sub_f h, SplitFormula.FL_refl⟩
    · exact ⟨Sum.inr (φ & ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
  case orₗ Δ φ ψ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_singleton] at x_y
    simp only [x_y, Finset.union_insert, SplitSequent.FL, Finset.subset_iff, Finset.mem_insert,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
    intro χ χ_cases
    rcases χ_cases with _|h|_ <;> subst_eqs
    · exact ⟨Sum.inl (φ v ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
    · exact ⟨χ, fₙ_sub_f h, SplitFormula.FL_refl⟩
    · exact ⟨Sum.inl (φ v ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
  case orᵣ Δ φ ψ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_singleton] at x_y
    simp only [x_y, Finset.union_insert, SplitSequent.FL, Finset.subset_iff, Finset.mem_insert,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
    intro χ χ_cases
    rcases χ_cases with _|h|_ <;> subst_eqs
    · exact ⟨Sum.inr (φ v ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
    · exact ⟨χ, fₙ_sub_f h, SplitFormula.FL_refl⟩
    · exact ⟨Sum.inr (φ v ψ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
  case boxₗ Δ φ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_singleton] at x_y
    simp only [x_y, SplitSequent.FL, Finset.subset_iff,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
    intro χ χ_cases
    rcases χ_cases with h|_ <;> subst_eqs
    · simp only [SplitSequent.D, Bool.decide_eq_true, Finset.mem_union, Finset.mem_filter,
        Finset.mem_filterMap, Sum.exists] at h
      rcases h with ⟨h,_⟩|h
      · refine ⟨χ, fₙ_sub_f h, by simp [SplitFormula.FL_refl]⟩
      · rcases χ with χ | χ
        · refine ⟨Sum.inl (◇χ), ?_, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
          exact fₙ_sub_f (by simpa using h)
        · refine ⟨Sum.inr (◇χ), ?_, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
          exact fₙ_sub_f (by simpa using h)
    · exact ⟨Sum.inl (□φ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
  case boxᵣ Δ φ in_Δ =>
    apply @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) at x_y
    simp only [this, List.mem_singleton] at x_y
    simp only [x_y, SplitSequent.FL, Finset.subset_iff,
      Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion]
    intro χ χ_cases
    rcases χ_cases with h|_ <;> subst_eqs
    · simp only [SplitSequent.D, Bool.decide_eq_true, Finset.mem_union, Finset.mem_filter,
        Finset.mem_filterMap, Sum.exists] at h
      rcases h with ⟨h,_⟩|h
      · refine ⟨χ, fₙ_sub_f h, by simp [SplitFormula.FL_refl]⟩
      · rcases χ with χ | χ
        · refine ⟨Sum.inl (◇χ), ?_, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
          exact fₙ_sub_f (by simpa using h)
        · refine ⟨Sum.inr (◇χ), ?_, by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
          exact fₙ_sub_f (by simpa using h)
    · exact ⟨Sum.inr (□φ), by simp [f, in_Δ], by simp [SplitFormula.FL, SplitFormula.FL_refl]⟩
  all_goals
    simp_all

/-- Every path is contained in FL closure.
@isnad1 id=le.1h3v.s5.0d30dc300f67 from=translated src=- shape=571bb801 vocab=d425aa11
-/
lemma path_in_FL {𝕏 : Proof} {x y : 𝕏.X} (x_y : Relation.ReflTransGen (edge 𝕏.α) x y) :
  f (r 𝕏.α y) ⊆ SplitSequent.FL (f (r 𝕏.α x)) := by
  induction x_y
  case refl => exact SplitSequent.FL_refl
  case tail y z x_y y_z fy_fx =>
    apply Finset.Subset.trans (edge_in_FL y_z)
    apply SplitSequent.FL_mon at fy_fx
    simp only [SplitSequent.FL_idem] at fy_fx
    exact fy_fx

/-! # Point Generated GL-split Proofs -/

/-- Structure morphism for Point Generation. -/
@[simp] def αPoint (𝕐 : Proof) (x : 𝕐.X) :
    {y : 𝕐.X // Relation.ReflTransGen (edge 𝕐.α) x y} →
      T.obj {y : 𝕐.X // Relation.ReflTransGen (edge 𝕐.α) x y} :=
  fun y ↦ ⟨(𝕐.α y.1).1,
    List.pmap (fun x y ↦ ⟨x, y⟩) (𝕐.α y.1).2
      (fun _ z_in ↦ Relation.ReflTransGen.tail y.2 z_in)⟩

/-- Point Generated Split Proof. -/
def pointGeneratedProof (𝕐 : Proof) (x : 𝕐.X) : Proof where
  X := {y : 𝕐.X // Relation.ReflTransGen (edge 𝕐.α) x y }
  α := αPoint 𝕐 x
  step := by
    intro ⟨y, y_in⟩
    have h := 𝕐.step y
    simp_all only [r, αPoint]
    cases r_def : (𝕐.α y).1 <;>
      simp_all only [p, αPoint, List.pmap, List.map_pmap, List.pmap_eq_map,
        List.empty_eq]

/--
@isnad1 id=le.0h3v.s5.8deaf3ed08cd from=translated src=- shape=97bf6610 vocab=14af8965
-/
lemma node_in_pg_sequent_in_FL (𝕏 : Proof) (x : 𝕏.X) :
    ∀ y : (pointGeneratedProof 𝕏 x).X,
      f (r (αPoint 𝕏 x) y) ⊆ SplitSequent.FL (f (r 𝕏.α x)) := by
  intro y
  exact path_in_FL y.2

/-! # Filtration of GL-Proofs -/

/-- Equivalence relation used for Filtration. -/
instance fEqEquiRel (𝕏 : Proof) : Setoid 𝕏.X where
  r x y := f (r 𝕏.α x) = f (r 𝕏.α y)
  iseqv := ⟨by intro x; exact rfl,
            by intro x y h; exact Eq.symm h,
            by intro x y z h1 h2; exact Eq.trans h1 h2⟩

/-- Structure morphism for Filtration. -/
@[simp] noncomputable def αQuot 𝕐 (x : Quotient (fEqEquiRel 𝕐)) :=
  let structureMap := 𝕐.α (Quotient.out x)
  (structureMap.1, structureMap.2.map (Quotient.mk (fEqEquiRel 𝕐)))

/-- Filtration of a GL-split Proof is a GL-split proof. -/
noncomputable def filtration (𝕐 : Proof) : Proof where
  X := Quotient (fEqEquiRel 𝕐)
  α := αQuot 𝕐
  step := by
    intro x
    cases x using Quotient.inductionOn
    case h x =>
      have hyp := fun x ↦ @Quotient.mk_out _ (fEqEquiRel 𝕐) x
      have h := 𝕐.step (@Quotient.out _ (fEqEquiRel 𝕐) ⟦x⟧)
      simp only [r, p, αQuot] at *
      convert h <;>
        simp_all only [Setoid.ker_def, List.empty_eq, Finset.union_singleton,
          Finset.union_insert, List.map_eq_singleton_iff, List.map_eq_nil_iff, List.map_map,
          List.map_inj_left, Function.comp_apply]
      all_goals
        intro x x_in
        exact hyp x

/-! # Finite Proof Property -/

/-- Given a split proof of `Δ` there exists a finite split proof of `Δ`.
@isnad1 id=ex.1h2v.s4.5190fcdb711d from=translated src=- shape=d0e62794 vocab=629b0c8a
-/
theorem finite_proof_of_proof (𝕏 : Proof) (Δ : SplitSequent) :
    (𝕏 ⊢ Δ) → ∃ 𝕐, Finite 𝕐.X ∧ (𝕐 ⊢ Δ) := by
  intro X_proves_Δ
  have ⟨x, f_Δ⟩ := X_proves_Δ
  use pointGeneratedProof (filtration 𝕏) (Quotient.mk (fEqEquiRel 𝕏) x)
  constructor
  · have h : Finite (SplitSequent.FL Δ).powerset := by
      apply Set.finite_coe_iff.1
      apply Finset.finite_toSet
    apply @Finite.of_injective _ _ h (fun y ↦
      ⟨f (r ((pointGeneratedProof (filtration 𝕏) ⟦x⟧).α) y), by
      simp only [Finset.mem_powerset]
      have in_fl := node_in_pg_sequent_in_FL (filtration 𝕏) ⟦x⟧ y
      have hΔ : Δ = f (r (filtration 𝕏).α ⟦x⟧) := by
        simp only [←f_Δ, filtration, r, αQuot]
        exact Eq.symm <| Quotient.mk_out x
      rw [hΔ]
      exact in_fl⟩)
    intro z1 z2 f_z_eq
    have f_z_eq := by simpa [pointGeneratedProof, filtration, r] using f_z_eq
    apply Subtype.ext
    apply Quotient.out_equiv_out.1
    exact f_z_eq
  · use ⟨Quotient.mk (fEqEquiRel 𝕏) x, Relation.ReflTransGen.refl⟩
    rw [←f_Δ]
    simp only [r, filtration, pointGeneratedProof, αPoint, αQuot]
    exact Quotient.mk_out x

/-! # Properties of (infinite) paths -/

/-- Auxiliary declaration used in the GL coalgebra development. -/
def nbEdge {X : Type} (α : X → T.obj X) (x y : X) := y ∈ p α x ∧ ¬ (r α x).isBox

/-- Edge relation restricted to nodes satisfying predicate `p`. -/
def edgeRestr {𝕏 : Proof} (p : 𝕏.X → Prop) : 𝕏.X → 𝕏.X → Prop :=
  fun x y ↦ edge 𝕏.α x y ∧ p x ∧ p y

/-- If a finite proof has no restricted loops, then there must exist a leaf.
@isnad1 id=ex.1h4v.s6.5424de428523 from=translated src=- shape=1a20e71b vocab=335f3b5f
-/
lemma finite_and_no_loop_implies_exists_leaf {𝕏 : Proof} [Finite 𝕏.X] (h : 𝕏.X → Prop)
    (x : 𝕏.X) (x_sat : h x) :
    (¬ ∃ y, Relation.TransGen (edgeRestr h) y y) →
    ∃ y : 𝕏.X, h y ∧ ∀ z ∈ (p 𝕏.α y), ¬ h z := by
  intro mp
  by_contra con
  simp_all only [not_exists, not_and, not_forall, not_not, exists_prop]
  let chain : Nat → {x : 𝕏.X // h x} :=
    Nat.rec ⟨x, x_sat⟩
      (fun n ih => ⟨(con ih.1 ih.2).choose, (con ih.1 ih.2).choose_spec.2⟩)
  have chain_prop : ∀ n, (edgeRestr h) (chain n).1 (chain (n + 1)).1 := by
    intro n
    induction n <;> simp only [edgeRestr, chain, Nat.rec_zero]
    case zero =>
      exact ⟨(Exists.choose_spec (con x x_sat)).1,
        x_sat, (Exists.choose_spec (con x x_sat)).2⟩
    case succ n ih =>
      exact ⟨(Exists.choose_spec (con (chain (n + 1)).1 (chain (n + 1)).2)).1,
        ih.2.2, (Exists.choose_spec (con (chain (n + 1)) ih.2.2)).2⟩
  have ci_cj : ∀ k n, Relation.TransGen (edgeRestr h) (chain k).1 (chain (k + n + 1)).1 := by
    intro m n
    induction n
    case zero => exact Relation.TransGen.single (chain_prop _)
    case succ k ih => exact Relation.TransGen.tail ih (chain_prop (m + k + 1))
  have chain_inj : Function.Injective chain := by
    intro i j con
    rcases Nat.lt_trichotomy i j with lt | eq | gt
    · exfalso
      apply mp (chain i).1
      have ⟨k, diff⟩ := Nat.exists_eq_add_of_lt lt
      convert ci_cj i k
      simp [con, diff]
    · exact eq
    · exfalso
      apply mp (chain i).1
      have ⟨k, diff⟩ := Nat.exists_eq_add_of_lt gt
      convert ci_cj j k
      simp [diff]
  have inf_X := Infinite.of_injective chain chain_inj
  apply inf_X.not_finite
  apply Subtype.finite

/--
@isnad1 id=mem.2h4v.s5.4a188eb6df25 from=translated src=- shape=4e7edf6f vocab=a3f154bc
-/
lemma in_vocab_of_path_left {𝕏 : Proof} {x y : 𝕏.X} (x_y : Relation.ReflTransGen (edge 𝕏.α) x y)
  {n} (n_in : n ∈ (SplitSequent.left (f (r 𝕏.α y))).vocab) :
    n ∈ (SplitSequent.left (f (r 𝕏.α x))).vocab := by
  induction x_y
  case refl => exact n_in
  case tail y z x_y y_z ih =>
    apply ih
    have Xh := 𝕏.step y
    simp only [Sequent.vocab, SplitSequent.left, Finset.mem_biUnion, Finset.mem_filterMap,
      Sum.getLeft?_eq_some_iff, exists_eq_right] at n_in
    have ⟨φ, φ_in_f, n_in_φ⟩ := n_in
    cases r_def : r 𝕏.α y <;>
      simp_all only [edge, List.empty_eq, Finset.union_singleton, Finset.union_insert,
        List.map_eq_singleton_iff, List.not_mem_nil] <;>
      simp only [f, SplitSequent.left, Sequent.vocab, Finset.mem_biUnion,
        Finset.mem_filterMap, Sum.getLeft?_eq_some_iff, exists_eq_right]
    case andₗ Δ φ₁ φ₂ in_Δ =>
      have := @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) y_z
      simp_all only [List.mem_cons, List.not_mem_nil, or_false]
      rcases this with l | l <;>
        simp only [l, fₙ_alternate, Finset.mem_insert, Finset.mem_sdiff,
          Finset.mem_singleton, Sum.inl.injEq] at φ_in_f
      all_goals
      · rcases φ_in_f with c1 | c2
        · exact ⟨φ₁ & φ₂, in_Δ, by simp [Formula.vocab, c1 ▸ n_in_φ]⟩
        · exact ⟨φ, c2.1, n_in_φ⟩
    case andᵣ Δ φ₁ φ₂ in_Δ =>
      have := @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) y_z
      simp_all only [List.mem_cons, List.not_mem_nil, or_false]
      rcases this with l | l <;>
        simp only [l, fₙ_alternate, Finset.mem_insert, Finset.mem_sdiff,
          Finset.mem_singleton, reduceCtorEq, false_or, not_false_eq_true,
          and_true] at φ_in_f
      all_goals
        exact ⟨φ, φ_in_f, n_in_φ⟩
    case orₗ Δ φ₁ φ₂ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
        and_true, fₙ_alternate, exists_eq_left', Finset.mem_insert, Sum.inl.injEq,
        Finset.mem_sdiff, Finset.mem_singleton, exists_eq_or_imp]
      subst y_z
      rcases φ_in_f with c1 | c2 | c3
      · exact ⟨φ₁ v φ₂, in_Δ, by simp [Formula.vocab, c1 ▸ n_in_φ]⟩
      · exact ⟨φ₁ v φ₂, in_Δ, by simp [Formula.vocab, c2 ▸ n_in_φ]⟩
      · exact ⟨φ, c3.1, n_in_φ⟩
    case orᵣ Δ φ₁ φ₂ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
        and_true, fₙ_alternate, exists_eq_left', Finset.mem_insert, reduceCtorEq,
        Finset.mem_sdiff, Finset.mem_singleton, not_false_eq_true, false_or]
    case boxₗ Δ φ₁ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
        and_true, SplitSequent.D, Bool.decide_eq_true, fₙ_alternate, exists_eq_left',
        Finset.mem_insert, Sum.inl.injEq, Finset.mem_union, Finset.mem_filter,
        Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_filterMap, Sum.exists,
        SplitSequent.opUnDi_eqₗₗ, exists_eq_right, reduceCtorEq, not_false_eq_true,
        SplitSequent.opUnDi_eqᵣₗ, and_false, exists_const, exists_eq_or_imp]
      subst y_z
      rcases φ_in_f with c1 | c2 | c3
      · exact ⟨□φ₁, in_Δ, by simp [Formula.vocab, c1 ▸ n_in_φ]⟩
      · exact ⟨φ, c2.1.1, n_in_φ⟩
      · exact ⟨◇φ, c3, by simp [Formula.vocab, n_in_φ]⟩
    case boxᵣ Δ φ₁ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
        and_true, SplitSequent.D, Bool.decide_eq_true, fₙ_alternate, exists_eq_left',
        Finset.mem_insert, reduceCtorEq, Finset.mem_union, Finset.mem_filter,
        Finset.mem_sdiff, Finset.mem_singleton, not_false_eq_true, Finset.mem_filterMap,
        Sum.exists, SplitSequent.opUnDi_eqₗₗ, exists_eq_right, Sum.inr.injEq,
        SplitSequent.opUnDi_eqᵣₗ, and_false, exists_const, false_or]
      rcases φ_in_f with c1 | c2
      · exact ⟨φ, c1.1, n_in_φ⟩
      · exact ⟨◇φ, c2, by simp [Formula.vocab, n_in_φ]⟩

/--
@isnad1 id=mem.2h4v.s5.88ed5141df83 from=translated src=- shape=4e7edf6f vocab=70baf7f7
-/
lemma in_vocab_of_path_right {𝕏 : Proof} {x y : 𝕏.X} (x_y : Relation.ReflTransGen (edge 𝕏.α) x y)
  {n} (n_in : n ∈ (SplitSequent.right (f (r 𝕏.α y))).vocab) :
    n ∈ (SplitSequent.right (f (r 𝕏.α x))).vocab := by
  induction x_y
  case refl => exact n_in
  case tail y z x_y y_z ih =>
    apply ih
    have Xh := 𝕏.step y
    simp only [Sequent.vocab, SplitSequent.right, Finset.mem_biUnion, Finset.mem_filterMap,
      Sum.getRight?_eq_some_iff, exists_eq_right] at n_in
    have ⟨φ, φ_in_f, n_in_φ⟩ := n_in
    cases r_def : r 𝕏.α y <;>
      simp_all only [edge, List.empty_eq, Finset.union_singleton, Finset.union_insert,
        List.map_eq_singleton_iff, List.not_mem_nil] <;>
      simp only [f, SplitSequent.right, Sequent.vocab, Finset.mem_biUnion,
        Finset.mem_filterMap, Sum.getRight?_eq_some_iff, exists_eq_right]
    case andᵣ Δ φ₁ φ₂ in_Δ =>
      have := @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) y_z
      simp_all only [List.mem_cons, List.not_mem_nil, or_false]
      rcases this with l | l <;>
        simp only [l, fₙ_alternate, Finset.mem_insert, Finset.mem_sdiff,
          Finset.mem_singleton, Sum.inr.injEq] at φ_in_f
      all_goals
      · rcases φ_in_f with c1 | c2
        · exact ⟨φ₁ & φ₂, in_Δ, by simp [Formula.vocab, c1 ▸ n_in_φ]⟩
        · exact ⟨φ, c2.1, n_in_φ⟩
    case andₗ Δ φ₁ φ₂ in_Δ =>
      have := @List.mem_map_of_mem _ _ _ _ (fun x ↦ f (r 𝕏.α x)) y_z
      simp_all only [List.mem_cons, List.not_mem_nil, or_false]
      rcases this with l | l <;>
        simp only [l, fₙ_alternate, Finset.mem_insert, Finset.mem_sdiff,
          Finset.mem_singleton, reduceCtorEq, false_or, not_false_eq_true,
          and_true] at φ_in_f
      all_goals
        exact ⟨φ, φ_in_f, n_in_φ⟩
    case orᵣ Δ φ₁ φ₂ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
        and_true, fₙ_alternate, exists_eq_left', Finset.mem_insert, Sum.inr.injEq,
        Finset.mem_sdiff, Finset.mem_singleton, exists_eq_or_imp]
      subst y_z
      rcases φ_in_f with c1 | c2 | c3
      · exact ⟨φ₁ v φ₂, in_Δ, by simp [Formula.vocab, c1 ▸ n_in_φ]⟩
      · exact ⟨φ₁ v φ₂, in_Δ, by simp [Formula.vocab, c2 ▸ n_in_φ]⟩
      · exact ⟨φ, c3.1, n_in_φ⟩
    case orₗ Δ φ₁ φ₂ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
        and_true, fₙ_alternate, exists_eq_left', Finset.mem_insert, reduceCtorEq,
        Finset.mem_sdiff, Finset.mem_singleton, not_false_eq_true, false_or]
    case boxᵣ Δ φ₁ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
        and_true, SplitSequent.D, Bool.decide_eq_true, fₙ_alternate, exists_eq_left',
        Finset.mem_insert, Sum.inr.injEq, Finset.mem_union, Finset.mem_filter,
        Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_filterMap, Sum.exists,
        reduceCtorEq, not_false_eq_true, SplitSequent.opUnDi_eqₗᵣ, and_false,
        exists_const, SplitSequent.opUnDi_eqᵣᵣ, exists_eq_right, false_or,
        exists_eq_or_imp]
      subst y_z
      rcases φ_in_f with c1 | c2 | c3
      · exact ⟨□φ₁, in_Δ, by simp [Formula.vocab, c1 ▸ n_in_φ]⟩
      · exact ⟨φ, c2.1.1, n_in_φ⟩
      · exact ⟨◇φ, c3, by simp [Formula.vocab, n_in_φ]⟩
    case boxₗ Δ φ₁ in_Δ =>
      have ⟨z, _, f_eq⟩ := Xh
      simp_all only [List.mem_cons, List.not_mem_nil, or_false, List.cons.injEq,
        and_true, SplitSequent.D, Bool.decide_eq_true, fₙ_alternate, exists_eq_left',
        Finset.mem_insert, reduceCtorEq, Finset.mem_union, Finset.mem_filter,
        Finset.mem_sdiff, Finset.mem_singleton, not_false_eq_true, Finset.mem_filterMap,
        Sum.exists, Sum.inl.injEq, SplitSequent.opUnDi_eqₗᵣ, and_false, exists_const,
        SplitSequent.opUnDi_eqᵣᵣ, exists_eq_right, false_or]
      rcases φ_in_f with c1 | c2
      · exact ⟨φ, c1.1, n_in_φ⟩
      · exact ⟨◇φ, c2, by simp [Formula.vocab, n_in_φ]⟩

end Split
end Lean4GlCoalgebras
-- Tengoku: 1 notation(s) of this module made scoped so they do not change other libraries (generated)
