/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Tengoku

/-! # Syntax (Section 2.1) -/

@[expose] public section

namespace PDL

mutual
  /-- PDL formulas, mutually defined with programs to support tests and boxes. -/
  inductive Formula : Type
    | bottom : Formula
    | atom_prop : Nat → Formula
    | neg : Formula → Formula
    | and : Formula → Formula → Formula
    | box : Program → Formula → Formula
  deriving Repr,DecidableEq
  /-- PDL programs with atomic actions, composition, choice, iteration, and tests. -/
  inductive Program : Type
    | atom_prog : Nat → Program
    | sequence : Program → Program → Program
    | union : Program → Program → Program
    | star : Program → Program
    | test : Formula → Program
  deriving Repr,DecidableEq
end

-- Reopen namespaces after mutual blocks to keep source-based declaration audits aligned.
end PDL

namespace PDL

/-! ## Abbreviations and Notation  -/

/-- Disjunction encoded using conjunction and negation. -/
@[simp]
def Formula.or : Formula → Formula → Formula
  | f, g => Formula.neg (Formula.and (Formula.neg f) (Formula.neg g))

/-- □(αs,φ) -/
def Formula.boxes : List Program → Formula → Formula
| δ, χ => List.foldr (fun β φ => Formula.box β φ) χ δ

/-- Sequential composition of a list of programs, with a true test as the empty sequence. -/
@[simp]
def Program.steps : List Program → Program
  | [] => Program.test (Formula.neg Formula.bottom)
  | (p :: ps) => Program.sequence p (Program.steps ps)

/-- An atomic proposition with the given natural-number index. -/
scoped prefix:70 "·" => Formula.atom_prop
/-- An atomic program with the given natural-number index. -/
scoped prefix:70 "·" => Program.atom_prog
/-- Formula negation. -/
scoped prefix:69 "~" => Formula.neg

@[simp]
instance Formula.instBot : Bot Formula := ⟨Formula.bottom⟩
@[simp]
instance Formula.insTop : Top Formula := ⟨Formula.neg Formula.bottom⟩

/-- Formula conjunction. -/
scoped infixr:66 " ⋀ " => Formula.and
/-- Formula disjunction. -/
scoped infixr:60 " ⋁ " => Formula.or
/-- Material implication between formulas. -/
scoped notation:55 φ:56 " ↣ " ψ:55 => ~ (φ ⋀ (~ψ))
/-- Material equivalence between formulas. -/
scoped notation:55 φ:56 " ⟷ " ψ:55 => (φ ↣ ψ) ⋀ (ψ ↣ φ)
/-- The box modality of a program. -/
scoped notation "⌈" α "⌉" P => Formula.box α P
/-- Iterated box modalities for a list of programs. -/
scoped notation "⌈⌈" as "⌉⌉" P => Formula.boxes as P

/-- Sequential composition of programs. -/
scoped infixl:33 ";'" => Program.sequence -- avoiding plain ";" which has a meaning in Lean 4
/-- Nondeterministic choice between programs. -/
scoped infixl:33 "⋓" => Program.union
/-- Kleene iteration of a program. -/
scoped prefix:33 "∗" => Program.star
/-- The test program associated with a formula. -/
scoped prefix:33 "?'" => Program.test -- avoiding plain "?" which has a meaning in Lean 4

/-- Union of a list of programs. The empty union is `?'⊥`, a program that cannot be
executed, so that `[(⋃ ∅)*]φ` is equivalent to `φ`. -/
def _root_.PDL.Program.unions : List Program → Program
  | [] => ?'⊥
  | [α] => α
  | α :: rest => α ⋓ Program.unions rest

/-- A basic formula is of the form `¬⊥`, `p`, `¬p`, `[a]_` or `¬[a]_`.
Note: in the article also `⊥` is basic, but not here because we want
to apply `OneSidedLocalRule.bot` to it. -/
@[simp]
def Formula.basic : Formula → Bool
  | ⊥ => False
  | ~⊥ => True
  | ·_ => True
  | ~·_ => True
  | ⌈·_⌉_ => True
  | ~⌈·_⌉_ => True
  | _ => False

/-- Whether a program is an atomic action. -/
def Program.isAtomic : Program → Prop
| ·_ => true
| _ => false

/--
@isnad1 id=ne.0h1v.s2.9908a28aa1f7 from=translated src=- shape=e63234f4 vocab=79d13f17
-/
lemma Formula.neq_neg_self (φ : Formula) : φ ≠ ~φ := by
  intro h
  cases φ <;> simp_all only [reduceCtorEq, neg.injEq]
  case neg φ => absurd h; exact Formula.neq_neg_self φ

-- Note: to make `decide` work we use `decidable_of_decidable_of_iff`.
instance : DecidablePred Program.isAtomic
| ·_ => decidable_of_decidable_of_iff (by simp [Program.isAtomic] : True ↔ _)
| _;' _ => decidable_of_decidable_of_iff (by simp [Program.isAtomic] : False ↔ _)
| a ⋓ _ => decidable_of_decidable_of_iff (by simp [Program.isAtomic] : False ↔ _)
| ∗_ => decidable_of_decidable_of_iff (by simp [Program.isAtomic] : False ↔ _)
| ?'_ => decidable_of_decidable_of_iff (by simp [Program.isAtomic] : False ↔ _)

/--
@isnad1 id=iff.0h1v.s3.8a2eb0937d8e from=translated src=- shape=ac6503a8 vocab=c15e9924
-/
theorem Program.isAtomic_iff {α : Program} : α.isAtomic ↔ ∃ a, α = (·a : Program) := by
  cases α <;> simp_all [isAtomic]

/-- Whether a program has an outer Kleene-star constructor. -/
def Program.isStar : Program → Prop
| ∗_ => true
| _ => false

instance : DecidablePred Program.isStar := by
  intro α
  cases α <;> simp only [Program.isStar, Bool.false_eq_true] <;>
  all_goals
    try exact instDecidableTrue
    try exact instDecidableFalse

/--
@isnad1 id=iff.0h1v.s3.bc3cf289c9e2 from=translated src=- shape=6952cb13 vocab=3bfa5205
-/
theorem Program.isStar_iff {α : Program} : α.isStar ↔ ∃ β, α = (∗β) := by
  cases α <;> simp_all [isStar]

/-! ## Tools for Box Formulas -/

/--
@isnad1 id=eq.0h1v.s3.9d4117029f0e from=translated src=- shape=f104d3d9 vocab=be0c34ca
-/
@[simp]
theorem Formula.boxes_nil {φ : Formula} : Formula.boxes [] φ = φ := by simp [Formula.boxes]

/--
@isnad1 id=eq.0h3v.s4.bf59e98dd911 from=translated src=- shape=8ce36672 vocab=0a68cc4f
-/
@[simp]
theorem Formula.boxes_cons {β δ φ} : Formula.boxes (β :: δ) φ = ⌈β⌉(Formula.boxes δ φ) := by
  simp [Formula.boxes]

/--
@isnad1 id=iff.0h3v.s4.1ebb05504e92 from=translated src=- shape=1705f1b1 vocab=c91cdb33
-/
@[simp]
lemma Formula.boxes_injective {αs φ ψ} : (⌈⌈αs⌉⌉φ) = (⌈⌈αs⌉⌉ψ) ↔ φ = ψ := by
  induction αs <;> simp_all

/--
@isnad1 id=eq.0h3v.s5.bd21e1c4e59d from=translated src=- shape=ec1e2949 vocab=57d2b6a5
-/
theorem boxes_last {δ α φ} : Formula.boxes (δ ++ [α]) φ = Formula.boxes δ (⌈α⌉φ) :=
  by
  induction δ <;> simp [Formula.boxes]

/--
@isnad1 id=eq.0h3v.s4.c661d7b4424d from=translated src=- shape=96a587c4 vocab=ef7412c5
-/
theorem boxes_append {as bs P} :
    Formula.boxes (as ++ bs) P = Formula.boxes as (Formula.boxes bs P) :=
  by
  induction as <;> simp [Formula.boxes]

/-- Separate a formula's leading boxes from its remaining formula. -/
def boxesOf : Formula → List Program × Formula
| (Formula.box prog nextf) => let (rest,endf) := boxesOf nextf; ⟨prog::rest, endf⟩
| f => ([], f)

/--
@isnad1 id=eq.1h3v.s4.6682c4de18f8 from=translated src=- shape=9ad42e55 vocab=4acffb3b
-/
lemma def_of_boxesOf_def {φ γ ψ} (h : boxesOf φ = (γ, ψ)) : φ = ⌈⌈γ⌉⌉ψ := by
  induction γ generalizing φ
  · unfold boxesOf at h
    cases φ <;> simp_all
  case cons α αs IH =>
    simp only [Formula.boxes_cons]
    cases φ <;> grind [boxesOf]

/-- Whether a formula has an outer box constructor. -/
def Formula.isBox : Formula → Prop
| (Formula.box _ _ ) => True
| _ => False

/--
@isnad1 id=not.0h1v.s3.03861dfce12d from=translated src=- shape=f5b67c07 vocab=10f47c1d
-/
@[simp]
lemma boxesOf_output_not_isBox {φ : Formula} : ¬ (boxesOf φ).2.isBox := by
  cases φ
  case box α φ =>
    have := @boxesOf_output_not_isBox φ
    simp_all [boxesOf, Formula.isBox]
  all_goals
    simp_all [boxesOf, Formula.isBox]

/--
@isnad1 id=not.1h3v.s4.822abb80bc55 from=translated src=- shape=e2c7fcb0 vocab=67f6b106
-/
lemma nonBox_of_boxesOf_def {φ L ψ} (bdef : boxesOf φ = (L, ψ)) : ¬ ψ.isBox := by
  have := @boxesOf_output_not_isBox φ; simp_all

/--
@isnad1 id=eq.1h1v.s4.e8ae4d55b940 from=translated src=- shape=4a510de6 vocab=12b17092
-/
lemma boxesOf_nonBox {φ} (notBox : ¬ φ.isBox) : boxesOf φ = ([], φ) := by
  cases φ <;> simp_all [Formula.isBox, boxesOf]

/-- If φ is not a box then we know the result of `boxesOf (⌈⌈δs⌉⌉⌈α⌉φ)`.
A more general version without α should also hold.
@isnad1 id=eq.1h3v.s5.3404ee63da51 from=translated src=- shape=4c17c6f6 vocab=42300514
-/
lemma defs_of_boxesOf_last_of_nonBox {φ}
    (notBox : ¬ φ.isBox) δs α : boxesOf (⌈⌈δs⌉⌉⌈α⌉φ) = (δs ++ [α], φ) := by
  cases δs
  case nil =>
    simp_all [boxesOf, boxesOf_nonBox notBox]
  case cons δ δs =>
    have IH := defs_of_boxesOf_last_of_nonBox notBox δs
    simp_all [boxesOf]

/--
@isnad1 id=ne.0h3v.s3.2cee566361a4 from=translated src=- shape=24bb6463 vocab=bfcbfe65
-/
lemma Formula.boxes_cons_neq_self φ β δ : (⌈β⌉⌈⌈δ⌉⌉φ) ≠ φ := by
  cases φ <;> try grind [Formula.boxes]
  case box α φ =>
    rw [← boxes_last]
    simp only [ne_eq, box.injEq, not_and]
    intro β_eq_α
    rw [boxes_last]
    cases δ
    · exact @Formula.boxes_cons_neq_self φ α []
    case cons γ δ =>
      simp only [boxes_cons]
      rw [← boxes_last]
      exact @Formula.boxes_cons_neq_self φ γ (δ ++ [α])

/-! ## Loaded Formulas

Loaded formulas consist of a non-empty sequence of loading boxes, and a normal formula.
For loading boxes we write `⌊α⌋` instead of `⌈α⌉`.
-/

mutual
/-- An ordinary formula or a formula with a distinguished loaded modal path. -/
inductive AnyFormula : Type
  | normal : Formula → AnyFormula -- φ
  | loaded : LoadFormula → AnyFormula -- χ
  deriving Repr, DecidableEq

/-- A box whose continuation may itself carry a loaded path. -/
inductive LoadFormula : Type
  | box : Program → AnyFormula → LoadFormula -- ⌊α⌋χ
  deriving Repr, DecidableEq
end

end PDL

namespace PDL

instance : Coe Formula AnyFormula := ⟨AnyFormula.normal⟩
instance : Coe LoadFormula AnyFormula := ⟨AnyFormula.loaded⟩

/-- Negation of an ordinary or loaded formula. -/
inductive AnyNegFormula
| neg : AnyFormula → AnyNegFormula

/-- Load a nonempty modal sequence given its prefix and final program. -/
def loadMulti : List Program → Program → Formula → LoadFormula
| bs, α, φ => List.foldr (fun β lf => LoadFormula.box β lf) (LoadFormula.box α φ) bs

/--
@isnad1 id=eq.0h2v.s3.e9f46f68d33c from=translated src=- shape=61d81d04 vocab=82a6ba2f
-/
@[simp]
theorem loadMulti_nil {α φ} : loadMulti [] α φ = LoadFormula.box α φ := by simp [loadMulti]

/--
@isnad1 id=eq.0h4v.s4.4efd9804be4b from=translated src=- shape=6c0a5256 vocab=bc2584dc
-/
@[simp]
theorem loadMulti_cons {β δ α φ} :
    loadMulti (β :: δ) α φ = LoadFormula.box β (loadMulti δ α φ) := by simp [loadMulti]

/-- Prepend a list of loaded boxes to a loaded continuation. -/
def LoadFormula.boxes : List Program → LoadFormula → LoadFormula
| δ, χ => List.foldr (fun β lf => LoadFormula.box β lf) χ δ

/--
@isnad1 id=eq.0h1v.s3.33e09d75b52f from=translated src=- shape=f104d3d9 vocab=dcff194e
-/
@[simp]
lemma LoadFormula.boxes_nil {χ} : LoadFormula.boxes [] χ = χ := by simp [LoadFormula.boxes]

/--
@isnad1 id=eq.0h3v.s4.acea2103b19d from=translated src=- shape=28a695b4 vocab=273a69cf
-/
lemma LoadFormula.boxes_cons {b bs φ} :
    LoadFormula.boxes (b :: bs) φ = LoadFormula.box b (LoadFormula.boxes bs φ) :=
  by
  induction bs <;> simp [LoadFormula.boxes]

/-- Erase loading annotations to obtain an ordinary formula. -/
@[simp]
def LoadFormula.unload : LoadFormula → Formula
| LoadFormula.box α (.normal φ) => ⌈α⌉φ
| LoadFormula.box α (.loaded χ) => ⌈α⌉(unload χ)

/--
@isnad1 id=eq.0h3v.s4.9953c384cbff from=translated src=- shape=3b76cb55 vocab=a1e329dd
-/
@[simp]
theorem unload_loadMulti : (loadMulti δ α φ).unload  = ⌈⌈δ⌉⌉⌈α⌉φ := by
  induction δ
  · simp [Formula.boxes, loadMulti]
  · simpa [Formula.boxes, LoadFormula.boxes, loadMulti]

/-- A negated loaded formula. -/
inductive NegLoadFormula : Type -- ¬χ
  | neg : LoadFormula → NegLoadFormula
  deriving Repr, DecidableEq

/-- A loaded box modality. -/
scoped notation "⌊" α "⌋" χ => LoadFormula.box α χ
/-- Iterated loaded boxes for a list of programs. -/
scoped notation "⌊⌊" αs "⌋⌋" χ => LoadFormula.boxes αs χ
/-- Negation of a loaded formula. -/
scoped notation "~'" χ => NegLoadFormula.neg χ
/-- Negation of an ordinary or loaded formula. -/
scoped notation "~''" φ:arg => AnyNegFormula.neg φ

/-- Erase loading annotations from a negated loaded formula. -/
@[simp]
def negUnload : NegLoadFormula → Formula
| NegLoadFormula.neg χ => ~ χ.unload

/--
@isnad1 id=eq.0h2v.s3.0f4ba8c693e0 from=translated src=- shape=c0f13c27 vocab=55e04403
-/
@[simp]
theorem unload_boxes {δ φ} : (⌊⌊δ⌋⌋φ).unload = ⌈⌈δ⌉⌉φ.unload := by
  induction δ
  · simp only [LoadFormula.boxes, List.foldr_nil, Formula.boxes]
  · simpa [Formula.boxes, LoadFormula.boxes]

/--
@isnad1 id=eq.0h2v.s4.23b91980e5a7 from=translated src=- shape=8a8d0995 vocab=d509275f
-/
@[simp]
theorem unload_neg_loaded {α χ} : (~'⌊α⌋(.loaded χ)).1.unload = ⌈α⌉(χ.unload) := by
  simp [LoadFormula.unload]

/--
@isnad1 id=eq.0h2v.s4.7b9184c0bb65 from=translated src=- shape=1fece3fb vocab=d3fdc25b
-/
@[simp]
theorem unload_neg_normal {α φ} : (~'⌊α⌋(.normal φ)).1.unload = ⌈α⌉φ := by
  simp [LoadFormula.unload]

/-- Load a possibly already loaded formula χ with a sequence δ of boxes.
The result is loaded iff δ≠[] or χ was loaded. -/
def AnyFormula.loadBoxes : List Program → AnyFormula → AnyFormula
| δ, χ => List.foldr (fun β lf => LoadFormula.box β lf) χ δ

/--
@isnad1 id=eq.0h1v.s3.6c88adb3f2ca from=translated src=- shape=f104d3d9 vocab=882f0fb8
-/
@[simp]
lemma AnyFormula.boxes_nil {ξ} : AnyFormula.loadBoxes [] ξ = ξ := by
  simp [AnyFormula.loadBoxes]

/--
@isnad1 id=eq.0h3v.s4.be9ffc3e6d72 from=translated src=- shape=2a728ef9 vocab=3d2ab112
-/
@[simp]
lemma AnyFormula.loadBoxes_cons {α γ ξ} :
    AnyFormula.loadBoxes (α :: γ) ξ = ⌊α⌋ (AnyFormula.loadBoxes γ ξ) := by
  simp [AnyFormula.loadBoxes]

/--
@isnad1 id=eq.0h3v.s4.8e9266000839 from=translated src=- shape=96a587c4 vocab=52b1fae0
-/
theorem AnyFormula.loadBoxes_append {as bs φ} :
    AnyFormula.loadBoxes (as ++ bs) φ = AnyFormula.loadBoxes as (AnyFormula.loadBoxes bs φ) :=
  by
  induction as <;> simp [AnyFormula.loadBoxes]

/--
@isnad1 id=eq.0h2v.s3.4392d7508507 from=translated src=- shape=816001f3 vocab=5590429c
-/
lemma AnyFormula.loadBoxes_loaded_eq_loaded_boxes {δ χ} :
    AnyFormula.loadBoxes δ (AnyFormula.loaded χ) = AnyFormula.loaded (⌊⌊δ⌋⌋χ) := by
  induction δ
  · simp
  case cons IH =>
    simp only [loadBoxes_cons, loaded.injEq]
    rw [IH]
    rfl

/-- Erase loading annotations, leaving ordinary formulas unchanged. -/
def AnyFormula.unload : AnyFormula → Formula
  | .normal φ => φ
  | .loaded χ => χ.unload

/--
@isnad1 id=eq.1h5v.s5.0eb613a49dae from=translated src=- shape=266f2975 vocab=9c49fa7b
-/
lemma box_loadBoxes_append_eq_of_loaded_eq_loadBoxes {αs}
    (h : AnyFormula.loaded χ' = AnyFormula.loadBoxes αs (AnyFormula.normal φ))
    : (⌊d⌋AnyFormula.loadBoxes (δ ++ αs) (AnyFormula.normal φ)) = ⌊⌊d :: δ⌋⌋χ' := by
  cases αs
  · exfalso
    simp_all
  case cons α αs =>
    simp only [AnyFormula.loadBoxes_cons, AnyFormula.loaded.injEq] at h
    subst h
    rw [LoadFormula.boxes_cons,AnyFormula.loadBoxes_append,AnyFormula.loadBoxes_cons]
    simp only [LoadFormula.box.injEq, true_and] -- d gone
    apply AnyFormula.loadBoxes_loaded_eq_loaded_boxes

/--
@isnad1 id=eq.0h3v.s4.e220cbbb4974 from=translated src=- shape=2cae0a41 vocab=110572d7
-/
@[simp]
lemma AnyFormulaBoxBoxes_eq_FormulaBoxLoadBoxes_inside_unload {αs} :
      ((⌊α⌋  AnyFormula.loadBoxes αs (AnyFormula.normal φ)).unload)
    = ( ⌈α⌉((AnyFormula.loadBoxes αs (AnyFormula.normal φ)).unload)) := by
  cases αs <;> simp_all [AnyFormula.loadBoxes, AnyFormula.unload]

/--
@isnad1 id=eq.0h2v.s3.98c856aa681c from=translated src=- shape=ec0760d8 vocab=38141be5
-/
lemma AnyFormula.loadBoxes_unload_eq_boxes {βs φ} :
    (AnyFormula.loadBoxes βs (AnyFormula.normal φ)).unload = ⌈⌈βs⌉⌉φ := by
  induction βs
  · simp [unload]
  case cons ih =>
    simp only [unload, loadBoxes_cons, AnyFormulaBoxBoxes_eq_FormulaBoxLoadBoxes_inside_unload,
      Formula.boxes_cons, Formula.box.injEq, true_and];
    exact ih

/--
@isnad1 id=eq.1h3v.s4.51b3779ff4ba from=translated src=- shape=53e836e6 vocab=44836435
-/
lemma loaded_eq_to_unload_eq χ αs φ
    (h : AnyFormula.loaded χ = AnyFormula.loadBoxes αs (AnyFormula.normal φ))
    : χ.unload = ⌈⌈αs⌉⌉φ
    := by
  cases αs
  · simp_all
  case cons α1 αs =>
    cases αs
    · simp_all
    case cons α2 αs =>
      simp only [Formula.boxes_cons]
      rcases χ with  ⟨β, af⟩
      simp only [AnyFormula.loadBoxes_cons, AnyFormula.loaded.injEq, LoadFormula.box.injEq] at h
      rcases h with ⟨β_eq_α1, af_def⟩
      have := loaded_eq_to_unload_eq ((⌊α2⌋AnyFormula.loadBoxes αs (.normal φ))) (α2 :: αs) _ rfl
      subst_eqs
      simp_all

/-! ## Spliting of loaded formulas -/

mutual
/-- Split any formula into the list of loaded boxes and the free formula. -/
@[simp]
def AnyFormula.split : (af : AnyFormula) → List Program × Formula
| .loaded lf => lf.split
| .normal f => ([], f)

/-- Split a loaded formula into the list of loaded boxes and the free formula. -/
@[simp]
def LoadFormula.split : (lf : LoadFormula) → List Program × Formula
| .box α af => (fun (δ,f) => (α :: δ, f)) af.split
end

end PDL

namespace PDL

/--
@isnad1 id=eq.0h3v.s5.3a9ba090603e from=translated src=- shape=e0cd2ab5 vocab=5ef5b9a8
-/
lemma LoadFormula.split_boxes_cons {βs α φ} :
    (⌊⌊βs⌋⌋⌊α⌋AnyFormula.normal φ).split = (βs ++ [α], φ) := by
  induction βs
  · simp_all
  · rw [List.cons_append]
    rw [LoadFormula.boxes_cons]
    simp only [split, AnyFormula.split, Prod.mk.injEq, List.cons.injEq, true_and]
    grind

/--
@isnad1 id=eq.0h1v.s4.5eaff1848053 from=translated src=- shape=03a56f7e vocab=8085454f
-/
@[simp]
theorem AnyFormula.split_normal (φ : Formula) : (AnyFormula.normal φ).split = ([],φ) := by
  simp [AnyFormula.split]

/--
@isnad1 id=eq.1h2v.s4.d7f3ab4720eb from=translated src=- shape=625bc216 vocab=179ad48d
-/
theorem AnyFormula.split_eq_nil_is_normal (ξ φ) : ξ.split = ([],φ) → ξ = AnyFormula.normal φ := by
  rcases ξ with _|⟨_,_⟩ <;> simp [AnyFormula.split]

mutual
/--
@isnad1 id=eq.1h2v.s4.e630ad29c30e from=translated src=- shape=e4ac657a vocab=700b7a98
-/
lemma LoadFormula.split_inj {ξ ξ' : LoadFormula} (h : ξ.split = ξ'.split) : ξ = ξ' := by
  rcases ξ with ⟨α, ξ⟩
  rcases ξ' with ⟨α', ξ'⟩
  simp only [LoadFormula.split, Prod.mk.injEq, List.cons.injEq, LoadFormula.box.injEq] at *
  constructor
  · tauto
  case right =>
    apply AnyFormula.split_inj
    aesop

/--
@isnad1 id=eq.1h2v.s4.90c944a7dc8e from=translated src=- shape=e4ac657a vocab=28d5578a
-/
lemma AnyFormula.split_inj {ξ ξ' : AnyFormula} (h : ξ.split = ξ'.split) : ξ = ξ' := by
  rcases ξ with φ|ξ <;> rcases ξ' with φ'|ξ'
  case normal.normal =>
    simp_all
  case normal.loaded =>
    simp_all only [AnyFormula.split, reduceCtorEq]
    cases ξ'; simp_all
  case loaded.normal =>
    cases ξ; simp_all
  case loaded.loaded =>
    simp_all only [AnyFormula.split, AnyFormula.loaded.injEq]
    exact LoadFormula.split_inj h
end

end PDL

namespace PDL

/--
@isnad1 id=eq.0h2v.s5.b5c8b5706ecf from=translated src=- shape=7c0344b7 vocab=7984a073
-/
theorem AnyFormula.box_split (af : AnyFormula) :
  (⌊α⌋af).split = (α :: af.split.1, af.split.2) := by
  cases af <;> simp

/--
@isnad1 id=ne.0h1v.s3.7e07058871f3 from=translated src=- shape=51f419af vocab=8fc35755
-/
@[simp]
theorem LoadFormula.split_list_not_empty (lf : LoadFormula) : lf.split.1 ≠ [] := by
  cases lf
  simp [LoadFormula.split]

/-- Construct a loaded modal sequence from a list known to be nonempty. -/
@[simp]
def loadMultiNonEmpty : (δ : List Program) → (h : δ ≠ []) → Formula → LoadFormula
| [ ],           h, _ => by exfalso; simp at *
| (α :: []),     _, φ => LoadFormula.box α φ
| (α :: d :: δ), _, φ => LoadFormula.box α (loadMultiNonEmpty (d :: δ) (by simp) φ)

/--
@isnad1 id=eq.2h3v.s5.e47ddf6a871c from=translated src=- shape=2d9d3b96 vocab=2c91474c
-/
@[simp]
theorem loadMulti_nonEmpty_box (h : δ ≠ []) :
    loadMultiNonEmpty (α :: δ) h' φ = ⌊α⌋(loadMultiNonEmpty δ h φ) := by
  cases δ
  · absurd h; rfl
  · simp at *

/--
@isnad1 id=eq.0h3v.s5.b30df9f464d6 from=translated src=- shape=75f7cc70 vocab=ab6a466f
-/
@[simp]
lemma loadMulti_split {αs} : (loadMulti αs α φ).split = (αs ++ [α], φ) := by
  induction αs <;> simp_all

/--
@isnad1 id=eq.1h2v.s4.057ffe8c7cbd from=translated src=- shape=7e311db8 vocab=96137fff
-/
@[simp]
lemma loadMulti_nonEmpty_unload {δ h φ} : (loadMultiNonEmpty δ h φ).unload  = ⌈⌈δ⌉⌉φ := by
  induction δ
  · exfalso; absurd h; rfl
  case cons α αs IH =>
    unfold loadMultiNonEmpty
    cases αs <;> simp_all

/--
@isnad1 id=eq.1h3v.s4.72d24cb5f8b4 from=translated src=- shape=d7246b74 vocab=2b8e99f8
-/
theorem LoadFormula.split_eq_loadMulti_nonEmpty {δ φ} (lf : LoadFormula) : (h : lf.split = (δ,φ)) →
    lf = loadMultiNonEmpty δ (by have := split_list_not_empty lf; simp_all) φ := by
  induction δ generalizing φ lf
  all_goals
    rcases lf_def : lf with ⟨α,af⟩
    intro h
  · simp [LoadFormula.split] at h
  case cons β δ IH =>
    cases af
    · unfold LoadFormula.split at h
      simp only [AnyFormula.split, Prod.mk.injEq, List.cons.injEq, List.nil_eq] at h
      rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
      subst_eqs
      simp_all
    case loaded lf2 =>
      specialize @IH φ lf2 ?_
      · rw [AnyFormula.box_split] at h
        simp only [AnyFormula.split, Prod.mk.injEq, List.cons.injEq] at *
        rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
        subst_eqs
        simp
      · rw [loadMulti_nonEmpty_box ?_]
        · simp only [box.injEq, AnyFormula.loaded.injEq]
          rw [AnyFormula.box_split] at h
          simp only [AnyFormula.split, Prod.mk.injEq, List.cons.injEq] at *
          rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
          subst_eqs
          simp only [true_and]
          convert IH
        · simp only [ne_eq]
          rw [AnyFormula.box_split] at h
          simp only [AnyFormula.split, Prod.mk.injEq, List.cons.injEq] at *
          rcases h with ⟨⟨α_eq_β, def_δ⟩, def_φ⟩
          subst_eqs
          simp

/--
@isnad1 id=eq.2h3v.s5.a9f902de4415 from=translated src=- shape=14b4bf3f vocab=e55527f6
-/
theorem LoadFormula.split_eq_loadMulti_nonEmpty' {δ φ} (lf : LoadFormula) (h : δ ≠ [])
    (h2 : lf.split = (δ, φ)) : lf = loadMultiNonEmpty δ h φ := by
  have := LoadFormula.split_eq_loadMulti_nonEmpty lf h2
  rw [this]

/--
@isnad1 id=eq.1h3v.s5.9aa64e69b7fe from=translated src=- shape=280971e0 vocab=0479c227
-/
theorem loadMulti_nonEmpty_eq_loadMulti {δ α h φ} :
    loadMultiNonEmpty (δ ++ [α]) h φ = loadMulti δ α φ := by
  induction δ <;> simp_all

/--
@isnad1 id=eq.1h4v.s5.d88f2f3386db from=translated src=- shape=0e093349 vocab=84fd2d3a
-/
theorem LoadFormula.split_eq_loadMulti (lf : LoadFormula) {δ α φ}
    (h : lf.split = (δ ++ [α], φ)) : lf = loadMulti δ α φ := by
  rw [LoadFormula.split_eq_loadMulti_nonEmpty' lf (by simp) h]
  apply loadMulti_nonEmpty_eq_loadMulti

/--
@isnad1 id=ex.0h1v.s5.f62d795e7f2a from=translated src=- shape=01880520 vocab=8d93076e
-/
theorem LoadFormula.exists_splitLast (lf : LoadFormula) :
    ∃ δ α, lf.split.1 = δ ++ [α] := by
  rcases lf with ⟨α, af⟩
  cases af
  case normal =>
    use [], α
    simp
  case loaded lf =>
    rcases LoadFormula.exists_splitLast lf with ⟨δ', α', IH⟩
    simp only [split, AnyFormula.split]
    rw [IH]
    use α :: δ', α'
    simp

/--
@isnad1 id=ex.0h1v.s4.652a91deb690 from=translated src=- shape=f172947d vocab=129de23d
-/
theorem LoadFormula.exists_loadMulti (lf : LoadFormula) :
    ∃ δ α φ, lf = loadMulti δ α φ := by
  rcases LoadFormula.exists_splitLast lf with ⟨δ, α, split1_def⟩
  use δ, α
  use lf.split.2
  apply LoadFormula.split_eq_loadMulti lf
  cases lfs_def : lf.split
  rw [lfs_def] at split1_def
  simp_all

/--
@isnad1 id=eq.0h3v.s5.04276447f776 from=translated src=- shape=34ec67a4 vocab=f959414d
-/
lemma loadMulti_eq_loadBoxes :
    AnyFormula.loaded (loadMulti δ α φ) = AnyFormula.loadBoxes (δ ++ [α]) φ := by
  induction δ <;> aesop

/-! ## splitLast -/

/-- Helper function for `YsetLoad'` to get last list element. -/
def splitLast : List α → Option (List α × α)
| [] => none
| (x :: xs) => some <| match splitLast xs with
  | none => ([], x)
  | some (ys, y) => (x::ys, y)

/--
@isnad1 id=eq.0h1v.s4.49035b4e90f7 from=translated src=- shape=aed3599f vocab=39efc26f
-/
@[simp]
theorem splitLast_nil : splitLast [] = (none : Option (List α × α)) := by simp [splitLast]

/--
@isnad1 id=eq.1h2v.s4.d20f4ebe1a29 from=translated src=- shape=4665a9b7 vocab=39efc26f
-/
theorem nil_of_splitLast_none {δs : List α} : splitLast δs = none → δs = [] := by
  cases δs <;> simp [splitLast]

/--
@isnad1 id=eq.0h3v.s5.d3339b46ef14 from=translated src=- shape=cfb5dde6 vocab=ceef44cc
-/
theorem splitLast_cons_eq_some (x : α) (xs : List α) :
    splitLast (x :: xs) = some ((x :: xs).dropLast, (x :: xs).getLast (List.cons_ne_nil x xs)) := by
  cases xs
  · simp [splitLast]
  case cons y ys =>
    have := splitLast_cons_eq_some y ys -- recursion!
    unfold splitLast
    rw [this]
    simp

/--
@isnad1 id=eq.0h3v.s5.03e249e00e8e from=translated src=- shape=77327f87 vocab=e3ae8069
-/
@[simp]
theorem splitLast_append_singleton {α} {xs : List α} {x : α} :
    splitLast (xs ++ [x]) = some (xs, x) := by
  induction xs <;> simp_all [splitLast]

/--
@isnad1 id=eq.1h3v.s4.daa7e5e721f2 from=translated src=- shape=a4513e5c vocab=dfa41828
-/
lemma splitLast_inj {α} {xs ys : List α} (h : splitLast xs = splitLast ys) :
    xs = ys := by
  induction xs using List.reverseRecOn <;> induction ys using List.reverseRecOn
  · rfl
  · exfalso
    simp_all
  · exfalso
    simp_all
  aesop

/--
@isnad1 id=eq.2h5v.s6.5517718aa761 from=translated src=- shape=aa51e320 vocab=137aa159
-/
lemma LoadFormula.split_splitLast_to_loadBoxes {δs φ δs_ δ ξ}
    (ξsp_def : ξ.split = (δs, φ))
    (sp_def : splitLast δs = some (δs_, δ))
    : ξ = AnyFormula.loadBoxes (δs_ ++ [δ]) (AnyFormula.normal φ) := by
  rw [← splitLast_append_singleton] at sp_def
  rw [splitLast_inj sp_def, ← loadMulti_split] at ξsp_def
  have : (loadMulti δs_ δ φ).split = AnyFormula.split (loadMulti δs_ δ φ) := rfl
  have := AnyFormula.split_inj (this ▸ ξsp_def)
  exact this ▸ loadMulti_eq_loadBoxes

/--
@isnad1 id=eq.1h3v.s5.ab0e94238714 from=translated src=- shape=e9fda79c vocab=c2e9d2b4
-/
lemma splitLast_undo_of_some {αs : List α} {βs_b : List α × α} (h : splitLast αs = some βs_b) :
    βs_b.1 ++ [βs_b.2] = αs := by
  rcases αs with _ |⟨α,αs⟩
  · exfalso
    simp_all
  have := @splitLast_cons_eq_some _ α αs
  rw [h] at this
  simp only [Option.some.injEq] at this
  subst this
  simp only
  apply List.dropLast_append_getLast

/--
@isnad1 id=eq.1h5v.s5.874169b263c4 from=translated src=- shape=7f73c20c vocab=b60a6fa8
-/
lemma loadMulti_of_splitLast_cons {α αs βs β φ} (h : splitLast (α :: αs) = some ⟨βs, β⟩) :
    loadMulti βs β φ = ⌊α⌋AnyFormula.loadBoxes αs (AnyFormula.normal φ) := by
  have : (α :: αs) = βs ++ [β] := by
    rw [← @splitLast_append_singleton] at h
    exact splitLast_inj h
  cases αs
  · unfold splitLast at h
    simp only [splitLast_nil, Option.some.injEq, Prod.mk.injEq, List.nil_eq] at h
    cases h
    subst_eqs
    simp at *
  case cons α2 αs =>
    have ⟨δβ2, new_h⟩ : ∃ δ2_β2, splitLast (α2 :: αs) = some δ2_β2 := by simp [splitLast]
    rw [AnyFormula.loadBoxes_cons]
    have IH := @loadMulti_of_splitLast_cons α2 αs _ _ φ new_h
    rw [← IH]; clear IH
    cases βs
    · exfalso
      unfold splitLast at h
      simp only [Option.some.injEq] at h
      cases h
    case cons β2 βs =>
      simp_all
      subst new_h
      simp_all

/-! ## Measures -/

mutual
  /-- The syntactic length of a program, mutually defined with formula length. -/
  @[simp, implicit_reducible]
  def lengthOfProgram : Program → Nat
    | ·_ => 1
    | α;'β => 1 + lengthOfProgram α + lengthOfProgram β
    | α⋓β => 1 + lengthOfProgram α + lengthOfProgram β
    | ∗α => 1 + lengthOfProgram α
    | ?'φ => 2 + lengthOfFormula φ -- 2 not 1, to make F^ℓ go down;-)
  /-- The syntactic length of a formula, mutually defined with program length. -/
  @[simp, implicit_reducible]
  def lengthOfFormula : Formula → Nat
    | Formula.bottom => 1
    | ·_ => 1
    | ~φ => 1 + lengthOfFormula φ
    | φ⋀ψ => 1 + lengthOfFormula φ + lengthOfFormula ψ
    | ⌈α⌉φ => 1 + lengthOfProgram α + lengthOfFormula φ
end

end PDL

namespace PDL

/-- Types equipped with a natural-valued syntactic length. -/
class HasLength (α : Type) where
  /-- The syntactic length of an object. -/
  lengthOf : α → ℕ

open HasLength
@[simp]
instance formulaHasLength : HasLength Formula := ⟨lengthOfFormula⟩
@[simp]
instance setFormulaHasLength : HasLength (Finset Formula) := ⟨fun X => X.sum lengthOfFormula⟩
@[simp]
instance listFormulaHasLength : HasLength (List Formula) := ⟨fun X => (X.map lengthOfFormula).sum⟩
@[simp]
instance programHasLength : HasLength Program := ⟨lengthOfProgram⟩
@[simp]
instance setProgramHasLength : HasLength (Finset Program) := ⟨fun X => X.sum lengthOfProgram⟩

/-- No formula is its own double negation.
@isnad1 id=ne.0h1v.s3.4c2517629c52 from=translated src=- shape=e89738c0 vocab=79d13f17
-/
lemma Formula.ne_neg_neg_self (φ : Formula) : φ ≠ ~~φ := by
  intro h; have := congrArg lengthOfFormula h; simp at this; omega

/-- A pair `{φ, ~φ}` is never a singleton.
@isnad1 id=ne.0h2v.s4.32f2aaf8e0b9 from=translated src=- shape=f59ecd97 vocab=e3c27e25
-/
lemma pair_neg_ne_singleton (φ ψ : Formula) : ({φ, ~φ} : Finset Formula) ≠ {ψ} := by
  intro h
  have h1 : φ ∈ ({ψ} : Finset Formula) := h ▸ (by simp)
  have h2 : (~φ) ∈ ({ψ} : Finset Formula) := h ▸ (by simp)
  simp only [Finset.mem_singleton] at h1 h2
  exact Formula.neq_neg_self φ (h1.trans h2.symm)

/-- The pairs `{φ, ~φ}` determine `φ`.
@isnad1 id=eq.1h2v.s5.2bbe7024c565 from=translated src=- shape=81b85f1a vocab=e3c27e25
-/
lemma pair_neg_inj {φ ψ : Formula} (h : ({φ, ~φ} : Finset Formula) = {ψ, ~ψ}) : φ = ψ := by
  have h1 : φ ∈ ({ψ, ~ψ} : Finset Formula) := h ▸ (by simp)
  have h2 : (~φ) ∈ ({ψ, ~ψ} : Finset Formula) := h ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact absurd (h2.symm.trans (congrArg Formula.neg h1)) (Formula.ne_neg_neg_self ψ)
    · exact Formula.neg.inj h2

/-! ## Sorting formulas

Needed to convert a `Finset Formula` to `List Formula`.

TODO: make this a separate file
-/

mutual

/-- Order: ⊥ < p < ¬φ < φ1∧φ2 < [α]φ

Note that we want this to be antisymmetric later, so we cannot just use < on some measure.
An alternative approach here would be to even go for `Denumerable`.
-/
def Formula.le : Formula → Formula → Prop
  | .bottom, .bottom => True
  | .bottom, _ => True
  | .atom_prop _, .bottom => False
  | .atom_prop p, .atom_prop p' => p ≤ p'
  | .atom_prop _, _ => True
  | .neg _, .bottom => False
  | .neg _, .atom_prop _ => False
  | .neg φ, .neg φ' => φ.le φ'
  | .neg _, _ => True
  | .and _ _, .bottom => False
  | .and _ _, .atom_prop _ => False
  | .and _ _, .neg _ => False
  | .and φ1 φ2, .and φ1' φ2' => φ1.le φ1' ∧ ((φ1 = φ1') → φ2.le φ2')
  | .and _ _, .box _ _ => True
  | .box _ _, .bottom => False
  | .box _ _, .atom_prop _ => False
  | .box _ _, .neg _ => False
  | .box _ _, .and _ _  => False
  | .box α φ, .box α' φ' => α.le α' ∧ ((α = α') → φ.le φ')

/-- The recursive ordering of program syntax used for finite enumerations. -/
def Program.le : Program → Program → Prop
  | .atom_prog a, .atom_prog a' => a ≤ a'
  | .atom_prog _, _ => True
  | .sequence _ _, .atom_prog _ => False
  | .sequence α β, .sequence α' β' => α.le α' ∧ ((α = α') → β.le β')
  | .sequence _ _, _ => True
  | .union _ _ , .atom_prog _ => False
  | .union _ _, .sequence _ _ => False
  | .union α β, .union α' β' => α.le α' ∧ ((α = α') → β.le β')
  | .union _ _, .star _ => True
  | .union _ _, .test _ => True
  | .star _, .atom_prog _ => False
  | .star _, .sequence _ _ => False
  | .star _, .union _ _ => False
  | .star α, .star α' => α.le α'
  | .star _, .test _ => True
  | .test _, .atom_prog _ => False
  | .test _, .sequence _ _ => False
  | .test _, .union _ _ => False
  | .test _, .star _ => False
  | .test τ, .test τ' => τ.le τ'
end

end PDL

namespace PDL

open HasLength

instance instLEFormula : LE Formula := ⟨Formula.le⟩
instance instLTFormula : LT Formula := ⟨fun φ1 φ2 ↦ φ1 ≠ φ2 ∧ φ1.le φ2⟩

instance instLEProgram : LE Program := ⟨Program.le⟩
instance instLTProgram : LT Program := ⟨fun α α' ↦ α ≠ α' ∧ α.le α'⟩

/-! ### Deciding the order -/

mutual

/-- The order on formulas is decidable. -/
def Formula.decLe : (f g : Formula) → Decidable (Formula.le f g)
  | .bottom, .bottom => isTrue trivial
  | .bottom, .atom_prop _ => isTrue trivial
  | .bottom, .neg _ => isTrue trivial
  | .bottom, .and _ _ => isTrue trivial
  | .bottom, .box _ _ => isTrue trivial
  | .atom_prop _, .bottom => isFalse not_false
  | .atom_prop p, .atom_prop p' => Nat.decLe p p'
  | .atom_prop _, .neg _ => isTrue trivial
  | .atom_prop _, .and _ _ => isTrue trivial
  | .atom_prop _, .box _ _ => isTrue trivial
  | .neg _, .bottom => isFalse not_false
  | .neg _, .atom_prop _ => isFalse not_false
  | .neg φ, .neg φ' => Formula.decLe φ φ'
  | .neg _, .and _ _ => isTrue trivial
  | .neg _, .box _ _ => isTrue trivial
  | .and _ _, .bottom => isFalse not_false
  | .and _ _, .atom_prop _ => isFalse not_false
  | .and _ _, .neg _ => isFalse not_false
  | .and φ1 φ2, .and φ1' φ2' =>
      @instDecidableAnd _ _ (Formula.decLe φ1 φ1')
        (@instDecidableForall _ _ inferInstance (Formula.decLe φ2 φ2'))
  | .and _ _, .box _ _ => isTrue trivial
  | .box _ _, .bottom => isFalse not_false
  | .box _ _, .atom_prop _ => isFalse not_false
  | .box _ _, .neg _ => isFalse not_false
  | .box _ _, .and _ _ => isFalse not_false
  | .box α φ, .box α' φ' =>
      @instDecidableAnd _ _ (Program.decLe α α')
        (@instDecidableForall _ _ inferInstance (Formula.decLe φ φ'))

/-- The order on programs is decidable. -/
def Program.decLe : (α β : Program) → Decidable (Program.le α β)
  | .atom_prog a, .atom_prog a' => Nat.decLe a a'
  | .atom_prog _, .sequence _ _ => isTrue trivial
  | .atom_prog _, .union _ _ => isTrue trivial
  | .atom_prog _, .star _ => isTrue trivial
  | .atom_prog _, .test _ => isTrue trivial
  | .sequence _ _, .atom_prog _ => isFalse not_false
  | .sequence α β, .sequence α' β' =>
      @instDecidableAnd _ _ (Program.decLe α α')
        (@instDecidableForall _ _ inferInstance (Program.decLe β β'))
  | .sequence _ _, .union _ _ => isTrue trivial
  | .sequence _ _, .star _ => isTrue trivial
  | .sequence _ _, .test _ => isTrue trivial
  | .union _ _, .atom_prog _ => isFalse not_false
  | .union _ _, .sequence _ _ => isFalse not_false
  | .union α β, .union α' β' =>
      @instDecidableAnd _ _ (Program.decLe α α')
        (@instDecidableForall _ _ inferInstance (Program.decLe β β'))
  | .union _ _, .star _ => isTrue trivial
  | .union _ _, .test _ => isTrue trivial
  | .star _, .atom_prog _ => isFalse not_false
  | .star _, .sequence _ _ => isFalse not_false
  | .star _, .union _ _ => isFalse not_false
  | .star α, .star α' => Program.decLe α α'
  | .star _, .test _ => isTrue trivial
  | .test _, .atom_prog _ => isFalse not_false
  | .test _, .sequence _ _ => isFalse not_false
  | .test _, .union _ _ => isFalse not_false
  | .test _, .star _ => isFalse not_false
  | .test τ, .test τ' => Formula.decLe τ τ'
end

end PDL

namespace PDL

open HasLength

instance : DecidableRel Formula.le := Formula.decLe
instance : DecidableRel Program.le := Program.decLe

instance : DecidableRel (fun (a b : Formula) ↦ a ≤ b) := Formula.decLe
instance : DecidableRel (fun (a b : Program) ↦ a ≤ b) := Program.decLe

/-! ### The order is a linear order -/

/-- Helper for the lexicographic clauses: reflexivity. -/
private theorem lex_rfl {A B : Type} {leA : A → A → Prop} {leB : B → B → Prop}
    {a : A} {b : B} (ha : leA a a) (hb : leB b b) :
    leA a a ∧ ((a = a) → leB b b) := ⟨ha, fun _ => hb⟩

/-- Helper for the lexicographic clauses: totality. -/
private theorem lex_total {A B : Type} {leA : A → A → Prop} {leB : B → B → Prop}
    {a a' : A} {b b' : B} (hrefl : leA a a)
    (hA : leA a a' ∨ leA a' a) (hB : leB b b' ∨ leB b' b) :
    (leA a a' ∧ ((a = a') → leB b b')) ∨ (leA a' a ∧ ((a' = a) → leB b' b)) := by
  by_cases he : a = a'
  · subst he
    rcases hB with h | h
    · exact Or.inl ⟨hrefl, fun _ => h⟩
    · exact Or.inr ⟨hrefl, fun _ => h⟩
  · rcases hA with h | h
    · exact Or.inl ⟨h, fun hc => absurd hc he⟩
    · exact Or.inr ⟨h, fun hc => absurd hc.symm he⟩

mutual

/-- The order on formulas is reflexive.
@isnad1 id=le.0h1v.s2.51cf8819547c from=translated src=- shape=b3bac8d8 vocab=f4a272b8
-/
theorem Formula.le_rfl : ∀ (φ : Formula), φ.le φ
  | .bottom => trivial
  | .atom_prop p => Nat.le_refl p
  | .neg φ => Formula.le_rfl φ
  | .and φ1 φ2 => lex_rfl (Formula.le_rfl φ1) (Formula.le_rfl φ2)
  | .box α φ => lex_rfl (Program.le_rfl α) (Formula.le_rfl φ)

/-- The order on programs is reflexive.
@isnad1 id=le.0h1v.s2.bbd03ea9fc7a from=translated src=- shape=b3bac8d8 vocab=8f743887
-/
theorem Program.le_rfl : ∀ (α : Program), α.le α
  | .atom_prog a => Nat.le_refl a
  | .sequence α β => lex_rfl (Program.le_rfl α) (Program.le_rfl β)
  | .union α β => lex_rfl (Program.le_rfl α) (Program.le_rfl β)
  | .star α => Program.le_rfl α
  | .test τ => Formula.le_rfl τ
end

end PDL

namespace PDL

open HasLength

mutual

/-- The order on formulas is antisymmetric.
@isnad1 id=eq.2h2v.s4.d65e04464ad0 from=translated src=- shape=5f71b5ec vocab=f4a272b8
-/
theorem Formula.le_antisymm : ∀ (φ ψ : Formula), φ.le ψ → ψ.le φ → φ = ψ
  | .bottom, .bottom, _, _ => rfl
  | .bottom, .atom_prop _, _, h2 => (h2 : False).elim
  | .bottom, .neg _, _, h2 => (h2 : False).elim
  | .bottom, .and _ _, _, h2 => (h2 : False).elim
  | .bottom, .box _ _, _, h2 => (h2 : False).elim
  | .atom_prop _, .bottom, h1, _ => (h1 : False).elim
  | .atom_prop _, .atom_prop _, h1, h2 => by
      simp only [Formula.atom_prop.injEq]
      exact Nat.le_antisymm h1 h2
  | .atom_prop _, .neg _, _, h2 => (h2 : False).elim
  | .atom_prop _, .and _ _, _, h2 => (h2 : False).elim
  | .atom_prop _, .box _ _, _, h2 => (h2 : False).elim
  | .neg _, .bottom, h1, _ => (h1 : False).elim
  | .neg _, .atom_prop _, h1, _ => (h1 : False).elim
  | .neg φ, .neg ψ, h1, h2 => by rw [Formula.le_antisymm φ ψ h1 h2]
  | .neg _, .and _ _, _, h2 => (h2 : False).elim
  | .neg _, .box _ _, _, h2 => (h2 : False).elim
  | .and _ _, .bottom, h1, _ => (h1 : False).elim
  | .and _ _, .atom_prop _, h1, _ => (h1 : False).elim
  | .and _ _, .neg _, h1, _ => (h1 : False).elim
  | .and φ1 φ2, .and ψ1 ψ2, h1, h2 => by
      have e1 : φ1 = ψ1 := Formula.le_antisymm φ1 ψ1 h1.1 h2.1
      subst e1
      rw [Formula.le_antisymm φ2 ψ2 (h1.2 rfl) (h2.2 rfl)]
  | .and _ _, .box _ _, _, h2 => (h2 : False).elim
  | .box _ _, .bottom, h1, _ => (h1 : False).elim
  | .box _ _, .atom_prop _, h1, _ => (h1 : False).elim
  | .box _ _, .neg _, h1, _ => (h1 : False).elim
  | .box _ _, .and _ _, h1, _ => (h1 : False).elim
  | .box α φ, .box β ψ, h1, h2 => by
      have e1 : α = β := Program.le_antisymm α β h1.1 h2.1
      subst e1
      rw [Formula.le_antisymm φ ψ (h1.2 rfl) (h2.2 rfl)]

/-- The order on programs is antisymmetric.
@isnad1 id=eq.2h2v.s4.415cc11ec8bf from=translated src=- shape=5f71b5ec vocab=8f743887
-/
theorem Program.le_antisymm : ∀ (α β : Program), α.le β → β.le α → α = β
  | .atom_prog _, .atom_prog _, h1, h2 => by
      simp only [Program.atom_prog.injEq]
      exact Nat.le_antisymm h1 h2
  | .atom_prog _, .sequence _ _, _, h2 => (h2 : False).elim
  | .atom_prog _, .union _ _, _, h2 => (h2 : False).elim
  | .atom_prog _, .star _, _, h2 => (h2 : False).elim
  | .atom_prog _, .test _, _, h2 => (h2 : False).elim
  | .sequence _ _, .atom_prog _, h1, _ => (h1 : False).elim
  | .sequence α1 α2, .sequence β1 β2, h1, h2 => by
      have e1 : α1 = β1 := Program.le_antisymm α1 β1 h1.1 h2.1
      subst e1
      rw [Program.le_antisymm α2 β2 (h1.2 rfl) (h2.2 rfl)]
  | .sequence _ _, .union _ _, _, h2 => (h2 : False).elim
  | .sequence _ _, .star _, _, h2 => (h2 : False).elim
  | .sequence _ _, .test _, _, h2 => (h2 : False).elim
  | .union _ _, .atom_prog _, h1, _ => (h1 : False).elim
  | .union _ _, .sequence _ _, h1, _ => (h1 : False).elim
  | .union α1 α2, .union β1 β2, h1, h2 => by
      have e1 : α1 = β1 := Program.le_antisymm α1 β1 h1.1 h2.1
      subst e1
      rw [Program.le_antisymm α2 β2 (h1.2 rfl) (h2.2 rfl)]
  | .union _ _, .star _, _, h2 => (h2 : False).elim
  | .union _ _, .test _, _, h2 => (h2 : False).elim
  | .star _, .atom_prog _, h1, _ => (h1 : False).elim
  | .star _, .sequence _ _, h1, _ => (h1 : False).elim
  | .star _, .union _ _, h1, _ => (h1 : False).elim
  | .star α, .star β, h1, h2 => by rw [Program.le_antisymm α β h1 h2]
  | .star _, .test _, _, h2 => (h2 : False).elim
  | .test _, .atom_prog _, h1, _ => (h1 : False).elim
  | .test _, .sequence _ _, h1, _ => (h1 : False).elim
  | .test _, .union _ _, h1, _ => (h1 : False).elim
  | .test _, .star _, h1, _ => (h1 : False).elim
  | .test τ, .test σ, h1, h2 => by rw [Formula.le_antisymm τ σ h1 h2]
end

end PDL

namespace PDL

open HasLength

mutual

/-- The order on formulas is total.
@isnad1 id=or.0h2v.s3.3704a831b9fb from=translated src=- shape=62a40b99 vocab=f4a272b8
-/
theorem Formula.le_total : ∀ (φ ψ : Formula), φ.le ψ ∨ ψ.le φ
  | .bottom, .bottom => Or.inl trivial
  | .bottom, .atom_prop _ => Or.inl trivial
  | .bottom, .neg _ => Or.inl trivial
  | .bottom, .and _ _ => Or.inl trivial
  | .bottom, .box _ _ => Or.inl trivial
  | .atom_prop _, .bottom => Or.inr trivial
  | .atom_prop p, .atom_prop p' => Nat.le_total p p'
  | .atom_prop _, .neg _ => Or.inl trivial
  | .atom_prop _, .and _ _ => Or.inl trivial
  | .atom_prop _, .box _ _ => Or.inl trivial
  | .neg _, .bottom => Or.inr trivial
  | .neg _, .atom_prop _ => Or.inr trivial
  | .neg φ, .neg ψ => Formula.le_total φ ψ
  | .neg _, .and _ _ => Or.inl trivial
  | .neg _, .box _ _ => Or.inl trivial
  | .and _ _, .bottom => Or.inr trivial
  | .and _ _, .atom_prop _ => Or.inr trivial
  | .and _ _, .neg _ => Or.inr trivial
  | .and φ1 φ2, .and ψ1 ψ2 =>
      lex_total (Formula.le_rfl φ1) (Formula.le_total φ1 ψ1) (Formula.le_total φ2 ψ2)
  | .and _ _, .box _ _ => Or.inl trivial
  | .box _ _, .bottom => Or.inr trivial
  | .box _ _, .atom_prop _ => Or.inr trivial
  | .box _ _, .neg _ => Or.inr trivial
  | .box _ _, .and _ _ => Or.inr trivial
  | .box α φ, .box β ψ =>
      lex_total (Program.le_rfl α) (Program.le_total α β) (Formula.le_total φ ψ)

/-- The order on programs is total.
@isnad1 id=or.0h2v.s3.9a9c92ba723a from=translated src=- shape=62a40b99 vocab=8f743887
-/
theorem Program.le_total : ∀ (α β : Program), α.le β ∨ β.le α
  | .atom_prog a, .atom_prog a' => Nat.le_total a a'
  | .atom_prog _, .sequence _ _ => Or.inl trivial
  | .atom_prog _, .union _ _ => Or.inl trivial
  | .atom_prog _, .star _ => Or.inl trivial
  | .atom_prog _, .test _ => Or.inl trivial
  | .sequence _ _, .atom_prog _ => Or.inr trivial
  | .sequence α1 α2, .sequence β1 β2 =>
      lex_total (Program.le_rfl α1) (Program.le_total α1 β1) (Program.le_total α2 β2)
  | .sequence _ _, .union _ _ => Or.inl trivial
  | .sequence _ _, .star _ => Or.inl trivial
  | .sequence _ _, .test _ => Or.inl trivial
  | .union _ _, .atom_prog _ => Or.inr trivial
  | .union _ _, .sequence _ _ => Or.inr trivial
  | .union α1 α2, .union β1 β2 =>
      lex_total (Program.le_rfl α1) (Program.le_total α1 β1) (Program.le_total α2 β2)
  | .union _ _, .star _ => Or.inl trivial
  | .union _ _, .test _ => Or.inl trivial
  | .star _, .atom_prog _ => Or.inr trivial
  | .star _, .sequence _ _ => Or.inr trivial
  | .star _, .union _ _ => Or.inr trivial
  | .star α, .star β => Program.le_total α β
  | .star _, .test _ => Or.inl trivial
  | .test _, .atom_prog _ => Or.inr trivial
  | .test _, .sequence _ _ => Or.inr trivial
  | .test _, .union _ _ => Or.inr trivial
  | .test _, .star _ => Or.inr trivial
  | .test τ, .test σ => Formula.le_total τ σ
end

end PDL

namespace PDL

open HasLength

mutual

/-- The order on formulas is transitive.
@isnad1 id=le.2h3v.s4.4c95f60d70c3 from=translated src=- shape=0bc0c4a6 vocab=f4a272b8
-/
theorem Formula.le_trans_aux : ∀ (φ ψ χ : Formula), φ.le ψ → ψ.le χ → φ.le χ := by
  intro φ ψ χ h1 h2
  cases φ <;> cases ψ <;> cases χ <;>
    try first
      | exact trivial
      | exact (h1 : False).elim
      | exact (h2 : False).elim
  case atom_prop.atom_prop.atom_prop => exact Nat.le_trans h1 h2
  case neg.neg.neg φ ψ χ => exact Formula.le_trans_aux φ ψ χ h1 h2
  case and.and.and φ1 φ2 ψ1 ψ2 χ1 χ2 =>
    refine ⟨Formula.le_trans_aux φ1 ψ1 χ1 h1.1 h2.1, fun he => ?_⟩
    have e : φ1 = ψ1 := Formula.le_antisymm φ1 ψ1 h1.1 (by rw [he]; exact h2.1)
    exact Formula.le_trans_aux φ2 ψ2 χ2 (h1.2 e) (h2.2 (by rw [← e]; exact he))
  case box.box.box α φ β ψ γ χ =>
    refine ⟨Program.le_trans_aux α β γ h1.1 h2.1, fun he => ?_⟩
    have e : α = β := Program.le_antisymm α β h1.1 (by rw [he]; exact h2.1)
    exact Formula.le_trans_aux φ ψ χ (h1.2 e) (h2.2 (by rw [← e]; exact he))

/-- The order on programs is transitive.
@isnad1 id=le.2h3v.s4.ec7700f1b163 from=translated src=- shape=0bc0c4a6 vocab=8f743887
-/
theorem Program.le_trans_aux : ∀ (α β γ : Program), α.le β → β.le γ → α.le γ := by
  intro α β γ h1 h2
  cases α <;> cases β <;> cases γ <;>
    try first
      | exact trivial
      | exact (h1 : False).elim
      | exact (h2 : False).elim
  case atom_prog.atom_prog.atom_prog => exact Nat.le_trans h1 h2
  case sequence.sequence.sequence α1 α2 β1 β2 γ1 γ2 =>
    refine ⟨Program.le_trans_aux α1 β1 γ1 h1.1 h2.1, fun he => ?_⟩
    have e : α1 = β1 := Program.le_antisymm α1 β1 h1.1 (by rw [he]; exact h2.1)
    exact Program.le_trans_aux α2 β2 γ2 (h1.2 e) (h2.2 (by rw [← e]; exact he))
  case union.union.union α1 α2 β1 β2 γ1 γ2 =>
    refine ⟨Program.le_trans_aux α1 β1 γ1 h1.1 h2.1, fun he => ?_⟩
    have e : α1 = β1 := Program.le_antisymm α1 β1 h1.1 (by rw [he]; exact h2.1)
    exact Program.le_trans_aux α2 β2 γ2 (h1.2 e) (h2.2 (by rw [← e]; exact he))
  case star.star.star α β γ => exact Program.le_trans_aux α β γ h1 h2
  case test.test.test τ σ ρ => exact Formula.le_trans_aux τ σ ρ h1 h2
end

end PDL

namespace PDL

open HasLength

/--
@isnad1 id=le.2h3v.s4.d26e209fbfdf from=translated src=- shape=8b2dd8a3 vocab=34e00371
-/
lemma Formula.le_trans : ∀ (f g h : Formula), f ≤ g → g ≤ h → f ≤ h :=
  Formula.le_trans_aux

/--
@isnad1 id=istrans.0h0v.s3.25b4a29c55e1 from=translated src=- shape=9944374c vocab=86b501ca
-/
instance instIsTransFormulaLe : IsTrans Formula (fun (a b : Formula) ↦ a ≤ b) :=
  ⟨Formula.le_trans⟩

instance : Std.Antisymm (fun (a b : Formula) ↦ a ≤ b) := ⟨Formula.le_antisymm⟩

instance : Std.Total (fun (a b : Formula) ↦ a ≤ b) := ⟨Formula.le_total⟩

/-- List the elements of a formula finset in the fixed formula order. -/
def _root_.Finset.pdlSort : Finset Formula → List Formula | FS => FS.sort

/--
@isnad1 id=iff.0h2v.s4.b674e30d9314 from=translated src=- shape=5a4bb582 vocab=81471a1b
-/
@[simp]
lemma Formula.mem_pdlSort {X : Finset Formula} : φ ∈ X.pdlSort ↔ φ ∈ X := by simp [Finset.pdlSort]

end PDL
