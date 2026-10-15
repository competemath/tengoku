/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Tengoku.LeanPool.LeanPool.PDL.Semantics
public import Tengoku.LeanPool.LeanPool.PDL.Vocab
public import Tengoku

/-! # (Big) Disjunction and Conjunction

Here we define ⋀ and ⋁ on formulas and seveal helper lemmas.
-/

@[expose] public section

namespace PDL

/-! ## Conjunction -/

/-- Conjunction of a list of formulas, with the empty conjunction equal to truth. -/
@[simp]
def con : List Formula → Formula
  | [] => ⊤
  | [f] => f
  | f :: rest => f⋀con rest

/--
@isnad1 id=eq.0h0v.s3.a7512d490552 from=translated src=- shape=76fe020d vocab=fa8bc63f
-/
theorem conempty : con ∅ = (⊤ : Formula) := by rfl

/--
@isnad1 id=eq.0h1v.s3.4760839d78d0 from=translated src=- shape=5aa60faa vocab=a11c312f
-/
@[simp]
theorem consingle {f : Formula} : con [f] = f := by rfl

/--
@isnad1 id=eq.1h2v.s4.de2d8a3945d4 from=translated src=- shape=c9bd5ef9 vocab=26591be4
-/
theorem listEq_to_conEq : l1 = l2 → con l1 = con l2 := by
  aesop

/--
@isnad1 id=iff.0h5v.s5.05daf0548f4e from=translated src=- shape=5b9d2752 vocab=276379cd
-/
theorem conEvalHT {X f W M} {w : W} :
    evaluate M w (con (f :: X)) ↔ evaluate M w f ∧ evaluate M w (con X) :=
  by
  induction X
  · simp
  · simp

/--
@isnad1 id=iff.0h4v.s5.0e523775b8a9 from=translated src=- shape=07f86ff8 vocab=6d7de4b9
-/
theorem conEval {W M X} {w : W} : evaluate M w (con X) ↔ ∀ f ∈ X, evaluate M w f :=
  by
  induction X
  · simp
  · rw [conEvalHT]
    simp only [List.mem_cons, forall_eq_or_imp, and_congr_right_iff]
    intro _
    assumption

/-- Vocabulary of Conjunction
@isnad1 id=iff.0h2v.s5.61ab008a3f96 from=translated src=- shape=0764fe71 vocab=fa378ab5
-/
theorem in_voc_con n (L : List Formula) :
    n ∈ (con L).voc ↔ ∃ φ ∈ L, n ∈ φ.voc := by
  induction L
  · simp [con, Formula.voc]
  case cons h t IH =>
    induction t -- needed to select case in `Con`
    · simp [con]
    case cons h t IH =>
      simp only [List.mem_cons, exists_eq_or_imp, con, Formula.voc, Finset.mem_union] at *
      rw [← IH]

/-- The conjunction of a `Finset` of formulas, via `Finset.pdlSort`. -/
def _root_.Finset.pdlCon (X : Finset Formula) : Formula := _root_.PDL.con X.pdlSort

/--
@isnad1 id=eq.0h0v.s3.60f11a78f81c from=translated src=- shape=76fe020d vocab=d01a200d
-/
@[simp]
theorem Finset.con_empty : Finset.pdlCon ∅ = (⊤ : Formula) := by
  simp [Finset.pdlCon, Finset.pdlSort]

/--
@isnad1 id=eq.0h1v.s3.e5cac4432309 from=translated src=- shape=41f33cba vocab=ea722882
-/
@[simp]
theorem Finset.con_singleton {f : Formula} : Finset.pdlCon {f} = f := by
  simp [Finset.pdlCon, Finset.pdlSort]

/--
@isnad1 id=iff.0h4v.s5.2a04e790dbb3 from=translated src=- shape=07f86ff8 vocab=66ac1ab5
-/
theorem Finset.conEval {W M} {X : Finset Formula} {w : W} :
    evaluate M w X.pdlCon ↔ ∀ f ∈ X, evaluate M w f := by
  simp [Finset.pdlCon, _root_.PDL.conEval]

/-- Evaluating a conjunction does not care about sorting.
@isnad1 id=iff.0h4v.s5.e575c6c1020f from=translated src=- shape=ad98e820 vocab=1e4eb608
-/
lemma evaluate_con_sort (X : Finset Formula) :
    evaluate M w (con (X.sort fun a b ↦ a ≤ b)) ↔ ∀ φ ∈ X, evaluate M w φ := by
  rw [conEval]
  simp

/-- Vocabulary of the conjunction of a `Finset`.
@isnad1 id=iff.0h2v.s5.e63562c554ed from=translated src=- shape=0764fe71 vocab=10141c4b
-/
theorem Finset.in_voc_con n (X : Finset Formula) :
    n ∈ X.pdlCon.voc ↔ ∃ φ ∈ X, n ∈ φ.voc := by
  simp [Finset.pdlCon, _root_.PDL.in_voc_con]

/-! ## Disjunction -/

/-- Disjunction of a list of formulas, with the empty disjunction equal to falsity. -/
@[simp]
def dis : List Formula → Formula
  | [] => ⊥
  | [f] => f
  | f :: rest => f ⋁ dis rest

/--
@isnad1 id=eq.0h0v.s3.f6f09be94296 from=translated src=- shape=76fe020d vocab=4da561cb
-/
@[simp]
theorem disempty : dis ∅ = (⊥ : Formula) := rfl

/--
@isnad1 id=eq.0h1v.s3.ee503864a2ed from=translated src=- shape=5aa60faa vocab=528a3002
-/
@[simp]
theorem dissingle {f : Formula} : dis [f] = f := rfl

/--
@isnad1 id=eq.1h2v.s4.d6afbaef4bcf from=translated src=- shape=c9bd5ef9 vocab=e71fb09e
-/
theorem listEq_to_disEq : l1 = l2 → dis l1 = dis l2 := by
  aesop

/--
@isnad1 id=iff.0h5v.s5.450ecc0b265a from=translated src=- shape=5b9d2752 vocab=07b15f34
-/
theorem disEvalHT {X f W M} {w : W} :
    evaluate M w (dis (f :: X)) ↔ evaluate M w f ∨ evaluate M w (dis X) :=
  by
  induction X
  · simp
  · simp
    tauto

/--
@isnad1 id=iff.0h4v.s5.59ba544b7e92 from=translated src=- shape=49fd384e vocab=014f5748
-/
theorem disEval {W M X} {w : W} : evaluate M w (dis X) ↔ ∃ f ∈ X, evaluate M w f :=
  by
  induction X
  · simp
  · rw [disEvalHT]
    simp_all

/-- Vocabulary of Disjunction
@isnad1 id=iff.0h2v.s5.4f092ddfb382 from=translated src=- shape=0764fe71 vocab=3a7ee471
-/
theorem in_voc_dis n (L : List Formula) :
    n ∈ (dis L).voc ↔ ∃ φ ∈ L, n ∈ φ.voc := by
  induction L
  · simp [dis, Formula.voc]
  case cons h t IH =>
    induction t -- needed to select case in `dis`
    · simp [dis]
    case cons h t IH =>
      simp only [List.mem_cons, exists_eq_or_imp, dis, Formula.or, Formula.voc, Finset.mem_union]
        at *
      rw [← IH]

/-- The disjunction of a `Finset` of formulas, via `Finset.pdlSort`. -/
def _root_.Finset.pdlDis (X : Finset Formula) : Formula := _root_.PDL.dis X.pdlSort

/--
@isnad1 id=eq.0h0v.s3.79d93ae373d8 from=translated src=- shape=76fe020d vocab=b5c87dd0
-/
@[simp]
theorem Finset.dis_empty : Finset.pdlDis ∅ = (⊥ : Formula) := by
  simp [Finset.pdlDis, Finset.pdlSort]

/--
@isnad1 id=eq.0h1v.s3.958805211939 from=translated src=- shape=41f33cba vocab=8b48c6fe
-/
@[simp]
theorem Finset.dis_singleton {f : Formula} : Finset.pdlDis {f} = f := by
  simp [Finset.pdlDis, Finset.pdlSort]

/--
@isnad1 id=iff.0h4v.s5.6a3c466b1bd1 from=translated src=- shape=49fd384e vocab=7a13474a
-/
theorem Finset.disEval {W M} {X : Finset Formula} {w : W} :
    evaluate M w X.pdlDis ↔ ∃ f ∈ X, evaluate M w f := by
  simp [Finset.pdlDis, _root_.PDL.disEval]

/-- Vocabulary of the disjunction of a `Finset`.
@isnad1 id=iff.0h2v.s5.bdcce45772aa from=translated src=- shape=0764fe71 vocab=4b52c539
-/
theorem Finset.in_voc_dis n (X : Finset Formula) :
    n ∈ X.pdlDis.voc ↔ ∃ φ ∈ X, n ∈ φ.voc := by
  simp [Finset.pdlDis, _root_.PDL.in_voc_dis]

/-! ## Disjunction of Conjunctions -/

/-- Disjunction of the conjunctions represented by a list of formula lists. -/
@[simp]
def discon : List (List Formula) → Formula
  | [] => ⊥
  | [X] => con X
  | X :: rest => con X ⋁ discon rest

/--
@isnad1 id=eq.0h0v.s4.54594595fa75 from=translated src=- shape=60fdcb3c vocab=f6029885
-/
theorem disconempty : discon {∅} = (⊤ : Formula) := by rfl

/--
@isnad1 id=eq.0h1v.s4.dec90bd9a7c9 from=translated src=- shape=e2d235fe vocab=84af44a4
-/
@[simp]
theorem disconsingle {f : Formula} : discon [[f]] = f := by rfl

/--
@isnad1 id=semequiv.0h2v.s4.50b5320a056c from=translated src=- shape=5867e702 vocab=4312266b
-/
theorem disconEvalHT {X} : ∀ XS, discon (X :: XS) ≡ con X ⋁ discon XS :=
  by
  unfold semEquiv
  intro XS W M w
  cases XS <;> simp

/-- Variant of `disconEval` for a specific length of `XS` to be provable by induction.
@isnad1 id=iff.1h5v.s5.df8b33cfcfb2 from=translated src=- shape=09c00d6c vocab=c0c9ff8e
-/
theorem disconEval' {W M} {w : W} :
    ∀ {N : Nat} XS,
      List.length XS = N → (evaluate M w (discon XS) ↔ ∃ Y ∈ XS, ∀ f ∈ Y, evaluate M w f) := by
  intro N
  induction N using Nat.strong_induction_on
  case h n IH =>
    intro XS def_n
    subst def_n
    rcases XS with _ | ⟨X,XS⟩
    · simp
    specialize IH XS.length (by simp) XS (by rfl)
    rw [disconEvalHT]
    rw [evalDis]
    rw [IH]
    constructor
    · -- →
      intro lhs
      rcases lhs with lhs|lhs
      · use X
        simp only [List.mem_cons, true_or, true_and]
        rw [conEval] at lhs
        tauto
      · rcases lhs with ⟨Y,claim⟩
        use Y
        simp only [List.mem_cons]
        tauto
    · -- ←
      intro rhs
      rcases rhs with ⟨Y,Y_in,Ysat⟩
      simp only [List.mem_cons] at Y_in
      rcases Y_in with Y_in|Y_in
      · left
        subst Y_in
        rw [conEval]; tauto
      · right
        use Y

/--
@isnad1 id=iff.0h4v.s5.b72944a35e9e from=translated src=- shape=3f82a295 vocab=f7c56f49
-/
theorem disconEval {W M} {w : W} :
    ∀ XS,
      (evaluate M w (discon XS) ↔ ∃ Y ∈ XS, ∀ f ∈ Y, evaluate M w f) :=
  by
    intro XS
    apply disconEval' XS rfl

/--
@isnad1 id=semequiv.0h2v.s4.dddd04a0b48a from=translated src=- shape=f616bc91 vocab=e5aef2d0
-/
theorem disconOr {XS YS} : discon (XS ∪ YS) ≡ discon XS ⋁ discon YS :=
  by
  unfold semEquiv
  intro W M w
  rw [disconEval (XS ∪ YS)]
  simp only [List.mem_union_iff, Formula.or, evaluate.eq_3, evaluate, not_and, not_not]
  rw [disconEval XS]
  rw [disconEval YS]
  constructor
  · -- →
    intro lhs
    rcases lhs with ⟨Z, Z_in, w_sat_Z⟩
    intro notL
    simp only [not_exists, not_and, not_forall] at notL
    cases Z_in
    case inl Z_in_XS =>
      specialize notL Z Z_in_XS
      rcases notL with ⟨f, f_in_Z, w_not_f⟩
      specialize w_sat_Z f f_in_Z
      absurd w_sat_Z
      exact w_not_f
    use Z
  · -- ←
    intro rhs
    cases (Classical.em (∃ Y, Y ∈ XS ∧ ∀ (f : Formula), f ∈ Y → evaluate M w f))
    case inl hyp =>
      rcases hyp with ⟨X, X_in, satX⟩
      use X
      exact ⟨Or.inl X_in, satX⟩
    case inr nothyp =>
      specialize rhs nothyp
      rcases rhs with ⟨Y, Y_in, satY⟩
      use Y
      exact ⟨Or.inr Y_in, satY⟩

/-! ### Sorting lists of formulas

To also sort a `Finset (Finset Formula)` we need an order on `List Formula`.
We use the lexicographic order `List.le` coming from the order on formulas.

TODO: these could be moved to `Pdl.Syntax`, next to `Finset.pdlSort`.
-/

/-- The linear order on formulas, bundling the results from `Pdl.Syntax`.
This is only used locally, to get the lexicographic order on `List Formula`. -/
@[instance_reducible]
def Formula.linearOrder : LinearOrder Formula where
  le := Formula.le
  lt := fun φ ψ => φ ≠ ψ ∧ φ.le ψ
  le_refl := Formula.le_rfl
  le_trans := Formula.le_trans
  le_antisymm := Formula.le_antisymm
  le_total := Formula.le_total
  lt_iff_le_not_ge := by
    intro φ ψ
    constructor
    · rintro ⟨hne, hle⟩
      exact ⟨hle, fun hba => hne (Formula.le_antisymm _ _ hle hba)⟩
    · rintro ⟨hle, hnot⟩
      exact ⟨by rintro rfl; exact hnot (Formula.le_rfl _), hle⟩
  toDecidableLE := Formula.decLe

attribute [local instance] Formula.linearOrder

/-- The lexicographic `List.le` on `List Formula` agrees with the `≤` coming from
the linear order `Formula.linearOrder`.
@isnad1 id=iff.0h2v.s4.28d3e5b1fa5a from=translated src=- shape=3a4c8c7c vocab=ce842133
-/
lemma List.le_iff_le_formula (l1 l2 : List Formula) : List.le l1 l2 ↔ l1 ≤ l2 := by
  change ¬ (l2 < l1) ↔ l1 ≤ l2
  exact not_lt

instance : DecidableRel (@List.le Formula instLTFormula) :=
  fun l1 l2 => decidable_of_iff _ (List.le_iff_le_formula l1 l2).symm

instance : IsTrans (List Formula) List.le :=
  ⟨fun _ _ _ h12 h23 => (List.le_iff_le_formula _ _).2
    (le_trans ((List.le_iff_le_formula _ _).1 h12) ((List.le_iff_le_formula _ _).1 h23))⟩

instance : Std.Antisymm (@List.le Formula instLTFormula) :=
  ⟨fun _ _ h12 h21 => le_antisymm ((List.le_iff_le_formula _ _).1 h12)
    ((List.le_iff_le_formula _ _).1 h21)⟩

instance : Std.Total (@List.le Formula instLTFormula) :=
  ⟨fun l1 l2 => (le_total l1 l2).imp (List.le_iff_le_formula _ _).2
    (List.le_iff_le_formula _ _).2⟩

/-- The disjunction of conjunctions given by a `Finset (Finset Formula)`.
The inner sets are sorted with `Finset.pdlSort` and the outer set is then sorted
lexicographically with `List.le`. -/
def _root_.Finset.pdlDiscon : Finset (Finset Formula) → Formula
  | XS => _root_.PDL.discon ((XS.image Finset.pdlSort).sort List.le)

/--
@isnad1 id=iff.0h4v.s5.6a649ad66702 from=translated src=- shape=3f82a295 vocab=352a6fac
-/
theorem Finset.disconEval {W M} {w : W} (XS : Finset (Finset Formula)) :
    evaluate M w XS.pdlDiscon ↔ ∃ Y ∈ XS, ∀ f ∈ Y, evaluate M w f := by
  rw [Finset.pdlDiscon, _root_.PDL.disconEval]
  simp only [Finset.mem_sort, Finset.mem_image]
  constructor
  · rintro ⟨l, ⟨Y, Y_in, rfl⟩, hl⟩
    exact ⟨Y, Y_in, fun f f_in => hl f (Formula.mem_pdlSort.2 f_in)⟩
  · rintro ⟨Y, Y_in, hY⟩
    exact ⟨Y.pdlSort, ⟨Y, Y_in, rfl⟩, fun f f_in => hY f (Formula.mem_pdlSort.1 f_in)⟩

/-! ## Pairwise Union -/

/-- All concatenations of one formula list from each input family. -/
@[simp]
def pairunionList : List (List Formula) → List (List Formula) → List (List Formula)
  | xls, yls => List.flatten (xls.map fun xl => yls.map fun yl => xl ++ yl)

/-- All unions of one formula finset from each input family. -/
@[simp]
def pairunionFinset : Finset (Finset Formula) → Finset (Finset Formula) → Finset (Finset Formula)
  | X, Y => X.biUnion fun ga => Y.biUnion fun gb => {ga ∪ gb}

/-- Containers supporting pairwise combination of families of formula collections. -/
class HasUplus (α : Type → Type) where
  /-- Combine every collection from the first family with every collection from the second. -/
  pairunion : α (α Formula) → α (α Formula) → α (α Formula)

/-- Pairwise combination of two families of formula collections. -/
scoped infixl:77 "⊎" => HasUplus.pairunion

@[simp]
instance listHasUplus : HasUplus List := ⟨pairunionList⟩
@[simp]
instance finsetHasUplus : HasUplus Finset := ⟨pairunionFinset⟩

/--
@isnad1 id=semequiv.0h2v.s4.9b1793c7ae02 from=translated src=- shape=6af60ea3 vocab=6dedaef6
-/
theorem disconAnd {XS YS} : discon (XS ⊎ YS) ≡ discon XS ⋀ discon YS :=
  by
  unfold semEquiv
  intro W M w
  rw [disconEval (XS ⊎ YS)]
  simp only [HasUplus.pairunion, pairunionList, List.mem_flatten, List.mem_map,
    exists_exists_and_eq_and, exists_exists_and_exists_and_eq_and, List.mem_append, evaluate]
  rw [disconEval XS]
  rw [disconEval YS]
  aesop

/--
@isnad1 id=mem.2h4v.s6.c2ec15f156ae from=translated src=- shape=2d6f9679 vocab=ba97e959
-/
theorem union_elem_uplus {XS YS : Finset (Finset Formula)} {X Y : Finset Formula} :
  X ∈ XS → Y ∈ YS → ((X ∪ Y) ∈ (XS ⊎ YS)) :=
  by
  intro X_in Y_in
  simp only [HasUplus.pairunion, pairunionFinset, Finset.mem_biUnion, Finset.mem_singleton]
  exact ⟨X, X_in, Y, Y_in, rfl⟩

/-- Helper for `oneSidedLocalRuleTruth`, used with `g = Yset`.
@isnad1 id=iff.0h6v.s6.6184dc06be00 from=translated src=- shape=b0b4d578 vocab=ca245ad4
-/
theorem mapCon_mapForall (M : KripkeModel W) w φ
    (g : (List Formula × List Program) → Formula → List Formula) :
    (∃ f ∈ List.map (fun Fδ => con (g Fδ φ)) X, evaluate M w f) ↔
    ∃ fs ∈ List.map (fun Fδ => g Fδ φ) X, ∀ f ∈ fs, evaluate M w f := by
  simp_all only [List.mem_map, Prod.exists, ↓existsAndEq, and_true]
  constructor <;> grind [conEval]

end PDL
