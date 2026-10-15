/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Tengoku

public import Tengoku.LeanPool.LeanPool.PDL.Vocab

/-! # Fischer-Ladner Closure

Here we define a closure on sets (well, actually lists) of formulas.
Our main reference for this closure is Section 6.1 of [HKT2000]
which also was used in a Rocq formalization in [DB2018].
The code for that work can be found at
[github.com/chdoc/comp-dec-pdl](https://github.com/chdoc/comp-dec-pdl)
and their FL closure definition starts at
[line 472 of `PDL_def.v`](https://github.com/chdoc/comp-dec-pdl/blob/master/PDL/PDL_def.v#L472).

See also Definition 4.79 and Exercise 4.8.2 in [BRV2001].
An alternative version following the proof of Theorem 3.2 in [FL1979]
but unfinished is in `Unused/FischerLadnerViaPreForms.lean`.

-/

@[expose] public section

namespace PDL

/-! ## Definition  -/

mutual
/-- The Fischer-Ladner closure of a formula.
See Section 6.1 of [HKT2000]. Note that there only implication is given.
For our `Formula` type we also need to cover conjunction and negation.
Also note that we are closing under single negations as well here.
The main work is done by `FLb`, which also ensures termination. -/
def FL : Formula → List Formula
| ⊥ => [⊥, ~⊥]
| ·p => [·p, ~·p]
| φ⋀ψ => [φ⋀ψ, ~(φ⋀ψ), ~φ, ~ψ] ++ FL φ ++ FL ψ -- ~φ and ~ψ needed for ~~ case.
| ⌈α⌉φ => [~⌈α⌉φ, ~φ] ++ FLb α φ ++ FL φ -- Note: `~⌈α⌉φ` seems needed for `FLb_trans`.
| ~φ => [~φ] ++ FL φ -- first element needed to deal with ~~φ, ~~~φ etc.

/-- The Fischer-Ladner closure of a box formula,
not recursing into the formula after the box. -/
def FLb : Program → Formula → List Formula
| ·a, φ => [ ⌈·a⌉φ, ~⌈·a⌉φ ]
| α⋓β, φ => [ ⌈α⋓β⌉φ, ~⌈α⋓β⌉φ ] ++ FLb α φ ++ FLb β φ
| α;'β, φ => [ ⌈α;'β⌉φ, ~⌈α;'β⌉φ ] ++ FLb α (⌈β⌉φ) ++ FLb β φ
| ∗α, φ => [ ⌈∗α⌉φ, ~⌈∗α⌉φ ] ++ FLb α (⌈∗α⌉φ)
| ?'τ, φ => [ ⌈?'τ⌉φ, ~⌈?'τ⌉φ, ~τ ] ++ FL τ
end

-- Reopen namespaces after mutual blocks to keep source-based declaration audits aligned.
end PDL

namespace PDL

/-! ## Lemmas  -/

/-- Whether a formula has an outer negation constructor. -/
def isNeg : Formula → Prop
| ~_ => True
| _ => False

/--
@isnad1 id=mem.1h1v.s4.52fa03c88a88 from=translated src=- shape=a9b44a76 vocab=3e8f90e8
-/
lemma FL_single_neg_closed {φ} :
    ¬ isNeg φ → ~φ ∈ FL φ := by
  cases φ <;> simp [FL, isNeg, Bot.bot]

/--
@isnad1 id=mem.0h1v.s3.4acd2820b8e3 from=translated src=- shape=24504379 vocab=3628a717
-/
@[simp]
lemma FL_refl {φ} :
    φ ∈ FL φ := by
  cases φ
  case box α φ =>
    cases α <;> simp [FL, FLb]
  all_goals
    simp [FL, Bot.bot]

/--
@isnad1 id=mem.0h2v.s4.a3d6371579e9 from=translated src=- shape=cdb76dc7 vocab=f6e35479
-/
@[simp]
lemma FLb_refl {α φ} :
    (⌈α⌉φ) ∈ FLb α φ := by
  cases α <;> simp [FLb]

/--
@isnad1 id=mem.0h2v.s4.221973662a07 from=translated src=- shape=c4c3268d vocab=9103f58a
-/
@[simp]
lemma neg_mem_FLb : (~⌈α⌉ψ) ∈ FLb α ψ := by cases α <;> simp [FLb]

mutual
/-- Lemma 6.1(i) from [HKT2000]
@isnad1 id=subset.1h2v.s4.f000be5d6e24 from=translated src=- shape=25aa6d0a vocab=e4ce404a
-/
lemma FL_trans {φ ψ} :
    ψ ∈ FL φ → FL ψ ⊆ FL φ := by
  intro ψ_in
  cases φ <;> simp only [FL, List.mem_cons, List.not_mem_nil, or_false, List.cons_append,
    List.nil_append, List.mem_append] at *
  · cases ψ_in <;> subst_eqs <;> simp [FL]
  · cases ψ_in <;> subst_eqs <;> simp [FL]
  · case neg φ =>
    cases ψ_in <;> subst_eqs
    · simp [FL]
    · have IH := @FL_trans φ
      aesop
  case and φ1 φ2 =>
    rcases ψ_in with h|h|h|h|h|h <;> subst_eqs
    · simp [FL]
    · simp [FL]
    · simp [FL]; grind
    · simp [FL]; grind
    · have IH1 := @FL_trans φ1 ψ h
      grind
    · have IH2 := @FL_trans φ2 ψ h
      grind
  case box α φ =>
    rcases ψ_in with h|h|h|h
    · subst_eqs
      simp [FL]
    · subst_eqs
      grind [FL]
    · have := FLb_trans h
      grind [FL]
    · have IH := @FL_trans φ ψ
      grind

/-- Lemma 6.1(ii) from [HKT2000]
@isnad1 id=subset.1h3v.s5.74d7f2204f8c from=translated src=- shape=4e1856be vocab=a0fe5990
-/
lemma FLb_trans {α φ ψ} :
    ψ ∈ FLb α φ → FL ψ ⊆ FLb α φ ++ FL (~φ) := by
  intro ψ_in
  cases α <;> simp only [FLb, List.mem_cons, List.not_mem_nil, or_false, List.cons_append,
    List.nil_append, List.mem_append, List.append_assoc] at *
  · cases ψ_in <;> subst_eqs <;> grind [FL, FLb]
  case sequence α1 α2 =>
    rcases ψ_in with h|h|h|h
    · subst_eqs; grind [FL,FLb]
    · subst_eqs; grind [FL,FLb]
    · have IH1 := @FLb_trans α1 (⌈α2⌉φ) ψ h
      intro x x_in
      specialize IH1 x_in
      simp only [FL, List.cons_append, List.nil_append, List.mem_append, List.mem_cons,
        or_self_left] at *
      aesop
    · have IH2 := @FLb_trans α2 φ ψ h
      grind [FL]
  case union α1 α2 =>
    rcases ψ_in with h|h|h|h
    · subst_eqs; grind [FL,FLb]
    · subst_eqs; grind [FL,FLb]
    · have IH1 := @FLb_trans α1 φ ψ h
      intro x x_in
      specialize IH1 x_in
      aesop
    · have IH2 := @FLb_trans α2 φ ψ h
      intro x x_in
      specialize IH2 x_in
      aesop
  case star α =>
    rcases ψ_in with h|h|h
    · subst_eqs; grind [FL,FLb]
    · subst_eqs; grind [FL,FLb]
    · have IH := @FLb_trans α (⌈∗α⌉φ) ψ h
      intro x x_in
      specialize IH x_in
      simp only [FL, List.cons_append, List.nil_append, List.mem_append, List.mem_cons,
        or_self_left] at *
      rcases IH with h|h|h|h|h
      · aesop
      · aesop
      · aesop
      · grind [FLb]
      · aesop
  case test τ =>
    rcases ψ_in with h|h|h
    · subst_eqs; grind [FL, FLb]
    · subst_eqs; simp [FL, FLb]; grind
    · have := @FL_trans τ ψ
      grind [FL]
end

end PDL

namespace PDL

/- Lemma 6.2(i) -/

/- A generalization of Lemma 6.2(i) -/

/- Lemma 6.2(ii) -/

/- Lemma 6.2(iii) -/

/- Lemma 6.2(iv) -/

/- Lemma 6.2(v) -/

/-! ## Closure of a list -/

/-- Concatenate the Fischer-Ladner closures of every formula in a list. -/
def FLL (L : List Formula) : List Formula := L.flatMap FL

/--
@isnad1 id=subset.0h1v.s3.7fa6fdeb2029 from=translated src=- shape=b357b47d vocab=4d348a4b
-/
@[simp]
lemma FLL_refl_sub {L} : L ⊆ FLL L := by induction L <;> simp_all [FLL]

/--
@isnad1 id=eq.0h0v.s3.b3b65952f95f from=translated src=- shape=9b1c3ca8 vocab=2e9dd0d8
-/
@[simp]
lemma FLL_nil : FLL [] = [] := List.flatMap_nil

/--
@isnad1 id=eq.0h1v.s3.1007ce0385dd from=translated src=- shape=b68af7a8 vocab=4f8f1226
-/
@[simp]
lemma FLL_singelton : FLL [φ] = FL φ := by simp [FLL]

/--
@isnad1 id=iff.0h2v.s4.7aeb188c1166 from=translated src=- shape=2fa07988 vocab=fd4ea109
-/
@[simp]
lemma FLL_idem_ext {L φ} : φ ∈ FLL (FLL L) ↔ φ ∈ FLL L := by
  constructor
  · unfold FLL
    intro φ_in
    have := @FL_trans
    grind
  · intro φ_in
    have := @FLL_refl_sub (FLL L)
    grind

/-! ## FL Closure of a Finset of Formulas -/

end PDL

namespace Finset
open PDL

/-- The union of the Fischer-Ladner closures of every formula in a finset. -/
def FL (X : Finset Formula) : Finset Formula :=
  X.sup (fun φ => (_root_.PDL.FL φ).toFinset)

/--
@isnad1 id=le.0h1v.s4.5f01df0fd512 from=translated src=- shape=b357b47d vocab=68574fef
-/
@[simp]
lemma FL_refl_sub {X : Finset Formula} : X ⊆ X.FL := by
  intro φ φ_in
  simp_all only [FL, mem_sup, List.mem_toFinset]
  have := @FLL_refl_sub X.pdlSort
  have := @FL_refl φ
  use φ

/--
@isnad1 id=le.1h2v.s5.f8d7a9000911 from=translated src=- shape=4ad33e2d vocab=68574fef
-/
lemma FL_sub {X Y : Finset Formula} : X ⊆ Y → FL X ⊆ FL Y := by
  unfold FL
  intro h x x_in
  aesop

/--
@isnad1 id=eq.0h0v.s3.e38e450d715e from=translated src=- shape=f2c814de vocab=7bf07867
-/
@[simp]
lemma FL_nil : Finset.FL {} = {} := rfl

/--
@isnad1 id=eq.0h1v.s4.073a17fcb4a9 from=translated src=- shape=fb1fba54 vocab=03519d81
-/
@[simp]
lemma FL_singelton {φ} : Finset.FL {φ} = (_root_.PDL.FL φ).toFinset := by simp [FL]

/--
@isnad1 id=iff.0h2v.s5.f1a5115f6403 from=translated src=- shape=2fa07988 vocab=378866fd
-/
@[simp]
lemma FL_idem_ext {X : Finset Formula} {φ} : φ ∈ FL (FL X) ↔ φ ∈ FL X := by
  constructor
  · unfold FL
    intro φ_in
    simp only [mem_sup, List.mem_toFinset] at *
    rcases φ_in  with ⟨φ2, ⟨⟨φ3, φ3_in, φ2_in⟩, φ_in⟩⟩
    have := FL_trans φ2_in
    grind
  · unfold FL
    intro φ_in
    simp only [mem_sup, List.mem_toFinset] at *
    rcases φ_in with ⟨φ2, φ2_in, φ_in⟩
    use φ2
    simp_all only [and_true]
    have := @FL_refl φ2
    use φ2

/--
@isnad1 id=iff.0h2v.s5.7dbcfb7cced7 from=translated src=- shape=971f5d8a vocab=68574fef
-/
lemma FL_sub_FL_iff_sub_FL {X Y : Finset Formula} : X ⊆ FL Y ↔ FL X ⊆ FL Y := by
  constructor
  · unfold FL
    rintro h φ' φ'_in
    simp_all only [mem_sup, List.mem_toFinset]
    rcases φ'_in with ⟨φ, φ_in, φ'_in⟩
    specialize h φ_in
    simp only [mem_sup, List.mem_toFinset] at h
    rcases h with ⟨φ'', φ''_in, φ_in⟩
    use φ''
    have := @FL_trans
    grind
  · intro X_U φ φ_in
    have := @FL_refl_sub
    grind

/--
@isnad1 id=eq.0h2v.s4.3b013c3072fc from=translated src=- shape=5f152bb3 vocab=b1230d14
-/
lemma FL_union_eq {X Y : Finset Formula} :
  FL (X ∪ Y) = FL X ∪ FL Y := by simp [FL]; grind

end Finset

namespace PDL

/-! ## FL stays in the Vocabulary -/

end PDL

namespace PDL

end PDL
