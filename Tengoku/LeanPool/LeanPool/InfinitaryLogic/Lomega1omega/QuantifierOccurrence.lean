/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Tengoku.LeanPool.LeanPool.InfinitaryLogic.Lomega1omega.QuantifierClass
/-!
# Signed quantifier *occurrence* (issue #15, budget gate 1)

`QuantifierClass.lean` answers "is **every** quantifier of this sign admissible?"; Feferman's
separator budgets need the dual, positive question: "**does** a quantifier of this sign occur?".

Defining occurrence as `¬ IsUniversal` / `¬ IsExistential` would work extensionally but makes every
budget calculation a double-negation exercise. So occurrence is given its own signed recursion,
with
exact constructor equations, and the two are then related by an exact bridge:

```
universalSigned s φ ↔ ¬ hasQuantSigned (!s) φ
IsUniversal φ ↔ ¬ HasExistential φ      IsExistential φ ↔ ¬ HasUniversal φ
```

The sign discipline is the same as in `QuantifierClass.lean` and `Polarity.lean`: an antecedent
flips, `iSup`/`iInf` preserve and are not quantifiers, and `all` is a *universal* occurrence at the
positive sign only.  Nothing here mentions interpolation; the set-level versions at the end are what
the separator budgets are stated against.
-/

@[expose] public section

namespace FirstOrder.Language

namespace BoundedFormulaω

variable {L : Language.{0, 0}} {α β : Type}

/-- **Signed quantifier occurrence.**  `hasQuantSigned true φ` says a quantifier occurs
*universally* in `φ`; `hasQuantSigned false φ` says one occurs *existentially* (a negatively
occurring `all`). -/
def hasQuantSigned : ∀ {n : ℕ}, Bool → L.BoundedFormulaω α n → Prop
  | _, _, .falsum => False
  | _, _, .equal _ _ => False
  | _, _, .rel _ _ => False
  | _, s, .imp φ ψ => hasQuantSigned (!s) φ ∨ hasQuantSigned s ψ
  | _, s, .all φ => s = true ∨ hasQuantSigned s φ
  | _, s, .iSup φs => ∃ i, hasQuantSigned s (φs i)
  | _, s, .iInf φs => ∃ i, hasQuantSigned s (φs i)

/-- An existential quantifier occurs in `φ`. -/
abbrev HasExistential {n : ℕ} (φ : L.BoundedFormulaω α n) : Prop := hasQuantSigned false φ

/-! ## Constructor equations -/

/--
@isnad1 id=not.0h4v.s4.5f8c7093df93 from=translated src=- shape=40729a8c vocab=6af71a05
-/
@[simp] theorem hasQuantSigned_falsum {n : ℕ} (s : Bool) :
    ¬ hasQuantSigned s (BoundedFormulaω.falsum : L.BoundedFormulaω α n) := id

/--
@isnad1 id=not.0h6v.s5.8489933156f2 from=translated src=- shape=2f1418fd vocab=e45bd0b8
-/
@[simp] theorem hasQuantSigned_equal {n : ℕ} (s : Bool) (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    ¬ hasQuantSigned s (BoundedFormulaω.equal t₁ t₂) := id

/--
@isnad1 id=not.0h7v.s5.fcddd27c0958 from=translated src=- shape=bf36179d vocab=8eacdb84
-/
@[simp] theorem hasQuantSigned_rel {n l : ℕ} (s : Bool) (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) : ¬ hasQuantSigned s (BoundedFormulaω.rel R ts) := id

/--
@isnad1 id=iff.0h6v.s5.ab3f7bb3eaa6 from=translated src=- shape=804f03b7 vocab=93345bcf
-/
@[simp] theorem hasQuantSigned_imp {n : ℕ} (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    hasQuantSigned s (φ.imp ψ) ↔ hasQuantSigned (!s) φ ∨ hasQuantSigned s ψ := Iff.rfl

/--
@isnad1 id=iff.0h5v.s5.0e31b2858976 from=translated src=- shape=60cbe6cc vocab=57b74a84
-/
@[simp] theorem hasQuantSigned_all {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α (n + 1)) :
    hasQuantSigned s φ.all ↔ s = true ∨ hasQuantSigned s φ := Iff.rfl

/--
@isnad1 id=iff.0h5v.s5.810362870101 from=translated src=- shape=efec1118 vocab=a0c7e850
-/
@[simp] theorem hasQuantSigned_iSup {n : ℕ} (s : Bool) (φs : ℕ → L.BoundedFormulaω α n) :
    hasQuantSigned s (BoundedFormulaω.iSup φs) ↔ ∃ i, hasQuantSigned s (φs i) := Iff.rfl

/--
@isnad1 id=iff.0h5v.s5.f83b7610355d from=translated src=- shape=efec1118 vocab=1cc8d6a0
-/
@[simp] theorem hasQuantSigned_iInf {n : ℕ} (s : Bool) (φs : ℕ → L.BoundedFormulaω α n) :
    hasQuantSigned s (BoundedFormulaω.iInf φs) ↔ ∃ i, hasQuantSigned s (φs i) := Iff.rfl

/-- Negation **exchanges** the two occurrence notions.
@isnad1 id=iff.0h5v.s4.461e6e0853e7 from=translated src=- shape=faef9b2f vocab=95fe1809
-/
@[simp] theorem hasQuantSigned_not {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α n) :
    hasQuantSigned s φ.not ↔ hasQuantSigned (!s) φ := by
  change hasQuantSigned (!s) φ ∨ hasQuantSigned s
    (BoundedFormulaω.falsum : L.BoundedFormulaω α n) ↔ _
  simp

/--
@isnad1 id=iff.0h6v.s5.2d39c504dd74 from=translated src=- shape=5c12b92d vocab=0168a5b5
-/
@[simp] theorem hasQuantSigned_and {n : ℕ} (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    hasQuantSigned s (φ.and ψ) ↔ hasQuantSigned s φ ∨ hasQuantSigned s ψ := by
  change hasQuantSigned s ((φ.imp ψ.not).not) ↔ _
  simp

/--
@isnad1 id=iff.0h5v.s5.5e6817abf5f7 from=translated src=- shape=60cbe6cc vocab=bfc144b7
-/
@[simp] theorem hasQuantSigned_ex {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α (n + 1)) :
    hasQuantSigned s φ.ex ↔ s = false ∨ hasQuantSigned s φ := by
  change hasQuantSigned s ((φ.not.all).not) ↔ _
  simp only [hasQuantSigned_not, hasQuantSigned_all]
  cases s <;> simp

/-! ## The exact bridge to the quantifier classes -/

/-- **The bridge.**  Being of a class is exactly the *absence* of an occurrence of the opposite
sign.
@isnad1 id=iff.0h5v.s4.9116873b5435 from=translated src=- shape=f6e85bcc vocab=2bd2bd68
-/
theorem universalSigned_iff_not_hasQuantSigned :
    ∀ {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α n),
      universalSigned s φ ↔ ¬ hasQuantSigned (!s) φ := by
  intro n s φ
  induction φ generalizing s with
  | falsum => simp
  | equal => simp
  | rel => simp
  | imp φ ψ ihφ ihψ =>
    rw [universalSigned_imp, hasQuantSigned_imp, not_or, ihφ (!s), ihψ s, Bool.not_not]
  | all φ ih =>
    rw [universalSigned_all, hasQuantSigned_all, not_or, ih s]
    cases s <;> simp
  | iSup φs ih =>
    rw [universalSigned_iSup, hasQuantSigned_iSup, not_exists]
    exact forall_congr' fun i => ih i s
  | iInf φs ih =>
    rw [universalSigned_iInf, hasQuantSigned_iInf, not_exists]
    exact forall_congr' fun i => ih i s

/--
@isnad1 id=iff.0h4v.s4.c07dfa74c845 from=translated src=- shape=50869706 vocab=0958fb3d
-/
theorem isUniversal_iff_not_hasExistential {n : ℕ} (φ : L.BoundedFormulaω α n) :
    IsUniversal φ ↔ ¬ HasExistential φ := universalSigned_iff_not_hasQuantSigned true φ

/-! ## Stability under the variable operations -/

/--
@isnad1 id=iff.0h8v.s5.ae23e8abd086 from=translated src=- shape=55abfce7 vocab=c44eaf0e
-/
theorem hasQuantSigned_relabel (s : Bool) (g : α → β ⊕ Fin n) :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α k),
      hasQuantSigned s (φ.relabel g) ↔ hasQuantSigned s φ := by
  intro k φ
  have h1 := universalSigned_iff_not_hasQuantSigned (!s) (φ.relabel g)
  have h2 := universalSigned_iff_not_hasQuantSigned (!s) φ
  rw [Bool.not_not] at h1 h2
  rw [← not_iff_not, ← h1, ← h2, universalSigned_relabel]

/--
@isnad1 id=iff.0h7v.s5.200990493867 from=translated src=- shape=769f9327 vocab=4d5ece8d
-/
theorem hasQuantSigned_subst (s : Bool) {n : ℕ} (φ : L.BoundedFormulaω α n) (tf : α → L.Term β) :
    hasQuantSigned s (φ.subst tf) ↔ hasQuantSigned s φ := by
  have h1 := universalSigned_iff_not_hasQuantSigned (!s) (φ.subst tf)
  have h2 := universalSigned_iff_not_hasQuantSigned (!s) φ
  rw [Bool.not_not] at h1 h2
  rw [← not_iff_not, ← h1, ← h2, universalSigned_subst]

/--
@isnad1 id=iff.0h4v.s5.a86eb4047fbc from=translated src=- shape=7a386d5c vocab=f47149e6
-/
theorem hasQuantSigned_openBounds (s : Bool) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty n),
      hasQuantSigned s (φ.openBounds) ↔ hasQuantSigned s φ
  | _, .falsum => Iff.rfl
  | _, .equal _ _ => Iff.rfl
  | _, .rel _ _ => Iff.rfl
  | _, .imp φ ψ => by
    change hasQuantSigned (!s) (φ.openBounds) ∨ hasQuantSigned s (ψ.openBounds) ↔ _
    rw [hasQuantSigned_openBounds _ φ, hasQuantSigned_openBounds s ψ]
    exact Iff.rfl
  | _, .all φ => by
    change s = true ∨ hasQuantSigned s ((φ.openBounds).relabel insertLastBound) ↔ _
    rw [hasQuantSigned_relabel, hasQuantSigned_openBounds s φ]
    exact Iff.rfl
  | _, .iSup φs => by
    change (∃ i, hasQuantSigned s ((φs i).openBounds)) ↔ _
    exact exists_congr fun i => hasQuantSigned_openBounds s (φs i)
  | _, .iInf φs => by
    change (∃ i, hasQuantSigned s ((φs i).openBounds)) ↔ _
    exact exists_congr fun i => hasQuantSigned_openBounds s (φs i)

end BoundedFormulaω

/-! ## Set-level occurrence: the budget sources -/

namespace Theoryω

open BoundedFormulaω

variable {L : Language.{0, 0}}

/-- A quantifier of sign `s` occurs somewhere in the set — the *source* of a separator budget. -/
def HasQuantSigned (s : Bool) (T : Set L.Sentenceω) : Prop := ∃ σ ∈ T, hasQuantSigned s σ

/-- An existential quantifier occurs somewhere in `T`. -/
private abbrev HasExistential (T : Set L.Sentenceω) : Prop := HasQuantSigned false T

variable {s : Bool} {T T' : Set L.Sentenceω} {σ : L.Sentenceω}

/--
@isnad1 id=hasquant.2h4v.s4.439a054d9db1 from=translated src=- shape=cbc3b124 vocab=336337c3
-/
theorem hasQuantSigned_mono (h : T ⊆ T') (hT : HasQuantSigned s T) : HasQuantSigned s T' := by
  obtain ⟨σ, hσ, hq⟩ := hT
  exact ⟨σ, h hσ, hq⟩

/--
@isnad1 id=hasquant.2h4v.s5.86d15885b015 from=translated src=- shape=4f8babf2 vocab=6c890396
-/
theorem hasQuantSigned_of_mem (hmem : σ ∈ T) (hq : hasQuantSigned s σ) : HasQuantSigned s T :=
  ⟨σ, hmem, hq⟩

/--
@isnad1 id=iff.0h4v.s5.43d334021d28 from=translated src=- shape=2fb47744 vocab=584c2be2
-/
@[simp] theorem hasQuantSigned_insert :
    HasQuantSigned s (insert σ T) ↔ hasQuantSigned s σ ∨ HasQuantSigned s T := by
  constructor
  · rintro ⟨ρ, hρ, hq⟩
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · exact Or.inl hq
    · exact Or.inr ⟨ρ, hρ, hq⟩
  · rintro (hq | ⟨ρ, hρ, hq⟩)
    · exact ⟨σ, Set.mem_insert _ _, hq⟩
    · exact ⟨ρ, Set.mem_insert_of_mem _ hρ, hq⟩

/-- **Non-growth**: inserting a sentence whose `s`-occurrences are already licensed does not enlarge
the budget.  This is the shape every consistency-property branch step needs.
@isnad1 id=iff.1h4v.s5.b05ffdb66ed5 from=translated src=- shape=6c679a56 vocab=584c2be2
-/
theorem hasQuantSigned_insert_of_le (h : hasQuantSigned s σ → HasQuantSigned s T) :
    HasQuantSigned s (insert σ T) ↔ HasQuantSigned s T := by
  rw [hasQuantSigned_insert]
  exact ⟨fun hq => hq.elim h id, Or.inr⟩

end Theoryω

end FirstOrder.Language
