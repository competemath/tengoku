/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Tengoku.LeanPool.LeanPool.InfinitaryLogic.Lomega1omega.Operations
/-!
# The universal and existential quantifier classes (issue #15, Unit 0)

The `∀₁`/`∃₁` classes of Harrison-Trainor–Kretschmer §2 (their hierarchy for counting quantifier
alternations in infinitary formulas), realized as a **signed quantifier traversal** on the existing
syntax:

* atomic formulas lie in **both** classes (they have no quantifier);
* an antecedent **flips** the class — `¬φ` is universal exactly when `φ` is existential;
* countable conjunctions and disjunctions **preserve** the class and are *not* counted as
  quantifiers (the source's clause 3, which is what distinguishes `∀n`/`∃n` from `Πn`/`Σn`);
* `∀` is **universal only**: in this syntax `ex φ = (φ.not.all).not`, so an existential quantifier
  *is* an `all` occurring negatively.

One `Bool`-parameterised recursion carries both classes, so their mutual dependence through negation
is definitional rather than a second induction — the same design as `Lomega1omega/Polarity.lean`,
and, as there, **no negation-normal form is constructed anywhere**.

This module is deliberately neutral: it depends only on the syntax layer and is intended to be
reused by any preservation theorem (issue #15's interpolation and relative preservation, and issue
#16's end extensions), not to live inside the interpolation development.
-/

@[expose] public section

namespace FirstOrder.Language

namespace BoundedFormulaω

variable {L : Language.{0, 0}} {α β : Type}

/-- **The signed quantifier class.**  `universalSigned true φ` says `φ` is *universal* (`∀₁`) and
`universalSigned false φ` says `φ` is *existential* (`∃₁`).  An antecedent flips the sign, the
countable connectives preserve it, and `all` is admissible only at the universal sign. -/
def universalSigned : ∀ {n : ℕ}, Bool → L.BoundedFormulaω α n → Prop
  | _, _, .falsum => True
  | _, _, .equal _ _ => True
  | _, _, .rel _ _ => True
  | _, s, .imp φ ψ => universalSigned (!s) φ ∧ universalSigned s ψ
  | _, s, .all φ => s = true ∧ universalSigned s φ
  | _, s, .iSup φs => ∀ i, universalSigned s (φs i)
  | _, s, .iInf φs => ∀ i, universalSigned s (φs i)

/-- `φ` is **universal** (`∀₁`): every quantifier occurrence is a positive `∀`. -/
abbrev IsUniversal {n : ℕ} (φ : L.BoundedFormulaω α n) : Prop := universalSigned true φ

/-! ## Constructor equations -/

/--
@isnad1 id=universa.0h4v.s4.5f5f36a29b68 from=translated src=- shape=74a0f4d5 vocab=eec0a367
-/
@[simp] theorem universalSigned_falsum {n : ℕ} (s : Bool) :
    universalSigned s (BoundedFormulaω.falsum : L.BoundedFormulaω α n) := trivial

/--
@isnad1 id=universa.0h6v.s5.d47253e820bf from=translated src=- shape=d4a0c46e vocab=81f07333
-/
@[simp] theorem universalSigned_equal {n : ℕ} (s : Bool) (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    universalSigned s (BoundedFormulaω.equal t₁ t₂) := trivial

/--
@isnad1 id=universa.0h7v.s5.afa2c5d41626 from=translated src=- shape=e6297459 vocab=5cae38ab
-/
@[simp] theorem universalSigned_rel {n l : ℕ} (s : Bool) (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) :
    universalSigned s (BoundedFormulaω.rel R ts) := trivial

/--
@isnad1 id=iff.0h6v.s5.0788d8be748b from=translated src=- shape=804f03b7 vocab=fcffde2e
-/
@[simp] theorem universalSigned_imp {n : ℕ} (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    universalSigned s (φ.imp ψ) ↔ universalSigned (!s) φ ∧ universalSigned s ψ := Iff.rfl

/--
@isnad1 id=iff.0h5v.s5.17a869c2b559 from=translated src=- shape=60cbe6cc vocab=89a97a47
-/
@[simp] theorem universalSigned_all {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α (n + 1)) :
    universalSigned s φ.all ↔ s = true ∧ universalSigned s φ := Iff.rfl

/--
@isnad1 id=iff.0h5v.s5.b1e0ef05e8c3 from=translated src=- shape=340d897c vocab=59416c6a
-/
@[simp] theorem universalSigned_iSup {n : ℕ} (s : Bool) (φs : ℕ → L.BoundedFormulaω α n) :
    universalSigned s (BoundedFormulaω.iSup φs) ↔ ∀ i, universalSigned s (φs i) := Iff.rfl

/--
@isnad1 id=iff.0h5v.s5.3de4da2b3312 from=translated src=- shape=340d897c vocab=a718f613
-/
@[simp] theorem universalSigned_iInf {n : ℕ} (s : Bool) (φs : ℕ → L.BoundedFormulaω α n) :
    universalSigned s (BoundedFormulaω.iInf φs) ↔ ∀ i, universalSigned s (φs i) := Iff.rfl

/-! ## The acceptance equations -/

/-! ## The derived connectives -/

/-! ## Stability under the variable operations -/

private theorem universalSigned_castLE (s : Bool) :
    ∀ {m n : ℕ} (h : m ≤ n) (φ : L.BoundedFormulaω α m),
      universalSigned s (φ.castLE h) ↔ universalSigned s φ
  | _, _, _, .falsum => Iff.rfl
  | _, _, _, .equal _ _ => Iff.rfl
  | _, _, _, .rel _ _ => Iff.rfl
  | _, _, h, .imp φ ψ => by
    change universalSigned (!s) (φ.castLE h) ∧ universalSigned s (ψ.castLE h) ↔ _
    rw [universalSigned_castLE _ h φ, universalSigned_castLE s h ψ]
    exact Iff.rfl
  | _, _, h, .all φ => by
    change s = true ∧ universalSigned s (φ.castLE (Nat.succ_le_succ h)) ↔ _
    rw [universalSigned_castLE s (Nat.succ_le_succ h) φ]
    exact Iff.rfl
  | _, _, h, .iSup φs => by
    change (∀ i, universalSigned s ((φs i).castLE h)) ↔ _
    exact forall_congr' fun i => universalSigned_castLE s h (φs i)
  | _, _, h, .iInf φs => by
    change (∀ i, universalSigned s ((φs i).castLE h)) ↔ _
    exact forall_congr' fun i => universalSigned_castLE s h (φs i)

/-- **Quantifier class is invariant under language maps.**  `mapLanguage` rewrites terms and symbol
tags only; every quantifier node is preserved, so the signed universal class is exact.
@isnad1 id=iff.0h7v.s5.acc4c5ff5a23 from=translated src=- shape=a28aa626 vocab=eb1afaea
-/
theorem universalSigned_mapLanguage {L' : Language.{0, 0}} (g : L →ᴸ L') (s : Bool) :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α k),
      universalSigned s (φ.mapLanguage g) ↔ universalSigned s φ := by
  intro k φ
  induction φ generalizing s with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    change universalSigned (!s) _ ∧ universalSigned s _ ↔ _
    exact and_congr (ihφ (!s)) (ihψ s)
  | all φ ih =>
    change s = true ∧ universalSigned s _ ↔ _
    exact and_congr_right fun _ => ih s
  | iSup φs ih =>
    change (∀ i, universalSigned s _) ↔ _
    exact forall_congr' fun i => ih i s
  | iInf φs ih =>
    change (∀ i, universalSigned s _) ↔ _
    exact forall_congr' fun i => ih i s

/--
@isnad1 id=iff.0h8v.s5.3b40f7c5adc9 from=translated src=- shape=55abfce7 vocab=0dc476b1
-/
theorem universalSigned_relabel (s : Bool) (g : α → β ⊕ Fin n) :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α k),
      universalSigned s (φ.relabel g) ↔ universalSigned s φ := by
  intro k φ
  induction φ generalizing s with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    change universalSigned (!s) _ ∧ universalSigned s _ ↔ _
    exact and_congr (ihφ (!s)) (ihψ s)
  | all φ ih =>
    change s = true ∧ universalSigned s _ ↔ _
    rw [universalSigned_castLE]
    exact and_congr_right fun _ => ih s
  | iSup φs ih =>
    change (∀ i, universalSigned s _) ↔ _
    exact forall_congr' fun i => ih i s
  | iInf φs ih =>
    change (∀ i, universalSigned s _) ↔ _
    exact forall_congr' fun i => ih i s

/--
@isnad1 id=iff.0h7v.s5.fbb9289bd2a7 from=translated src=- shape=769f9327 vocab=cbdbf648
-/
theorem universalSigned_subst (s : Bool) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω α n) (tf : α → L.Term β),
      universalSigned s (φ.subst tf) ↔ universalSigned s φ
  | _, .falsum, _ => Iff.rfl
  | _, .equal _ _, _ => Iff.rfl
  | _, .rel _ _, _ => Iff.rfl
  | _, .imp φ ψ, tf => by
    change universalSigned (!s) (φ.subst tf) ∧ universalSigned s (ψ.subst tf) ↔ _
    rw [universalSigned_subst _ φ tf, universalSigned_subst s ψ tf]
    exact Iff.rfl
  | _, .all φ, tf => by
    change s = true ∧ universalSigned s (φ.subst tf) ↔ _
    rw [universalSigned_subst s φ tf]
    exact Iff.rfl
  | _, .iSup φs, tf => by
    change (∀ i, universalSigned s ((φs i).subst tf)) ↔ _
    exact forall_congr' fun i => universalSigned_subst s (φs i) tf
  | _, .iInf φs, tf => by
    change (∀ i, universalSigned s ((φs i).subst tf)) ↔ _
    exact forall_congr' fun i => universalSigned_subst s (φs i) tf

end BoundedFormulaω

end FirstOrder.Language
