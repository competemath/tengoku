/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.SetTheory.GoodsteinHereditaryExponentBorrow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Hereditary natural-number encoding

This file constructs a genuine hereditary base representation by repeated quotient and remainder.
-/

namespace SandronesLibrary.SetTheory.Googology

open SandronesLibrary.SetTheory.Ordinal

noncomputable section

/-- Horner hereditary encoding: recursively encode the quotient, multiply it by the base, then add
the remainder digit.-/
def hereditaryNatEncode (base : ℕ) (hbase : 2 ≤ base) (n : ℕ) : HereditaryBaseExpr :=
  Nat.strongRec (motive := fun _ => HereditaryBaseExpr) (fun n rec =>
    if hn : n = 0 then .zero else
      .add (.mul (.basePow (.digit 1))
        (rec (n / base) (Nat.div_lt_self (Nat.pos_of_ne_zero hn)
          (lt_of_lt_of_le Nat.one_lt_two hbase)))) (.digit (n % base))) n

/--
@isnad1 id=eq.1h1v.s4.6c7eb2aba074 from=translated src=- shape=76292773 vocab=760db1a9
-/
theorem hereditaryNatEncode_zero (base : ℕ) (hbase : 2 ≤ base) :
    hereditaryNatEncode base hbase 0 = .zero := by
  rw [hereditaryNatEncode, Nat.strongRec_eq]
  simp

/--
@isnad1 id=eq.2h2v.s5.611817b3255d from=translated src=- shape=97032ad5 vocab=69b1a92e
-/
theorem hereditaryNatEncode_of_pos (base : ℕ) (hbase : 2 ≤ base)
    {n : ℕ} (hn : 0 < n) :
    hereditaryNatEncode base hbase n =
      .add (.mul (.basePow (.digit 1))
        (hereditaryNatEncode base hbase (n / base))) (.digit (n % base)) := by
  rw [hereditaryNatEncode, Nat.strongRec_eq]
  simp only [dite_eq_right (Nat.ne_of_gt hn)]
  rfl

/--
> **Entry**: settheory.googology.hereditary-natural-encoding
> **一句话**: 对任意 `base≥2` 和自然数 `n`，商余递归构造合法遗传基表达式，且其求值精确等于 `n`。
> **依赖**: `settheory.googology.hereditary-base`
> **mathlib**: `Nat.strongRec`、`Nat.div_add_mod`
@isnad1 id=and.1h2v.s4.462479ea50d8 from=translated src=- shape=e7d4ab09 vocab=9661fb89
-/
theorem hereditaryNatEncode_valid_eval (base : ℕ) (hbase : 2 ≤ base) :
    ∀ n, (hereditaryNatEncode base hbase n).Valid base ∧
      (hereditaryNatEncode base hbase n).eval base = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain rfl | hn := n.eq_zero_or_pos
      · simp [hereditaryNatEncode_zero, HereditaryBaseExpr.Valid,
          HereditaryBaseExpr.eval]
      · rw [hereditaryNatEncode_of_pos base hbase hn]
        have hdiv : n / base < n := Nat.div_lt_self hn
          (lt_of_lt_of_le Nat.one_lt_two hbase)
        have hrec := ih (n / base) hdiv
        constructor
        · exact ⟨⟨lt_of_lt_of_le Nat.one_lt_two hbase, hrec.1⟩,
            Nat.mod_lt n (by omega)⟩
        · simp only [HereditaryBaseExpr.eval, hrec.2, pow_one]
          rw [Nat.div_add_mod]

/-- A mechanically available strict ordinal ceiling for the encoded tree.  It contains no
comparison information about different inputs and is insufficient for a general borrow lemma.-/
def hereditaryNatEncodeOmegaCeiling (base : ℕ) (hbase : 2 ≤ base) (n : ℕ) : Ordinal :=
  Order.succ (hereditaryNatEncode base hbase n).omegaValue

/--
@isnad1 id=lt.1h2v.s4.18b3ead5946f from=translated src=- shape=1b4d2069 vocab=40c60552
-/
theorem hereditaryNatEncode_omega_lt_ceiling (base : ℕ) (hbase : 2 ≤ base) (n : ℕ) :
    (hereditaryNatEncode base hbase n).omegaValue <
      hereditaryNatEncodeOmegaCeiling base hbase n :=
  Order.lt_succ _

end
end SandronesLibrary.SetTheory.Googology
