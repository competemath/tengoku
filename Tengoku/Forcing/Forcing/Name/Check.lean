/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Seed.Order.PFilter
import Tengoku.Forcing.Forcing.Name.Valuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Check names

The check name `x̌` embeds the ambient universe into names: every branch is tagged with the
distinguished element `⊤`, and valuation undoes the embedding. The `Set P` valuation API
exposes the exact prices:

* constructing a check name needs only a distinguished element (`[Top P]` — no order);
* evaluating it correctly needs only `⊤ ∈ S` (`val_check_equiv`, `zval_check`);
* `[Preorder P] [OrderTop P]` plus the filter laws supply that membership automatically
  (`Order.PFilter.top_mem`), so the forcing-filter statement is a corollary
  (`zval_check_pfilter`).

The intensional law is a `PSet.Equiv`, the extensional law an honest `ZFSet` equality.
On-the-nose `PSet` equality of `(check x).val S` with `x` is not expected in general — the
index type of the valuation is a subtype over a trivially-true condition.

## Main definitions

* `Forcing.PName.check`: the check name of a `PSet`.
* `Forcing.PName.checkZF`: the check name of a `ZFSet`, via `Quotient.out`.

## Main results

* `Forcing.PName.val_check_equiv`, `Forcing.PName.zval_check`: valuation undoes check, under
  exactly `⊤ ∈ S`.
* `Forcing.PName.zval_check_pfilter`, `Forcing.PName.zval_checkZF_pfilter`: the filter
  corollaries.
-/

universe u

namespace Forcing.PName

variable {P : Type u}

/-- The check name `x̌`: every branch tagged with the distinguished element. Needs only
`[Top P]` — no order.-/
def check [Top P] : PSet.{u} → PName P
  | .mk α A => .mk α (fun a ↦ check (A a)) fun _ ↦ (⊤ : P)

/--
@isnad1 id=eq.0h3v.s5.203667f15f1a from=translated src=- shape=df1aa195 vocab=3ac1af6c
-/
@[simp] theorem check_mk [Top P] (α : Type u) (A : α → PSet.{u}) :
    (check (.mk α A) : PName P) = mk α (fun a ↦ check (A a)) fun _ ↦ (⊤ : P) :=
  rfl

/-- **Valuation undoes check**, intensionally: along any condition set containing `⊤`, the
check name of `x` values to a `PSet` extensionally equal to `x`.
@isnad1 id=equiv.1h3v.s4.2da2bdf50b80 from=translated src=- shape=ed124ac1 vocab=a7d4f38f
-/
theorem val_check_equiv [Top P] {S : Set P} (hS : (⊤ : P) ∈ S) (x : PSet.{u}) :
    PSet.Equiv ((check x : PName P).val S) x := by
  induction x with
  | mk α A IH =>
    exact ⟨fun i ↦ ⟨i.1, IH i.1⟩, fun a ↦ ⟨⟨a, hS⟩, IH a⟩⟩

/-- **Valuation undoes check**, extensionally: the honest equality, at `ZFSet`.
@isnad1 id=eq.1h3v.s5.424c946353df from=translated src=- shape=61a5c072 vocab=a162307d
-/
theorem zval_check [Top P] {S : Set P} (hS : (⊤ : P) ∈ S) (x : PSet.{u}) :
    zval S (check x) = ZFSet.mk x :=
  ZFSet.sound (val_check_equiv hS x)

/-- The forcing-filter corollary: the order and the filter laws supply `⊤ ∈ G` automatically
(`Order.PFilter.top_mem`).
@isnad1 id=eq.0h3v.s5.9e6af32d3bf6 from=translated src=- shape=c6957ecc vocab=f94acd4c
-/
theorem zval_check_pfilter [Preorder P] [OrderTop P] (G : Order.PFilter P) (x : PSet.{u}) :
    zval (G : Set P) (check x) = ZFSet.mk x :=
  zval_check G.top_mem x

/-- Check from the quotient side, via `Quotient.out`.-/
noncomputable def checkZF [Top P] (x : ZFSet.{u}) : PName P :=
  check x.out

/-- Valuation undoes `checkZF`, under exactly `⊤ ∈ S`.
@isnad1 id=eq.1h3v.s4.8ea316ce78c0 from=translated src=- shape=e6217ad1 vocab=4d0ec712
-/
theorem zval_checkZF [Top P] {S : Set P} (hS : (⊤ : P) ∈ S) (x : ZFSet.{u}) :
    zval S (checkZF x) = x := by
  rw [checkZF, zval_check hS, ZFSet.mk_out]

/-- The forcing-filter corollary for `checkZF`.
@isnad1 id=eq.0h3v.s5.c8c26a51e6c5 from=translated src=- shape=4242fba8 vocab=4c1759e0
-/
theorem zval_checkZF_pfilter [Preorder P] [OrderTop P] (G : Order.PFilter P) (x : ZFSet.{u}) :
    zval (G : Set P) (checkZF x) = x :=
  zval_checkZF G.top_mem x

end Forcing.PName
