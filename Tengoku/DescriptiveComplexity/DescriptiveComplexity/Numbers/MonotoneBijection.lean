/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Tengoku

/-!
# The monotone bijection between two sets of the same size

A threshold in the unary representation of `DescriptiveComplexity.Numbers.Unary` is
the size of a marked set, and “this set has exactly that size” is certified by
a bijection with the marked set. A *count* of certificates needs the certificate
to be unique, and a bijection is not: two sets of size `k` have `k!` of them.
On a linearly ordered finite universe exactly one of them is monotone, and that
is the one a counting kernel guesses.

* `DescriptiveComplexity.MonoBij K S F`: the binary relation `F` is the graph of a
  monotone bijection from `K` onto `S`, as four first-order conditions;
* `DescriptiveComplexity.MonoBij.ncard_eq`: such a graph makes the two sets the same
  size;
* `DescriptiveComplexity.exists_monoBij`, `DescriptiveComplexity.MonoBij.ext`: on a finite
  linear order, two sets of the same size have one, and only one.
-/

namespace DescriptiveComplexity

variable {A : Type}

/-- The relation `F` is the graph of a monotone bijection from `K` onto `S`: it
relates members of `K` to members of `S`, it is total on `K` and onto `S`, and
it preserves and reflects the order. The last condition makes it functional
and injective as well. -/
def MonoBij [LE A] (K S : A → Prop) (F : A → A → Prop) : Prop :=
  (∀ x y, F x y → K x ∧ S y) ∧ (∀ x, K x → ∃ y, F x y) ∧ (∀ y, S y → ∃ x, F x y) ∧
    ∀ x x' y y', F x y → F x' y' → (x ≤ x' ↔ y ≤ y')

/-- The graph of an order isomorphism between two sets is a monotone
bijection.
@isnad1 id=monobij.0h4v.s7.f506b0c36de4 from=translated src=- shape=1a1c65a0 vocab=7882a155
-/
theorem monoBij_of_orderIso [LE A] {K S : A → Prop} (e : {x // K x} ≃o {y // S y}) :
    MonoBij K S fun x y => ∃ hx : K x, (e ⟨x, hx⟩).1 = y := by
  refine ⟨?_, fun x hx => ⟨_, hx, rfl⟩, fun y hy => ?_, ?_⟩
  · rintro x y ⟨hx, rfl⟩
    exact ⟨hx, (e ⟨x, hx⟩).2⟩
  · refine ⟨(e.symm ⟨y, hy⟩).1, (e.symm ⟨y, hy⟩).2, ?_⟩
    rw [Subtype.coe_eta, e.apply_symm_apply]
  · rintro x x' y y' ⟨hx, rfl⟩ ⟨hx', rfl⟩
    exact (e.map_rel_iff (a := ⟨x, hx⟩) (b := ⟨x', hx'⟩)).symm

section Linear

variable [LinearOrder A] {K S : A → Prop} {F G : A → A → Prop}

/-- A monotone bijection is functional.
@isnad1 id=eq.1h9v.s5.39f294a9169d from=translated src=- shape=760f0ce3 vocab=83fcabe1
-/
theorem MonoBij.functional (h : MonoBij K S F) {x y y' : A} (hy : F x y) (hy' : F x y') :
    y = y' :=
  le_antisymm ((h.2.2.2 x x y y' hy hy').mp le_rfl) ((h.2.2.2 x x y' y hy' hy).mp le_rfl)

/-- A monotone bijection is injective.
@isnad1 id=eq.1h9v.s5.bb0e9046b115 from=translated src=- shape=b5631505 vocab=83fcabe1
-/
theorem MonoBij.injective (h : MonoBij K S F) {x x' y : A} (hx : F x y) (hx' : F x' y) :
    x = x' :=
  le_antisymm ((h.2.2.2 x x' y y hx hx').mpr le_rfl) ((h.2.2.2 x' x y y hx' hx).mpr le_rfl)

/-- The order isomorphism a monotone bijection is the graph of. -/
noncomputable def MonoBij.orderIso (h : MonoBij K S F) : {x // K x} ≃o {y // S y} where
  toFun x := ⟨(h.2.1 x.1 x.2).choose, (h.1 _ _ (h.2.1 x.1 x.2).choose_spec).2⟩
  invFun y := ⟨(h.2.2.1 y.1 y.2).choose, (h.1 _ _ (h.2.2.1 y.1 y.2).choose_spec).1⟩
  left_inv x := Subtype.ext
    (h.injective (h.2.2.1 _ (h.1 _ _ (h.2.1 x.1 x.2).choose_spec).2).choose_spec
      (h.2.1 x.1 x.2).choose_spec)
  right_inv y := Subtype.ext
    (h.functional (h.2.1 _ (h.1 _ _ (h.2.2.1 y.1 y.2).choose_spec).1).choose_spec
      (h.2.2.1 y.1 y.2).choose_spec)
  map_rel_iff' {x x'} :=
    (h.2.2.2 _ _ _ _ (h.2.1 x.1 x.2).choose_spec (h.2.1 x'.1 x'.2).choose_spec).symm

/--
@isnad1 id=var.1h5v.s7.e5e14107ef8b from=translated src=- shape=7d74dede vocab=f05908fa
-/
theorem MonoBij.rel_orderIso (h : MonoBij K S F) (x : {x // K x}) :
    F x.1 (h.orderIso x).1 :=
  (h.2.1 x.1 x.2).choose_spec

/-- A monotone bijection is the graph of its order isomorphism.
@isnad1 id=iff.1h6v.s7.b08844b35546 from=translated src=- shape=585d04c6 vocab=9c6f6fd6
-/
theorem MonoBij.iff_orderIso (h : MonoBij K S F) (x y : A) :
    F x y ↔ ∃ hx : K x, (h.orderIso ⟨x, hx⟩).1 = y := by
  constructor
  · intro hxy
    exact ⟨(h.1 x y hxy).1, h.functional (h.rel_orderIso ⟨x, (h.1 x y hxy).1⟩) hxy⟩
  · rintro ⟨hx, rfl⟩
    exact h.rel_orderIso ⟨x, hx⟩

/-- Two sets related by a monotone bijection have the same size.
@isnad1 id=eq.1h4v.s5.f72acc982dc5 from=translated src=- shape=3bd35368 vocab=bcc6e604
-/
theorem MonoBij.ncard_eq (h : MonoBij K S F) : {y | S y}.ncard = {x | K x}.ncard :=
  (Nat.card_coe_set_eq {y | S y}).symm.trans
    ((Nat.card_congr h.orderIso.toEquiv.symm).trans (Nat.card_coe_set_eq {x | K x}))

variable [Finite A]

/-- **A monotone bijection between two sets is unique.**
@isnad1 id=eq.2h5v.s6.4ce50851453d from=translated src=- shape=696d6185 vocab=d8bf49eb
-/
theorem MonoBij.ext (h : MonoBij K S F) (h' : MonoBij K S G) : F = G := by
  funext x y
  rw [h.iff_orderIso, h'.iff_orderIso, Subsingleton.elim h.orderIso h'.orderIso]

/-- **Two sets of the same size have a monotone bijection.**
@isnad1 id=ex.1h3v.s6.b9012bf48fb3 from=translated src=- shape=9f5e401e vocab=f48ec51b
-/
theorem exists_monoBij (hcard : {y | S y}.ncard = {x | K x}.ncard) :
    ∃ F : A → A → Prop, MonoBij K S F := by
  classical
  have := Fintype.ofFinite {x // K x}
  have := Fintype.ofFinite {y // S y}
  have hc : Fintype.card {y // S y} = Fintype.card {x // K x} := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact (Nat.card_coe_set_eq {y | S y}).trans
      (hcard.trans (Nat.card_coe_set_eq {x | K x}).symm)
  exact ⟨_, monoBij_of_orderIso
    ((monoEquivOfFin {x // K x} rfl).symm.trans (monoEquivOfFin {y // S y} hc))⟩

end Linear

end DescriptiveComplexity
