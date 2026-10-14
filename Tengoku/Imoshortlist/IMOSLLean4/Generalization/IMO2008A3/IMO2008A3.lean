/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku.Imoshortlist.IMOSLLean4.Main.IMO2008.A3
public import Tengoku

/-!
# IMO 2008 A3 (Generalization)

A *Spanish couple* on an ordered set $S$ is a pair of strictly increasing functions
  $(f, g)$ from $S$ to itself such that for any $x ∈ S$,
$$ f(g(g(x))) < g(f(x)). $$
Determine all **well-ordered sets** $S$ such that there exists a Spanish couple on $S$.

### Answer

Such sets are precisely those order-isomorphic to $T × ℕ × ℕ$ with lexicographical order,
  for some well-ordered set $T$.
In terms of ordinals, this holds if and only if the ordinal number of $S$ is of
  the form $ω^2 o$ for some ordinal $o$, where $ω$ is the ordinal number of $ℕ$.

### Implementation details

We define an ordered set $S$ to be `good` if there exists a Spanish couple on $S$.
The theorem `good.conjOrderIso_iff` shows that `good` is preserved under order isomorphisms.
We define `isGoodOrdinal` to be the quotient predicate of `good` on ordinals.
We state the main result in terms of well-ordered sets.
For the ordinal version, see `isGoodOrdinal.iff_omega0_sq_dvd`.

The construction of Spanish couple on lexicographical product is implemented via
  `SpanishCouple.prodLexLeft`, while the construction of Spanish couple on an upper subset
  is implemented via `SpanishCouple.sumLexRestrictRight`, where we view the whole set as a
  disjoint union `α ⊕ₗ β` with the subset being `β`.
-/

@[expose] public section

namespace IMOSL
namespace IMO2008A3

/-! ### Miscelanneous lemmas on ordered sets -/

/-- `StrictMono` transfers through an order isomorphism.
@isnad1 id=strictmo.1h4v.s6.f2802067110c from=translated src=- shape=31d328a2 vocab=c5a73815
-/
theorem StrictMono_conjOrderIso [Preorder α] [Preorder β]
    {f : α → α} (hf : StrictMono f) (e : α ≃o β) :
    StrictMono (e.toEquiv.conj f) :=
  λ _ _ h ↦ e.strictMono (hf (e.symm.strictMono h))

/-- TODO: Remove this instance once `mathlib` variant appears. -/
instance [LT α] [WellFoundedLT α] [LT β] [WellFoundedLT β] : WellFoundedLT (α ⊕ₗ β) :=
  ⟨Sum.lex_wf wellFounded_lt wellFounded_lt⟩

section

variable [LinearOrder α] [WellFoundedLT α] [LinearOrder β] [WellFoundedLT β]
  {f : α ⊕ₗ β → α ⊕ₗ β} (hf : StrictMono f)
include hf

/-- Given a strictly increasing function `f : α ⊕ₗ β → α ⊕ₗ β`, where `α` and `β`
  are well-ordered, the image `f(b) ∈ β` for any `b ∈ β`.
@isnad1 id=eq.1h4v.s7.89722fb049ac from=translated src=- shape=cce0dbf1 vocab=11c84e78
-/
theorem sum_isRight_of_strictMono (b : β) : Sum.isRight (ofLex.conj f (Sum.inr b)) :=
  match h : ofLex.conj f (Sum.inr b) with
  | Sum.inl _ => absurd ((hf.id_le _).trans_eq h) Sum.lex_inr_inl
  | Sum.inr _ => rfl

/-- Given a strictly increasing function `f : α ⊕ₗ β → α ⊕ₗ β`, where `α` and `β`
  are well-ordered, `f` restricts to a function `g : β → β`. -/
def sum_getRight_of_strictMono (b : β) : β :=
  Sum.getRight _ (sum_isRight_of_strictMono hf b)

/-- Given a strictly increasing function `f : α ⊕ₗ β → α ⊕ₗ β`, where `α` and `β`
  are well-ordered, `g` given above is indeed a restriction on `f`.
@isnad1 id=eq.1h4v.s7.601feede67b8 from=translated src=- shape=9cffd8cb vocab=dafd6949
-/
theorem sum_getRight_of_strictMono_apply :
    toLex (Sum.inr (sum_getRight_of_strictMono hf b)) = f (toLex (Sum.inr b)) :=
  Sum.inr_getRight _ _

/-- Given a strictly increasing function `f : α ⊕ₗ β → α ⊕ₗ β`, where `α` and `β`
  are well-ordered, the restriction to `β` is also strictly increasing.
@isnad1 id=strictmo.1h3v.s7.a272288256bb from=translated src=- shape=f4a700e5 vocab=0bbc32ba
-/
theorem sum_getRight_of_strictMono_strictMono :
    StrictMono (sum_getRight_of_strictMono hf) :=
  λ _ _ h ↦ by simpa only [← Sum.Lex.inr_lt_inr_iff (α := α) (β := β),
    sum_getRight_of_strictMono_apply] using hf (Sum.Lex.inr_lt_inr_iff.mpr h)

end

/-! ### More properties of Spanish couples -/

namespace SpanishCouple

/-- Given a Spanish couple `f` on `α` and an order isomorphism `e : α ≃o β`,
  make a Spanish couple on `β` by conjugating with `e`. -/
def conjOrderIso [Preorder α] [Preorder β] (X : SpanishCouple α) (e : α ≃o β) :
    SpanishCouple β where
  f := e.toEquiv.conj X.f
  f_strictMono := StrictMono_conjOrderIso X.f_strictMono e
  g := e.toEquiv.conj X.g
  g_strictMono := StrictMono_conjOrderIso X.g_strictMono e
  spec x := by simpa using X.spec (e.symm x)

/-- Given a Spanish couple `(f, g)` on `β`, make a Spanish couple `(f', g')` on `α ×ₗ β`,
  defined by `f'(a, b) = (a, f(b))` and `g'(a, b) = (a, g(b))`. -/
def prodLexLeft (α) [Preorder α] [Preorder β] (X : SpanishCouple β) :
    SpanishCouple (α ×ₗ β) where
  f := toLex.conj (Prod.map id X.f)
  f_strictMono := ProdMapLex_strictMono strictMono_id X.f_strictMono
  g := toLex.conj (Prod.map id X.g)
  g_strictMono := ProdMapLex_strictMono strictMono_id X.g_strictMono
  spec := Lex.rec λ p ↦ Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, X.spec p.2⟩)

/-- Given a spanish couple on `α ⊕ₗ β`, where `α` and `β` are well-ordered sets,
  make a Spanish couple on `β` by restricting into the `β` coordinate. -/
def sumLexRestrictRight [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] (X : SpanishCouple (α ⊕ₗ β)) :
    SpanishCouple β where
  f := sum_getRight_of_strictMono X.f_strictMono
  f_strictMono := sum_getRight_of_strictMono_strictMono _
  g := sum_getRight_of_strictMono X.g_strictMono
  g_strictMono := sum_getRight_of_strictMono_strictMono _
  spec x := (Sum.Lex.inr_lt_inr_iff (α := α)).mp <| by
    simpa only [sum_getRight_of_strictMono_apply] using X.spec (toLex (Sum.inr x))

end SpanishCouple

/-! ### The `good` predicate on pre-orders -/

/-- A pre-order `α` is called `good` if there is a Spanish couple on `α`. -/
def good (α) [Preorder α] := Nonempty (SpanishCouple α)

/-- `PUnit` is not good.
@isnad1 id=not.0h0v.s3.3872959a1c53 from=translated src=- shape=87ceb31f vocab=758e499e
-/
theorem PUnit_is_not_good : ¬good PUnit :=
  λ ⟨X⟩ ↦ X.spec default

/-- `Nat` is not good.
@isnad1 id=not.0h0v.s2.18fdd5ec5776 from=translated src=- shape=87ceb31f vocab=37e8376e
-/
theorem Nat_is_not_good : ¬good ℕ :=
  λ ⟨X⟩ ↦ final_solution_part1.elim X

/-- `Nat ×ₗ Nat` is good.
@isnad1 id=good.0h0v.s3.c495f50d4b38 from=translated src=- shape=41e3855d vocab=ff4bc4cf
-/
theorem NatNatLex_is_good : good (ℕ ×ₗ ℕ) :=
  ⟨final_solution_part2⟩

namespace good

/-- If `α` is good and `α ≃o β`, then `β` is good.
@isnad1 id=good.1h3v.s4.d1dd2bb70b13 from=translated src=- shape=8157dbee vocab=61eaebe6
-/
theorem conjOrderIso [Preorder α] [Preorder β] (hα : good α) (e : α ≃o β) : good β :=
  hα.elim λ X ↦ ⟨X.conjOrderIso e⟩

/-- If `α ≃o β`, then `α` is good if and only if `β` is good.
@isnad1 id=iff.0h3v.s4.88f4b7107bdb from=translated src=- shape=b720df5a vocab=61eaebe6
-/
theorem conjOrderIso_iff [Preorder α] [Preorder β] (e : α ≃o β) : good α ↔ good β :=
  ⟨λ hα ↦ hα.conjOrderIso e, λ hβ ↦ hβ.conjOrderIso e.symm⟩

/-- If `β` is good, then `α ×ₗ β` is good.
@isnad1 id=good.1h2v.s4.9f9759c5378e from=translated src=- shape=98fbbc16 vocab=c3a6b248
-/
theorem prodLexLeft (α) [Preorder α] [Preorder β] (hβ : good β) : good (α ×ₗ β) :=
  hβ.elim λ X ↦ ⟨X.prodLexLeft α⟩

/-- If `α ⊕ₗ β` is good, then `β` is good.
@isnad1 id=good.1h2v.s6.18f62c492db7 from=translated src=- shape=1d0dc7fe vocab=4f9020a2
-/
theorem sumLexRestrictRight [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] (h : good (α ⊕ₗ β)) : good β :=
  h.elim λ X ↦ ⟨X.sumLexRestrictRight⟩

end good

/-! ### The quotient predicate `isGoodOrdinal` of `good` -/

open Ordinal

namespace good

variable [LinearOrder α] [WellFoundedLT α] [LinearOrder β] [WellFoundedLT β]
  (h : type (λ x y : α ↦ x < y) = type (λ x y : β ↦ x < y))
include h

/-- If `α` and `β` are of the same ordinal type and `α` is good, then `β` is good.
@isnad1 id=good.2h2v.s6.60f7c880dc6c from=translated src=- shape=ad3557c7 vocab=27ea8e91
-/
theorem of_type_eq (hα : good α) : good β :=
  (type_eq.mp h).elim λ r ↦ hα.conjOrderIso (OrderIso.ofRelIsoLT r)

/-- If `α` and `β` are of the same ordinal type, then `α` is good iff `β` is good.
@isnad1 id=iff.1h2v.s6.1d18442989e0 from=translated src=- shape=5dbd4203 vocab=27ea8e91
-/
theorem iff_of_type_eq : good α ↔ good β :=
  ⟨good.of_type_eq h, good.of_type_eq h.symm⟩

end good

/-- The quotient predicate of `good`. -/
def isGoodOrdinal (o : Ordinal) : Prop :=
  o.liftOnWellOrder (λ α _ _ ↦ good α) (λ _ _ _ _ _ _ h ↦ Iff.eq (good.iff_of_type_eq h))

/-- Definition of `isGoodOrdinal` on a quotient of a well-ordered type.
@isnad1 id=iff.0h1v.s5.1abbd06f8910 from=translated src=- shape=cc15bea7 vocab=85a25d81
-/
theorem isGoodOrdinal_iff_good [LinearOrder α] [WellFoundedLT α] :
    isGoodOrdinal (type λ x y : α ↦ x < y) ↔ good α :=
  (liftOnWellOrder_type _ _).to_iff

/-- Definition of `isGoodOrdinal` of an ordinal with respect to a suitable well-order.
@isnad1 id=iff.1h2v.s6.18245a5327f7 from=translated src=- shape=82c9e269 vocab=392b8a1a
-/
theorem isGoodOrdinal_iff_good'.{u, v} {α : Type u} [LinearOrder α] [WellFoundedLT α]
    {o : Ordinal.{v}} (ho : lift.{u, v} o = lift.{v, u} (type λ x y : α ↦ x < y)) :
    isGoodOrdinal o ↔ good α := by
  induction o using Ordinal.inductionOnWellOrder with | type β => ?_
  obtain ⟨e⟩ := lift_type_eq.{_, _, 0}.mp ho
  exact isGoodOrdinal_iff_good.trans (good.conjOrderIso_iff (OrderIso.ofRelIsoLT e))

/-- The ordinal `1` is not good.
@isnad1 id=not.0h0v.s3.eed85023ffb0 from=translated src=- shape=8d7dbbf6 vocab=3ae0d3a3
-/
theorem one_not_isGoodOrdinal : ¬isGoodOrdinal 1 := by
  rw [← type_eq_one_of_unique (λ x y : PUnit ↦ x < y), isGoodOrdinal_iff_good]
  exact PUnit_is_not_good

/-- The ordinal `ω` is not good.
@isnad1 id=not.0h0v.s1.aca70a8460d8 from=translated src=- shape=87ceb31f vocab=ad7baca8
-/
theorem omega0_not_isGoodOrdinal : ¬isGoodOrdinal ω :=
  mt (isGoodOrdinal_iff_good' lift_omega0).mp Nat_is_not_good

/-- The ordinal type of `Nat ×ₗ Nat` is `ω^2`.
@isnad1 id=eq.0h0v.s5.fa66b2bbd4b0 from=translated src=- shape=66cbeefd vocab=7fd4d555
-/
theorem type_LexNatNat : type (λ x y : ℕ ×ₗ ℕ ↦ x < y) = ω ^ 2 :=
  (sq (type λ m n : ℕ ↦ m < n)).symm.trans (congrArg (· ^ 2) type_nat_lt)

/-- The ordinal `ω^2` is good.
@isnad1 id=isgoodor.0h0v.s4.d0fd188f4e9f from=translated src=- shape=8c555b01 vocab=75f0db35
-/
theorem omega0_sq_isGoodOrdinal : isGoodOrdinal (ω ^ 2) := by
  refine (isGoodOrdinal_iff_good' ?_).mpr NatNatLex_is_good
  rw [type_LexNatNat, lift_uzero, sq, sq, lift_mul, lift_omega0]

namespace isGoodOrdinal

/-- If `a` is a good ordinal, then `ab` is a good ordinal for any ordinal `b`.
@isnad1 id=isgoodor.1h2v.s4.e07389fe86d3 from=translated src=- shape=6298efac vocab=d91a1cac
-/
theorem mul_right (ha : isGoodOrdinal a) (b : Ordinal) : isGoodOrdinal (a * b) := by
  ---- Indeed, if `a = [α]` and `b = [β]`, then `ab = [β ×ₗ α]`.
  induction a using Ordinal.inductionOnWellOrder with | type α => ?_
  induction b using Ordinal.inductionOnWellOrder with | type β => ?_
  change isGoodOrdinal (type λ x y : β ×ₗ α ↦ x < y)
  exact isGoodOrdinal_iff_good.mpr ((isGoodOrdinal_iff_good.mp ha).prodLexLeft β)

/-- If `a` is a good ordinal and `a ∣ b`, then `b` is a good ordinal.
@isnad1 id=isgoodor.2h2v.s4.d2766045a7db from=translated src=- shape=31385369 vocab=39f15747
-/
theorem trans_dvd (ha : isGoodOrdinal a) (h : a ∣ b) : isGoodOrdinal b :=
  h.elim λ c hc ↦ hc ▸ ha.mul_right c

/-- If `a + b` is a good ordinal, then `b` is a good ordinal.
@isnad1 id=isgoodor.1h2v.s4.21fb72e57c58 from=translated src=- shape=77f9d9f4 vocab=cf8c27dd
-/
theorem add_left_cancel (h : isGoodOrdinal (a + b)) : isGoodOrdinal b := by
  ---- Indeed, if `a = [α]` and `b = [β]`, then `a + b = [α ⊕ₗ β]`.
  induction a using Ordinal.inductionOnWellOrder with | type α => ?_
  induction b using Ordinal.inductionOnWellOrder with | type β => ?_
  change isGoodOrdinal (type (λ x y : α ⊕ₗ β ↦ x < y)) at h
  exact isGoodOrdinal_iff_good.mpr (isGoodOrdinal_iff_good.mp h).sumLexRestrictRight

/-- If `o` is a good ordinal, then `ω ∣ o`.
@isnad1 id=dvd.1h1v.s4.345c2eeaab35 from=translated src=- shape=f0a351af vocab=f74af356
-/
theorem omega0_dvd (ho : isGoodOrdinal o) : ω ∣ o := by
  ---- If not, then `o = o₀ + 1` is good; but then `1` is good, contradiction.
  obtain ⟨o₀, rfl⟩ | ho : o ∈ Set.range Order.succ ∨ Order.IsSuccPrelimit o :=
    Order.mem_range_succ_or_isSuccPrelimit o
  exacts [absurd ho.add_left_cancel one_not_isGoodOrdinal,
    isSuccPrelimit_iff_omega0_dvd.mp ho]

/-- If `o` is a good ordinal, then `ω^2 ∣ o`.
@isnad1 id=dvd.1h1v.s5.cd5bc57f5b5a from=translated src=- shape=c2466856 vocab=b39f46da
-/
theorem omega0_sq_dvd (ho : isGoodOrdinal o) : ω ^ 2 ∣ o := by
  ---- First write `o = ωo₀` for some ordinal `o₀`.
  obtain ⟨o₀, rfl⟩ : ω ∣ o := ho.omega0_dvd
  ---- Either `o₀ = o₁ + 1` for some `o₁` or `o₀` is a limit ordinal.
  obtain ⟨o₀, rfl⟩ | ho₀ : o₀ ∈ Set.range Order.succ ∨ Order.IsSuccPrelimit o₀ :=
    Order.mem_range_succ_or_isSuccPrelimit o₀
  ---- If `o₀ = o₁ + 1` for some `o₁`, then `ω` is good; contradiction.
  · rw [Order.succ_eq_add_one, mul_add_one] at ho
    exact absurd ho.add_left_cancel omega0_not_isGoodOrdinal
  ---- If `o₀` is a limit ordinal, then `ω ∣ o₀` and so `ω^2 ∣ o`.
  · exact sq ω ▸ mul_dvd_mul_left ω (isSuccPrelimit_iff_omega0_dvd.mp ho₀)

/-- An ordinal `o` is good if and only if `ω^2 ∣ o`.
@isnad1 id=iff.0h1v.s5.e1a42f02bf89 from=translated src=- shape=59bdcc67 vocab=b39f46da
-/
theorem iff_omega0_sq_dvd : isGoodOrdinal o ↔ ω ^ 2 ∣ o :=
  ⟨isGoodOrdinal.omega0_sq_dvd, omega0_sq_isGoodOrdinal.trans_dvd⟩

end isGoodOrdinal

/-! ### Summary -/

/-- Final solution to the generalized version
@isnad1 id=iff.0h1v.s6.79ca1810393a from=translated src=- shape=6e1177af vocab=6dfb70ff
-/
theorem Generalization.final_solution {α : Type} [LinearOrder α] [WellFoundedLT α] :
    good α ↔ ∃ (β : Type) (_ : LinearOrder β) (_ : WellFoundedLT β),
      Nonempty (α ≃o β ×ₗ ℕ ×ₗ ℕ) := by
  ---- The backwards direction is more straightforward.
  refine Iff.symm ⟨?_, λ hα ↦ ?_⟩
  · rintro ⟨β, _, _, ⟨e⟩⟩
    exact (good.conjOrderIso_iff e).mpr (NatNatLex_is_good.prodLexLeft β)
  ---- Now suppose that `α` is good. Then `ω^2` divides the ordinal number `o = [α]`.
  obtain ⟨o₀, ho₀⟩ : ω ^ 2 ∣ type (λ x y : α ↦ x < y) :=
    (isGoodOrdinal_iff_good.mpr hα).omega0_sq_dvd
  ---- If we write `[α] = ω^2 [β]`, then `β` works.
  induction o₀ using Ordinal.inductionOnWellOrder with | type β => ?_
  refine ⟨β, by assumption, by assumption, ?_⟩
  rw [← type_LexNatNat, ← type_prod_lex, type_eq] at ho₀
  exact ho₀.map OrderIso.ofRelIsoLT
