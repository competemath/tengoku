module

public import Tengoku.Seed.NumberTheory.Padics.RingHoms
public import Tengoku.Seed.RingTheory.Teichmuller
public import Tengoku.Seed.NumberTheory.DirichletCharacter.Basic
public import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots
import Tengoku.Seed.CategoryTheory.Category.Init
import Tengoku.Seed.FieldTheory.Finite.Basic
import Tengoku.Seed.LinearAlgebra.SModEq.Pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Characters of `Gal(ℚ(ζ_p)/ℚ)` - Teichmüller character

Let `p` be a prime. The Teichmüller character `ω: ZMod p →*₀ ℤ_[p]`
sends each nonzero residue class `a ∈ (ZMod p)ˣ` to the unique `(p-1)`-th
root of unity in `ℤ_[p]` that reduces to `a` modulo `p`, and sends the
zero residue class to `0`.

The construction reuses mathlib's `Perfection.teichmuller₀`: since the
residue field `ℤ_[p] ⧸ maximalIdeal ℤ_[p]` is canonically isomorphic to
`ZMod p`, which is perfect (finite of characteristic `p`), `ZMod p` is
identified with the perfection, after which the generic Teichmüller map
lands in `ℤ_[p]`.

## Main definitions

- `KummerCriterion.teichmuller` - `ω: ZMod p →*₀ ℤ_[p]`.

## Main results

- `toZMod_teichmuller` - `ω(a) ≡ a (mod p)`.
- `teichmuller_pow_sub_one` - `ω(a)^{p-1} = 1` for `a ≠ 0`.
- The `MonoidWithZeroHom` structure is provided by the bundled
 definition, so `teichmuller_zero`, `teichmuller_one`,
 `teichmuller_mul` follow.

## References

- Diekmann, *FLT for regular primes* (2023), Lemma 20.
- Washington, *Introduction to Cyclotomic Fields*, §5.1.
-/

@[expose] public section

noncomputable section

open Perfection PadicInt IsLocalRing

namespace KummerCriterion

variable (p : ℕ) [hp : Fact p.Prime]

/-- `ℤ_[p] ⧸ maximalIdeal ℤ_[p] ≃+* ZMod p`. Reuses
`PadicInt.residueField` (whose codomain `IsLocalRing.ResidueField ℤ_[p]`
is definitionally `ℤ_[p] ⧸ maximalIdeal ℤ_[p]`).-/
noncomputable def maximalIdealQuotientEquivZMod : ℤ_[p] ⧸ maximalIdeal ℤ_[p] ≃+* ZMod p :=
  PadicInt.residueField

/--
@isnad1 id=charp.0h1v.s7.013506069a65 from=translated src=- shape=5ea02c55 vocab=c93f4555
-/
instance maximalIdealQuotient_charP : CharP (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) p :=
  charP_of_injective_ringHom (f := (maximalIdealQuotientEquivZMod p).symm.toRingHom)
    (maximalIdealQuotientEquivZMod p).symm.injective p

/--
@isnad1 id=finite.0h1v.s5.70895ff6a37e from=translated src=- shape=25c87775 vocab=f8dc3dc8
-/
instance maximalIdealQuotient_finite : Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) :=
  Finite.of_equiv _ (maximalIdealQuotientEquivZMod p).symm.toEquiv

/-- The Teichmüller character `ω : ZMod p →*₀ ℤ_[p]`, built from
`Perfection.teichmuller₀` through the residue-field equivalence.-/
noncomputable def teichmuller : ZMod p →*₀ ℤ_[p] :=
  (Perfection.teichmuller₀ p (maximalIdeal ℤ_[p])).comp <|
    (PerfectionMap.id p (ℤ_[p] ⧸ maximalIdeal ℤ_[p])).equiv.toRingHom.toMonoidWithZeroHom.comp
      (maximalIdealQuotientEquivZMod p).symm.toRingHom.toMonoidWithZeroHom

variable {p}

/--
@isnad1 id=eq.0h1v.s7.7e880c38c3cd from=translated src=- shape=ece98fc8 vocab=416f0fb3
-/
@[simp]
lemma teichmuller_zero : teichmuller p 0 = 0 := map_zero _

/--
@isnad1 id=eq.0h1v.s7.1277dcff523e from=translated src=- shape=ece98fc8 vocab=416f0fb3
-/
@[simp]
lemma teichmuller_one : teichmuller p 1 = 1 := map_one _

/-- `ω(a) ≡ a (mod p)` for every `a ∈ ZMod p`.
@isnad1 id=eq.0h2v.s7.ce1082abe0f3 from=translated src=- shape=10d36f55 vocab=b52a5a4d
-/
@[simp]
lemma toZMod_teichmuller (a : ZMod p) : PadicInt.toZMod (teichmuller p a) = a := by
  change PadicInt.toZMod
    (Perfection.teichmuller₀ p (maximalIdeal ℤ_[p])
      ((PerfectionMap.id p (ℤ_[p] ⧸ maximalIdeal ℤ_[p])).equiv
        ((maximalIdealQuotientEquivZMod p).symm a))) = a
  rw [PadicInt.toZMod_eq_residueField_comp_residue, RingHom.comp_apply]
  change PadicInt.residueField (Ideal.Quotient.mk _ _) = a
  rw [Perfection.mk_teichmuller₀, PerfectionMap.comp_equiv]
  exact (maximalIdealQuotientEquivZMod p).apply_symm_apply a

/-- `ω(a)^(p-1) = 1` for nonzero `a ∈ ZMod p`.
@isnad1 id=eq.1h2v.s7.c11a848b3891 from=translated src=- shape=d60f40b8 vocab=535c0a25
-/
lemma teichmuller_pow_sub_one {a : ZMod p} (ha : a ≠ 0) : teichmuller p a ^ (p - 1) = 1 := by
  rw [← map_pow, ZMod.pow_card_sub_one_eq_one ha, map_one]

/-- `ω` is injective on `ZMod p` (follows from `toZMod ∘ ω = id`).
@isnad1 id=injectiv.0h1v.s6.058fd84e2f34 from=translated src=- shape=47973aa0 vocab=c019eb51
-/
lemma teichmuller_injective : Function.Injective (teichmuller p) := fun _ _ hab => by
  simpa using congrArg PadicInt.toZMod hab

/-- Fixed point of Frobenius: `ω(a)^p = ω(a)` for any `a : ZMod p`.
@isnad1 id=eq.0h2v.s7.5901d0518842 from=translated src=- shape=9085a030 vocab=37771628
-/
lemma teichmuller_pow_card (a : ZMod p) : teichmuller p a ^ p = teichmuller p a := by
  rw [← map_pow, ZMod.pow_card]

/-- The Teichmüller character `ω: ZMod p →*₀ ℤ_[p]` packaged as a
`DirichletCharacter ℤ_[p] p`.-/
noncomputable def teichmullerChar (p : ℕ) [Fact p.Prime] : DirichletCharacter ℤ_[p] p where
  toFun := teichmuller p
  map_one' := map_one _
  map_mul' := map_mul _
  map_nonunit' := fun a ha => by
    rw [show a = 0 from by_contra fun hne => ha (isUnit_iff_ne_zero.mpr hne), teichmuller_zero]

/--
@isnad1 id=eq.0h2v.s7.a15e1cb0f0f1 from=translated src=- shape=ee6c7d2a vocab=b41fd75e
-/
@[simp]
lemma teichmullerChar_apply (a : ZMod p) : teichmullerChar p a = teichmuller p a := rfl

/-- If `g: (ZMod p)ˣ` generates the unit group, then
`ω(g) = teichmuller p (g: ZMod p)` is a primitive `(p-1)`-th root of
unity in `ℤ_[p]`.
@isnad1 id=isprimit.1h2v.s8.fbf393d71759 from=translated src=- shape=33e6a34a vocab=29fc82c5
-/
lemma teichmuller_isPrimitiveRoot_of_generator {g : (ZMod p)ˣ}
    (hg_gen : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g) :
    IsPrimitiveRoot (teichmuller p (g : ZMod p)) (p - 1) := by
  refine ⟨?_, fun l hl => ?_⟩
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one,
      Units.val_one, map_one]
  · have h_units : g ^ l = 1 := Units.ext <| by
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact teichmuller_injective (by rwa [map_pow, map_one])
    have h_order : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg_gen, Nat.card_eq_fintype_card, ZMod.card_units]
    rw [← h_order]; exact orderOf_dvd_of_pow_eq_one h_units

/-- `ω^(p-1) = 1` in the Dirichlet character group: the `(p-1)`-th power
of the Teichmüller character is the trivial character. This is the
concrete form of "characters cycle with period `p-1`".
@isnad1 id=eq.0h1v.s7.b860ebe25a88 from=translated src=- shape=439efdd7 vocab=32aa798f
-/
lemma teichmullerChar_pow_sub_one_eq_one : (teichmullerChar p) ^ (p - 1) = 1 := by
  ext a : 1
  rw [MulChar.pow_apply_coe, teichmullerChar_apply, MulChar.one_apply_coe]
  exact teichmuller_pow_sub_one a.ne_zero

/-- The Teichmüller character has order exactly `p - 1` in
`DirichletCharacter ℤ_[p] p`. Combined with
`card_dirichletCharacter`, this says `ω` generates the character
group.
@isnad1 id=eq.0h1v.s6.bdb1c9cc20c4 from=translated src=- shape=6829b6c2 vocab=ced68f0d
-/
lemma orderOf_teichmullerChar : orderOf (teichmullerChar p) = p - 1 := by
  refine Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one (teichmullerChar_pow_sub_one_eq_one (p := p))) ?_
  obtain ⟨g, hg_gen⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have h_apply := congrArg (fun χ : DirichletCharacter ℤ_[p] p => χ (g : ZMod p))
    (pow_orderOf_eq_one (teichmullerChar p))
  simp only [MulChar.pow_apply_coe, teichmullerChar_apply, MulChar.one_apply_coe] at h_apply
  exact (teichmuller_isPrimitiveRoot_of_generator hg_gen).2 _ h_apply

/-- `ω(-1) = -1` for any odd prime `p`.
@isnad1 id=eq.1h1v.s7.078176cfc854 from=translated src=- shape=02260765 vocab=a6c9dfe6
-/
lemma teichmuller_neg_one (hp_odd : p ≠ 2) : teichmuller p (-1) = -1 := by
  have h_sq : teichmuller p (-1 : ZMod p) ^ 2 = 1 := by
    rw [sq, ← map_mul, neg_one_mul, neg_neg, map_one]
  rcases sq_eq_one_iff.mp h_sq with h1 | h_neg
  · have : Fact (2 < p) := ⟨lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd)⟩
    exact absurd (by simpa using congrArg PadicInt.toZMod h1) ZMod.neg_one_ne_one
  · exact h_neg

/-- `ω^i(-1) = (-1)^i` for `p` an odd prime.
@isnad1 id=eq.1h2v.s8.12dc0232cab7 from=translated src=- shape=4143387e vocab=ef1f60b8
-/
lemma teichmullerChar_pow_apply_neg_one (hp_odd : p ≠ 2) (i : ℕ) :
    ((teichmullerChar p) ^ i) (-1 : ZMod p) = (-1 : ℤ_[p]) ^ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [pow_zero, pow_zero]; exact MulChar.one_apply isUnit_one.neg
  · rw [MulChar.pow_apply' _ hi.ne', teichmullerChar_apply, teichmuller_neg_one hp_odd]

end KummerCriterion
