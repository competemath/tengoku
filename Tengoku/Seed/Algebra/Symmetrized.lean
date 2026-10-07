/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Jordan.Basic
public import Tengoku.Seed.Algebra.Module.Defs

/-!
# Symmetrized algebra

A commutative multiplication on a real or complex space can be constructed from any multiplication
by "symmetrization" i.e.
$$
a \circ b = \frac{1}{2}(ab + ba)
$$

We provide the symmetrized version of a type `α` as `SymAlg α`, with notation `αˢʸᵐ`.

## Implementation notes

The approach taken here is inspired by `Mathlib/Algebra/Opposites.lean`. We use Oxford Spellings
(IETF en-GB-oxendict).

## Note

See `SymmetricAlgebra` instead if you are looking for the symmetric algebra of a module.

## References

* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
-/

@[expose] public section


open Function

/-- The symmetrized algebra (denoted as `αˢʸᵐ`)
has the same underlying space as the original algebra `α`. -/
def SymAlg (α : Type*) : Type _ :=
  α

@[inherit_doc] postfix:max "ˢʸᵐ" => SymAlg

namespace SymAlg

variable {α : Type*}

/-- The element of `SymAlg α` that represents `a : α`. -/
@[match_pattern]
def sym : α ≃ αˢʸᵐ :=
  Equiv.refl _

/-- The element of `α` represented by `x : αˢʸᵐ`. -/
-- We add `@[pp_nodot]` in case RFC https://github.com/leanprover/lean4/issues/6178 happens.
@[pp_nodot]
def unsym : αˢʸᵐ ≃ α :=
  Equiv.refl _

/--
@isnad1 id=eq.0h2v.s5.b35920756006 from=seed src=0 shape=fa7330c4 vocab=cd110234
-/
@[simp]
theorem unsym_sym (a : α) : unsym (sym a) = a :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.5035f3302cbe from=seed src=0 shape=a979b882 vocab=cd110234
-/
@[simp]
theorem sym_unsym (a : α) : sym (unsym a) = a :=
  rfl

/--
@isnad1 id=eq.0h1v.s6.e7f724de683f from=seed src=0 shape=ae0f59a5 vocab=2c681d23
-/
@[simp]
theorem sym_comp_unsym : (sym : α → αˢʸᵐ) ∘ unsym = id :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.b49fff24eae2 from=seed src=0 shape=60cb1567 vocab=2c681d23
-/
@[simp]
theorem unsym_comp_sym : (unsym : αˢʸᵐ → α) ∘ sym = id :=
  rfl

/--
@isnad1 id=eq.0h1v.s3.329128fe1875 from=seed src=0 shape=9d746310 vocab=f95c0e2e
-/
@[simp]
theorem sym_symm : (@sym α).symm = unsym :=
  rfl

/--
@isnad1 id=eq.0h1v.s3.74bd4d590396 from=seed src=0 shape=e5cab704 vocab=f95c0e2e
-/
@[simp]
theorem unsym_symm : (@unsym α).symm = sym :=
  rfl

/--
@isnad1 id=bijectiv.0h1v.s4.46d55350ea00 from=seed src=0 shape=68eb7635 vocab=de3df54d
-/
theorem sym_bijective : Bijective (sym : α → αˢʸᵐ) :=
  sym.bijective

/--
@isnad1 id=bijectiv.0h1v.s4.6e07a1083e2e from=seed src=0 shape=64d0dd7a vocab=8e9ad54e
-/
theorem unsym_bijective : Bijective (unsym : αˢʸᵐ → α) :=
  unsym.symm.bijective

/--
@isnad1 id=injectiv.0h1v.s4.73063dc652f9 from=seed src=0 shape=68eb7635 vocab=5673615f
-/
theorem sym_injective : Injective (sym : α → αˢʸᵐ) :=
  sym.injective

/--
@isnad1 id=surjecti.0h1v.s4.06a23ceb5220 from=seed src=0 shape=68eb7635 vocab=b6e8d316
-/
theorem sym_surjective : Surjective (sym : α → αˢʸᵐ) :=
  sym.surjective

/--
@isnad1 id=injectiv.0h1v.s4.22000736ab63 from=seed src=0 shape=64d0dd7a vocab=2a424a24
-/
theorem unsym_injective : Injective (unsym : αˢʸᵐ → α) :=
  unsym.injective

/--
@isnad1 id=surjecti.0h1v.s4.b394e5706556 from=seed src=0 shape=64d0dd7a vocab=3ee3e1ee
-/
theorem unsym_surjective : Surjective (unsym : αˢʸᵐ → α) :=
  unsym.surjective

/--
@isnad1 id=iff.0h3v.s6.44e221a8e97c from=seed src=0 shape=5e10f266 vocab=de84bd41
-/
theorem sym_inj {a b : α} : sym a = sym b ↔ a = b :=
  sym_injective.eq_iff

/--
@isnad1 id=iff.0h3v.s6.c98d334aad89 from=seed src=0 shape=49fd6368 vocab=3d89e9ab
-/
theorem unsym_inj {a b : αˢʸᵐ} : unsym a = unsym b ↔ a = b :=
  unsym_injective.eq_iff

instance [Nontrivial α] : Nontrivial αˢʸᵐ :=
  sym_injective.nontrivial

instance [Inhabited α] : Inhabited αˢʸᵐ :=
  ⟨sym default⟩

instance [Subsingleton α] : Subsingleton αˢʸᵐ :=
  unsym_injective.subsingleton

instance [Unique α] : Unique αˢʸᵐ :=
  Unique.mk' _

instance [IsEmpty α] : IsEmpty αˢʸᵐ :=
  Function.isEmpty unsym

@[to_additive]
instance [One α] : One αˢʸᵐ where one := sym 1

instance [Add α] : Add αˢʸᵐ where add a b := sym (unsym a + unsym b)

instance [Sub α] : Sub αˢʸᵐ where sub a b := sym (unsym a - unsym b)

instance [Neg α] : Neg αˢʸᵐ where neg a := sym (-unsym a)

-- Introduce the symmetrized multiplication
instance [Add α] [Mul α] [One α] [OfNat α 2] [Invertible (2 : α)] : Mul αˢʸᵐ where
  mul a b := sym (⅟2 * (unsym a * unsym b + unsym b * unsym a))

@[to_additive existing]
instance [Inv α] : Inv αˢʸᵐ where inv a := sym <| (unsym a)⁻¹

instance (R : Type*) [SMul R α] : SMul R αˢʸᵐ where smul r a := sym (r • unsym a)

/--
@isnad1 id=eq.0h1v.s5.585ff39b2a82 from=seed src=0 shape=759a5eb9 vocab=a9795dab
-/
@[to_additive (attr := simp)]
theorem sym_one [One α] : sym (1 : α) = 1 :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.1f316bd373c0 from=seed src=0 shape=5a2d305d vocab=d0930b96
-/
@[to_additive (attr := simp)]
theorem unsym_one [One α] : unsym (1 : αˢʸᵐ) = 1 :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.1cc0cc7823c3 from=seed src=0 shape=048cfcd0 vocab=8fa7b7a0
-/
@[simp]
theorem sym_add [Add α] (a b : α) : sym (a + b) = sym a + sym b :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.70e7d31c706b from=seed src=0 shape=118c49f2 vocab=ec587b15
-/
@[simp]
theorem unsym_add [Add α] (a b : αˢʸᵐ) : unsym (a + b) = unsym a + unsym b :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.fb7b2cbf5db0 from=seed src=0 shape=048cfcd0 vocab=cbb3762d
-/
@[simp]
theorem sym_sub [Sub α] (a b : α) : sym (a - b) = sym a - sym b :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.52bbee2c0dbc from=seed src=0 shape=118c49f2 vocab=ae245573
-/
@[simp]
theorem unsym_sub [Sub α] (a b : αˢʸᵐ) : unsym (a - b) = unsym a - unsym b :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.54ee5d1af0da from=seed src=0 shape=e8511e99 vocab=bcbc4943
-/
@[simp]
theorem sym_neg [Neg α] (a : α) : sym (-a) = -sym a :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.40094c2759e3 from=seed src=0 shape=c86298d1 vocab=9aac0d9b
-/
@[simp]
theorem unsym_neg [Neg α] (a : αˢʸᵐ) : unsym (-a) = -unsym a :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.6f26959fdb63 from=seed src=0 shape=94b4b893 vocab=3abc3ee4
-/
theorem mul_def [Add α] [Mul α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : αˢʸᵐ) :
    a * b = sym (⅟2 * (unsym a * unsym b + unsym b * unsym a)) := rfl

/--
@isnad1 id=eq.0h3v.s7.b8651836dcb5 from=seed src=0 shape=a6a6a0fe vocab=11a7a5cf
-/
theorem unsym_mul [Mul α] [Add α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : αˢʸᵐ) :
    unsym (a * b) = ⅟2 * (unsym a * unsym b + unsym b * unsym a) := rfl

/--
@isnad1 id=eq.0h3v.s7.37e5c1037aa0 from=seed src=0 shape=b5e8fc30 vocab=83d7131e
-/
theorem sym_mul_sym [Mul α] [Add α] [One α] [OfNat α 2] [Invertible (2 : α)] (a b : α) :
    sym a * sym b = sym (⅟2 * (a * b + b * a)) :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.ceb5d2c81e7a from=seed src=0 shape=e8511e99 vocab=8c176b3b
-/
@[simp, to_additive existing]
theorem sym_inv [Inv α] (a : α) : sym a⁻¹ = (sym a)⁻¹ :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.71ea20ee368a from=seed src=0 shape=c86298d1 vocab=672a325b
-/
@[simp, to_additive existing]
theorem unsym_inv [Inv α] (a : αˢʸᵐ) : unsym a⁻¹ = (unsym a)⁻¹ :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.b2698b5e90fc from=seed src=0 shape=9b1277ca vocab=29586b4c
-/
@[simp]
theorem sym_smul {R : Type*} [SMul R α] (c : R) (a : α) : sym (c • a) = c • sym a :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.65264bf687b0 from=seed src=0 shape=311bbda4 vocab=3d20a5fd
-/
@[simp]
theorem unsym_smul {R : Type*} [SMul R α] (c : R) (a : αˢʸᵐ) : unsym (c • a) = c • unsym a :=
  rfl

/--
@isnad1 id=iff.0h2v.s5.c34049f7a08b from=seed src=0 shape=9151a5dd vocab=d0930b96
-/
@[to_additive (attr := simp)]
theorem unsym_eq_one_iff [One α] (a : αˢʸᵐ) : unsym a = 1 ↔ a = 1 :=
  unsym_injective.eq_iff' rfl

/--
@isnad1 id=iff.0h2v.s5.6eff8540e104 from=seed src=0 shape=6a647082 vocab=a9795dab
-/
@[to_additive (attr := simp)]
theorem sym_eq_one_iff [One α] (a : α) : sym a = 1 ↔ a = 1 :=
  sym_injective.eq_iff' rfl

/--
@isnad1 id=iff.0h2v.s5.bf49647af784 from=seed src=0 shape=9151a5dd vocab=d0930b96
-/
@[to_additive]
theorem unsym_ne_one_iff [One α] (a : αˢʸᵐ) : unsym a ≠ (1 : α) ↔ a ≠ (1 : αˢʸᵐ) :=
  not_congr <| unsym_eq_one_iff a

/--
@isnad1 id=iff.0h2v.s5.688349fbfa40 from=seed src=0 shape=6a647082 vocab=a9795dab
-/
@[to_additive]
theorem sym_ne_one_iff [One α] (a : α) : sym a ≠ (1 : αˢʸᵐ) ↔ a ≠ (1 : α) :=
  not_congr <| sym_eq_one_iff a

instance addCommSemigroup [AddCommSemigroup α] : AddCommSemigroup αˢʸᵐ :=
  unsym_injective.addCommSemigroup _ unsym_add

instance addMonoid [AddMonoid α] : AddMonoid αˢʸᵐ :=
  unsym_injective.addMonoid _ unsym_zero unsym_add fun _ _ => rfl

instance addGroup [AddGroup α] : AddGroup αˢʸᵐ :=
  unsym_injective.addGroup _ unsym_zero unsym_add unsym_neg unsym_sub (fun _ _ => rfl) fun _ _ =>
    rfl

instance addCommMonoid [AddCommMonoid α] : AddCommMonoid αˢʸᵐ :=
  { SymAlg.addCommSemigroup, SymAlg.addMonoid with }

instance addCommGroup [AddCommGroup α] : AddCommGroup αˢʸᵐ :=
  { SymAlg.addCommMonoid, SymAlg.addGroup with }

instance {R : Type*} [Semiring R] [AddCommMonoid α] [Module R α] : Module R αˢʸᵐ :=
  Function.Injective.module R ⟨⟨unsym, unsym_zero⟩, unsym_add⟩ unsym_injective unsym_smul

instance [Mul α] [AddMonoidWithOne α] [Invertible (2 : α)] (a : α) [Invertible a] :
    Invertible (sym a) where
  invOf := sym (⅟a)
  invOf_mul_self := by
    rw [sym_mul_sym, mul_invOf_self, invOf_mul_self, one_add_one_eq_two, invOf_mul_self, sym_one]
  mul_invOf_self := by
    rw [sym_mul_sym, mul_invOf_self, invOf_mul_self, one_add_one_eq_two, invOf_mul_self, sym_one]

/--
@isnad1 id=eq.0h2v.s7.8fec5513f787 from=seed src=0 shape=d7635aa9 vocab=69c5e6e4
-/
@[simp]
theorem invOf_sym [Mul α] [AddMonoidWithOne α] [Invertible (2 : α)] (a : α) [Invertible a] :
    ⅟(sym a) = sym (⅟a) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
instance nonAssocSemiring [Semiring α] [Invertible (2 : α)] : NonAssocSemiring αˢʸᵐ :=
  { SymAlg.addCommMonoid with
    zero_mul := fun _ => by
      rw [mul_def, unsym_zero, zero_mul, mul_zero, add_zero,
        mul_zero, sym_zero]
    mul_zero := fun _ => by
      rw [mul_def, unsym_zero, zero_mul, mul_zero, add_zero,
        mul_zero, sym_zero]
    mul_one := fun _ => by
      rw [mul_def, unsym_one, mul_one, one_mul, ← two_mul, invOf_mul_cancel_left, sym_unsym]
    one_mul := fun _ => by
      rw [mul_def, unsym_one, mul_one, one_mul, ← two_mul, invOf_mul_cancel_left, sym_unsym]
    left_distrib := fun a b c => by
      rw [mul_def, mul_def, mul_def, ← sym_add, ← mul_add, unsym_add, add_mul]
      congr 2
      rw [mul_add]
      abel
    right_distrib := fun a b c => by
      rw [mul_def, mul_def, mul_def, ← sym_add, ← mul_add, unsym_add, add_mul]
      congr 2
      rw [mul_add]
      abel }

/-- The symmetrization of a real (unital, associative) algebra is a non-associative ring. -/
instance [Ring α] [Invertible (2 : α)] : NonAssocRing αˢʸᵐ :=
  { SymAlg.nonAssocSemiring, SymAlg.addCommGroup with }

/-! The squaring operation coincides for both multiplications -/


/--
@isnad1 id=eq.0h2v.s7.fb13c661718a from=seed src=0 shape=37ca9b61 vocab=f1d48f23
-/
theorem unsym_mul_self [Semiring α] [Invertible (2 : α)] (a : αˢʸᵐ) :
    unsym (a * a) = unsym a * unsym a := by
  rw [mul_def, unsym_sym, ← two_mul, invOf_mul_cancel_left]

/--
@isnad1 id=eq.0h2v.s7.45fae25a9577 from=seed src=0 shape=f7098f2b vocab=0c156b04
-/
theorem sym_mul_self [Semiring α] [Invertible (2 : α)] (a : α) : sym (a * a) = sym a * sym a := by
  rw [sym_mul_sym, ← two_mul, invOf_mul_cancel_left]

/--
@isnad1 id=eq.0h3v.s6.f43a2bcce49d from=seed src=0 shape=926ad0ce vocab=6fd5b900
-/
theorem mul_comm [Mul α] [AddCommSemigroup α] [One α] [OfNat α 2] [Invertible (2 : α)]
    (a b : αˢʸᵐ) :
    a * b = b * a := by rw [mul_def, mul_def, add_comm]

instance [Ring α] [Invertible (2 : α)] : CommMagma αˢʸᵐ where
  mul_comm := SymAlg.mul_comm

instance [Ring α] [Invertible (2 : α)] : IsCommJordan αˢʸᵐ where
  lmul_comm_rmul_rmul a b := by
    have commute_half_left := fun a : α => by
      have := (Commute.one_left a).add_left (Commute.one_left a)
      rw [one_add_one_eq_two] at this
      exact this.invOf_left.eq
    calc a * b * (a * a)
      _ = sym (⅟2 * ⅟2 * (unsym a * unsym b * unsym (a * a) +
          unsym b * unsym a * unsym (a * a) +
          unsym (a * a) * unsym a * unsym b +
          unsym (a * a) * unsym b * unsym a)) := ?_
      _ = sym (⅟2 * (unsym a *
          unsym (sym (⅟2 * (unsym b * unsym (a * a) + unsym (a * a) * unsym b))) +
          unsym (sym (⅟2 * (unsym b * unsym (a * a) + unsym (a * a) * unsym b))) * unsym a)) := ?_
      _ = a * (b * (a * a)) := ?_
    -- Rearrange LHS
    · rw [mul_def, mul_def a b, unsym_sym, ← mul_assoc, ← commute_half_left (unsym (a * a)),
        mul_assoc, mul_assoc, ← mul_add, ← mul_assoc, add_mul, mul_add (unsym (a * a)),
        ← add_assoc, ← mul_assoc, ← mul_assoc]
    · rw [unsym_sym, sym_inj, ← mul_assoc, ← commute_half_left (unsym a), mul_assoc (⅟2) (unsym a),
        mul_assoc (⅟2) _ (unsym a), ← mul_add, ← mul_assoc]
      conv_rhs => rw [mul_add (unsym a)]
      rw [add_mul, ← add_assoc, ← mul_assoc, ← mul_assoc]
      rw [unsym_mul_self]
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← sub_eq_zero, ← mul_sub]
      convert! mul_zero (⅟(2 : α) * ⅟(2 : α))
      rw [add_sub_add_right_eq_sub, add_assoc, add_assoc, add_sub_add_left_eq_sub, add_comm,
        add_sub_add_right_eq_sub, sub_eq_zero]
    -- Rearrange RHS
    · rw [← mul_def, ← mul_def]

end SymAlg
