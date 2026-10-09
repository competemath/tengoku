/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Archimedean.Real.Basic
public import Tengoku.Seed.Algebra.Order.Ring.Archimedean
public import Tengoku.Seed.Algebra.Ring.Subring.Order
public import Tengoku.Seed.Order.Quotient
public import Tengoku.Seed.RingTheory.Valuation.ValuationSubring

import Tengoku.Seed.Algebra.Order.Archimedean.Real.Hom

/-!
# Standard part function

Given a finite element in a non-archimedean field, the standard part function rounds it to the
unique closest real number. That is, it chops off any infinitesimals.

Let `K` be a linearly ordered field. The subset of finite elements (i.e. those bounded by a natural
number) is a `ValuationSubring`, which means we can construct its residue field
`FiniteResidueField`, roughly corresponding to the finite elements quotiented by infinitesimals.
This field inherits a `LinearOrder` instance, which makes it into an Archimedean linearly ordered
field, meaning we can uniquely embed it in the reals.

Given a finite element of the field, the `ArchimedeanClass.stdPart` function returns the real number
corresponding to this unique embedding. This function generalizes, among other things, the standard
part function on `Hyperreal`.

## References

* https://en.wikipedia.org/wiki/Standard_part_function
-/

@[expose] public noncomputable section

namespace ArchimedeanClass
variable
  {K : Type*} [LinearOrder K] [Field K] [IsOrderedRing K] {x y : K}
  {R : Type*} [LinearOrder R] [CommRing R] [IsStrictOrderedRing R] [Archimedean R]

/-! ### Finite residue field -/

variable (K) in
/-- The valuation subring of elements in non-negative Archimedean classes, i.e. elements bounded by
some natural number. -/
def FiniteElement : Type _ :=
  (addValuation K).toValuation.valuationSubring
deriving CommRing, IsDomain, ValuationRing, LinearOrder, IsStrictOrderedRing

namespace FiniteElement

/--
@isnad1 id=eq.0h1v.s9.6102c049c6bc from=seed src=0 shape=2ee773c9 vocab=b0c43ea0
-/
@[simp] theorem val_zero : (0 : FiniteElement K).1 = 0 := rfl
/--
@isnad1 id=eq.0h1v.s9.5e5aad76a108 from=seed src=0 shape=2ee773c9 vocab=b0c43ea0
-/
@[simp] theorem val_one : (1 : FiniteElement K).1 = 1 := rfl
/--
@isnad1 id=eq.0h3v.s10.5b585bee0950 from=seed src=0 shape=c4282ee0 vocab=9978b265
-/
@[simp] theorem val_add (x y : FiniteElement K) : (x + y).1 = x.1 + y.1 := rfl
/--
@isnad1 id=eq.0h3v.s10.fcf17ca37709 from=seed src=0 shape=c4282ee0 vocab=964d0348
-/
@[simp] theorem val_sub (x y : FiniteElement K) : (x - y).1 = x.1 - y.1 := rfl
/--
@isnad1 id=eq.0h3v.s10.6529a6bdb7e5 from=seed src=0 shape=c4282ee0 vocab=28b59758
-/
@[simp] theorem val_mul (x y : FiniteElement K) : (x * y).1 = x.1 * y.1 := rfl

/--
@isnad1 id=eq.1h3v.s9.0c06d5fe758d from=seed src=0 shape=f385a084 vocab=b0c43ea0
-/
@[ext] theorem ext {x y : FiniteElement K} (h : x.1 = y.1) : x = y := Subtype.ext h

/-- The constructor for `FiniteElement`. -/
protected def mk (x : K) (h : 0 ≤ mk x) : FiniteElement K := ⟨x, h⟩

/--
@isnad1 id=eq.0h1v.s6.67d8dfd0a603 from=seed src=0 shape=6d885a12 vocab=b4b602df
-/
@[simp] theorem mk_zero : FiniteElement.mk (0 : K) (by simp) = 0 := rfl
/--
@isnad1 id=eq.0h1v.s6.39b4bea583e5 from=seed src=0 shape=6d885a12 vocab=0508e957
-/
@[simp] theorem mk_one : FiniteElement.mk (1 : K) (by simp) = 1 := rfl
/--
@isnad1 id=eq.0h2v.s6.879cb86ad1cf from=seed src=0 shape=cfa28684 vocab=200b74bb
-/
@[simp] theorem mk_natCast (n : ℕ) : FiniteElement.mk (n : K) (mk_natCast_nonneg n) = n := rfl
/--
@isnad1 id=eq.0h2v.s6.9b0b0d4d28ab from=seed src=0 shape=cfa28684 vocab=5dcfc9a9
-/
@[simp] theorem mk_intCast (n : ℤ) : FiniteElement.mk (n : K) (mk_intCast_nonneg n) = n := rfl

/--
@isnad1 id=eq.1h2v.s8.7cf2f8c7df63 from=seed src=0 shape=9496cde8 vocab=e82f1823
-/
@[simp]
theorem neg_mk {x : K} (h : 0 ≤ mk x) :
    -FiniteElement.mk x h = FiniteElement.mk (-x) (by rwa [mk_neg]) :=
  rfl

/--
@isnad1 id=eq.2h3v.s8.26d7244d1746 from=seed src=0 shape=fda39bc7 vocab=bbd8ffd6
-/
@[simp]
theorem mk_add_mk (x y : K) (hx hy) :
    .mk x hx + .mk y hy = FiniteElement.mk (x + y) ((le_min hx hy).trans <| min_le_mk_add ..) :=
  rfl

/--
@isnad1 id=eq.2h3v.s8.05ad95a51750 from=seed src=0 shape=fda39bc7 vocab=4e3a0115
-/
@[simp]
theorem mk_sub_mk (x y : K) (hx hy) :
    .mk x hx - .mk y hy = FiniteElement.mk (x - y) ((le_min hx hy).trans <| min_le_mk_sub ..) :=
  rfl

/--
@isnad1 id=eq.2h3v.s9.7186df3bd30a from=seed src=0 shape=fda39bc7 vocab=2ad8b1b8
-/
@[simp]
theorem mk_mul_mk (x y : K) (hx hy) :
    .mk x hx * .mk y hy = FiniteElement.mk (x * y) (add_nonneg hx hy) :=
  rfl

/--
@isnad1 id=iff.2h3v.s8.1db444a85659 from=seed src=0 shape=90f0828a vocab=1138d180
-/
@[simp]
theorem mk_le_mk (x y : K) (hx hy) : FiniteElement.mk x hx ≤ .mk y hy ↔ x ≤ y :=
  .rfl

/--
@isnad1 id=iff.2h3v.s8.d09e04a87f5e from=seed src=0 shape=83fe6796 vocab=73d23dde
-/
@[simp]
theorem mk_lt_mk (x y : K) (hx hy) : FiniteElement.mk x hx < .mk y hy ↔ x < y :=
  .rfl

/--
@isnad1 id=iff.0h2v.s9.8531aff97a5f from=seed src=0 shape=310cfc0c vocab=6ed18598
-/
theorem not_isUnit_iff_mk_pos {x : FiniteElement K} : ¬ IsUnit x ↔ 0 < mk x.1 :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one

/--
@isnad1 id=iff.0h2v.s9.0e3d3b410d1f from=seed src=0 shape=7d5af77e vocab=b3b1cf58
-/
theorem isUnit_iff_mk_eq_zero {x : FiniteElement K} : IsUnit x ↔ mk x.1 = 0 := by
  rw [← not_iff_not, not_isUnit_iff_mk_pos, lt_iff_not_ge, x.2.ge_iff_eq']

instance : RatCast (FiniteElement K) where
  ratCast q := .mk q (mk_ratCast_nonneg q)

/--
@isnad1 id=eq.0h2v.s5.1b0d16e68481 from=seed src=0 shape=cfa28684 vocab=6fac7076
-/
@[simp] theorem mk_ratCast (q : ℚ) : FiniteElement.mk (q : K) (mk_ratCast_nonneg q) = q := rfl

@[no_expose]
instance : FloorRing (FiniteElement K) :=
  .ofBounded _ fun x ↦ by
    obtain ⟨n, hn⟩ := x.2
    refine ⟨n, (le_abs_self x).trans ?_⟩
    simpa using! hn

end FiniteElement

set_option backward.isDefEq.respectTransparency.types false in
variable (K) in
/-- The residue field of `FiniteElement`. This quotient inherits an order from `K`,
which makes it into a linearly ordered Archimedean field. -/
def FiniteResidueField : Type _ :=
  IsLocalRing.ResidueField (FiniteElement K)
deriving Field

namespace FiniteResidueField

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=ordconne.0h2v.s9.b0559f699d86 from=seed src=0 shape=38f21726 vocab=7354eeec
-/
instance ordConnected_preimage_mk' : ∀ x, Set.OrdConnected <| Quotient.mk
    (Submodule.quotientRel (IsLocalRing.maximalIdeal (FiniteElement K))) ⁻¹' {x} := by
  refine fun x ↦ ⟨?_⟩
  rintro x rfl y hy z ⟨hxz, hzy⟩
  have := hxz.trans hzy
  rw [Set.mem_preimage, Set.mem_singleton_iff, Quotient.eq, Submodule.quotientRel_def,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, FiniteElement.not_isUnit_iff_mk_pos] at hy ⊢
  apply hy.trans_le (mk_antitoneOn _ _ _) <;> simpa

set_option backward.isDefEq.respectTransparency.types false in
instance : LinearOrder (FiniteResidueField K) :=
  haveI := Classical.decRel fun x y : FiniteElement K ↦
    letI := Submodule.quotientRel (IsLocalRing.maximalIdeal (FiniteElement K))
    x ≈ y
  inferInstanceAs <| LinearOrder (Quotient _)

set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient map from finite elements on the field to the associated residue field. -/
def mk : FiniteElement K →+*o FiniteResidueField K where
  monotone' _ _ h := Quotient.mk_monotone h
  __ := IsLocalRing.residue (FiniteElement K)

/--
@isnad1 id=var.0h4v.s8.ac22aaceba39 from=seed src=0 shape=b4bab0a9 vocab=3e7daeed
-/
@[induction_eliminator]
theorem ind {motive : FiniteResidueField K → Prop} (mk : ∀ x, motive (mk x)) : ∀ x, motive x :=
  Quotient.ind mk

/--
@isnad1 id=ordconne.0h2v.s8.b38b6f460e29 from=seed src=0 shape=3d6c6cfc vocab=4c142740
-/
instance ordConnected_preimage_mk :
    ∀ x, Set.OrdConnected (mk ⁻¹' ({x} : Set (FiniteResidueField K))) :=
  ordConnected_preimage_mk'

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=iff.0h3v.s10.678a56e86c2d from=seed src=0 shape=13f0437f vocab=c4fbcd0c
-/
theorem mk_eq_mk {x y : FiniteElement K} : mk x = mk y ↔ 0 < ArchimedeanClass.mk (x.1 - y.1) := by
  apply Quotient.eq.trans
  rw [Submodule.quotientRel_def, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    FiniteElement.not_isUnit_iff_mk_pos, AddSubgroupClass.coe_sub]

/--
@isnad1 id=iff.0h2v.s9.40999ed8bece from=seed src=0 shape=14021985 vocab=66d61c88
-/
theorem mk_eq_zero {x : FiniteElement K} : mk x = 0 ↔ 0 < ArchimedeanClass.mk x.1 := by
  apply mk_eq_mk.trans
  simp

/--
@isnad1 id=iff.0h2v.s9.1d56ac112f2b from=seed src=0 shape=47422d50 vocab=a256df72
-/
theorem mk_ne_zero {x : FiniteElement K} : mk x ≠ 0 ↔ ArchimedeanClass.mk x.1 = 0 := by
  rw [ne_eq, mk_eq_zero, not_lt, x.2.ge_iff_eq']

/--
@isnad1 id=iff.0h3v.s10.dc1e2bdea394 from=seed src=0 shape=94ff959a vocab=c565908d
-/
theorem mk_le_mk {x y : FiniteElement K} : mk x ≤ mk y ↔ x ≤ y ∨ mk x = mk y := by
  refine (Quotient.mk_le_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

/--
@isnad1 id=iff.0h3v.s10.58c39741311b from=seed src=0 shape=94ff959a vocab=5718f990
-/
theorem mk_lt_mk {x y : FiniteElement K} : mk x < mk y ↔ x < y ∧ mk x ≠ mk y := by
  refine (Quotient.mk_lt_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

/--
@isnad1 id=lt.1h3v.s9.43e1d477fcfe from=seed src=0 shape=5636dffd vocab=5718f990
-/
theorem lt_of_mk_lt_mk {x y : FiniteElement K} (h : mk x < mk y) : x < y :=
  (mk_lt_mk.1 h).1

private theorem mul_le_mul_of_nonneg_left' {x y z : FiniteResidueField K} (h : x ≤ y) (hz : 0 ≤ z) :
    z * x ≤ z * y := by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  rw [← map_mul, ← map_mul]
  rw [← map_zero mk] at hz
  rw [mk_le_mk] at h hz ⊢
  grind [mul_le_mul_of_nonneg_left]

instance : IsOrderedRing (FiniteResidueField K) where
  zero_le_one := mk.monotone' zero_le_one
  add_le_add_left x y h z := by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    obtain h | h := mk_le_mk.1 h
    · exact mk.monotone' <| add_le_add_left h _
    · rw [h]
  mul_le_mul_of_nonneg_left _ hx _ _ h := mul_le_mul_of_nonneg_left' h hx
  mul_le_mul_of_nonneg_right x hx y z h := by
    simp_rw [mul_comm _ x]
    exact mul_le_mul_of_nonneg_left' h hx

instance : Archimedean (FiniteResidueField K) where
  arch x y hy := by
    induction x with | mk x
    induction y with | mk y
    obtain hx | hx := le_or_gt (mk x) 0
    · use 0
      rwa [zero_nsmul]
    · obtain ⟨n, hn⟩ := ((mk_ne_zero.1 hy.ne').trans (mk_ne_zero.1 hx.ne').symm).le
      refine ⟨n, mk.monotone' ?_⟩
      change x.1 ≤ n • y.1
      convert! ← hn
      · exact abs_of_pos <| lt_of_mk_lt_mk hx
      · exact abs_of_pos <| lt_of_mk_lt_mk hy

/--
@isnad1 id=eq.0h2v.s8.b5551c4d3a4c from=seed src=0 shape=58f4648a vocab=513d8ecd
-/
@[simp]
theorem mk_ratCast (q : ℚ) : mk (q : FiniteElement K) = q := by
  change mk (FiniteElement.mk ..) = _
  cases q with | div n d hd
  rw [← mul_left_inj' (c := ↑d) (mod_cast hd), ← map_natCast mk d, ← map_mul,
    ← FiniteElement.mk_natCast, FiniteElement.mk_mul_mk]
  simp_all

/-- An embedding from an Archimedean field into `K` induces an embedding into
`FiniteResidueField K`. -/
def ofArchimedean (f : R →+*o K) : R →+*o FiniteResidueField K where
  toFun r := mk <| .mk _ (mk_map_nonneg_of_archimedean f r)
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by
    simp_rw [map_add]
    exact mk.map_add
      (.mk _ (mk_map_nonneg_of_archimedean f x)) (.mk _ (mk_map_nonneg_of_archimedean f y))
  map_mul' x y := by
    simp_rw [map_mul]
    exact mk.map_mul
      (.mk _ (mk_map_nonneg_of_archimedean f x)) (.mk _ (mk_map_nonneg_of_archimedean f y))
  monotone' x y h := mk.monotone' <| f.monotone' h

/--
@isnad1 id=eq.0h4v.s9.0d1ee65d8f86 from=seed src=0 shape=4c1111a2 vocab=9dfac0a0
-/
theorem ofArchimedean_apply (f : R →+*o K) (r : R) :
    ofArchimedean f r = mk (.mk _ (mk_map_nonneg_of_archimedean f r)) :=
  rfl

/--
@isnad1 id=injectiv.0h3v.s8.b5fc767be9c6 from=seed src=0 shape=29e62e98 vocab=17b0c390
-/
theorem ofArchimedean_injective (f : R →+*o K) : Function.Injective (ofArchimedean f) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  contrapose! hr
  rw [ofArchimedean_apply, mk_ne_zero]
  exact mk_map_of_archimedean' f hr

/--
@isnad1 id=iff.0h5v.s9.a3403020a015 from=seed src=0 shape=068ced70 vocab=92c647ae
-/
@[simp]
theorem ofArchimedean_inj (f : R →+*o K) {x y : R} :
    ofArchimedean f x = ofArchimedean f y ↔ x = y :=
  (ofArchimedean_injective f).eq_iff

end FiniteResidueField

/-! ### Standard part -/

/-- The standard part of a `FiniteElement` is the unique real number with an infinitesimal
difference.

For any infinite inputs, this function outputs a junk value of 0. -/
@[no_expose]
def stdPart (x : K) : ℝ :=
  if h : 0 ≤ mk x then
    OrderRingHom.comp Classical.ofNonempty FiniteResidueField.mk (.mk x h) else 0

/--
@isnad1 id=eq.1h3v.s9.b00f963e19ad from=seed src=0 shape=d15995bd vocab=e8078136
-/
theorem stdPart_of_mk_nonneg (f : FiniteResidueField K →+*o ℝ) (h : 0 ≤ mk x) :
    stdPart x = f (.mk <| .mk x h) := by
  rw [stdPart, dite_eq_left h, OrderRingHom.comp_apply]
  congr
  exact Subsingleton.allEq _ _

/--
@isnad1 id=iff.0h2v.s6.80583e3d5294 from=seed src=0 shape=93bf1b85 vocab=e5272918
-/
@[simp]
theorem stdPart_eq_zero {x : K} : stdPart x = 0 ↔ mk x ≠ 0 where
  mpr h := by
    obtain h | h := h.lt_or_gt
    · exact dite_eq_right h.not_ge
    · rw [stdPart, dite_eq_left h.le, OrderRingHom.comp_apply, FiniteResidueField.mk_eq_zero.2 h,
        map_zero]
  mp := by
    contrapose!
    intro h
    rwa [stdPart_of_mk_nonneg Classical.ofNonempty h.ge, map_ne_zero, FiniteResidueField.mk_ne_zero]

/--
@isnad1 id=eq.1h2v.s6.4ca38b6ab4b4 from=seed src=0 shape=cd233fa4 vocab=e5272918
-/
alias ⟨_, stdPart_of_mk_ne_zero⟩ := stdPart_eq_zero

/--
@isnad1 id=monotone.0h1v.s7.6daaf1047336 from=seed src=0 shape=2d62cc42 vocab=3eaaf9dd
-/
theorem stdPart_monotoneOn : MonotoneOn stdPart {x : K | 0 ≤ mk x} := by
  intro x (hx : 0 ≤ mk x) y (hy : 0 ≤ mk y) h
  unfold stdPart
  rw [dite_eq_left hx, dite_eq_left hy]
  apply OrderRingHom.monotone'
  rwa [FiniteElement.mk_le_mk]

/--
@isnad1 id=eq.0h1v.s5.1a98835ceb7e from=seed src=0 shape=4ba56750 vocab=bb6db836
-/
@[simp]
theorem stdPart_zero : stdPart (0 : K) = 0 := by
  rw [stdPart, dite_eq_left] <;> simp

/--
@isnad1 id=eq.0h1v.s5.d7abb4f03438 from=seed src=0 shape=4ba56750 vocab=bb6db836
-/
@[simp]
theorem stdPart_one : stdPart (1 : K) = 1 := by
  rw [stdPart, dite_eq_left] <;> simp

/--
@isnad1 id=eq.0h2v.s6.87b773a79573 from=seed src=0 shape=3f038156 vocab=f8e66bf5
-/
@[simp]
theorem stdPart_neg (x : K) : stdPart (-x) = -stdPart x := by
  simp_rw [stdPart, ArchimedeanClass.mk_neg]
  split_ifs
  · rw [← FiniteElement.neg_mk, map_neg]
  · simp

/--
@isnad1 id=eq.0h2v.s5.2ede2fdecc73 from=seed src=0 shape=3f038156 vocab=6bea20c8
-/
@[simp]
theorem stdPart_inv (x : K) : stdPart x⁻¹ = (stdPart x)⁻¹ := by
  obtain hx | hx := eq_or_ne (mk x) 0
  · unfold stdPart
    have hx' : 0 ≤ mk x⁻¹ := by simp_all
    rw [dite_eq_left hx.ge, dite_eq_left hx']
    · apply eq_inv_of_mul_eq_one_left
      suffices FiniteElement.mk x⁻¹ hx' * .mk x hx.ge = 1 by
        rw [← map_mul, this, map_one]
      ext
      apply inv_mul_cancel₀
      aesop
  · rw [stdPart_of_mk_ne_zero hx, stdPart_of_mk_ne_zero, inv_zero]
    rwa [mk_inv, neg_ne_zero]

/--
@isnad1 id=eq.2h3v.s8.4112982bc081 from=seed src=0 shape=8a93f8f6 vocab=0d93773e
-/
theorem stdPart_add (hx : 0 ≤ mk x) (hy : 0 ≤ mk y) : stdPart (x + y) = stdPart x + stdPart y := by
  unfold stdPart
  rw [dite_eq_left hx, dite_eq_left hy, dite_eq_left]
  exact map_add _ (FiniteElement.mk x hx) (.mk y hy)

/--
@isnad1 id=eq.1h3v.s7.071da33f21a9 from=seed src=0 shape=c7d4c5b5 vocab=ec79a440
-/
theorem stdPart_add_eq_right (hx : 0 < mk x) : stdPart (x + y) = stdPart y := by
  obtain hy | hy := le_or_gt 0 (mk y)
  · rw [stdPart_add hx.le hy, stdPart_of_mk_ne_zero hx.ne', zero_add]
  · rw [stdPart_of_mk_ne_zero hy.ne, stdPart_of_mk_ne_zero]
    rw [mk_add_eq_mk_right (hy.trans hx)]
    exact hy.ne

/--
@isnad1 id=eq.1h3v.s7.5d1a2028bd3f from=seed src=0 shape=fbe65b58 vocab=ec79a440
-/
theorem stdPart_add_eq_left (hy : 0 < mk y) : stdPart (x + y) = stdPart x := by
  rw [add_comm, stdPart_add_eq_right hy]

/--
@isnad1 id=eq.2h3v.s8.1b94518bf32b from=seed src=0 shape=8a93f8f6 vocab=4e84909e
-/
theorem stdPart_sub (hx : 0 ≤ mk x) (hy : 0 ≤ mk y) : stdPart (x - y) = stdPart x - stdPart y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, stdPart_add hx, stdPart_neg]
  rwa [mk_neg]

/--
@isnad1 id=eq.1h3v.s7.6d27588d7ab9 from=seed src=0 shape=271f51c5 vocab=95d368b8
-/
theorem stdPart_sub_eq_right (hx : 0 < mk x) : stdPart (x - y) = -stdPart y := by
  rw [sub_eq_add_neg, stdPart_add_eq_right hx, stdPart_neg]

/--
@isnad1 id=eq.1h3v.s7.b91b53937155 from=seed src=0 shape=fbe65b58 vocab=2f68c8e7
-/
theorem stdPart_sub_eq_left (hy : 0 < mk y) : stdPart (x - y) = stdPart x := by
  rw [sub_eq_add_neg, stdPart_add_eq_left (by simpa)]

/--
@isnad1 id=eq.2h3v.s8.45c6938dd78c from=seed src=0 shape=8a93f8f6 vocab=d806ce30
-/
theorem stdPart_mul (hx : 0 ≤ mk x) (hy : 0 ≤ mk y) : stdPart (x * y) = stdPart x * stdPart y := by
  unfold stdPart
  rw [dite_eq_left hx, dite_eq_left hy, dite_eq_left]
  exact map_mul _ (FiniteElement.mk x hx) (.mk y hy)

/--
@isnad1 id=eq.2h3v.s8.8a7f520e9034 from=seed src=0 shape=5133cd70 vocab=dbcbdfaa
-/
theorem stdPart_div (hx : 0 ≤ mk x) (hy : 0 ≤ -mk y) :
    stdPart (x / y) = stdPart x / stdPart y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, stdPart_mul hx, stdPart_inv]
  rwa [mk_inv]

/--
@isnad1 id=eq.0h2v.s5.d2b70420f61e from=seed src=0 shape=627e3b57 vocab=cb27b491
-/
@[simp]
theorem stdPart_ratCast (q : ℚ) : stdPart (q : K) = q := by
  rw [stdPart_of_mk_nonneg Classical.ofNonempty (mk_ratCast_nonneg q), FiniteElement.mk_ratCast,
    FiniteResidueField.mk_ratCast, map_ratCast]

/--
@isnad1 id=eq.0h2v.s5.126602b1b5a3 from=seed src=0 shape=627e3b57 vocab=7568f922
-/
@[simp]
theorem stdPart_intCast (n : ℤ) : stdPart (n : K) = n :=
  mod_cast stdPart_ratCast n

/--
@isnad1 id=eq.0h2v.s5.1d4af996f433 from=seed src=0 shape=627e3b57 vocab=14c33f26
-/
@[simp]
theorem stdPart_natCast (n : ℕ) : stdPart (n : K) = n :=
  mod_cast stdPart_intCast n

/--
@isnad1 id=eq.0h2v.s5.b9bf1245201d from=seed src=0 shape=4eaed06c vocab=2d10ac20
-/
@[simp]
theorem stdPart_ofNat (n : ℕ) [n.AtLeastTwo] : stdPart (ofNat(n) : K) = n :=
  stdPart_natCast n

/--
@isnad1 id=eq.0h3v.s6.48084263f4fb from=seed src=0 shape=7d03b479 vocab=f20bd210
-/
@[simp]
theorem stdPart_map_real (f : ℝ →+*o K) (r : ℝ) : stdPart (f r) = r := by
  rw [stdPart, dite_eq_left]
  exact r.ringHom_apply <| OrderRingHom.comp _ (FiniteResidueField.ofArchimedean f)

/--
@isnad1 id=eq.0h1v.s3.d0a5539a0125 from=seed src=0 shape=9023e767 vocab=0c1638a8
-/
@[simp]
theorem stdPart_real (r : ℝ) : stdPart r = r :=
  stdPart_map_real (.id ℝ) r

/--
@isnad1 id=eq.1h3v.s9.b388b7641618 from=seed src=0 shape=6500e3bd vocab=1912557c
-/
theorem ofArchimedean_stdPart (f : ℝ →+*o K) (hx : 0 ≤ mk x) :
    FiniteResidueField.ofArchimedean f (stdPart x) = .mk (.mk x hx) := by
  rw [stdPart, dite_eq_left hx, ← OrderRingHom.comp_apply, ← OrderRingHom.comp_assoc,
    OrderRingHom.comp_apply, OrderRingHom.apply_eq_self]

/--
@isnad1 id=le.1h2v.s6.aca5597e1626 from=seed src=0 shape=8199c0f2 vocab=03422b0a
-/
theorem stdPart_nonneg {x : K} (h : 0 ≤ x) : 0 ≤ stdPart x := by
  obtain hx | hx := eq_or_ne (ArchimedeanClass.mk x) 0
  · rw [stdPart, dite_eq_left hx.ge]
    exact map_nonneg _ h
  · rw [stdPart_of_mk_ne_zero hx]

/--
@isnad1 id=le.1h2v.s6.1bb2e61c9e4d from=seed src=0 shape=53bfea19 vocab=03422b0a
-/
theorem stdPart_nonpos {x : K} (h : x ≤ 0) : stdPart x ≤ 0 := by
  simpa using stdPart_nonneg (neg_nonneg.2 h)

/-- The standard part of `x` is the unique real `r` such that `x - r` is infinitesimal.
@isnad1 id=iff.1h4v.s8.9f95be62767c from=seed src=0 shape=786ac4de vocab=0d5e5e32
-/
theorem mk_sub_pos_iff (f : ℝ →+*o K) {r : ℝ} (hx : 0 ≤ mk x) :
    0 < mk (x - f r) ↔ stdPart x = r := by
  refine (FiniteResidueField.mk_eq_zero
    (x := .mk x hx - .mk _ (mk_map_nonneg_of_archimedean f r))).symm.trans ?_
  rw [map_sub, ← FiniteResidueField.ofArchimedean_apply, ← ofArchimedean_stdPart f hx,
    sub_eq_zero, FiniteResidueField.ofArchimedean_inj f]

/--
@isnad1 id=lt.1h3v.s8.4b0367bbbc70 from=seed src=0 shape=33af1632 vocab=0d5e5e32
-/
theorem mk_sub_stdPart_pos (f : ℝ →+*o K) (hx : 0 ≤ mk x) : 0 < mk (x - f (stdPart x)) :=
  (mk_sub_pos_iff f hx).2 rfl

/--
@isnad1 id=lt.2h4v.s8.2e0802b9951f from=seed src=0 shape=76677f17 vocab=295f868a
-/
theorem lt_of_lt_stdPart (f : ℝ →+*o K) {r : ℝ} (hx : 0 ≤ mk x) (h : r < stdPart x) : f r < x := by
  rw [← sub_lt_sub_iff_right (c := f (stdPart x)), ← map_sub]
  apply lt_of_mk_lt_mk_of_nonpos
  · rw [mk_map_of_archimedean', mk_sub_pos_iff f hx]
    rw [ne_eq, sub_eq_zero]
    exact h.ne
  · simpa using f.monotone' h.le

/--
@isnad1 id=lt.2h4v.s8.8592f3842b9a from=seed src=0 shape=9876142a vocab=295f868a
-/
theorem lt_of_stdPart_lt (f : ℝ →+*o K) {r : ℝ} (hx : 0 ≤ mk x) (h : stdPart x < r) : x < f r := by
  rw [← neg_lt_neg_iff, ← map_neg]
  apply lt_of_lt_stdPart <;> simpa

/--
@isnad1 id=le.2h4v.s8.ee0353444a9f from=seed src=0 shape=79565075 vocab=a1910e05
-/
theorem stdPart_le_of_le (f : ℝ →+*o K) {r : ℝ} (hx : 0 ≤ mk x) (h : x ≤ f r) : stdPart x ≤ r :=
  le_imp_le_iff_lt_imp_lt.2 (lt_of_lt_stdPart f hx) h

/--
@isnad1 id=le.2h4v.s8.42ac4b15f951 from=seed src=0 shape=f0e6993a vocab=a1910e05
-/
theorem le_stdPart_of_le (f : ℝ →+*o K) {r : ℝ} (hx : 0 ≤ mk x) (h : f r ≤ x) : r ≤ stdPart x :=
  le_imp_le_iff_lt_imp_lt.2 (lt_of_stdPart_lt f hx) h

/--
@isnad1 id=eq.2h4v.s7.4268e0bb1403 from=seed src=0 shape=7acf3bdb vocab=6f767644
-/
theorem stdPart_eq (f : ℝ →+*o K) {r : ℝ} (hl : ∀ s < r, f s ≤ x) (hr : ∀ s > r, x ≤ f s) :
    stdPart x = r := by
  have hx : 0 ≤ mk x := by
    apply mk_nonneg_of_le_of_le_of_archimedean f (hl (r - 1) _) (hr (r + 1) _) <;> simp
  obtain h | rfl | h := lt_trichotomy (stdPart x) r
  · obtain ⟨s, hs, hs'⟩ := exists_between h
    cases (le_stdPart_of_le f hx (hl _ hs')).not_gt hs
  · rfl
  · obtain ⟨s, hs, hs'⟩ := exists_between h
    cases (stdPart_le_of_le f hx (hr _ hs)).not_gt hs'

/--
@isnad1 id=eq.0h3v.s7.ee65ee3b641d from=seed src=0 shape=ee2f0dd2 vocab=59cc6cdf
-/
theorem stdPart_eq_sInf (f : ℝ →+*o K) (x : K) : stdPart x = sInf {r | x < f r} := by
  obtain hx | hx := le_or_gt 0 (mk x)
  · obtain ⟨a, ha⟩ := exists_int_lt_of_mk_nonneg hx
    obtain ⟨b, hb⟩ := exists_int_gt_of_mk_nonneg hx
    have hn : {r | x < f r}.Nonempty := ⟨b, by simpa using hb⟩
    have hb : BddBelow {r | x < f r} := by
      refine ⟨a, fun r hr ↦ ?_⟩
      by_contra! hra
      exact (f.monotone' hra.le).not_gt (by simpa using ha.trans hr)
    apply stdPart_eq f <;> intro r hr
    · simpa using notMem_of_lt_csInf hr hb
    · obtain ⟨s, hs, hs'⟩ := (csInf_lt_iff hb hn).1 hr
      exact hs.le.trans (f.monotone' hs'.le)
  · rw [stdPart_of_mk_ne_zero hx.ne]
    have hr {r} := hx.trans_le (mk_map_nonneg_of_archimedean f r)
    obtain h | h := le_or_gt 0 x
    · convert! Real.sInf_empty.symm
      rw [Set.eq_empty_iff_forall_notMem]
      exact fun r ↦ (lt_of_mk_lt_mk_of_nonneg hr h).not_gt
    · convert! Real.sInf_univ.symm
      rw [Set.eq_univ_iff_forall]
      exact fun r ↦ lt_of_mk_lt_mk_of_nonpos hr h.le

/--
@isnad1 id=eq.0h3v.s7.9a0cfd452e8d from=seed src=0 shape=b870b042 vocab=9ac9048d
-/
theorem stdPart_eq_sSup (f : ℝ →+*o K) (x : K) : stdPart x = sSup {r | f r < x} := by
  rw [← neg_inj, ← stdPart_neg, stdPart_eq_sInf f, ← Real.sInf_neg]
  congr 1
  ext
  simp [neg_lt]

end ArchimedeanClass
