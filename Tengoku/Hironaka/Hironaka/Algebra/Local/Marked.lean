/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Tengoku.Hironaka.Hironaka.Algebra.Local.Order
public import Tengoku.Seed.RingTheory.RegularLocalRing.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Marked ideals and their cosupport

A *marked ideal* [Kol07, Definitions 48 and 59] is a pair `(I, m)` of an ideal and a natural
number, the mark being the order one pretends `I` has; a *marked element* (Kollár: marked
function) is a pair `(f, m)`.  This file gives the local, ring-level forms: the cosupport
predicate says `m ≤ ord I` ("the closed point lies in `cosupp (I, m)`"); products add the marks
and sums are defined for equal marks only; the four elementary properties of the cosupport
listed in [Kol07, Definition 59] are restatements of the calculus of the order
(`Hironaka/Algebra/Local/Order.lean`).  The marked derivative `D(I, m) = (D(I), m - 1)` acts on this
structure in `Hironaka/Algebra/Local/Derivative.lean`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing

/-- **A marked ideal** [Kol07, Definitions 48 and 59]: an ideal `I` together with a mark
`m : ℕ`.-/
@[ext]
structure MarkedIdeal (R : Type*) [CommRing R] where
  /-- The ideal.-/
  I : Ideal R
  /-- The mark.-/
  m : ℕ

/-- **A marked element** (Kollár's "marked function", [Kol07, Definition 59]): an element `f`
together with a mark `m : ℕ`.-/
@[ext]
structure MarkedElem (R : Type*) where
  /-- The element.-/
  f : R
  /-- The mark.-/
  m : ℕ

namespace MarkedIdeal

variable {R : Type*} [CommRing R]

/-- The product `(I₁, m₁) · (I₂, m₂) = (I₁ I₂, m₁ + m₂)` [Kol07, Definition 59].-/
instance : Mul (MarkedIdeal R) := ⟨fun J K => ⟨J.I * K.I, J.m + K.m⟩⟩

/--
@isnad1 id=eq.0h3v.s6.7d45f6b6e9d6 from=translated src=- shape=e69ef69b vocab=780ccbc4
-/
@[simp] theorem mul_I (J K : MarkedIdeal R) : (J * K).I = J.I * K.I := rfl

/--
@isnad1 id=eq.0h3v.s5.21507795a9e9 from=translated src=- shape=2947689f vocab=00a4108b
-/
@[simp] theorem mul_m (J K : MarkedIdeal R) : (J * K).m = J.m + K.m := rfl

/--
@isnad1 id=eq.0h3v.s6.8743fcb35281 from=translated src=- shape=7cdcc7e2 vocab=426fa68c
-/
theorem mul_def (J K : MarkedIdeal R) : J * K = ⟨J.I * K.I, J.m + K.m⟩ := rfl

/-- The sum `(I₁, m) + (I₂, m) = (I₁ + I₂, m)`, "only sensible when the markings are the same"
[Kol07, Definition 59].-/
def add (J K : MarkedIdeal R) (_h : J.m = K.m) : MarkedIdeal R := ⟨J.I ⊔ K.I, J.m⟩

/--
@isnad1 id=eq.1h3v.s6.a04e35403e8a from=translated src=- shape=0c07e3c0 vocab=13637091
-/
@[simp] theorem add_I (J K : MarkedIdeal R) (h : J.m = K.m) : (J.add K h).I = J.I ⊔ K.I := rfl

/--
@isnad1 id=eq.1h3v.s5.c8d3ea6c939f from=translated src=- shape=8f478045 vocab=969ba2cd
-/
@[simp] theorem add_m (J K : MarkedIdeal R) (h : J.m = K.m) : (J.add K h).m = J.m := rfl

section Local

variable [IsLocalRing R]

/-- The local cosupport predicate: "the closed point lies in `cosupp (I, m)`"
[Kol07, Definition 59], i.e. `m ≤ ord I`.-/
def InCosupp (J : MarkedIdeal R) : Prop := (J.m : ℕ∞) ≤ ord J.I

/--
@isnad1 id=iff.0h2v.s7.c5781649916a from=translated src=- shape=92c2c1ff vocab=e2cc12ae
-/
theorem inCosupp_iff_le_pow (J : MarkedIdeal R) : J.InCosupp ↔ J.I ≤ maximalIdeal R ^ J.m :=
  le_ord_iff

/-- `cosupp (J, m) ⊆ cosupp (I, m)` for `I ≤ J` (property (1) of [Kol07, Definition 59]).
@isnad1 id=incosupp.2h4v.s6.59e227163111 from=translated src=- shape=f9476ceb vocab=db8e46e6
-/
theorem inCosupp_anti {I J : Ideal R} {m : ℕ} (h : I ≤ J) (hJ : InCosupp ⟨J, m⟩) :
    InCosupp ⟨I, m⟩ :=
  hJ.trans (ord_anti h)

/-- `cosupp (I₁, m₁) ∩ cosupp (I₂, m₂) ⊆ cosupp (I₁ I₂, m₁ + m₂)` (property (2) of
[Kol07, Definition 59]).
@isnad1 id=incosupp.2h3v.s5.780d9801f5b7 from=translated src=- shape=c3c55775 vocab=cfdbe1ec
-/
theorem inCosupp_mul {J K : MarkedIdeal R} (hJ : J.InCosupp) (hK : K.InCosupp) :
    (J * K).InCosupp := by
  unfold InCosupp at *
  rw [mul_I, mul_m, Nat.cast_add]
  exact (add_le_add hJ hK).trans (le_ord_mul _ _)

/-- `cosupp (I, m) ⊆ cosupp (I^c, mc)`: the inclusion of property (3) of [Kol07, Definition 59]
valid in every local ring.
@isnad1 id=incosupp.1h3v.s6.734b641a60be from=translated src=- shape=fcf0b807 vocab=177ce9e0
-/
theorem inCosupp_pow {J : MarkedIdeal R} (c : ℕ) (h : J.InCosupp) :
    InCosupp ⟨J.I ^ c, J.m * c⟩ := by
  unfold InCosupp at *
  dsimp only
  rw [Nat.cast_mul, mul_comm]
  exact (mul_le_mul_of_nonneg_left h zero_le).trans (le_ord_pow _ _)

/-- `cosupp (I₁ + I₂, m) = cosupp (I₁, m) ∩ cosupp (I₂, m)` (property (4) of
[Kol07, Definition 59]).
@isnad1 id=iff.1h3v.s5.fbccdac30807 from=translated src=- shape=5b32c679 vocab=2a4bb8c7
-/
theorem inCosupp_add_iff {J K : MarkedIdeal R} (h : J.m = K.m) :
    (J.add K h).InCosupp ↔ J.InCosupp ∧ K.InCosupp := by
  unfold InCosupp
  rw [add_I, add_m, ord_sup, le_min_iff, h]

end Local

section Regular

variable [IsRegularLocalRing R]

/-- `cosupp (I, m) = cosupp (I^c, mc)` for `c ≥ 1` (property (3) of [Kol07, Definition 59]),
given multiplicativity of the order on elements (through `ord (I^c) = c · ord I`,
`ord_pow_of_ordElem_mul`).
@isnad1 id=iff.2h3v.s7.3330b3ff3979 from=translated src=- shape=52dd3ed2 vocab=ca9c7e09
-/
theorem inCosupp_pow_iff_of_ordElem_mul
    (hmul : ∀ f g : R, ordElem (f * g) = ordElem f + ordElem g) (J : MarkedIdeal R) {c : ℕ}
    (hc : 1 ≤ c) : J.InCosupp ↔ InCosupp ⟨J.I ^ c, J.m * c⟩ := by
  refine ⟨inCosupp_pow c, fun h => ?_⟩
  unfold InCosupp at *
  dsimp only at h
  rw [ord_pow_of_ordElem_mul hmul J.I hc, Nat.cast_mul, mul_comm] at h
  exact (ENat.mul_le_mul_left_iff (by exact_mod_cast (show c ≠ 0 by omega))
    (ENat.natCast_ne_top c)).mp h

end Regular

end MarkedIdeal

namespace MarkedElem

variable {R : Type*}

/-- `(f₁, m₁) · (f₂, m₂) = (f₁ f₂, m₁ + m₂)` [Kol07, Definition 59].-/
instance [Mul R] : Mul (MarkedElem R) := ⟨fun a b => ⟨a.f * b.f, a.m + b.m⟩⟩

/--
@isnad1 id=eq.0h3v.s5.97ec5a0333ef from=translated src=- shape=0090f101 vocab=f44980c1
-/
@[simp] theorem mul_f [Mul R] (a b : MarkedElem R) : (a * b).f = a.f * b.f := rfl

/--
@isnad1 id=eq.0h3v.s5.f7f9c850482d from=translated src=- shape=2947689f vocab=9fc96686
-/
@[simp] theorem mul_m [Mul R] (a b : MarkedElem R) : (a * b).m = a.m + b.m := rfl

/--
@isnad1 id=eq.0h3v.s5.13eb174022fd from=translated src=- shape=04e0dc8f vocab=5da2a569
-/
theorem mul_def [Mul R] (a b : MarkedElem R) : a * b = ⟨a.f * b.f, a.m + b.m⟩ := rfl

/-- `(f₁, m) + (f₂, m) = (f₁ + f₂, m)` for equal marks [Kol07, Definition 59].-/
def add [Add R] (a b : MarkedElem R) (_h : a.m = b.m) : MarkedElem R := ⟨a.f + b.f, a.m⟩

/--
@isnad1 id=eq.1h3v.s5.48dacb3f8d3d from=translated src=- shape=f33c502f vocab=1c08458b
-/
@[simp] theorem add_f [Add R] (a b : MarkedElem R) (h : a.m = b.m) : (a.add b h).f = a.f + b.f :=
  rfl

/--
@isnad1 id=eq.1h3v.s5.115ca6ea53ea from=translated src=- shape=8f478045 vocab=126eb488
-/
@[simp] theorem add_m [Add R] (a b : MarkedElem R) (h : a.m = b.m) : (a.add b h).m = a.m := rfl

variable [CommRing R]

/-- The marked ideal `(⟨f⟩, m)` of a marked element `(f, m)`.-/
def toMarkedIdeal (a : MarkedElem R) : MarkedIdeal R := ⟨Ideal.span {a.f}, a.m⟩

/--
@isnad1 id=eq.0h2v.s5.d5dd4db25943 from=translated src=- shape=b09fee5e vocab=10a5bf1f
-/
@[simp] theorem toMarkedIdeal_I (a : MarkedElem R) : a.toMarkedIdeal.I = Ideal.span {a.f} := rfl

/--
@isnad1 id=eq.0h2v.s4.c522f347dc01 from=translated src=- shape=cb7da94c vocab=cb0ba865
-/
@[simp] theorem toMarkedIdeal_m (a : MarkedElem R) : a.toMarkedIdeal.m = a.m := rfl

/--
@isnad1 id=eq.0h3v.s6.7982538510c1 from=translated src=- shape=e69ef69b vocab=76ba0dff
-/
theorem toMarkedIdeal_mul (a b : MarkedElem R) :
    (a * b).toMarkedIdeal = a.toMarkedIdeal * b.toMarkedIdeal :=
  MarkedIdeal.ext (Ideal.span_singleton_mul_span_singleton _ _).symm rfl

variable [IsLocalRing R]

/-- The cosupport predicate for marked elements: `m ≤ ord f`.-/
def InCosupp (a : MarkedElem R) : Prop := (a.m : ℕ∞) ≤ ordElem a.f

/--
@isnad1 id=iff.0h2v.s4.aa3d644403e1 from=translated src=- shape=69fc15e4 vocab=3e9d94bf
-/
theorem inCosupp_toMarkedIdeal (a : MarkedElem R) : a.toMarkedIdeal.InCosupp ↔ a.InCosupp :=
  Iff.rfl

/--
@isnad1 id=iff.0h2v.s6.765b4b8146e9 from=translated src=- shape=e184621b vocab=49e46608
-/
theorem inCosupp_iff_mem_pow (a : MarkedElem R) : a.InCosupp ↔ a.f ∈ maximalIdeal R ^ a.m :=
  mem_maximalIdeal_pow_iff_le_ordElem.symm

end MarkedElem

end IsLocalRing
