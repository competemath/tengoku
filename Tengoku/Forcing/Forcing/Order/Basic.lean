/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Seed.Order.Bounds.Defs
import Tengoku.Seed.Order.UpperLower.Closure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic forcing vocabulary

Compatibility of conditions and the density notions used throughout the forcing library, on an
arbitrary preorder.

**Orientation convention: smaller means stronger.** For conditions `p q : P`, `q ≤ p` means `q` is
a stronger condition than `p` (it carries more information). All public statements in this library
use this orientation; density notions are direct aliases of mathlib's coinitiality vocabulary,
which already points the right way.

## Main definitions

* `Forcing.Compatible p q`: the conditions `p` and `q` have a common strengthening.
* `Forcing.Incompatible p q`: they do not.
* `Forcing.IsDense D`: every condition has a strengthening in `D` (alias of `IsCoinitial D`).
* `Forcing.IsDenseBelow D p`: every strengthening of `p` has a further strengthening in `D`
  (alias of `IsCoinitialFor (Set.Iic p) D`).
* `Forcing.IsPredense D`: every condition is compatible with some member of `D`.
* `Forcing.IsDenseOpen D`: `D` is dense and closed under strengthening.

## Main results

* `Forcing.IsDense.isPredense`: dense sets are predense.
* `Forcing.isDense_iff_forall_isDenseBelow`: density is density below every condition.
* `Forcing.IsDenseBelow.mono_condition`, `Forcing.IsDenseBelow.trans`: density below a condition
  is stable under strengthening and transitive.
* `Forcing.IsDense.isDenseOpen_lowerClosure`: the downward closure of a dense set is dense open.
-/

namespace Forcing

variable {P : Type*} [Preorder P] {p q : P} {D E : Set P}

/-- Two conditions are *compatible* if they have a common strengthening.-/
def Compatible (p q : P) : Prop :=
  ∃ r, r ≤ p ∧ r ≤ q

/-- Two conditions are *incompatible* if they have no common strengthening.-/
def Incompatible (p q : P) : Prop :=
  ¬Compatible p q

instance : Std.Refl (Compatible : P → P → Prop) :=
  ⟨fun p ↦ ⟨p, le_rfl, le_rfl⟩⟩

instance : Std.Symm (Compatible : P → P → Prop) :=
  ⟨fun _ _ ⟨r, hp, hq⟩ ↦ ⟨r, hq, hp⟩⟩

/--
@isnad1 id=compatib.0h2v.s3.fd0f77048df0 from=translated src=- shape=e6608552 vocab=2cb5fcc5
-/
@[simp] theorem Compatible.refl (p : P) : Compatible p p :=
  Std.Refl.refl p

/--
@isnad1 id=compatib.1h3v.s4.5e637a367052 from=translated src=- shape=2da0c23b vocab=2cb5fcc5
-/
theorem Compatible.symm (h : Compatible p q) : Compatible q p :=
  Std.Symm.symm p q h

/--
@isnad1 id=iff.0h3v.s4.4b88cb8fabc9 from=translated src=- shape=bc89b7d4 vocab=2cb5fcc5
-/
theorem compatible_comm : Compatible p q ↔ Compatible q p :=
  ⟨.symm, .symm⟩

/--
@isnad1 id=compatib.1h3v.s4.9c04853112df from=translated src=- shape=12591dea vocab=47e67d57
-/
theorem Compatible.of_le (h : q ≤ p) : Compatible q p :=
  ⟨q, le_rfl, h⟩

/--
@isnad1 id=incompat.1h3v.s4.db9abc56639b from=translated src=- shape=2da0c23b vocab=e66f4493
-/
theorem Incompatible.symm (h : Incompatible p q) : Incompatible q p :=
  fun hc ↦ h hc.symm

/--
@isnad1 id=iff.0h3v.s4.65c3cb136d6d from=translated src=- shape=bc89b7d4 vocab=e66f4493
-/
theorem incompatible_comm : Incompatible p q ↔ Incompatible q p :=
  ⟨.symm, .symm⟩

/--
@isnad1 id=ne.1h3v.s4.b14e3e1ffeb1 from=translated src=- shape=4ab508a5 vocab=e66f4493
-/
theorem Incompatible.ne (h : Incompatible p q) : p ≠ q := by
  rintro rfl
  exact h (.refl p)

/--
@isnad1 id=not.0h2v.s3.400285a6d1bc from=translated src=- shape=d8399986 vocab=e66f4493
-/
@[simp] theorem not_incompatible_self (p : P) : ¬Incompatible p p :=
  fun h ↦ h (.refl p)

/-- A set of conditions is *dense* if every condition has a strengthening in it. This is
mathlib's `IsCoinitial`, already in forcing orientation.-/
abbrev IsDense (D : Set P) : Prop :=
  IsCoinitial D

/-- A set of conditions is *dense below `p`* if every strengthening of `p` has a further
strengthening in it. This is mathlib's `IsCoinitialFor` from the cone below `p`.-/
abbrev IsDenseBelow (D : Set P) (p : P) : Prop :=
  IsCoinitialFor (Set.Iic p) D

/-- A set of conditions is *predense* if every condition is compatible with one of its
members.-/
def IsPredense (D : Set P) : Prop :=
  ∀ p, ∃ q ∈ D, Compatible p q

/-- A set of conditions is *dense open* if it is dense and closed under strengthening.-/
def IsDenseOpen (D : Set P) : Prop :=
  IsDense D ∧ IsLowerSet D

/--
@isnad1 id=iff.0h2v.s4.1ee2de468fd7 from=translated src=- shape=18cb2c77 vocab=482d0751
-/
theorem isDense_iff_isCoinitial : IsDense D ↔ IsCoinitial D :=
  .rfl

/--
@isnad1 id=iff.0h3v.s4.ceaa5ae2899f from=translated src=- shape=3cbafaf5 vocab=6483da2d
-/
theorem isDenseBelow_iff_isCoinitialFor : IsDenseBelow D p ↔ IsCoinitialFor (Set.Iic p) D :=
  .rfl

/--
@isnad1 id=ispreden.1h2v.s4.a0147218401c from=translated src=- shape=93e860ac vocab=aae78d8e
-/
theorem IsDense.isPredense (h : IsDense D) : IsPredense D := by
  intro p
  obtain ⟨q, hqD, hqp⟩ := h p
  exact ⟨q, hqD, q, hqp, le_rfl⟩

/--
@isnad1 id=isdense.1h2v.s4.1769ad89e6d3 from=translated src=- shape=93e860ac vocab=ef712307
-/
theorem IsDenseOpen.isDense (h : IsDenseOpen D) : IsDense D :=
  h.1

/--
@isnad1 id=islowers.1h2v.s4.7ee8c25ac067 from=translated src=- shape=93e860ac vocab=14915596
-/
theorem IsDenseOpen.isLowerSet (h : IsDenseOpen D) : IsLowerSet D :=
  h.2

/--
@isnad1 id=isdenseb.1h3v.s4.f8b185c8a8e0 from=translated src=- shape=34f004a9 vocab=650fe40b
-/
theorem IsDense.isDenseBelow (h : IsDense D) (p : P) : IsDenseBelow D p :=
  fun q _ ↦ h q

/--
@isnad1 id=iff.0h2v.s4.6ef11e3dab4b from=translated src=- shape=079d69d3 vocab=650fe40b
-/
theorem isDense_iff_forall_isDenseBelow : IsDense D ↔ ∀ p, IsDenseBelow D p :=
  ⟨fun h p ↦ h.isDenseBelow p, fun h p ↦ h p (Set.mem_Iic.2 le_rfl)⟩

/--
@isnad1 id=isdenseb.0h2v.s3.c3b8cdc7de18 from=translated src=- shape=8d0018bb vocab=88304398
-/
theorem isDenseBelow_Iic (p : P) : IsDenseBelow (Set.Iic p) p :=
  fun q hq ↦ ⟨q, hq, le_rfl⟩

/-- Pullback stability: density below a condition persists to every strengthening of it. Note
that this is a genuinely local statement — `isDense_iff_forall_isDenseBelow` relates global to
local density but is not this theorem.
@isnad1 id=isdenseb.2h4v.s4.ca8d74d9f62f from=translated src=- shape=0f48043a vocab=edf41eaf
-/
theorem IsDenseBelow.mono_condition (hD : IsDenseBelow D p) (hqp : q ≤ p) : IsDenseBelow D q :=
  fun _ hr ↦ hD (Set.mem_Iic.2 ((Set.mem_Iic.1 hr).trans hqp))

/-- Transitivity: if `D` is dense below `p` and `E` is dense below every member of `D`, then `E`
is dense below `p`. Together with `IsDenseBelow.mono_condition` this is the coverage calculation
in forcing-order form; no sieve or Grothendieck-topology machinery is involved.
@isnad1 id=isdenseb.2h4v.s5.1b7d0f37b524 from=translated src=- shape=466e5840 vocab=1d130d9b
-/
theorem IsDenseBelow.trans (hD : IsDenseBelow D p) (hE : ∀ q ∈ D, IsDenseBelow E q) :
    IsDenseBelow E p := by
  intro q hq
  obtain ⟨r, hrD, hrq⟩ := hD hq
  obtain ⟨s, hsE, hsr⟩ := hE r hrD (Set.mem_Iic.2 le_rfl)
  exact ⟨s, hsE, hsr.trans hrq⟩

/-- The downward closure of a dense set is dense open.
@isnad1 id=isdenseo.1h2v.s5.64cab664f791 from=translated src=- shape=6bf7a1d2 vocab=f5814d7a
-/
theorem IsDense.isDenseOpen_lowerClosure (h : IsDense D) :
    IsDenseOpen (↑(lowerClosure D) : Set P) := by
  refine ⟨fun p ↦ ?_, (lowerClosure D).lower⟩
  obtain ⟨q, hqD, hqp⟩ := h p
  exact ⟨q, subset_lowerClosure hqD, hqp⟩

/-!
### Sanity examples

Small checks that the orientation and the distinctions between the density notions behave as
intended. In `ℕ` with the usual order, `0` strengthens everything, so `{0}` is dense; `{1}` is
predense (any two naturals are compatible via `0`) but not dense (nothing in it strengthens `0`).
-/

end Forcing
