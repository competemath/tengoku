/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Star.NonUnitalSubsemiring
public import Tengoku.Seed.Algebra.Ring.Subsemiring.Basic

/-!
# Star subrings

A \*-subring is a subring of a \*-ring which is closed under `*`.
-/

@[expose] public section

universe v

/-- A (unital) star subsemiring is a non-associative ring which is closed under the `star`
operation. -/
structure StarSubsemiring (R : Type v) [NonAssocSemiring R] [Star R] : Type v
    extends Subsemiring R where
  /-- The `carrier` of a `StarSubsemiring` is closed under the `star` operation. -/
  star_mem' {a} : a ∈ carrier → star a ∈ carrier

section StarSubsemiring

namespace StarSubsemiring

/-- Reinterpret a `StarSubsemiring` as a `Subsemiring`. -/
add_decl_doc StarSubsemiring.toSubsemiring

instance setLike {R : Type v} [NonAssocSemiring R] [Star R] :
    SetLike (StarSubsemiring R) R where
  coe {s} := s.carrier
  coe_injective p q h := by obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩ := p; cases q; congr

instance {R : Type v} [NonAssocSemiring R] [Star R] : PartialOrder (StarSubsemiring R) :=
  .ofSetLike (StarSubsemiring R) R

initialize_simps_projections StarSubsemiring (carrier → coe, as_prefix coe)

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

/-- The actual `StarSubsemiring` obtained from an element of a `StarSubsemiringClass`. -/
@[simps]
def ofClass {S R : Type*} [NonAssocSemiring R] [SetLike S R] [StarRing R] [SubsemiringClass S R]
    [StarMemClass S R] (s : S) : StarSubsemiring R where
  carrier := s
  add_mem' := add_mem
  zero_mem' := zero_mem _
  mul_mem' := mul_mem
  one_mem' := one_mem _
  star_mem' := star_mem

instance (priority := 100) : CanLift (Set R) (StarSubsemiring R) (↑)
    (fun s ↦ 0 ∈ s ∧ (∀ {x y}, x ∈ s → y ∈ s → x + y ∈ s) ∧ 1 ∈ s ∧
      (∀ {x y}, x ∈ s → y ∈ s → x * y ∈ s) ∧ (∀ {x}, x ∈ s → star x ∈ s)) where
  prf s h :=
    ⟨ { carrier := s
        zero_mem' := h.1
        add_mem' := h.2.1
        one_mem' := h.2.2.1
        mul_mem' := h.2.2.2.1
        star_mem' := h.2.2.2.2 },
      rfl ⟩

/--
@isnad1 id=starmemc.0h1v.s6.bd1ee0f85f0a from=seed src=0 shape=338784ee vocab=532545c5
-/
instance starMemClass : StarMemClass (StarSubsemiring R) R where
  star_mem {s} := s.star_mem'

/--
@isnad1 id=subsemir.0h1v.s5.97aa42773693 from=seed src=0 shape=338784ee vocab=98c39f9b
-/
instance subsemiringClass : SubsemiringClass (StarSubsemiring R) R where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'
  one_mem {s} := s.one_mem'

-- this uses the `Star` instance `s` inherits from `StarMemClass (StarSubsemiring R A) A`
instance starRing (s : StarSubsemiring R) : StarRing s :=
  { StarMemClass.instStar s with
    star_involutive := fun r => Subtype.ext (star_star (r : R))
    star_mul := fun r₁ r₂ => Subtype.ext (star_mul (r₁ : R) (r₂ : R))
    star_add := fun r₁ r₂ => Subtype.ext (star_add (r₁ : R) (r₂ : R)) }

instance semiring (s : StarSubsemiring R) : NonAssocSemiring s :=
  s.toSubsemiring.toNonAssocSemiring

/--
@isnad1 id=iff.0h3v.s7.54c4973e7eec from=seed src=0 shape=c23fe308 vocab=6ec7fcdd
-/
theorem mem_carrier {s : StarSubsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

/--
@isnad1 id=eq.1h3v.s7.a27706f77bc3 from=seed src=0 shape=660c7984 vocab=27f7f9c7
-/
@[ext]
theorem ext {S T : StarSubsemiring R} (h : ∀ x : R, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/--
@isnad1 id=eq.1h2v.s7.9e9fbce91d89 from=seed src=0 shape=d05fa324 vocab=074c6b8b
-/
@[simp]
lemma coe_mk (S : Subsemiring R) (h) : ((⟨S, h⟩ : StarSubsemiring R) : Set R) = S := rfl

/--
@isnad1 id=iff.0h3v.s7.5016ca042371 from=seed src=0 shape=507d78e4 vocab=6fe314a2
-/
@[simp]
theorem mem_toSubsemiring {S : StarSubsemiring R} {x} : x ∈ S.toSubsemiring ↔ x ∈ S :=
  Iff.rfl

/--
@isnad1 id=eq.0h2v.s6.98536fcf558a from=seed src=0 shape=557b0bcc vocab=0ea5c873
-/
@[simp]
theorem coe_toSubsemiring (S : StarSubsemiring R) : (S.toSubsemiring : Set R) = S :=
  rfl

/--
@isnad1 id=injectiv.0h1v.s5.071af1387c20 from=seed src=0 shape=cbac796f vocab=a4663528
-/
theorem toSubsemiring_injective :
    Function.Injective (toSubsemiring : StarSubsemiring R → Subsemiring R) := fun S T h =>
  ext fun x => by rw [← mem_toSubsemiring, ← mem_toSubsemiring, h]

/--
@isnad1 id=iff.0h3v.s6.b30ac5f28ec8 from=seed src=0 shape=a17b5190 vocab=d1a3db13
-/
theorem toSubsemiring_inj {S U : StarSubsemiring R} : S.toSubsemiring = U.toSubsemiring ↔ S = U :=
  toSubsemiring_injective.eq_iff

/--
@isnad1 id=iff.0h3v.s7.732b7ddeda8e from=seed src=0 shape=a17b5190 vocab=23172fe6
-/
theorem toSubsemiring_le_iff {S₁ S₂ : StarSubsemiring R} :
    S₁.toSubsemiring ≤ S₂.toSubsemiring ↔ S₁ ≤ S₂ :=
  Iff.rfl

/-- Copy of a non-unital star subalgebra with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : StarSubsemiring R where
  toSubsemiring := Subsemiring.copy S.toSubsemiring s hs
  star_mem' := @fun a ha => hs ▸ (S.star_mem' (by simpa [hs] using ha) : star a ∈ (S : Set R))

/--
@isnad1 id=eq.1h3v.s7.421118622b59 from=seed src=0 shape=b67da15d vocab=8c167046
-/
@[simp, norm_cast]
theorem coe_copy (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : (S.copy s hs : Set R) = s :=
  rfl

/--
@isnad1 id=eq.1h3v.s6.d714f6670ed5 from=seed src=0 shape=ccbd82c9 vocab=8c167046
-/
theorem copy_eq (S : StarSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

section Center

variable (R)

/-- The center of a semiring `R` is the set of elements that commute and associate with everything
in `R` -/
def center (R) [NonAssocSemiring R] [StarRing R] : StarSubsemiring R where
  toSubsemiring := Subsemiring.center R
  star_mem' := Set.star_mem_center

end Center

end StarSubsemiring

end StarSubsemiring
section SubStarSemigroup

variable (A) [Mul A] [StarMul A]

namespace SubStarSemigroup

/-- The center of magma `A` is the set of elements that commute and associate
with everything in `A`, here realized as a `SubStarSemigroup`. -/
def center : SubStarSemigroup A :=
  { Subsemigroup.center A with
    star_mem' := Set.star_mem_center }

end SubStarSemigroup

end SubStarSemigroup
