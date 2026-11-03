/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Algebra.Homology.ShortComplex.ShortExact
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Abelian.Stability.Charge
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Abelian
import Tengoku.Seed.CategoryTheory.Abelian.Basic
import Tengoku.Seed.CategoryTheory.Subobject.Lattice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Stability functions on abelian categories

This file introduces the repository-owned stability-function interface.  Its
central charge is additive on short exact sequences and sends every nonzero
object to the semi-closed upper half-plane.  Phase, stability, and
semistability are then defined intrinsically from that charge.

The module is Mathlib-only and is the canonical stability-function interface
for this repository.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex Real

universe u v

namespace CategoryTheory.Triangulated

variable {O : Type*} {G : Type*} [AddCommGroup G]

/-- **A stability function relative to a class datum.**  One structure; the
abelian and ambient theories are two instantiations of it.-/
structure StabilityFunctionOn (D : ClassDatum O G) where
  /-- The central charge, as a hom out of the class group.-/
  Z : G →+ ℂ
  /-- Relevant objects have charge in the strict half-plane.-/
  nonzero_mem : IsStabilityCharge D Z

/-- **A weak stability function relative to a class datum.**-/
structure WeakStabilityFunctionOn (D : ClassDatum O G) where
  /-- The central charge, as a hom out of the class group.-/
  Z : G →+ ℂ
  /-- Relevant objects have charge in the closed half-plane.-/
  nonzero_mem : IsWeakStabilityCharge D Z

/-- **Every stability function is a weak one**, at any class datum.-/
def StabilityFunctionOn.toWeak {D : ClassDatum O G} (Z : StabilityFunctionOn D) :
    WeakStabilityFunctionOn D where
  Z := Z.Z
  nonzero_mem := Z.nonzero_mem.weak

/--
@isnad1 id=eq.0h4v.s5.554e3e54326e from=translated src=- shape=89cb4443 vocab=d360001a
-/
@[simp]
theorem StabilityFunctionOn.toWeak_Z {D : ClassDatum O G} (Z : StabilityFunctionOn D) :
    Z.toWeak.Z = Z.Z := rfl

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- The class datum of an abelian category: nonzero objects, classes in `K₀Ab`.-/
def abelianDatum : ClassDatum A (K₀Ab A) where
  Relevant E := ¬IsZero E
  cl := K₀Ab.of

/-- **An additive central charge on an abelian category** whose nonzero values
lie in the semi-closed upper half-plane.

This is `StabilityFunctionOn` at `abelianDatum`, not a structure of its own.
`charge` remains available as an abbreviation and `map_zero` / `map_iso` /
`additive` remain available as theorems, so consumers are unaffected.-/
abbrev StabilityFunction := StabilityFunctionOn (abelianDatum A)

variable {A}

/--
@isnad1 id=eq.0h2v.s6.20d224ab1f2e from=translated src=- shape=ec8b8019 vocab=3260aeef
-/
@[simp]
theorem abelianDatum_cl (E : A) : (abelianDatum A).cl E = K₀Ab.of E := rfl

/--
@isnad1 id=iff.0h2v.s6.616c7e7b6d6d from=translated src=- shape=37a20f0d vocab=61157d78
-/
@[simp]
theorem abelianDatum_relevant (E : A) : (abelianDatum A).Relevant E ↔ ¬IsZero E := Iff.rfl

variable (A)

namespace StabilityFunction

variable {A}

/-- The central charge on objects.-/
abbrev charge (Z : StabilityFunction A) (E : A) : ℂ := Z.Z (K₀Ab.of E)

/--
@isnad1 id=eq.0h3v.s7.d76b8783fb44 from=translated src=- shape=a55bf753 vocab=51f2b008
-/
@[simp]
theorem charge_apply (Z : StabilityFunction A) (E : A) :
    Z.charge E = Z.Z (K₀Ab.of E) := rfl

/-- **Zero objects have zero charge** — a theorem now, not a field.
@isnad1 id=eq.1h3v.s5.ae1df5d7c68d from=translated src=- shape=164fc834 vocab=8394cbaf
-/
theorem map_zero (Z : StabilityFunction A) (E : A) (hE : IsZero E) :
    Z.charge E = 0 := by
  rw [charge_apply, K₀Ab.of_isZero hE]
  exact Z.Z.map_zero

/-- **Isomorphic objects have the same charge** — a theorem now, not a field.
@isnad1 id=eq.0h5v.s5.842c194506ae from=translated src=- shape=cc9e6acb vocab=a309ce30
-/
theorem map_iso (Z : StabilityFunction A) {E F : A} (e : E ≅ F) :
    Z.charge E = Z.charge F := by
  rw [charge_apply, charge_apply, K₀Ab.of_iso e]

/-- **The charge is additive on short exact sequences** — a theorem now, not a
field.
@isnad1 id=eq.1h3v.s6.76b1adb91bcd from=translated src=- shape=4b040dc4 vocab=38cf217a
-/
theorem additive (Z : StabilityFunction A) (S : ShortComplex A) (hS : S.ShortExact) :
    Z.charge S.X₂ = Z.charge S.X₁ + Z.charge S.X₃ := by
  rw [charge_apply, charge_apply, charge_apply, K₀Ab.of_shortExact S hS, map_add]

/-- Two stability functions with the same charge on objects are equal.  This now
needs `K₀Ab.hom_ext` rather than structure eta: equal charges on generators is
what forces the two homs to agree.
@isnad1 id=eq.1h3v.s5.2318694bab67 from=translated src=- shape=c98ea306 vocab=7e23b65e
-/
@[ext]
theorem ext {Z W : StabilityFunction A} (hcharge : Z.charge = W.charge) : Z = W := by
  obtain ⟨Z, _⟩ := Z
  obtain ⟨W, _⟩ := W
  simp only [StabilityFunctionOn.mk.injEq]
  exact K₀Ab.hom_ext (fun X ↦ congrFun hcharge X)

/-- The phase of an object, normalized to lie in `(0, 1]` when the object is
nonzero.  The phase of a zero object is `0`.-/
def phase (Z : StabilityFunction A) (E : A) : ℝ :=
  arg (Z.charge E) / Real.pi

/--
@isnad1 id=lt.1h3v.s5.35090fe8ff13 from=translated src=- shape=9407537e vocab=f4d08240
-/
theorem phase_pos (Z : StabilityFunction A) (E : A) (hE : ¬IsZero E) :
    0 < Z.phase E := by
  exact div_pos
    (arg_pos_of_mem_semiClosedUpperHalfPlane (Z.nonzero_mem E hE))
    Real.pi_pos

/--
@isnad1 id=le.0h3v.s4.3b3f068944f0 from=translated src=- shape=a3cd9a08 vocab=6c4071d3
-/
theorem phase_le_one (Z : StabilityFunction A) (E : A) : Z.phase E ≤ 1 := by
  exact div_le_one_of_le₀ (arg_le_pi (Z.charge E)) Real.pi_pos.le

/--
@isnad1 id=mem.1h3v.s5.50cb1043577d from=translated src=- shape=72b39e72 vocab=3b656e9f
-/
theorem phase_mem_Ioc (Z : StabilityFunction A) (E : A) (hE : ¬IsZero E) :
    Z.phase E ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨Z.phase_pos E hE, Z.phase_le_one E⟩

/-- A nonzero object is semistable when no nonzero subobject has larger
phase.-/
def IsSemistable (Z : StabilityFunction A) (E : A) : Prop :=
  ¬IsZero E ∧ ∀ B : Subobject E, ¬IsZero (B : A) →
    Z.phase (B : A) ≤ Z.phase E

/-- A nonzero object is stable when every nonzero proper subobject has strictly
smaller phase.-/
def IsStable (Z : StabilityFunction A) (E : A) : Prop :=
  ¬IsZero E ∧ ∀ B : Subobject E, ¬IsZero (B : A) → B ≠ ⊤ →
    Z.phase (B : A) < Z.phase E

/--
@isnad1 id=ex.2h3v.s6.d9baf74e4ffd from=translated src=- shape=76b95633 vocab=e3bb8248
-/
theorem exists_destabilizing_of_not_semistable (Z : StabilityFunction A)
    (E : A) (hE : ¬IsZero E) (h : ¬Z.IsSemistable E) :
    ∃ B : Subobject E, ¬IsZero (B : A) ∧ Z.phase E < Z.phase (B : A) := by
  simp only [IsSemistable, not_and_or, not_forall, not_le, exists_prop] at h
  rcases h with h | ⟨B, hB, hphase⟩
  · exact absurd hE h
  · exact ⟨B, hB, hphase⟩

/--
@isnad1 id=eq.0h5v.s5.842c194506ae from=translated src=- shape=cc9e6acb vocab=a309ce30
-/
theorem charge_eq_of_iso (Z : StabilityFunction A) {E F : A} (e : E ≅ F) :
    Z.charge E = Z.charge F :=
  Z.map_iso e

/--
@isnad1 id=eq.0h5v.s5.f570aeda9bd5 from=translated src=- shape=cc9e6acb vocab=c250fa41
-/
theorem phase_eq_of_iso (Z : StabilityFunction A) {E F : A} (e : E ≅ F) :
    Z.phase E = Z.phase F := by
  simp only [phase, Z.charge_eq_of_iso e]

/--
@isnad1 id=issemist.1h5v.s5.b341cc814aad from=translated src=- shape=f5e7c679 vocab=8ebaece4
-/
theorem isSemistable_of_iso (Z : StabilityFunction A) {E F : A}
    (e : E ≅ F) (h : Z.IsSemistable E) : Z.IsSemistable F := by
  refine ⟨fun hF => h.1 (hF.of_iso e), fun B hB => ?_⟩
  let B' : Subobject E := Subobject.mk (B.arrow ≫ e.inv)
  have hB' : ¬IsZero (B' : A) := by
    intro hzero
    exact hB (hzero.of_iso (Subobject.underlyingIso (B.arrow ≫ e.inv)).symm)
  have hle := h.2 B' hB'
  rw [Z.phase_eq_of_iso (Subobject.underlyingIso (B.arrow ≫ e.inv))] at hle
  rwa [Z.phase_eq_of_iso e] at hle

/--
@isnad1 id=iff.0h5v.s5.3fa50444a033 from=translated src=- shape=dcd3e9d2 vocab=8ebaece4
-/
theorem isSemistable_iff_of_iso (Z : StabilityFunction A) {E F : A}
    (e : E ≅ F) : Z.IsSemistable E ↔ Z.IsSemistable F :=
  ⟨Z.isSemistable_of_iso e, Z.isSemistable_of_iso e.symm⟩

end StabilityFunction

end CategoryTheory.Triangulated
