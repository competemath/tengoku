/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/

module

public import Tengoku.Seed.Algebra.LieRinehartAlgebra.Defs

/-!
# Lie-Rinehart subalgebras

This file defines Lie-Rinehart subalgebras of a Lie-Rinehart algebra and provides basic related
definitions and results.

## Main definitions/ statements:

* `LieRinehartSubalgebra` as an `A`-submodule of `L` stable under the Lie bracket. (This is also
applicable to Lie-Rinehart rings and more generally any `A`-module with a Lie ring structure).

* A Lie-Rinehart subalgebra of a Lie-Rinehart ring is a Lie-Rinehart ring

* A Lie-Rinehart subalgebra of a Lie-Rinehart algebra is a Lie-Rinehart algebra over the same ring.

-/

public section

open scoped LieRinehartAlgebra

variable (A L : Type*) [CommRing A] [LieRing L] [Module A L]

/-- A Lie-Rinehart subalgebra of a Lie-Rinehart algebra `(R A L)` is an `A`-submodule of `L`, which
is stable under the Lie bracket. (This can be defined independently of `R` and most
Lie-Rinehart algebra axioms). -/
structure LieRinehartSubalgebra extends Submodule A L where
  lie_mem' {a b} : a ∈ carrier → b ∈ carrier → ⁅a, b⁆ ∈ carrier

instance : Zero (LieRinehartSubalgebra A L) :=
  ⟨⟨0, fun {x y hx _hy} ↦ by simp [(Submodule.mem_bot A).mp hx]⟩⟩

instance : Inhabited (LieRinehartSubalgebra A L) :=
  ⟨0⟩

namespace LieRinehartSubalgebra

instance : SetLike (LieRinehartSubalgebra A L) L where
  coe L' := L'.carrier
  coe_injective L' L'' h := by
    rcases L'
    rcases L''
    congr
    exact SetLike.coe_injective h

instance : PartialOrder (LieRinehartSubalgebra A L) := .ofSetLike (LieRinehartSubalgebra A L) L

instance : AddSubgroupClass (LieRinehartSubalgebra A L) L where
  add_mem := Submodule.add_mem _
  zero_mem L' := L'.zero_mem'
  neg_mem {L'} x hx := show -x ∈ L'.toSubmodule from neg_mem hx

instance : SMulMemClass (LieRinehartSubalgebra A L) A L where
  smul_mem {s} := SMulMemClass.smul_mem (s := s.toSubmodule)

/-- A Lie-Rinehart subalgebra forms a Lie ring. -/
instance lieRing (L' : LieRinehartSubalgebra A L) : LieRing L' where
  bracket x y := ⟨⁅x.val, y.val⁆, L'.lie_mem' x.property y.property⟩
  lie_add x y z := by aesop
  add_lie x y z := by aesop
  lie_self x := by aesop
  leibniz_lie x y z := by aesop

variable {A L}
variable (L' : LieRinehartSubalgebra A L)

/--
@isnad1 id=mem.0h3v.s6.ca0f9ce20f3e from=seed src=0 shape=8b819c83 vocab=4ed1f642
-/
protected theorem zero_mem : (0 : L) ∈ L' :=
  zero_mem L'

/--
@isnad1 id=mem.2h5v.s6.47add7dc815e from=seed src=0 shape=2f49991e vocab=fd01e097
-/
protected theorem add_mem {x y : L} : x ∈ L' → y ∈ L' → (x + y : L) ∈ L' :=
  add_mem

/--
@isnad1 id=mem.2h5v.s6.918397e7f86e from=seed src=0 shape=2f49991e vocab=da659a1d
-/
protected theorem sub_mem {x y : L} : x ∈ L' → y ∈ L' → (x - y : L) ∈ L' :=
  sub_mem

/--
@isnad1 id=mem.1h5v.s7.ebcbf1543c17 from=seed src=0 shape=aefd344b vocab=7c9113e5
-/
protected theorem smul_mem (t : A) {x : L} (h : x ∈ L') : t • x ∈ L' :=
  SMulMemClass.smul_mem _ h

/--
@isnad1 id=mem.2h5v.s6.3cb66dce62f7 from=seed src=0 shape=da1f0c46 vocab=e5a1c040
-/
theorem lie_mem {x y : L} (hx : x ∈ L') (hy : y ∈ L') : (⁅x, y⁆ : L) ∈ L' :=
  L'.lie_mem' hx hy

/--
@isnad1 id=iff.0h4v.s6.314e50938678 from=seed src=0 shape=7ba35fbb vocab=0b81a2bc
-/
theorem mem_carrier {x : L} : x ∈ L'.carrier ↔ x ∈ (L' : Set L) :=
  Iff.rfl

/--
@isnad1 id=iff.3h5v.s9.6bf80b6b67ef from=seed src=0 shape=c3644cb8 vocab=79b7deb2
-/
theorem mem_mk_iff (S : Set L) (h₁ h₂ h₃ h₄) {x : L} :
    x ∈ (⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieRinehartSubalgebra A L) ↔ x ∈ S :=
  Iff.rfl

/--
@isnad1 id=iff.0h4v.s6.b43277aca6d0 from=seed src=0 shape=1e85670b vocab=5e9f65ff
-/
@[simp]
theorem mem_toSubmodule {x : L} : x ∈ L'.toSubmodule ↔ x ∈ L' :=
  Iff.rfl

/--
@isnad1 id=iff.1h4v.s8.435e145baaf0 from=seed src=0 shape=ea216cb4 vocab=2636bd73
-/
@[simp]
theorem mem_mk_iff' (p : Submodule A L) (h) {x : L} :
    x ∈ (⟨p, h⟩ : LieRinehartSubalgebra A L) ↔ x ∈ p :=
  Iff.rfl

/--
@isnad1 id=iff.0h4v.s6.69450412170f from=seed src=0 shape=c491cde1 vocab=cf030a44
-/
theorem mem_coe {x : L} : x ∈ (L' : Set L) ↔ x ∈ L' :=
  Iff.rfl

/--
@isnad1 id=eq.0h5v.s8.7cf5a6372e71 from=seed src=0 shape=306220ac vocab=dba33f34
-/
@[simp, norm_cast]
theorem coe_bracket (x y : L') : (↑⁅x, y⁆ : L) = ⁅(↑x : L), ↑y⁆ :=
  rfl

/--
@isnad1 id=iff.0h5v.s7.3dd972a24f78 from=seed src=0 shape=8ee7a9ca vocab=f609d984
-/
theorem ext_iff (x y : L') : x = y ↔ (x : L) = y := Subtype.ext_iff

/--
@isnad1 id=iff.0h4v.s7.01f0052a45fa from=seed src=0 shape=841614d3 vocab=f609d984
-/
theorem coe_zero_iff_zero (x : L') : (x : L) = 0 ↔ x = 0 := (ext_iff L' x 0).symm

/--
@isnad1 id=eq.1h4v.s6.3fe1eac71611 from=seed src=0 shape=bb5d2512 vocab=4ed1f642
-/
@[ext]
theorem ext (L₁' L₂' : LieRinehartSubalgebra A L) (h : ∀ x, x ∈ L₁' ↔ x ∈ L₂') : L₁' = L₂' :=
  SetLike.ext h

/--
@isnad1 id=iff.0h4v.s6.382f5934b2b3 from=seed src=0 shape=180357c0 vocab=4ed1f642
-/
theorem ext_iff' (L₁' L₂' : LieRinehartSubalgebra A L) : L₁' = L₂' ↔ ∀ x, x ∈ L₁' ↔ x ∈ L₂' :=
  SetLike.ext_iff

/--
@isnad1 id=eq.3h4v.s9.9d3244cd7753 from=seed src=0 shape=6befddb0 vocab=e9fc0bba
-/
@[simp]
theorem mk_coe (S : Set L) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨⟨S, h₁⟩, h₂⟩, h₃⟩, h₄⟩ : LieRinehartSubalgebra A L) : Set L) = S :=
  rfl

/--
@isnad1 id=eq.1h3v.s7.2b33bc3b5102 from=seed src=0 shape=4605b841 vocab=4408e2d2
-/
theorem toSubmodule_mk (p : Submodule A L) (h) :
    ({ p with lie_mem' := h } : LieRinehartSubalgebra A L).toSubmodule = p := rfl

/--
@isnad1 id=injectiv.0h2v.s5.2f7ac867b7e4 from=seed src=0 shape=87515b0a vocab=3f0649cd
-/
theorem coe_injective : Function.Injective ((↑) : LieRinehartSubalgebra A L → Set L) :=
  SetLike.coe_injective

/--
@isnad1 id=iff.0h4v.s6.2bc5680d33b1 from=seed src=0 shape=858c610d vocab=e048e17b
-/
@[norm_cast]
theorem coe_set_eq (L₁' L₂' : LieRinehartSubalgebra A L) : (L₁' : Set L) = L₂' ↔ L₁' = L₂' :=
  SetLike.coe_set_eq

/--
@isnad1 id=injectiv.0h2v.s5.02c86c9c166f from=seed src=0 shape=0cc94c66 vocab=03f5246a
-/
theorem toSubmodule_injective : Function.Injective (toSubmodule (A := A) (L := L)) := by
  intro L₁' L₂' h
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h

/--
@isnad1 id=eq.0h3v.s6.7d85a6f82d38 from=seed src=0 shape=1b166f70 vocab=b66776aa
-/
theorem coe_toSubmodule : (L'.toSubmodule : Set L) = L' :=
  rfl

section LieModule

variable {M : Type*} [AddCommGroup M] [LieRingModule L M]

instance : Bracket L' M where
  bracket x m := ⁅(x : L), m⁆

/--
@isnad1 id=eq.0h6v.s7.c775c4c3bb6a from=seed src=0 shape=621256d9 vocab=280edb55
-/
@[simp]
theorem coe_bracket_of_module (x : L') (m : M) : ⁅x, m⁆ = ⁅(x : L), m⁆ :=
  rfl

instance : IsLieTower L' L M where
  leibniz_lie x y m := leibniz_lie x.val y m

/-- Given a Lie-Rinehart algebra `L` containing a LieRinehart subalgebra `L' ⊆ L`, together with a
Lie ring module `M` of `L`, we may regard `M` as a Lie ring module of `L'` by restriction. -/
instance lieRingModule : LieRingModule L' M where
  add_lie x y m := add_lie (x : L) y m
  lie_add x y m := lie_add (x : L) y m
  leibniz_lie x y m := leibniz_lie x (y : L) m

end LieModule

variable [LieRingModule L A] [LieRinehartRing A L]

/-- A Lie-Rinehart subalgebra of a Lie-Rinehart ring forms a new Lie-Rinehart ring. -/
instance : LieRinehartRing A L' where
  lie_smul_eq_mul' a b x := LieRinehartRing.lie_smul_eq_mul a b (x : L)
  leibniz_mul_right' x a b := LieRinehartRing.leibniz_mul_right (x : L) a b
  leibniz_smul_right' _ _ _ := by simp [ext_iff]

variable (R : Type*) [CommRing R] [Algebra R A] [LieAlgebra R L] [LieRinehartAlgebra R A L]

/-- A Lie-Rinehart subalgebra of a Lie-Rinehart algebra forms a Lie algebra. -/
instance lieAlgebra : LieAlgebra R L' where
  lie_smul := by aesop

/-- Converts a Lie-Rinehart subalgebra to the corresponding Lie subalgebra. -/
@[expose] def toLieSubalgebra : LieSubalgebra R L where
  toSubmodule := L'.toSubmodule.restrictScalars R
  lie_mem' := L'.lie_mem'

/--
@isnad1 id=injectiv.0h3v.s6.023f185dc766 from=seed src=0 shape=a96496a4 vocab=dce2afb2
-/
theorem toLieSubalgebra_injective : Function.Injective (fun L' =>
    L'.toLieSubalgebra R : LieRinehartSubalgebra A L → LieSubalgebra R L) :=  fun L₁' L₂' h ↦ by
  rw [SetLike.ext'_iff] at h
  rw [← coe_set_eq]
  exact h

/--
@isnad1 id=iff.0h5v.s7.3243f7dfb0da from=seed src=0 shape=5e0b7d2c vocab=fb7024eb
-/
@[simp]
theorem toLieSubalgebra_inj (L₁' L₂' : LieRinehartSubalgebra A L) :
    (L₁'.toLieSubalgebra R) = (L₂'.toLieSubalgebra R) ↔ L₁' = L₂' :=
  (toLieSubalgebra_injective R).eq_iff

/--
@isnad1 id=eq.0h4v.s7.4a9c9fab85f2 from=seed src=0 shape=ef9852c6 vocab=a65f225b
-/
theorem coe_toLieSubalgebra : ((L'.toLieSubalgebra R) : Set L) = L' := rfl

section LieModule

variable {M : Type*} [AddCommGroup M] [LieRingModule L M] [Module R M]

/-- Given a Lie-Rinehart algebra  `L` containing a LieRinehart subalgebra `L' ⊆ L`, together with a
Lie module `M` of `L`, we may regard `M` as a Lie module of `L'` by restriction.
@isnad1 id=liemodul.0h5v.s7.0c61b72a7b7f from=seed src=0 shape=662629ac vocab=8ad0bb38
-/
instance lieModule [LieModule R L M] : LieModule R L' M where
  smul_lie t x m := by
    rw [coe_bracket_of_module, Submodule.coe_smul_of_tower, smul_lie, coe_bracket_of_module]
  lie_smul t x m := by simp only [coe_bracket_of_module, lie_smul]

end LieModule

/-- A Lie-Rinehart subalgebra forms a new Lie-Rinehart algebra. -/
instance : LieRinehartAlgebra R A L' where

/-- The embedding of a Lie-Rinehart subalgebra into the ambient space as a morphism of
Lie-Rinehart algebras. -/
@[expose] def incl : L' →ₗ⁅(AlgHom.id R A)⁆ L where
  __ := L'.toSubmodule.subtype.restrictScalars R
  map_lie' {x y} := coe_bracket L' x y
  map_smul_apply' a x := L'.toSubmodule.subtype.map_smul a x
  apply_lie' a x := AlgHom.id_apply ⁅x, a⁆

/--
@isnad1 id=eq.0h4v.s8.a2c74b3df0e9 from=seed src=0 shape=e17d632a vocab=080cbda7
-/
@[simp]
theorem coe_incl : ⇑(L'.incl R) = ((↑) : L' → L) := rfl

end LieRinehartSubalgebra
