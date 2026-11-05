/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Tengoku.AclGeom.AclGeom.Correspondence.GroupChunk
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The affine group action and its fixed points

The elementary algebraic endgame of blueprint Lemma `affine-action`:

* `AffineTransformation k` is the semidirect product `kˣ ⋉ k`;
* multiplication is exactly `(c,d)(a,b) = (ca, cb+d)`;
* its action on the affine line is `(a,b) • x = ax+b`;
* translations form a normal subgroup and conjugation scales their
  parameter;
* a nonidentity affine transformation fixes at most one point unless it is
  the identity, with the fixed point explicitly `b / (1-a)`.

These are the fixed-point and coordinate bookkeeping statements used after
the curve-theoretic rigidity argument has forced the action into genus zero.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete (M4b P7 / blueprint Lemma 8.4 algebraic endgame).
-/

namespace AclGeom

noncomputable section

/-- An invertible affine transformation `x ↦ ax+b` of a field.-/
@[ext]
structure AffineTransformation (k : Type*) [Field k] where
  /-- The nonzero multiplier `a`.-/
  multiplier : kˣ
  /-- The translation parameter `b`.-/
  shift : k

namespace AffineTransformation

variable {k : Type*} [Field k]

/-- Composition of affine transformations, with the left factor acting
last: `(c,d)(a,b) = (ca, cb+d)`.-/
def mul (g h : AffineTransformation k) : AffineTransformation k where
  multiplier := g.multiplier * h.multiplier
  shift := (g.multiplier : k) * h.shift + g.shift

/-- The identity affine transformation.-/
def one : AffineTransformation k where
  multiplier := 1
  shift := 0

/-- The inverse of `x ↦ ax+b` is `x ↦ a⁻¹x-a⁻¹b`.-/
def inv (g : AffineTransformation k) : AffineTransformation k where
  multiplier := g.multiplier⁻¹
  shift := -(g.multiplier⁻¹ : k) * g.shift

instance : Mul (AffineTransformation k) := ⟨mul⟩
instance : One (AffineTransformation k) := ⟨one⟩
instance : Inv (AffineTransformation k) := ⟨inv⟩

/--
@isnad1 id=eq.0h3v.s6.b5581ffcaf69 from=translated src=- shape=e69ef69b vocab=5be9b1bc
-/
@[simp] theorem multiplier_mul (g h : AffineTransformation k) :
    (g * h).multiplier = g.multiplier * h.multiplier := rfl

/--
@isnad1 id=eq.0h3v.s6.b8acc35d6657 from=translated src=- shape=3d42b901 vocab=476d160e
-/
@[simp] theorem shift_mul (g h : AffineTransformation k) :
    (g * h).shift = (g.multiplier : k) * h.shift + g.shift := rfl

/--
@isnad1 id=eq.0h1v.s6.46e6f71f4b07 from=translated src=- shape=7b5bff60 vocab=90efa2ca
-/
@[simp] theorem multiplier_one : (1 : AffineTransformation k).multiplier = 1 := rfl

/--
@isnad1 id=eq.0h1v.s5.1d1053e64506 from=translated src=- shape=c6b7a0b8 vocab=71011333
-/
@[simp] theorem shift_one : (1 : AffineTransformation k).shift = 0 := rfl

/--
@isnad1 id=eq.0h2v.s5.1ef2c934c0bc from=translated src=- shape=5c68212b vocab=9c019572
-/
@[simp] theorem multiplier_inv (g : AffineTransformation k) :
    g⁻¹.multiplier = g.multiplier⁻¹ := rfl

/--
@isnad1 id=eq.0h2v.s6.2050caabd155 from=translated src=- shape=3e4b6722 vocab=5b54a33a
-/
@[simp] theorem shift_inv (g : AffineTransformation k) :
    g⁻¹.shift = -(g.multiplier⁻¹ : k) * g.shift := rfl

/-- The affine transformations form the semidirect-product group
`kˣ ⋉ k`.-/
instance : Group (AffineTransformation k) :=
  Group.ofLeftAxioms
    (fun g h l ↦ by
      ext
      · simp [mul_assoc]
      · simp only [shift_mul, multiplier_mul, Units.val_mul]
        ring)
    (fun g ↦ by ext <;> simp)
    (fun g ↦ by
      ext
      · simp
      · simp only [shift_mul, shift_inv, multiplier_inv, Units.val_inv_eq_inv_val,
          shift_one]
        field_simp
        ring)

/-- Evaluation of an affine transformation on the affine line.-/
def apply (g : AffineTransformation k) (x : k) : k :=
  (g.multiplier : k) * x + g.shift

instance : SMul (AffineTransformation k) k := ⟨apply⟩

/--
@isnad1 id=eq.0h3v.s6.86bd6f588031 from=translated src=- shape=2850be85 vocab=8a87b63f
-/
@[simp] theorem smul_def (g : AffineTransformation k) (x : k) :
    g • x = (g.multiplier : k) * x + g.shift := rfl

/--
@isnad1 id=eq.0h2v.s5.f808a71612a4 from=translated src=- shape=da5adff8 vocab=aa8e2fcc
-/
@[simp] theorem one_smul (x : k) : (1 : AffineTransformation k) • x = x := by
  simp [smul_def]

/--
@isnad1 id=eq.0h4v.s6.52de49ad4499 from=translated src=- shape=8a9d141a vocab=bd07d9fd
-/
@[simp] theorem mul_smul (g h : AffineTransformation k) (x : k) :
    (g * h) • x = g • h • x := by
  simp only [smul_def, multiplier_mul, shift_mul, Units.val_mul]
  ring

instance : MulAction (AffineTransformation k) k where
  one_smul := one_smul
  mul_smul := mul_smul

/-- The pure translation `x ↦ x+b`.-/
def translation (b : k) : AffineTransformation k where
  multiplier := 1
  shift := b

/-- The pure scaling `x ↦ ax`.-/
def scaling (a : kˣ) : AffineTransformation k where
  multiplier := a
  shift := 0

/--
@isnad1 id=eq.0h2v.s5.5c17bcf78ce0 from=translated src=- shape=b0d7e649 vocab=3b799c13
-/
@[simp] theorem translation_multiplier (b : k) :
    (translation b).multiplier = 1 := rfl

/--
@isnad1 id=eq.0h2v.s4.7caac78d8154 from=translated src=- shape=1c9622f3 vocab=53ceda7c
-/
@[simp] theorem translation_shift (b : k) : (translation b).shift = b := rfl

/--
@isnad1 id=eq.0h3v.s5.e2b664126fb1 from=translated src=- shape=96698720 vocab=24d54d22
-/
@[simp] theorem translation_smul (b x : k) : translation b • x = x + b := by
  simp [smul_def, translation]

/--
@isnad1 id=eq.0h3v.s5.208680e2a4ad from=translated src=- shape=44e7dc92 vocab=8ac3a0ff
-/
@[simp] theorem translation_mul_translation (b d : k) :
    translation b * translation d = translation (b + d) := by
  ext <;> simp [translation, add_comm]

/--
@isnad1 id=eq.0h2v.s5.e2083f568eb6 from=translated src=- shape=e5bb9134 vocab=c0679425
-/
@[simp] theorem translation_inv (b : k) :
    (translation b)⁻¹ = translation (-b) := by
  ext <;> simp [translation]

/-- Conjugation by an affine transformation scales the translation
parameter by its multiplier.  This is the normal-subgroup calculation in
blueprint (8.4b).
@isnad1 id=eq.0h3v.s6.a5590c7627c1 from=translated src=- shape=850f4893 vocab=52ea1b8b
-/
theorem mul_translation_mul_inv (g : AffineTransformation k) (b : k) :
    g * translation b * g⁻¹ = translation ((g.multiplier : k) * b) := by
  ext
  · simp [translation]
  · simp only [shift_mul, multiplier_mul, translation_shift, translation_multiplier,
      shift_inv, Units.val_mul, Units.val_one]
    have ha : (g.multiplier : k) ≠ 0 := Units.ne_zero g.multiplier
    field_simp
    ring

/-- The fixed-point equation for `x ↦ ax+b`.
@isnad1 id=iff.0h3v.s6.6094dfe4ab49 from=translated src=- shape=9b202000 vocab=df8e185e
-/
theorem smul_eq_iff (g : AffineTransformation k) (x : k) :
    g • x = x ↔ (1 - (g.multiplier : k)) * x = g.shift := by
  change (g.multiplier : k) * x + g.shift = x ↔ _
  constructor
  · intro h
    rw [sub_mul, one_mul]
    exact (eq_sub_of_add_eq' h).symm
  · intro h
    rw [sub_mul, one_mul] at h
    have hb : g.shift + (g.multiplier : k) * x = x :=
      (eq_sub_iff_add_eq).1 h.symm
    simpa [add_comm] using hb

/-- The explicit fixed point when the multiplier is not one.-/
def fixedPoint (g : AffineTransformation k) : k :=
  g.shift / (1 - (g.multiplier : k))

/-- An affine transformation with multiplier different from one fixes its
explicit fixed point.
@isnad1 id=eq.1h2v.s6.7f98d5b71ff1 from=translated src=- shape=60a6d2b0 vocab=21e1bad5
-/
theorem smul_fixedPoint (g : AffineTransformation k)
    (ha : (g.multiplier : k) ≠ 1) : g • g.fixedPoint = g.fixedPoint := by
  rw [smul_eq_iff]
  exact mul_div_cancel₀ g.shift (sub_ne_zero.mpr ha.symm)

/-- The fixed point is unique when the multiplier is not one.-/
theorem eq_fixedPoint_of_smul_eq (g : AffineTransformation k) {x : k}
    (ha : (g.multiplier : k) ≠ 1) (hx : g • x = x) : x = g.fixedPoint := by
  rw [smul_eq_iff] at hx
  rw [fixedPoint, eq_div_iff (sub_ne_zero.mpr ha.symm)]
  simpa [mul_comm] using hx

/-- A pure translation has a fixed point exactly when it is the identity
translation.
@isnad1 id=iff.0h3v.s5.d34fdba69b63 from=translated src=- shape=25753d70 vocab=b2f71410
-/
theorem translation_smul_eq_iff {b x : k} : translation b • x = x ↔ b = 0 := by
  simp

/-- A nontrivial translation has no fixed point.
@isnad1 id=ne.1h3v.s5.b6e296d81837 from=translated src=- shape=6780b73a vocab=b2f71410
-/
theorem translation_fixedPoint_free {b : k} (hb : b ≠ 0) (x : k) :
    translation b • x ≠ x :=
  fun h ↦ hb (translation_smul_eq_iff.1 h)

/-- An affine transformation fixing two distinct points is the identity.
This is the fixed-point rigidity used to discard finite kernels of the curve
action.-/
theorem eq_one_of_smul_eq_of_smul_eq (g : AffineTransformation k) {x y : k}
    (hx : g • x = x) (hy : g • y = y) (hxy : x ≠ y) : g = 1 := by
  have ha : (g.multiplier : k) = 1 := by
    by_contra hne
    exact hxy ((g.eq_fixedPoint_of_smul_eq hne hx).trans
      (g.eq_fixedPoint_of_smul_eq hne hy).symm)
  apply AffineTransformation.ext
  · exact Units.ext ha
  · rw [smul_eq_iff, ha, sub_self, zero_mul] at hx
    simpa using hx.symm

end AffineTransformation

end

end AclGeom

namespace AclGeom.AffineTransformation
noncomputable section
variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- Transcendence makes evaluation of affine transformations injective.
 Named consumers: the fixed-place representation and the actual local coefficient map.
@isnad1 id=injectiv.1h3v.s7.ad852b4fe913 from=translated src=- shape=265f1974 vocab=0736ceca
-/
theorem eval_injective {t : F} (ht : Transcendental k t) :
    Function.Injective (fun A : AffineTransformation k ↦
      algebraMap k F (A.multiplier : k) * t + algebraMap k F A.shift) := by
  intro A B h
  change algebraMap k F (A.multiplier : k) * t + algebraMap k F A.shift =
    algebraMap k F (B.multiplier : k) * t + algebraMap k F B.shift at h
  by_cases ha : (A.multiplier : k) = (B.multiplier : k)
  · have hb : A.shift = B.shift := by
      apply (algebraMap k F).injective
      rw [ha] at h
      exact add_left_cancel h
    exact AffineTransformation.ext (Units.ext ha) hb
  · have hd : algebraMap k F ((A.multiplier : k) - (B.multiplier : k)) ≠ 0 :=
      (map_ne_zero _).2 (sub_ne_zero.mpr ha)
    have he : t = algebraMap k F
        ((B.shift - A.shift) / ((A.multiplier : k) - (B.multiplier : k))) := by
      rw [map_div₀]
      apply (eq_div_iff hd).2
      rw [map_sub, map_sub]
      linear_combination h
    exfalso
    apply ht
    rw [he]
    exact isAlgebraic_algebraMap _

end
end AclGeom.AffineTransformation
