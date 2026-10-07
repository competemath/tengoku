/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.FunctionField
public import Tengoku.Seed.AlgebraicGeometry.Noetherian
public import Tengoku.Seed.RingTheory.OrderOfVanishing.Noetherian

/-!
# Order of vanishing in a scheme

In this file we define the order of vanishing of an element of the function field of a locally
Noetherian integral scheme at a point of codimension `1`.
-/

@[expose] public section

open WithZero AlgebraicGeometry Order TopologicalSpace CategoryTheory

universe u

variable {X : Scheme.{u}}

namespace AlgebraicGeometry.Scheme

variable [IsIntegral X] [IsLocallyNoetherian X]

/--
Order of vanishing on a locally Noetherian integral scheme as a monoid with zero hom to `ℤᵐ⁰`.
-/
noncomputable
def ordHom (z : X) (hz : coheight z = 1) : X.functionField →*₀ ℤᵐ⁰ :=
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  Ring.ordFrac (X.presheaf.stalk z)

/--
@isnad1 id=eq.3h4v.s10.639091cd96ab from=seed src=0 shape=54b282e2 vocab=13d0e6d0
-/
lemma ordHom_of_isUnit {U : X.Opens}
    [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X} (hx : coheight x = 1) (hx' : x ∈ U) :
    ordHom x hx (X.germToFunctionField U f) = 1 := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  rw [← algebraMap_germ_eq_germToFunctionField _ hx']
  exact Ring.ordFrac_of_isUnit (hf.map (X.presheaf.germ U x hx').hom)

/--
The order of vanishing of an element of the function field of a locally Noetherian integral scheme
at a point. This has a junk value of `0` if `f = 0` or if `coheight z ≠ 1`.
-/
@[no_expose]
noncomputable
def ord (f : X.functionField) (z : X) : ℤ :=
  if hz : coheight z = 1
  then Multiplicative.toAdd <| (X.ordHom z hz f).unzeroD 1
  else 0

/--
@isnad1 id=eq.1h3v.s7.62c9bc5c21f8 from=seed src=0 shape=3cf315ce vocab=7aa6a33c
-/
lemma ord_eq_ordHom_of_coheight_eq_one {z : X} (hz : coheight z = 1) (f : X.functionField) :
    ord f z = Multiplicative.toAdd ((X.ordHom z hz f).unzeroD 1) := dite_eq_left hz

/--
@isnad1 id=eq.1h3v.s5.b45e73af2aae from=seed src=0 shape=9d30fcb6 vocab=86cfdd5f
-/
@[simp]
lemma ord_eq_zero_of_coheight_neq_one {z : X} (hz : coheight z ≠ 1) (f : X.functionField) :
    ord f z = 0 := dite_eq_right hz

/--
@isnad1 id=eq.0h1v.s7.2339942c53f9 from=seed src=0 shape=9a8a39e1 vocab=f0b161cd
-/
@[simp]
lemma ord_zero : ord (0 : X.functionField) = 0 := by
  ext z
  by_cases h : coheight z = 1
  · simp [ord_eq_ordHom_of_coheight_eq_one h, unzeroD]
  · simp [h]

/--
@isnad1 id=eq.2h3v.s7.85a0e0403632 from=seed src=0 shape=d24cd050 vocab=c650ead3
-/
lemma ord_eq_unzero_ordHom {x : X} (hx : coheight x = 1) {f : X.functionField} (hf : f ≠ 0) :
    ord f x = (WithZero.unzero ((map_ne_zero (ordHom x hx)).mpr hf)).toAdd := by
  simp [ord, hx, unzeroD_eq_unzero ((map_ne_zero (ordHom x hx)).mpr hf)]

/--
@isnad1 id=iff.2h4v.s7.d6417448410d from=seed src=0 shape=7ef06c4e vocab=3a5ff108
-/
lemma ord_eq_iff {z : X} (hz : coheight z = 1) {f : X.functionField} (hf : f ≠ 0) {n : ℤ} :
    ord f z = n ↔ ordHom z hz f = Multiplicative.ofAdd n := by
  rw [ord_eq_unzero_ordHom hz hf]
  exact WithZero.toAdd_unzero_eq_iff _ _

/--
@isnad1 id=eq.2h4v.s7.770d1e868580 from=seed src=0 shape=c81aecf7 vocab=de08e5ee
-/
@[simp]
lemma ord_mul {x : X} {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) : ord (f * g) x = ord f x + ord g x := by
  by_cases! hx : coheight x ≠ 1
  · simp [hx]
  rw [ord_eq_iff hx <| (mul_ne_zero_iff_right hg).mpr hf]
  simp [hf, hg, ord_eq_ordHom_of_coheight_eq_one hx, unzeroD_eq_unzero]

/--
@isnad1 id=eq.2h4v.s10.1cf7f57e2295 from=seed src=0 shape=12772cf0 vocab=284bec0b
-/
lemma ord_of_isUnit {U : X.Opens} [Nonempty U] {f : Γ(X, U)} (hf : IsUnit f) {x : X}
    (hx' : x ∈ U) : ord (X.germToFunctionField U f) x = 0 := by
  by_cases! hx : coheight x ≠ 1
  · simp [hx]
  simp [map_ne_zero_iff, germToFunctionField_injective, IsUnit.ne_zero hf,
    ord_eq_iff hx, ordHom_of_isUnit hf hx hx']

/--
@isnad1 id=iff.4h5v.s8.ec9fdf9fd4ef from=seed src=0 shape=1283a93b vocab=d0f29e8d
-/
lemma ord_le_ord_iff {x y : X} (hx : coheight x = 1) (hy : coheight y = 1) {f g : X.functionField}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    ord f x ≤ ord g y ↔ ordHom x hx f ≤ ordHom y hy g := by
  simp [ord_eq_unzero_ordHom hx hf, ord_eq_unzero_ordHom hy hg, Multiplicative.toAdd_le]

/--
@isnad1 id=iff.2h4v.s7.628125b82cc5 from=seed src=0 shape=8c4af89d vocab=7e6ba108
-/
lemma le_ord_iff {x : X} (hx : coheight x = 1) {f : X.functionField}
    (hf : f ≠ 0) {n : ℤ} :
    n ≤ ord f x ↔ Multiplicative.ofAdd n ≤ ordHom x hx f := by
  rw [ord_eq_unzero_ordHom hx hf]
  nth_rw 1 [← toAdd_ofAdd n]
  rw [Multiplicative.toAdd_le, le_unzero_iff]

/--
@isnad1 id=le.1h4v.s7.f849a0c8c4d3 from=seed src=0 shape=dcb810ac vocab=b5904a4a
-/
lemma ord_add {x : X} [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {f g : X.functionField} (hfg : f + g ≠ 0) :
    min (ord f x) (ord g x) ≤ ord (f + g) x := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  by_cases! hx : coheight x ≠ 1
  · simp [hx]
  rw [inf_le_iff, ord_le_ord_iff hx hx hf hfg, ord_le_ord_iff hx hx hg hfg]
  exact inf_le_iff.mp <| Ring.ordFrac_add (R := X.presheaf.stalk x) _ _ hfg

/--
@isnad1 id=le.2h5v.s10.e6b12b33e679 from=seed src=0 shape=ece4d918 vocab=bcbba44f
-/
lemma ord_le_smul {x : X} {U : X.Opens} [Nonempty U] (hxU : x ∈ U)
    {a : Γ(X, U)} (ha : a ≠ 0) (f : X.functionField) : ord f x ≤ ord (a • f) x := by
  by_cases! hx : coheight x ≠ 1
  · simp [hx]
  by_cases hf : f = 0
  · simp [hf]
  have : a • f ≠ 0 := by simp [ha, Algebra.smul_def, hf, germToFunctionField_injective,
    RingHom.algebraMap_toAlgebra, map_ne_zero_iff]
  rw [ord_le_ord_iff hx hx hf this]
  algebraize [(X.presheaf.germ U x hxU).hom]
  have : Ring.KrullDimLE 1 ↑(X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have : IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk x) ↑X.functionField :=
    functionField_isScalarTower X U ⟨x, hxU⟩
  simp [ordHom, Ring.ordFrac_le_smul, RingHom.algebraMap_toAlgebra, map_ne_zero_iff,
    germ_injective_of_isIntegral, ha]

end AlgebraicGeometry.Scheme
