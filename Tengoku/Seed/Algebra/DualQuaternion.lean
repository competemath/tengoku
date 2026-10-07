/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.DualNumber
public import Tengoku.Seed.Algebra.Quaternion

/-!
# Dual quaternions

Similar to the way that rotations in 3D space can be represented by quaternions of unit length,
rigid motions in 3D space can be represented by dual quaternions of unit length.

## Main results

* `Quaternion.dualNumberEquiv`: quaternions over dual numbers or dual
  numbers over quaternions are equivalent constructions.

## References

* <https://en.wikipedia.org/wiki/Dual_quaternion>
-/

@[expose] public section


variable {R : Type*} [CommRing R]

namespace Quaternion

set_option backward.isDefEq.respectTransparency.types false in
/-- The dual quaternions can be equivalently represented as a quaternion with dual coefficients,
or as a dual number with quaternion coefficients.

See also `Matrix.dualNumberEquiv` for a similar result. -/
def dualNumberEquiv : Quaternion (DualNumber R) ≃ₐ[R] DualNumber (Quaternion R) where
  toFun q :=
    (⟨q.re.fst, q.imI.fst, q.imJ.fst, q.imK.fst⟩, ⟨q.re.snd, q.imI.snd, q.imJ.snd, q.imK.snd⟩)
  invFun d :=
    ⟨(d.fst.re, d.snd.re), (d.fst.imI, d.snd.imI), (d.fst.imJ, d.snd.imJ), (d.fst.imK, d.snd.imK)⟩
  map_mul' := by
    intros
    ext : 1
    · rfl
    · dsimp
      congr 1 <;> simp <;> ring
  map_add' := by
    intros
    rfl
  commutes' _ := rfl

/-! Lemmas characterizing `Quaternion.dualNumberEquiv`. -/


-- `simps` can't work on `DualNumber` because it's not a structure
/--
@isnad1 id=eq.0h2v.s11.9b1666975e5b from=seed src=0 shape=de9e068b vocab=370ac20b
-/
@[simp]
theorem re_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.re = q.re.fst :=
  rfl

/--
@isnad1 id=eq.0h2v.s11.ac9cf8571ec6 from=seed src=0 shape=de9e068b vocab=6c2f5e4c
-/
@[simp]
theorem imI_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.imI = q.imI.fst :=
  rfl

/--
@isnad1 id=eq.0h2v.s11.b24a7996c02d from=seed src=0 shape=de9e068b vocab=8c0fa457
-/
@[simp]
theorem imJ_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.imJ = q.imJ.fst :=
  rfl

/--
@isnad1 id=eq.0h2v.s11.47d7a1f8f567 from=seed src=0 shape=de9e068b vocab=13602119
-/
@[simp]
theorem imK_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).fst.imK = q.imK.fst :=
  rfl

/--
@isnad1 id=eq.0h2v.s11.acc0d86564a4 from=seed src=0 shape=de9e068b vocab=a871bc85
-/
@[simp]
theorem re_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.re = q.re.snd :=
  rfl

/--
@isnad1 id=eq.0h2v.s11.157d7a55d202 from=seed src=0 shape=de9e068b vocab=d79bd19f
-/
@[simp]
theorem imI_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.imI = q.imI.snd :=
  rfl

/--
@isnad1 id=eq.0h2v.s11.3a42c23248a0 from=seed src=0 shape=de9e068b vocab=20150bc4
-/
@[simp]
theorem imJ_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.imJ = q.imJ.snd :=
  rfl

/--
@isnad1 id=eq.0h2v.s11.5067da92fd4e from=seed src=0 shape=de9e068b vocab=ffd7db07
-/
@[simp]
theorem imK_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (dualNumberEquiv q).snd.imK = q.imK.snd :=
  rfl

/--
@isnad1 id=eq.0h2v.s11.be992bfa4dab from=seed src=0 shape=851ee395 vocab=12df61b4
-/
@[simp]
theorem fst_re_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).re.fst = d.fst.re :=
  rfl

/--
@isnad1 id=eq.0h2v.s11.7864e3482943 from=seed src=0 shape=851ee395 vocab=536853c1
-/
@[simp]
theorem fst_imI_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imI.fst = d.fst.imI :=
  rfl

/--
@isnad1 id=eq.0h2v.s11.c4bb5cec13a1 from=seed src=0 shape=851ee395 vocab=8f33e594
-/
@[simp]
theorem fst_imJ_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imJ.fst = d.fst.imJ :=
  rfl

/--
@isnad1 id=eq.0h2v.s11.e7d07a1b5b11 from=seed src=0 shape=851ee395 vocab=df4ba980
-/
@[simp]
theorem fst_imK_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imK.fst = d.fst.imK :=
  rfl

/--
@isnad1 id=eq.0h2v.s11.141809118876 from=seed src=0 shape=851ee395 vocab=a6470265
-/
@[simp]
theorem snd_re_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).re.snd = d.snd.re :=
  rfl

/--
@isnad1 id=eq.0h2v.s11.5e41b562219c from=seed src=0 shape=851ee395 vocab=13008648
-/
@[simp]
theorem snd_imI_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imI.snd = d.snd.imI :=
  rfl

/--
@isnad1 id=eq.0h2v.s11.acd2aa53662b from=seed src=0 shape=851ee395 vocab=a3ec9546
-/
@[simp]
theorem snd_imJ_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imJ.snd = d.snd.imJ :=
  rfl

/--
@isnad1 id=eq.0h2v.s11.6d3ef249682b from=seed src=0 shape=851ee395 vocab=08de1b28
-/
@[simp]
theorem snd_imK_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (dualNumberEquiv.symm d).imK.snd = d.snd.imK :=
  rfl

end Quaternion
