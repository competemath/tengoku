import Tengoku.DgLean.DG.Module.Hom
import Tengoku.DgLean.DG.Module.Shift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Shifting cochains of the Hom complex

Let `A` be a dg ring and `M`, `N` dg `A`-modules. This file studies how the cochains
`DG.Cochain A M N n` of the Hom complex behave with respect to the shifts `DG.Shift a M` and
`DG.Shift a N`. It is a port of Mathlib's `Mathlib/Algebra/Homology/HomotopyCategory/
HomComplexShift.lean`, with the same names and the same signs.

## Main definitions

For integers `n`, `a`, `n'`:

* `DG.Cochain.rightShift z a n' h : Cochain A M (Shift a N) n'` for `z : Cochain A M N n` and
  `h : n' + a = n`: the map `x ↦ z x`, without sign; its inverse is `DG.Cochain.rightUnshift`.
* `DG.Cochain.leftShift z a n' h : Cochain A (Shift a M) N n'` for `z : Cochain A M N n` and
  `h : n + a = n'`: the map `x ↦ (-1)^{a n' + a (a - 1) / 2} • z x`; its inverse is
  `DG.Cochain.leftUnshift`.
* `DG.Cochain.shift z a : Cochain A (Shift a M) (Shift a N) n`: the map `x ↦ z x`, without sign.
* The corresponding additive equivalences `DG.Cochain.rightShiftAddEquiv`,
  `DG.Cochain.leftShiftAddEquiv`, the additive map `DG.Cochain.shiftAddHom`, and the versions for
  cocycles `DG.Cocycle.rightShift`, `DG.Cocycle.leftShift`, `DG.Cocycle.shift`, ...

## Main results

* `DG.Cochain.δ_rightShift`, `DG.Cochain.δ_leftShift`, `DG.Cochain.δ_shift`: the differential
  commutes with the shifts up to the sign `(-1)^a`.
* `DG.Cochain.leftShift_comp`, `DG.Cochain.rightUnshift_comp`, `DG.Cochain.rightShift_comp`,
  `DG.Cochain.shift_comp`: compatibility with composition.
* `DG.Cochain.leftShift_rightShift_eq_negOnePow_rightShift_leftShift`: the left and right
  shifts commute up to the sign `(-1)^a`.

## Signs

The signs are exactly those of Mathlib, which follow the conventions of the introduction of
B. Conrad, *Grothendieck duality and base change*. With the action on `Shift a M` twisted by
`(-1)^{a |b|}` (see `DG.Shift`), all these maps are `A`-linear with the Koszul sign, i.e. they are
cochains: for `rightShift` and `shift` the twist is exactly compensated by the change of degree,
and for `leftShift` the twist `(-1)^{a |b|}` and the Koszul sign `(-1)^{n |b|}` of `z` combine to
the Koszul sign `(-1)^{n' |b|}` of a cochain of degree `n' = n + a`, whatever constant sign is
put in front. In particular no deviation from Mathlib's signs is needed.

Since cochains are functions here, Mathlib's lemmas `rightShift_v`, `leftShift_v`, ... on
components become the evaluation lemmas `rightShift_apply`, `leftShift_apply`, ....
Composition is written in the usual order (see `DG.Cochain.comp`): Mathlib's `γ.comp γ' h`
is `γ'.comp γ h` here.
-/

open scoped DG

namespace DG

namespace Cochain

open Shift

variable {A : Type*} {M N P : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]

/-- Two Koszul signs agree when the degrees differ by an even integer.-/
theorem _root_.DG.koszulSign_eq_of_sub_eq_two_mul {m n : ℤ} (k : ℤ) (h : m - n = 2 * k) :
    koszulSign m = koszulSign n :=
  (Int.negOnePow_eq_iff m n).2 ⟨k, by omega⟩

/-- The sign `(-1)^{a n' + a (a - 1) / 2}` appearing in `Cochain.leftShift`.-/
abbrev leftShiftSign (a n' : ℤ) : ℤˣ := koszulSign (a * n' + a * (a - 1) / 2)

section Defs

variable {n : ℤ} (z : Cochain A M N n)

/-- The cochain `Cochain A M (Shift a N) n'` attached to `z : Cochain A M N n` when
`n' + a = n`: the same underlying map, without sign (Mathlib's `Cochain.rightShift`).-/
def rightShift (a n' : ℤ) (hn' : n' + a = n) : Cochain A M (Shift a N) n' where
  toFun x := Shift.mk a (z x)
  map_zero' := by simp
  map_add' x y := by rw [map_add, mk_add]
  map_mem' i x hx := by
    rw [mem_grading_iff, add_assoc, hn']
    exact z.map_mem hx
  map_smul' {i b} hb x := by
    rw [z.map_smul hb, smul_mk hb, ← mk_units_smul, smul_smul, ← koszulSign_add, ← add_mul, hn']

/--
@isnad1 id=eq.1h8v.s8.f0a518c32999 from=translated src=- shape=50bdd478 vocab=f3c972d6
-/
@[simp]
theorem rightShift_apply (a n' : ℤ) (hn' : n' + a = n) (x : M) :
    z.rightShift a n' hn' x = Shift.mk a (z x) := rfl

/-- The cochain `Cochain A (Shift a M) N n'` attached to `z : Cochain A M N n` when
`n + a = n'`: the map `x ↦ (-1)^{a n' + a (a - 1) / 2} • z x` (Mathlib's
`Cochain.leftShift`, with the same sign).-/
def leftShift (a n' : ℤ) (hn' : n + a = n') : Cochain A (Shift a M) N n' where
  toFun x := leftShiftSign a n' • z (unmk a x)
  map_zero' := by simp
  map_add' x y := by rw [unmk_add, map_add, smul_add]
  map_mem' i x hx := by
    refine units_smul_mem_grading _ ?_
    rw [← hn', add_comm n a, ← add_assoc]
    exact z.map_mem (unmk_mem_grading hx)
  map_smul' {i b} hb x := by
    rw [unmk_smul hb, map_units_smul, z.map_smul hb, smul_comm b (leftShiftSign a n'),
      smul_smul, smul_smul, smul_smul, ← hn']
    congr 1
    simp only [← koszulSign_add]
    congr 1
    ring

/--
@isnad1 id=eq.1h8v.s8.0430b5e5c376 from=translated src=- shape=a793ba1e vocab=abc89efb
-/
theorem leftShift_apply (a n' : ℤ) (hn' : n + a = n') (x : Shift a M) :
    z.leftShift a n' hn' x = leftShiftSign a n' • z (unmk a x) := rfl

/--
@isnad1 id=eq.1h8v.s8.53dff7a34808 from=translated src=- shape=544fcb7f vocab=eab98b46
-/
@[simp]
theorem leftShift_apply_mk (a n' : ℤ) (hn' : n + a = n') (x : M) :
    z.leftShift a n' hn' (Shift.mk a x) = leftShiftSign a n' • z x := rfl

/-- The cochain `Cochain A (Shift a M) (Shift a N) n` attached to `z : Cochain A M N n`: the
same underlying map, without sign (Mathlib's `Cochain.shift`).-/
def shift (a : ℤ) : Cochain A (Shift a M) (Shift a N) n where
  toFun x := Shift.mk a (z (unmk a x))
  map_zero' := by simp
  map_add' x y := by rw [unmk_add, map_add, mk_add]
  map_mem' i x hx := by
    rw [mem_grading_iff, add_right_comm]
    exact z.map_mem (unmk_mem_grading hx)
  map_smul' {i b} hb x := by
    rw [unmk_smul hb, map_units_smul, z.map_smul hb, smul_mk hb, ← mk_units_smul, smul_smul,
      smul_smul, mul_comm]

/--
@isnad1 id=eq.0h7v.s8.387c81f77716 from=translated src=- shape=2560cba0 vocab=b6429eed
-/
theorem shift_apply (a : ℤ) (x : Shift a M) :
    z.shift a x = Shift.mk a (z (unmk a x)) := rfl

/--
@isnad1 id=eq.0h7v.s8.5184df301224 from=translated src=- shape=7a41a09d vocab=78fae006
-/
@[simp]
theorem shift_apply_mk (a : ℤ) (x : M) : z.shift a (Shift.mk a x) = Shift.mk a (z x) := rfl

end Defs

/-- The cochain `Cochain A M N n` attached to `z : Cochain A M (Shift a N) n'` when
`n' + a = n`: the inverse of `Cochain.rightShift` (Mathlib's `Cochain.rightUnshift`).-/
def rightUnshift {n' a : ℤ} (z : Cochain A M (Shift a N) n') (n : ℤ) (hn : n' + a = n) :
    Cochain A M N n where
  toFun x := unmk a (z x)
  map_zero' := by simp
  map_add' x y := by rw [map_add, unmk_add]
  map_mem' i x hx := by
    rw [← hn, ← add_assoc]
    exact unmk_mem_grading (z.map_mem hx)
  map_smul' {i b} hb x := by
    rw [z.map_smul hb, unmk_units_smul, unmk_smul hb, smul_smul, ← koszulSign_add, ← add_mul, hn]

/--
@isnad1 id=eq.1h8v.s8.24f7662ad610 from=translated src=- shape=b9eeace9 vocab=620e3688
-/
@[simp]
theorem rightUnshift_apply {n' a : ℤ} (z : Cochain A M (Shift a N) n') (n : ℤ)
    (hn : n' + a = n) (x : M) : z.rightUnshift n hn x = unmk a (z x) := rfl

/-- The cochain `Cochain A M N n` attached to `z : Cochain A (Shift a M) N n'` when
`n + a = n'`: the inverse of `Cochain.leftShift`, `x ↦ (-1)^{a n' + a (a - 1) / 2} • z x`
(Mathlib's `Cochain.leftUnshift`).-/
def leftUnshift {n' a : ℤ} (z : Cochain A (Shift a M) N n') (n : ℤ) (hn : n + a = n') :
    Cochain A M N n where
  toFun x := leftShiftSign a n' • z (Shift.mk a x)
  map_zero' := by simp
  map_add' x y := by rw [mk_add, map_add, smul_add]
  map_mem' i x hx := by
    refine units_smul_mem_grading _ ?_
    convert z.map_mem (mk_mem_grading (n := a) hx) using 2
    omega
  map_smul' {i b} hb x := by
    subst hn
    rw [mk_smul hb, map_units_smul, z.map_smul hb, smul_comm b (leftShiftSign a _),
      smul_smul, smul_smul, smul_smul]
    congr 1
    simp only [leftShiftSign, ← koszulSign_add]
    exact koszulSign_eq_of_sub_eq_two_mul (a * i) (by ring)

/--
@isnad1 id=eq.1h8v.s8.eaaa8211fb7b from=translated src=- shape=22572fb0 vocab=958a5d56
-/
@[simp]
theorem leftUnshift_apply {n' a : ℤ} (z : Cochain A (Shift a M) N n') (n : ℤ)
    (hn : n + a = n') (x : M) : z.leftUnshift n hn x = leftShiftSign a n' • z (Shift.mk a x) :=
  rfl

section Lemmas

variable {n : ℤ} (z z₁ z₂ : Cochain A M N n)

/--
@isnad1 id=eq.1h7v.s7.66bdd9423878 from=translated src=- shape=38df58b9 vocab=1b6a17be
-/
@[simp]
theorem rightUnshift_rightShift (a n' : ℤ) (hn' : n' + a = n) :
    (z.rightShift a n' hn').rightUnshift n hn' = z := rfl

/--
@isnad1 id=eq.1h7v.s7.3fdc57522322 from=translated src=- shape=06fb4da9 vocab=ddb2138a
-/
@[simp]
theorem rightShift_rightUnshift {a n' : ℤ} (z : Cochain A M (Shift a N) n') (n : ℤ)
    (hn' : n' + a = n) : (z.rightUnshift n hn').rightShift a n' hn' = z := rfl

/--
@isnad1 id=eq.1h7v.s7.28675a87fd17 from=translated src=- shape=385667f9 vocab=04503230
-/
@[simp]
theorem leftUnshift_leftShift (a n' : ℤ) (hn' : n + a = n') :
    (z.leftShift a n' hn').leftUnshift n hn' = z := by
  ext x
  simp [leftShift_apply, smul_smul]

/--
@isnad1 id=eq.1h7v.s7.cb3b2a09633f from=translated src=- shape=797a87db vocab=b55c3514
-/
@[simp]
theorem leftShift_leftUnshift {a n' : ℤ} (z : Cochain A (Shift a M) N n') (n : ℤ)
    (hn' : n + a = n') : (z.leftUnshift n hn').leftShift a n' hn' = z := by
  ext x
  simp [leftShift_apply, smul_smul]

/--
@isnad1 id=eq.1h8v.s8.e20daf7c28fd from=translated src=- shape=418e94fe vocab=63f85e2b
-/
@[simp]
theorem rightShift_add (a n' : ℤ) (hn' : n' + a = n) :
    (z₁ + z₂).rightShift a n' hn' = z₁.rightShift a n' hn' + z₂.rightShift a n' hn' := rfl

/--
@isnad1 id=eq.1h8v.s8.fb14f44eb82c from=translated src=- shape=b906aa48 vocab=57aa9bda
-/
@[simp]
theorem leftShift_add (a n' : ℤ) (hn' : n + a = n') :
    (z₁ + z₂).leftShift a n' hn' = z₁.leftShift a n' hn' + z₂.leftShift a n' hn' := by
  ext x
  simp [leftShift_apply, smul_add]

/--
@isnad1 id=eq.0h7v.s8.f0599645e955 from=translated src=- shape=423a1c5b vocab=db3ccda6
-/
@[simp]
theorem shift_add (a : ℤ) : (z₁ + z₂).shift a = z₁.shift a + z₂.shift a := rfl

variable (A M N) in
/-- The additive equivalence `Cochain A M N n ≃+ Cochain A M (Shift a N) n'` when
`n' + a = n`.-/
@[simps]
def rightShiftAddEquiv (n a n' : ℤ) (hn' : n' + a = n) :
    Cochain A M N n ≃+ Cochain A M (Shift a N) n' where
  toFun z := z.rightShift a n' hn'
  invFun z := z.rightUnshift n hn'
  left_inv z := rightUnshift_rightShift z a n' hn'
  right_inv z := rightShift_rightUnshift z n hn'
  map_add' z₁ z₂ := rightShift_add z₁ z₂ a n' hn'

variable (A M N) in
/-- The additive equivalence `Cochain A M N n ≃+ Cochain A (Shift a M) N n'` when
`n + a = n'`.-/
@[simps]
def leftShiftAddEquiv (n a n' : ℤ) (hn' : n + a = n') :
    Cochain A M N n ≃+ Cochain A (Shift a M) N n' where
  toFun z := z.leftShift a n' hn'
  invFun z := z.leftUnshift n hn'
  left_inv z := leftUnshift_leftShift z a n' hn'
  right_inv z := leftShift_leftUnshift z n hn'
  map_add' z₁ z₂ := leftShift_add z₁ z₂ a n' hn'

variable (A M N) in
/-- The additive map `Cochain A M N n →+ Cochain A (Shift a M) (Shift a N) n`.-/
@[simps]
def shiftAddHom (n a : ℤ) : Cochain A M N n →+ Cochain A (Shift a M) (Shift a N) n where
  toFun z := z.shift a
  map_zero' := rfl
  map_add' z₁ z₂ := shift_add z₁ z₂ a

variable (A M N n)

/--
@isnad1 id=eq.1h6v.s8.a1fce5a51854 from=translated src=- shape=2ad749a8 vocab=63f85e2b
-/
@[simp]
theorem rightShift_zero (a n' : ℤ) (hn' : n' + a = n) :
    (0 : Cochain A M N n).rightShift a n' hn' = 0 := rfl

/--
@isnad1 id=eq.1h6v.s7.1713e946da15 from=translated src=- shape=198dd1d0 vocab=4576c821
-/
@[simp]
theorem rightUnshift_zero (a n' : ℤ) (hn' : n' + a = n) :
    (0 : Cochain A M (Shift a N) n').rightUnshift n hn' = 0 := rfl

/--
@isnad1 id=eq.1h6v.s8.de3f4ad81aee from=translated src=- shape=73ab4d99 vocab=57aa9bda
-/
@[simp]
theorem leftShift_zero (a n' : ℤ) (hn' : n + a = n') :
    (0 : Cochain A M N n).leftShift a n' hn' = 0 :=
  map_zero (leftShiftAddEquiv A M N n a n' hn')

/--
@isnad1 id=eq.1h6v.s7.74abf08ea869 from=translated src=- shape=94b6863e vocab=cbb56bd3
-/
@[simp]
theorem leftUnshift_zero (a n' : ℤ) (hn' : n + a = n') :
    (0 : Cochain A (Shift a M) N n').leftUnshift n hn' = 0 :=
  map_zero (leftShiftAddEquiv A M N n a n' hn').symm

/--
@isnad1 id=eq.0h5v.s8.f58b8ed87169 from=translated src=- shape=1a75a760 vocab=33b5113a
-/
@[simp]
theorem shift_zero (a : ℤ) : (0 : Cochain A M N n).shift a = 0 := rfl

variable {A M N n}

/--
@isnad1 id=eq.1h7v.s7.d8546d34ec16 from=translated src=- shape=9fc5ecec vocab=15f275ae
-/
@[simp]
theorem rightShift_neg (a n' : ℤ) (hn' : n' + a = n) :
    (-z).rightShift a n' hn' = -z.rightShift a n' hn' := rfl

/--
@isnad1 id=eq.1h8v.s8.76ea255e4b98 from=translated src=- shape=5688a595 vocab=a38c0cb5
-/
@[simp]
theorem rightShift_sub (a n' : ℤ) (hn' : n' + a = n) :
    (z₁ - z₂).rightShift a n' hn' = z₁.rightShift a n' hn' - z₂.rightShift a n' hn' := rfl

/--
@isnad1 id=eq.1h7v.s7.a73af4ec04c2 from=translated src=- shape=5e70e5ca vocab=585f080d
-/
@[simp]
theorem rightUnshift_neg {n' a : ℤ} (z : Cochain A M (Shift a N) n') (n : ℤ) (hn : n' + a = n) :
    (-z).rightUnshift n hn = -z.rightUnshift n hn := rfl

/--
@isnad1 id=eq.1h8v.s8.fd2ca0301d0f from=translated src=- shape=882e30df vocab=4576c821
-/
@[simp]
theorem rightUnshift_add {n' a : ℤ} (z₁ z₂ : Cochain A M (Shift a N) n') (n : ℤ)
    (hn : n' + a = n) :
    (z₁ + z₂).rightUnshift n hn = z₁.rightUnshift n hn + z₂.rightUnshift n hn := rfl

/--
@isnad1 id=eq.1h7v.s7.ca020e7db6fe from=translated src=- shape=85bd2dbc vocab=72792343
-/
@[simp]
theorem leftShift_neg (a n' : ℤ) (hn' : n + a = n') :
    (-z).leftShift a n' hn' = -z.leftShift a n' hn' :=
  map_neg (leftShiftAddEquiv A M N n a n' hn') z

/--
@isnad1 id=eq.1h8v.s8.d96895f1ea8d from=translated src=- shape=69c25cb6 vocab=06ca9630
-/
@[simp]
theorem leftShift_sub (a n' : ℤ) (hn' : n + a = n') :
    (z₁ - z₂).leftShift a n' hn' = z₁.leftShift a n' hn' - z₂.leftShift a n' hn' :=
  map_sub (leftShiftAddEquiv A M N n a n' hn') z₁ z₂

/--
@isnad1 id=eq.1h7v.s7.c5400dc1fad0 from=translated src=- shape=17c65f65 vocab=45961a1b
-/
@[simp]
theorem leftUnshift_neg {n' a : ℤ} (z : Cochain A (Shift a M) N n') (n : ℤ) (hn : n + a = n') :
    (-z).leftUnshift n hn = -z.leftUnshift n hn :=
  map_neg (leftShiftAddEquiv A M N n a n' hn).symm z

/--
@isnad1 id=eq.1h8v.s8.cfb89a548f68 from=translated src=- shape=7292d3e3 vocab=cbb56bd3
-/
@[simp]
theorem leftUnshift_add {n' a : ℤ} (z₁ z₂ : Cochain A (Shift a M) N n') (n : ℤ)
    (hn : n + a = n') :
    (z₁ + z₂).leftUnshift n hn = z₁.leftUnshift n hn + z₂.leftUnshift n hn :=
  map_add (leftShiftAddEquiv A M N n a n' hn).symm z₁ z₂

/--
@isnad1 id=eq.0h6v.s8.534b4115d3d7 from=translated src=- shape=86792d50 vocab=8379a0d7
-/
@[simp]
theorem shift_neg (a : ℤ) : (-z).shift a = -z.shift a := rfl

/--
@isnad1 id=eq.0h7v.s8.d52af26bb93c from=translated src=- shape=423a1c5b vocab=4871e4b8
-/
@[simp]
theorem shift_sub (a : ℤ) : (z₁ - z₂).shift a = z₁.shift a - z₂.shift a := rfl

/--
@isnad1 id=eq.1h8v.s8.b7a9efeb36ab from=translated src=- shape=3f608e18 vocab=7c4dadbb
-/
@[simp]
theorem rightShift_zsmul (a n' : ℤ) (hn' : n' + a = n) (k : ℤ) :
    (k • z).rightShift a n' hn' = k • z.rightShift a n' hn' := rfl

/--
@isnad1 id=eq.1h8v.s8.5a1827da4d64 from=translated src=- shape=1fb4a96b vocab=5a4eeda4
-/
@[simp]
theorem rightShift_units_smul (a n' : ℤ) (hn' : n' + a = n) (u : ℤˣ) :
    (u • z).rightShift a n' hn' = u • z.rightShift a n' hn' := rfl

/--
@isnad1 id=eq.1h8v.s8.83281c779e98 from=translated src=- shape=895bd67a vocab=c392d6c4
-/
@[simp]
theorem rightUnshift_units_smul {n' a : ℤ} (z : Cochain A M (Shift a N) n') (n : ℤ)
    (hn : n' + a = n) (u : ℤˣ) : (u • z).rightUnshift n hn = u • z.rightUnshift n hn := rfl

/--
@isnad1 id=eq.1h8v.s8.03bb8f663cb5 from=translated src=- shape=037edf6e vocab=461bce11
-/
@[simp]
theorem leftShift_zsmul (a n' : ℤ) (hn' : n + a = n') (k : ℤ) :
    (k • z).leftShift a n' hn' = k • z.leftShift a n' hn' :=
  map_zsmul (leftShiftAddEquiv A M N n a n' hn') k z

/--
@isnad1 id=eq.1h8v.s8.be5ca959f6a4 from=translated src=- shape=95afcc5e vocab=b8ff7c55
-/
@[simp]
theorem leftShift_units_smul (a n' : ℤ) (hn' : n + a = n') (u : ℤˣ) :
    (u • z).leftShift a n' hn' = u • z.leftShift a n' hn' := by
  rw [Units.smul_def, Units.smul_def, leftShift_zsmul]

/--
@isnad1 id=eq.1h8v.s8.ca44449b892b from=translated src=- shape=169cc34a vocab=abf5dbf4
-/
@[simp]
theorem leftUnshift_units_smul {n' a : ℤ} (z : Cochain A (Shift a M) N n') (n : ℤ)
    (hn : n + a = n') (u : ℤˣ) : (u • z).leftUnshift n hn = u • z.leftUnshift n hn := by
  rw [Units.smul_def, Units.smul_def]
  exact map_zsmul (leftShiftAddEquiv A M N n a n' hn).symm _ z

/--
@isnad1 id=eq.0h7v.s8.b8e265fe5329 from=translated src=- shape=71043d9b vocab=53dfa475
-/
@[simp]
theorem shift_zsmul (a k : ℤ) : (k • z).shift a = k • z.shift a := rfl

/--
@isnad1 id=eq.0h7v.s8.e1817175c8f6 from=translated src=- shape=5e2dea5d vocab=c1d26364
-/
@[simp]
theorem shift_units_smul (a : ℤ) (u : ℤˣ) : (u • z).shift a = u • z.shift a := rfl

/--
@isnad1 id=eq.0h3v.s7.8849431e641b from=translated src=- shape=79492565 vocab=1a86e589
-/
@[simp]
theorem shift_id (a : ℤ) : (Cochain.id A M).shift a = Cochain.id A (Shift a M) := rfl

/--
@isnad1 id=eq.0h5v.s7.968a8d596878 from=translated src=- shape=849b6d01 vocab=539f9faf
-/
@[simp]
theorem shift_ofHom (φ : M →ᵈᵍ[A] N) (a : ℤ) : (ofHom φ).shift a = ofHom (φ.shift a) := rfl

/-! ### Composition -/

/-- The left shift of a composition (Mathlib's `Cochain.leftShift_comp`): for `z` of degree
`n` and `z'` of degree `m`, `(z' ∘ z).leftShift a = (-1)^{a m} • z' ∘ z.leftShift a`.
@isnad1 id=eq.3h12v.s8.f55ae17f7c33 from=translated src=- shape=96dd5a1e vocab=a5d5bde7
-/
theorem leftShift_comp (a n' : ℤ) (hn' : n + a = n') {m t t' : ℤ} (z' : Cochain A N P m)
    (h : n + m = t) (ht' : t + a = t') :
    (z'.comp z h).leftShift a t' ht' = koszulSign (a * m) • z'.comp (z.leftShift a n' hn')
      (by rw [← ht', ← h, ← hn', add_assoc, add_comm a, add_assoc]) := by
  ext x
  simp only [leftShift_apply, comp_apply, units_smul_apply, map_units_smul, smul_smul]
  congr 1
  simp only [leftShiftSign, ← koszulSign_add]
  congr 1
  rw [← ht', ← h, ← hn']
  ring

/--
@isnad1 id=eq.1h9v.s8.c979211dd3f4 from=translated src=- shape=9ce3757f vocab=61daac0b
-/
@[simp]
theorem leftShift_comp_zero_cochain (a n' : ℤ) (hn' : n + a = n') (z' : Cochain A N P 0) :
    (z'.comp z (add_zero n)).leftShift a n' hn' =
      z'.comp (z.leftShift a n' hn') (add_zero n') := by
  rw [leftShift_comp z a n' hn' z' (add_zero _) hn', mul_zero, koszulSign, Int.negOnePow_zero,
    one_smul]

/-- The shift of a composition is the composition of the shifts.
@isnad1 id=eq.1h10v.s8.77c1b133edec from=translated src=- shape=1acb2e5c vocab=77257fe2
-/
@[simp]
theorem shift_comp (a : ℤ) {m nm : ℤ} (z' : Cochain A N P m) (h : n + m = nm) :
    (z'.comp z h).shift a = (z'.shift a).comp (z.shift a) h := rfl

end Lemmas

/-! ### The differential -/

section Differential

variable [DGModule A M] [DGModule A N]

variable {n : ℤ} (z : Cochain A M N n)

/--
@isnad1 id=eq.2h9v.s8.6a3780c65e23 from=translated src=- shape=cbf61fe3 vocab=222e1aa9
-/
theorem δ_rightShift (a n' m' : ℤ) (hn' : n' + a = n) (m : ℤ) (hm' : m' + a = m) :
    δ n' m' (z.rightShift a n' hn') = koszulSign a • (δ n m z).rightShift a m' hm' := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by omega
    ext x
    apply (unmk a).injective
    simp only [δ_apply _ _ hnm', δ_apply _ _ hnm, rightShift_apply, units_smul_apply, unmk_sub,
      unmk_d, unmk_units_smul, unmk_mk, smul_sub, smul_smul, ← koszulSign_add]
    congr 2
    rw [Int.negOnePow_eq_iff]
    exact ⟨-a, by omega⟩
  · have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by omega)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, rightShift_zero, smul_zero]

/--
@isnad1 id=eq.2h9v.s8.cb59b6200e78 from=translated src=- shape=6d7102cc vocab=8c69348a
-/
theorem δ_rightUnshift {a n' : ℤ} (z : Cochain A M (Shift a N) n') (n : ℤ) (hn : n' + a = n)
    (m m' : ℤ) (hm' : m' + a = m) :
    δ n m (z.rightUnshift n hn) = koszulSign a • (δ n' m' z).rightUnshift m hm' := by
  obtain ⟨z, rfl⟩ := (rightShiftAddEquiv A M N n a n' hn).surjective z
  simp only [rightShiftAddEquiv_apply, rightUnshift_rightShift, z.δ_rightShift a n' m' hn m hm',
    rightUnshift_units_smul, smul_smul, Int.units_mul_self, one_smul]

/--
@isnad1 id=eq.2h9v.s8.58529773d2ae from=translated src=- shape=fe775aeb vocab=827e9003
-/
theorem δ_leftShift (a n' m' : ℤ) (hn' : n + a = n') (m : ℤ) (hm' : m + a = m') :
    δ n' m' (z.leftShift a n' hn') = koszulSign a • (δ n m z).leftShift a m' hm' := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by omega
    ext x
    simp only [δ_apply _ _ hnm', δ_apply _ _ hnm, leftShift_apply, units_smul_apply, unmk_d,
      d_units_smul, map_units_smul, smul_sub, smul_smul, leftShiftSign, ← koszulSign_add]
    congr 2
    all_goals rw [← hnm', ← hn']
    · exact koszulSign_eq_of_sub_eq_two_mul (-a) (by ring)
    · congr 1
      ring
  · have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by omega)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, leftShift_zero, smul_zero]

/--
@isnad1 id=eq.2h9v.s8.28027905fbf5 from=translated src=- shape=f99cce52 vocab=85397ace
-/
theorem δ_leftUnshift {a n' : ℤ} (z : Cochain A (Shift a M) N n') (n : ℤ) (hn : n + a = n')
    (m m' : ℤ) (hm' : m + a = m') :
    δ n m (z.leftUnshift n hn) = koszulSign a • (δ n' m' z).leftUnshift m hm' := by
  obtain ⟨z, rfl⟩ := (leftShiftAddEquiv A M N n a n' hn).surjective z
  simp only [leftShiftAddEquiv_apply, leftUnshift_leftShift, z.δ_leftShift a n' m' hn m hm',
    leftUnshift_units_smul, smul_smul, Int.units_mul_self, one_smul]

/--
@isnad1 id=eq.0h7v.s8.e5a4f90d25d5 from=translated src=- shape=acebfc5e vocab=7f9bd640
-/
@[simp]
theorem δ_shift (a m : ℤ) : δ n m (z.shift a) = koszulSign a • (δ n m z).shift a := by
  by_cases hnm : n + 1 = m
  · ext x
    apply (unmk a).injective
    simp only [δ_apply _ _ hnm, shift_apply, units_smul_apply, unmk_sub, unmk_d,
      unmk_units_smul, unmk_mk, map_units_smul, smul_sub, smul_smul]
    rw [mul_comm]
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm, shift_zero, smul_zero]

end Differential

/-! ### Left and right shifts -/

section LeftRight

variable {n : ℤ} (z : Cochain A M N n)

end LeftRight

end Cochain

namespace Cocycle

open Cochain

variable {A : Type*} {M N : Type*} [Ring A] [DGAddCommGroup A] [DGRing A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]
  {n : ℤ}

/-- The cocycle `Cocycle A M (Shift a N) n'` attached to `z : Cocycle A M N n` when
`n' + a = n`.-/
@[simps!]
def rightShift (z : Cocycle A M N n) (a n' : ℤ) (hn' : n' + a = n) :
    Cocycle A M (Shift a N) n' :=
  Cocycle.mk ((z : Cochain A M N n).rightShift a n' hn') _ rfl (by
    simp only [δ_rightShift _ a n' (n' + 1) hn' (n + 1) (by omega), δ_eq_zero, rightShift_zero,
      smul_zero])

/-- The cocycle `Cocycle A M N n` attached to `z : Cocycle A M (Shift a N) n'` when
`n' + a = n`.-/
@[simps!]
def rightUnshift {n' a : ℤ} (z : Cocycle A M (Shift a N) n') (n : ℤ) (hn : n' + a = n) :
    Cocycle A M N n :=
  Cocycle.mk ((z : Cochain A M (Shift a N) n').rightUnshift n hn) _ rfl (by
    rw [δ_rightUnshift _ n hn (n + 1) (n + 1 - a) (by omega), δ_eq_zero, rightUnshift_zero,
      smul_zero])

/-- The cocycle `Cocycle A (Shift a M) N n'` attached to `z : Cocycle A M N n` when
`n + a = n'`.-/
@[simps!]
def leftShift (z : Cocycle A M N n) (a n' : ℤ) (hn' : n + a = n') :
    Cocycle A (Shift a M) N n' :=
  Cocycle.mk ((z : Cochain A M N n).leftShift a n' hn') _ rfl (by
    simp only [δ_leftShift _ a n' (n' + 1) hn' (n + 1) (by omega), δ_eq_zero, leftShift_zero,
      smul_zero])

/-- The cocycle `Cocycle A M N n` attached to `z : Cocycle A (Shift a M) N n'` when
`n + a = n'`.-/
@[simps!]
def leftUnshift {n' a : ℤ} (z : Cocycle A (Shift a M) N n') (n : ℤ) (hn : n + a = n') :
    Cocycle A M N n :=
  Cocycle.mk ((z : Cochain A (Shift a M) N n').leftUnshift n hn) _ rfl (by
    rw [δ_leftUnshift _ n hn (n + 1) (n + 1 + a) rfl, δ_eq_zero, leftUnshift_zero, smul_zero])

/-- The cocycle `Cocycle A (Shift a M) (Shift a N) n` attached to `z : Cocycle A M N n`.-/
@[simps!]
def shift (z : Cocycle A M N n) (a : ℤ) : Cocycle A (Shift a M) (Shift a N) n :=
  Cocycle.mk ((z : Cochain A M N n).shift a) _ rfl
    (by simp only [δ_shift, δ_eq_zero, shift_zero, smul_zero])

end Cocycle

end DG
