import Tengoku.DgLean.DG.Category.Homotopy.Shift
import Tengoku.DgLean.DG.Module.HomShift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Shifting cochains of the Hom complex of dg modules over a dg category

Let `C` be a dg category and `M`, `N` dg modules over `C`. This file studies how the cochains
`DG.CatModule.Cochain M N n` behave with respect to the shifts `M⟦a⟧ = shift a M` and
`N⟦a⟧`. It is a port of `DG.Module.HomShift` (itself a port of Mathlib's
`Mathlib/Algebra/Homology/HomotopyCategory/HomComplexShift.lean`), with the same names, in the
namespace `DG.CatModule`, and the same signs.

## Main definitions

For integers `n`, `a`, `n'`:

* `DG.CatModule.Cochain.rightShift z a n' h : Cochain M (shift a N) n'` for
  `z : Cochain M N n` and `h : n' + a = n`: the maps `x ↦ z x`, without sign; its inverse is
  `DG.CatModule.Cochain.rightUnshift`.
* `DG.CatModule.Cochain.leftShift z a n' h : Cochain (shift a M) N n'` for `z : Cochain M N n`
  and `h : n + a = n'`: the maps `x ↦ (-1)^{a n' + a (a - 1) / 2} • z x`; its inverse is
  `DG.CatModule.Cochain.leftUnshift`.
* `DG.CatModule.Cochain.shift z a : Cochain (shift a M) (shift a N) n`, without sign.
* The additive equivalences `rightShiftAddEquiv`, `leftShiftAddEquiv`, the additive map
  `shiftAddHom`, and the versions for cocycles `DG.CatModule.Cocycle.rightShift`, ...

## Main results

* `DG.CatModule.Cochain.δ_rightShift`, `δ_leftShift`, `δ_shift`: the differential commutes
  with the shifts up to the sign `(-1)^a`.
* `DG.CatModule.Cochain.leftShift_comp`, `rightShift_comp`, `shift_comp`, ...: compatibility
  with composition.
* `DG.CatModule.Cochain.leftShift_rightShift_eq_negOnePow_rightShift_leftShift`.

The sign `DG.Cochain.leftShiftSign` and the lemma `DG.koszulSign_eq_of_sub_eq_two_mul` of the
dg-ring version are reused.
-/

open scoped DG

open CategoryTheory

universe w v u

namespace DG

namespace CatModule

variable {C : Type u} [Category.{v} C] [Preadditive C] [∀ X Y : C, DGAddCommGroup (X ⟶ Y)]
  [DGCategory C]

namespace Cochain

open DG.Cochain (leftShiftSign)

variable {M N P : CatModule.{w} C}

section Defs

variable {n : ℤ} (z : Cochain M N n)

/-- The cochain `Cochain M (shift a N) n'` attached to `z : Cochain M N n` when `n' + a = n`:
the same underlying maps, without sign (Mathlib's `Cochain.rightShift`).-/
def rightShift (a n' : ℤ) (hn' : n' + a = n) : Cochain M (shift a N) n' where
  app X := (shift.mk a).toAddMonoidHom.comp (z.app X)
  map_mem' {X i x} hx := by
    change shift.mk a (z.app X x) ∈ grading (i + n')
    rw [shift.mem_grading_iff, add_assoc, hn']
    exact z.map_mem hx
  map_smul' {X Y i f} hf x := by
    change shift.mk a (z.app Y (f • x)) = _ • (f • shift.mk a (z.app X x))
    rw [z.map_smul hf, shift.smul_mk hf, ← shift.mk_units_smul, smul_smul, ← koszulSign_add,
      ← add_mul, hn']

/--
@isnad1 id=eq.1h9v.s10.68b92a99f401 from=translated src=- shape=0dd88d21 vocab=9a74051a
-/
@[simp]
theorem rightShift_apply (a n' : ℤ) (hn' : n' + a = n) {X : C} (x : M.obj X) :
    (z.rightShift a n' hn').app X x = shift.mk a (z.app X x) := rfl

/-- The cochain `Cochain (shift a M) N n'` attached to `z : Cochain M N n` when `n + a = n'`:
the maps `x ↦ (-1)^{a n' + a (a - 1) / 2} • z x` (Mathlib's `Cochain.leftShift`, with the same
sign).-/
def leftShift (a n' : ℤ) (hn' : n + a = n') : Cochain (shift a M) N n' where
  app X := leftShiftSign a n' • (z.app X).comp (shift.unmk a).toAddMonoidHom
  map_mem' {X i x} hx := by
    change leftShiftSign a n' • z.app X (shift.unmk a x) ∈ grading (i + n')
    refine units_smul_mem_grading _ ?_
    rw [← hn', add_comm n a, ← add_assoc]
    exact z.map_mem (shift.unmk_mem_grading hx)
  map_smul' {X Y i f} hf x := by
    change leftShiftSign a n' • z.app Y (shift.unmk a (f • x)) =
      _ • (f • (leftShiftSign a n' • z.app X (shift.unmk a x)))
    rw [shift.unmk_smul hf, map_units_smul, z.map_smul hf, smul_units_smul,
      smul_smul, smul_smul, smul_smul, ← hn']
    congr 1
    simp only [← koszulSign_add]
    congr 1
    ring

/--
@isnad1 id=eq.1h9v.s10.2bdfde9b31c2 from=translated src=- shape=2e7a6998 vocab=b60b193b
-/
theorem leftShift_apply (a n' : ℤ) (hn' : n + a = n') {X : C} (x : (shift a M).obj X) :
    (z.leftShift a n' hn').app X x = leftShiftSign a n' • z.app X (shift.unmk a x) := rfl

/--
@isnad1 id=eq.1h9v.s10.ede81648d5c9 from=translated src=- shape=77097b73 vocab=4fbb3b37
-/
@[simp]
theorem leftShift_apply_mk (a n' : ℤ) (hn' : n + a = n') {X : C} (x : M.obj X) :
    (z.leftShift a n' hn').app X (shift.mk a x) = leftShiftSign a n' • z.app X x := rfl

/-- The cochain `Cochain (shift a M) (shift a N) n` attached to `z : Cochain M N n`: the same
underlying maps, without sign (Mathlib's `Cochain.shift`).-/
def shift (a : ℤ) : Cochain (CatModule.shift a M) (CatModule.shift a N) n where
  app X := (shift.mk a).toAddMonoidHom.comp ((z.app X).comp (shift.unmk a).toAddMonoidHom)
  map_mem' {X i x} hx := by
    change shift.mk a (z.app X (shift.unmk a x)) ∈ grading (i + n)
    rw [shift.mem_grading_iff, add_right_comm]
    exact z.map_mem (shift.unmk_mem_grading hx)
  map_smul' {X Y i f} hf x := by
    change shift.mk a (z.app Y (shift.unmk a (f • x))) =
      _ • (f • shift.mk a (z.app X (shift.unmk a x)))
    rw [shift.unmk_smul hf, map_units_smul, z.map_smul hf, shift.smul_mk hf,
      ← shift.mk_units_smul, smul_smul, smul_smul, mul_comm]

/--
@isnad1 id=eq.0h8v.s10.6b7a9c22101d from=translated src=- shape=358bfcde vocab=8a0082f8
-/
theorem shift_apply (a : ℤ) {X : C} (x : (CatModule.shift a M).obj X) :
    (z.shift a).app X x = shift.mk a (z.app X (shift.unmk a x)) := rfl

/--
@isnad1 id=eq.0h8v.s10.69f08c6a8294 from=translated src=- shape=7a519e4a vocab=f2071eae
-/
@[simp]
theorem shift_apply_mk (a : ℤ) {X : C} (x : M.obj X) :
    (z.shift a).app X (shift.mk a x) = shift.mk a (z.app X x) := rfl

end Defs

/-- The cochain `Cochain M N n` attached to `z : Cochain M (shift a N) n'` when `n' + a = n`:
the inverse of `Cochain.rightShift` (Mathlib's `Cochain.rightUnshift`).-/
def rightUnshift {n' a : ℤ} (z : Cochain M (CatModule.shift a N) n') (n : ℤ)
    (hn : n' + a = n) : Cochain M N n where
  app X := (shift.unmk a).toAddMonoidHom.comp (z.app X)
  map_mem' {X i x} hx := by
    change shift.unmk a (z.app X x) ∈ grading (i + n)
    rw [← hn, ← add_assoc]
    exact shift.unmk_mem_grading (z.map_mem hx)
  map_smul' {X Y i f} hf x := by
    change shift.unmk a (z.app Y (f • x)) = _ • (f • shift.unmk a (z.app X x))
    rw [z.map_smul hf, shift.unmk_units_smul, shift.unmk_smul hf, smul_smul, ← koszulSign_add,
      ← add_mul, hn]

/--
@isnad1 id=eq.1h9v.s10.b3293c0ffd4e from=translated src=- shape=1b9ab237 vocab=f4e4e90c
-/
@[simp]
theorem rightUnshift_apply {n' a : ℤ} (z : Cochain M (CatModule.shift a N) n') (n : ℤ)
    (hn : n' + a = n) {X : C} (x : M.obj X) :
    (z.rightUnshift n hn).app X x = shift.unmk a (z.app X x) := rfl

/-- The cochain `Cochain M N n` attached to `z : Cochain (shift a M) N n'` when `n + a = n'`:
the inverse of `Cochain.leftShift`, `x ↦ (-1)^{a n' + a (a - 1) / 2} • z x` (Mathlib's
`Cochain.leftUnshift`).-/
def leftUnshift {n' a : ℤ} (z : Cochain (CatModule.shift a M) N n') (n : ℤ)
    (hn : n + a = n') : Cochain M N n where
  app X := leftShiftSign a n' • (z.app X).comp (shift.mk a).toAddMonoidHom
  map_mem' {X i x} hx := by
    change leftShiftSign a n' • z.app X (shift.mk a x) ∈ grading (i + n)
    refine units_smul_mem_grading _ ?_
    convert z.map_mem (shift.mk_mem_grading (n := a) hx) using 2
    omega
  map_smul' {X Y i f} hf x := by
    change leftShiftSign a n' • z.app Y (shift.mk a (f • x)) =
      _ • (f • (leftShiftSign a n' • z.app X (shift.mk a x)))
    subst hn
    rw [shift.mk_smul hf, map_units_smul, z.map_smul hf, smul_units_smul,
      smul_smul, smul_smul, smul_smul]
    congr 1
    simp only [leftShiftSign, ← koszulSign_add]
    exact koszulSign_eq_of_sub_eq_two_mul (a * i) (by ring)

/--
@isnad1 id=eq.1h9v.s10.b7d97c09167b from=translated src=- shape=db7e3c7b vocab=60683df5
-/
@[simp]
theorem leftUnshift_apply {n' a : ℤ} (z : Cochain (CatModule.shift a M) N n') (n : ℤ)
    (hn : n + a = n') {X : C} (x : M.obj X) :
    (z.leftUnshift n hn).app X x = leftShiftSign a n' • z.app X (shift.mk a x) :=
  rfl

section Lemmas

variable {n : ℤ} (z z₁ z₂ : Cochain M N n)

/--
@isnad1 id=eq.1h7v.s6.cacb97731c24 from=translated src=- shape=86ed959f vocab=d0e40e08
-/
@[simp]
theorem rightUnshift_rightShift (a n' : ℤ) (hn' : n' + a = n) :
    (z.rightShift a n' hn').rightUnshift n hn' = z := rfl

/--
@isnad1 id=eq.1h7v.s6.6217f5eaf495 from=translated src=- shape=b0e96cb6 vocab=0820f283
-/
@[simp]
theorem rightShift_rightUnshift {a n' : ℤ} (z : Cochain M (CatModule.shift a N) n') (n : ℤ)
    (hn' : n' + a = n) : (z.rightUnshift n hn').rightShift a n' hn' = z := rfl

/--
@isnad1 id=eq.1h7v.s6.752497f08d4f from=translated src=- shape=cfe4f199 vocab=cca487d9
-/
@[simp]
theorem leftUnshift_leftShift (a n' : ℤ) (hn' : n + a = n') :
    (z.leftShift a n' hn').leftUnshift n hn' = z := by
  ext X x
  rw [leftUnshift_apply, leftShift_apply_mk, smul_smul, Int.units_mul_self, one_smul]

/--
@isnad1 id=eq.1h7v.s6.624532611fc7 from=translated src=- shape=db11502c vocab=9727a616
-/
@[simp]
theorem leftShift_leftUnshift {a n' : ℤ} (z : Cochain (CatModule.shift a M) N n') (n : ℤ)
    (hn' : n + a = n') : (z.leftUnshift n hn').leftShift a n' hn' = z := by
  ext X x
  obtain ⟨x, rfl⟩ := shift.mk_surjective x
  rw [leftShift_apply_mk, leftUnshift_apply, smul_smul, Int.units_mul_self, one_smul]

/--
@isnad1 id=eq.1h8v.s8.c9e0004c1d51 from=translated src=- shape=e9a5d6c6 vocab=a3bd8fbf
-/
@[simp]
theorem rightShift_add (a n' : ℤ) (hn' : n' + a = n) :
    (z₁ + z₂).rightShift a n' hn' = z₁.rightShift a n' hn' + z₂.rightShift a n' hn' :=
  ext fun _ _ => map_add (shift.mk a) _ _

/--
@isnad1 id=eq.1h8v.s8.0ef575987301 from=translated src=- shape=fb667914 vocab=39842c07
-/
@[simp]
theorem leftShift_add (a n' : ℤ) (hn' : n + a = n') :
    (z₁ + z₂).leftShift a n' hn' = z₁.leftShift a n' hn' + z₂.leftShift a n' hn' := by
  ext X x
  rw [leftShift_apply, Cochain.add_apply, Cochain.add_apply, leftShift_apply, leftShift_apply,
    _root_.smul_add]

/--
@isnad1 id=eq.0h7v.s8.f4b8af441a0d from=translated src=- shape=8e62e87e vocab=0a0b4bd8
-/
@[simp]
theorem shift_add (a : ℤ) : (z₁ + z₂).shift a = z₁.shift a + z₂.shift a :=
  ext fun _ _ => map_add (shift.mk a) _ _

variable (M N) in
/-- The additive equivalence `Cochain M N n ≃+ Cochain M (shift a N) n'` when `n' + a = n`.-/
@[simps]
def rightShiftAddEquiv (n a n' : ℤ) (hn' : n' + a = n) :
    Cochain M N n ≃+ Cochain M (CatModule.shift a N) n' where
  toFun z := z.rightShift a n' hn'
  invFun z := z.rightUnshift n hn'
  left_inv z := rightUnshift_rightShift z a n' hn'
  right_inv z := rightShift_rightUnshift z n hn'
  map_add' z₁ z₂ := rightShift_add z₁ z₂ a n' hn'

variable (M N) in
/-- The additive equivalence `Cochain M N n ≃+ Cochain (shift a M) N n'` when `n + a = n'`.-/
@[simps]
def leftShiftAddEquiv (n a n' : ℤ) (hn' : n + a = n') :
    Cochain M N n ≃+ Cochain (CatModule.shift a M) N n' where
  toFun z := z.leftShift a n' hn'
  invFun z := z.leftUnshift n hn'
  left_inv z := leftUnshift_leftShift z a n' hn'
  right_inv z := leftShift_leftUnshift z n hn'
  map_add' z₁ z₂ := leftShift_add z₁ z₂ a n' hn'

variable (M N) in
/-- The additive map `Cochain M N n →+ Cochain (shift a M) (shift a N) n`.-/
@[simps]
def shiftAddHom (n a : ℤ) :
    Cochain M N n →+ Cochain (CatModule.shift a M) (CatModule.shift a N) n where
  toFun z := z.shift a
  map_zero' := ext fun _ _ => map_zero (shift.mk (M := N) a)
  map_add' z₁ z₂ := shift_add z₁ z₂ a

variable (M N n)

/--
@isnad1 id=eq.1h6v.s7.4e11acebf8d9 from=translated src=- shape=3bfae3ff vocab=a3bd8fbf
-/
@[simp]
theorem rightShift_zero (a n' : ℤ) (hn' : n' + a = n) :
    (0 : Cochain M N n).rightShift a n' hn' = 0 :=
  map_zero (rightShiftAddEquiv M N n a n' hn')

/--
@isnad1 id=eq.1h6v.s7.0088b0d77f3e from=translated src=- shape=447dde56 vocab=403ef4b4
-/
@[simp]
theorem rightUnshift_zero (a n' : ℤ) (hn' : n' + a = n) :
    (0 : Cochain M (CatModule.shift a N) n').rightUnshift n hn' = 0 :=
  map_zero (rightShiftAddEquiv M N n a n' hn').symm

/--
@isnad1 id=eq.1h6v.s7.a27478042a6f from=translated src=- shape=59bc8c47 vocab=39842c07
-/
@[simp]
theorem leftShift_zero (a n' : ℤ) (hn' : n + a = n') :
    (0 : Cochain M N n).leftShift a n' hn' = 0 :=
  map_zero (leftShiftAddEquiv M N n a n' hn')

/--
@isnad1 id=eq.1h6v.s7.9c003ef5bf96 from=translated src=- shape=4a2832ab vocab=cd9272d6
-/
@[simp]
theorem leftUnshift_zero (a n' : ℤ) (hn' : n + a = n') :
    (0 : Cochain (CatModule.shift a M) N n').leftUnshift n hn' = 0 :=
  map_zero (leftShiftAddEquiv M N n a n' hn').symm

/--
@isnad1 id=eq.0h5v.s7.ab6e2c859b2a from=translated src=- shape=846b677a vocab=cd3a3ba6
-/
@[simp]
theorem shift_zero (a : ℤ) : (0 : Cochain M N n).shift a = 0 :=
  map_zero (shiftAddHom M N n a)

variable {M N n}

/--
@isnad1 id=eq.1h7v.s7.52062b5a1377 from=translated src=- shape=94e0c065 vocab=399ab0d2
-/
@[simp]
theorem rightShift_neg (a n' : ℤ) (hn' : n' + a = n) :
    (-z).rightShift a n' hn' = -z.rightShift a n' hn' :=
  map_neg (rightShiftAddEquiv M N n a n' hn') z

/--
@isnad1 id=eq.1h8v.s8.ddcc4ae9754f from=translated src=- shape=ffc8040c vocab=eaf92327
-/
@[simp]
theorem rightShift_sub (a n' : ℤ) (hn' : n' + a = n) :
    (z₁ - z₂).rightShift a n' hn' = z₁.rightShift a n' hn' - z₂.rightShift a n' hn' :=
  map_sub (rightShiftAddEquiv M N n a n' hn') z₁ z₂

/--
@isnad1 id=eq.1h7v.s7.b635fb3b3fbf from=translated src=- shape=5fafd1bf vocab=f3b4d52f
-/
@[simp]
theorem rightUnshift_neg {n' a : ℤ} (z : Cochain M (CatModule.shift a N) n') (n : ℤ)
    (hn : n' + a = n) : (-z).rightUnshift n hn = -z.rightUnshift n hn :=
  map_neg (rightShiftAddEquiv M N n a n' hn).symm z

/--
@isnad1 id=eq.1h8v.s8.8d593551cf5e from=translated src=- shape=1a5d60b5 vocab=403ef4b4
-/
@[simp]
theorem rightUnshift_add {n' a : ℤ} (z₁ z₂ : Cochain M (CatModule.shift a N) n') (n : ℤ)
    (hn : n' + a = n) :
    (z₁ + z₂).rightUnshift n hn = z₁.rightUnshift n hn + z₂.rightUnshift n hn :=
  map_add (rightShiftAddEquiv M N n a n' hn).symm z₁ z₂

/--
@isnad1 id=eq.1h7v.s7.a6e71d3763e2 from=translated src=- shape=27d6a79f vocab=44067622
-/
@[simp]
theorem leftShift_neg (a n' : ℤ) (hn' : n + a = n') :
    (-z).leftShift a n' hn' = -z.leftShift a n' hn' :=
  map_neg (leftShiftAddEquiv M N n a n' hn') z

/--
@isnad1 id=eq.1h8v.s8.5bb22f880854 from=translated src=- shape=e9a1ff6e vocab=d7790694
-/
@[simp]
theorem leftShift_sub (a n' : ℤ) (hn' : n + a = n') :
    (z₁ - z₂).leftShift a n' hn' = z₁.leftShift a n' hn' - z₂.leftShift a n' hn' :=
  map_sub (leftShiftAddEquiv M N n a n' hn') z₁ z₂

/--
@isnad1 id=eq.1h7v.s7.d443fa185d7d from=translated src=- shape=1edfdce5 vocab=e1aa5351
-/
@[simp]
theorem leftUnshift_neg {n' a : ℤ} (z : Cochain (CatModule.shift a M) N n') (n : ℤ)
    (hn : n + a = n') : (-z).leftUnshift n hn = -z.leftUnshift n hn :=
  map_neg (leftShiftAddEquiv M N n a n' hn).symm z

/--
@isnad1 id=eq.1h8v.s8.1fd4c34837fe from=translated src=- shape=f0124f1b vocab=cd9272d6
-/
@[simp]
theorem leftUnshift_add {n' a : ℤ} (z₁ z₂ : Cochain (CatModule.shift a M) N n') (n : ℤ)
    (hn : n + a = n') :
    (z₁ + z₂).leftUnshift n hn = z₁.leftUnshift n hn + z₂.leftUnshift n hn :=
  map_add (leftShiftAddEquiv M N n a n' hn).symm z₁ z₂

/--
@isnad1 id=eq.0h6v.s7.43aa6bf0ded7 from=translated src=- shape=fa562052 vocab=ecc5f430
-/
@[simp]
theorem shift_neg (a : ℤ) : (-z).shift a = -z.shift a := map_neg (shiftAddHom M N n a) z

/--
@isnad1 id=eq.0h7v.s8.1ff907b8f432 from=translated src=- shape=8e62e87e vocab=a4673946
-/
@[simp]
theorem shift_sub (a : ℤ) : (z₁ - z₂).shift a = z₁.shift a - z₂.shift a :=
  map_sub (shiftAddHom M N n a) z₁ z₂

/--
@isnad1 id=eq.1h8v.s7.e5fa569ba13f from=translated src=- shape=4980a9b0 vocab=e8631a65
-/
@[simp]
theorem rightShift_zsmul (a n' : ℤ) (hn' : n' + a = n) (k : ℤ) :
    (k • z).rightShift a n' hn' = k • z.rightShift a n' hn' :=
  map_zsmul (rightShiftAddEquiv M N n a n' hn') k z

/--
@isnad1 id=eq.1h8v.s8.6b5f60692224 from=translated src=- shape=e5b5c171 vocab=ff8993e8
-/
@[simp]
theorem rightShift_units_smul (a n' : ℤ) (hn' : n' + a = n) (u : ℤˣ) :
    (u • z).rightShift a n' hn' = u • z.rightShift a n' hn' := by
  rw [Units.smul_def, Units.smul_def, rightShift_zsmul]

/--
@isnad1 id=eq.1h8v.s8.09f871bdd2f9 from=translated src=- shape=7197c00b vocab=510e013f
-/
@[simp]
theorem rightUnshift_units_smul {n' a : ℤ} (z : Cochain M (CatModule.shift a N) n') (n : ℤ)
    (hn : n' + a = n) (u : ℤˣ) : (u • z).rightUnshift n hn = u • z.rightUnshift n hn := by
  rw [Units.smul_def, Units.smul_def]
  exact map_zsmul (rightShiftAddEquiv M N n a n' hn).symm _ z

/--
@isnad1 id=eq.1h8v.s7.dff22f40618a from=translated src=- shape=9e68ba8b vocab=38d9b8bd
-/
@[simp]
theorem leftShift_zsmul (a n' : ℤ) (hn' : n + a = n') (k : ℤ) :
    (k • z).leftShift a n' hn' = k • z.leftShift a n' hn' :=
  map_zsmul (leftShiftAddEquiv M N n a n' hn') k z

/--
@isnad1 id=eq.1h8v.s8.1907cd53a177 from=translated src=- shape=3a8609a4 vocab=8330a6df
-/
@[simp]
theorem leftShift_units_smul (a n' : ℤ) (hn' : n + a = n') (u : ℤˣ) :
    (u • z).leftShift a n' hn' = u • z.leftShift a n' hn' := by
  rw [Units.smul_def, Units.smul_def, leftShift_zsmul]

/--
@isnad1 id=eq.1h8v.s8.13fe37930e43 from=translated src=- shape=46317558 vocab=11f77cc5
-/
@[simp]
theorem leftUnshift_units_smul {n' a : ℤ} (z : Cochain (CatModule.shift a M) N n') (n : ℤ)
    (hn : n + a = n') (u : ℤˣ) : (u • z).leftUnshift n hn = u • z.leftUnshift n hn := by
  rw [Units.smul_def, Units.smul_def]
  exact map_zsmul (leftShiftAddEquiv M N n a n' hn).symm _ z

/--
@isnad1 id=eq.0h7v.s7.c88b3f680a6a from=translated src=- shape=5bbc16b1 vocab=908b11e6
-/
@[simp]
theorem shift_zsmul (a k : ℤ) : (k • z).shift a = k • z.shift a :=
  map_zsmul (shiftAddHom M N n a) k z

/--
@isnad1 id=eq.0h7v.s8.cfbf1a974d01 from=translated src=- shape=5bc3cec3 vocab=e2f46072
-/
@[simp]
theorem shift_units_smul (a : ℤ) (u : ℤˣ) : (u • z).shift a = u • z.shift a := by
  rw [Units.smul_def, Units.smul_def, shift_zsmul]

/--
@isnad1 id=eq.0h3v.s6.a6ac8d22923a from=translated src=- shape=62b41eb2 vocab=322061dc
-/
@[simp]
theorem shift_id (a : ℤ) : (Cochain.id M).shift a = Cochain.id (CatModule.shift a M) := rfl

/--
@isnad1 id=eq.0h5v.s7.ad4d6ba78d47 from=translated src=- shape=c98b71eb vocab=093952c9
-/
@[simp]
theorem shift_ofHom (φ : M ⟶ N) (a : ℤ) : (ofHom φ).shift a = ofHom (shiftMap a φ) := rfl

/-! ### Composition -/

/-- The left shift of a composition (Mathlib's `Cochain.leftShift_comp`): for `z` of degree
`n` and `z'` of degree `m`, `(z' ∘ z).leftShift a = (-1)^{a m} • z' ∘ z.leftShift a`.
@isnad1 id=eq.3h12v.s8.17139c5052dd from=translated src=- shape=3d5a8464 vocab=c8e6b3f9
-/
theorem leftShift_comp (a n' : ℤ) (hn' : n + a = n') {m t t' : ℤ} (z' : Cochain N P m)
    (h : n + m = t) (ht' : t + a = t') :
    (z'.comp z h).leftShift a t' ht' = koszulSign (a * m) • z'.comp (z.leftShift a n' hn')
      (by rw [← ht', ← h, ← hn', add_assoc, add_comm a, add_assoc]) := by
  ext X x
  simp only [leftShift_apply, comp_apply, units_smul_apply, map_units_smul, smul_smul]
  congr 1
  simp only [leftShiftSign, ← koszulSign_add]
  congr 1
  rw [← ht', ← h, ← hn']
  ring

/--
@isnad1 id=eq.1h9v.s7.6713988cb131 from=translated src=- shape=c9d306d8 vocab=f7806bdb
-/
@[simp]
theorem leftShift_comp_zero_cochain (a n' : ℤ) (hn' : n + a = n') (z' : Cochain N P 0) :
    (z'.comp z (add_zero n)).leftShift a n' hn' =
      z'.comp (z.leftShift a n' hn') (add_zero n') := by
  rw [leftShift_comp z a n' hn' z' (add_zero _) hn', mul_zero, koszulSign, Int.negOnePow_zero,
    one_smul]

/-- The shift of a composition is the composition of the shifts.
@isnad1 id=eq.1h10v.s7.66e50beca18b from=translated src=- shape=158a7eea vocab=bc6ff318
-/
@[simp]
theorem shift_comp (a : ℤ) {m nm : ℤ} (z' : Cochain N P m) (h : n + m = nm) :
    (z'.comp z h).shift a = (z'.shift a).comp (z.shift a) h := rfl

end Lemmas

/-! ### The differential -/

section Differential

variable {n : ℤ} (z : Cochain M N n)

/--
@isnad1 id=eq.2h9v.s7.73c9d77fd6fc from=translated src=- shape=cc964d3f vocab=535df72e
-/
theorem δ_rightShift (a n' m' : ℤ) (hn' : n' + a = n) (m : ℤ) (hm' : m' + a = m) :
    δ n' m' (z.rightShift a n' hn') = koszulSign a • (δ n m z).rightShift a m' hm' := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by omega
    ext X x
    apply (shift.unmk a).injective
    simp only [δ_apply _ _ hnm', δ_apply _ _ hnm, rightShift_apply, units_smul_apply, map_sub,
      shift.unmk_d, shift.unmk_units_smul, shift.unmk_mk, _root_.smul_sub, smul_smul,
      ← koszulSign_add]
    congr 2
    rw [Int.negOnePow_eq_iff]
    exact ⟨-a, by omega⟩
  · have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by omega)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, rightShift_zero, _root_.smul_zero]

/--
@isnad1 id=eq.2h9v.s7.b80a625fb863 from=translated src=- shape=73550d97 vocab=7b64e87c
-/
theorem δ_rightUnshift {a n' : ℤ} (z : Cochain M (CatModule.shift a N) n') (n : ℤ)
    (hn : n' + a = n) (m m' : ℤ) (hm' : m' + a = m) :
    δ n m (z.rightUnshift n hn) = koszulSign a • (δ n' m' z).rightUnshift m hm' := by
  obtain ⟨z, rfl⟩ := (rightShiftAddEquiv M N n a n' hn).surjective z
  simp only [rightShiftAddEquiv_apply, rightUnshift_rightShift, z.δ_rightShift a n' m' hn m hm',
    rightUnshift_units_smul, smul_smul, Int.units_mul_self, one_smul]

/--
@isnad1 id=eq.2h9v.s7.38abfdb6c064 from=translated src=- shape=56faa143 vocab=14841bcd
-/
theorem δ_leftShift (a n' m' : ℤ) (hn' : n + a = n') (m : ℤ) (hm' : m + a = m') :
    δ n' m' (z.leftShift a n' hn') = koszulSign a • (δ n m z).leftShift a m' hm' := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by omega
    ext X x
    simp only [δ_apply _ _ hnm', δ_apply _ _ hnm, leftShift_apply, units_smul_apply,
      shift.unmk_d, d_units_smul, map_units_smul, _root_.smul_sub, smul_smul,
      leftShiftSign, ← koszulSign_add]
    congr 2
    all_goals rw [← hnm', ← hn']
    · exact koszulSign_eq_of_sub_eq_two_mul (-a) (by ring)
    · congr 1
      ring
  · have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by omega)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, leftShift_zero, _root_.smul_zero]

/--
@isnad1 id=eq.2h9v.s7.df99c5e0cf4c from=translated src=- shape=9c67321e vocab=92936209
-/
theorem δ_leftUnshift {a n' : ℤ} (z : Cochain (CatModule.shift a M) N n') (n : ℤ)
    (hn : n + a = n') (m m' : ℤ) (hm' : m + a = m') :
    δ n m (z.leftUnshift n hn) = koszulSign a • (δ n' m' z).leftUnshift m hm' := by
  obtain ⟨z, rfl⟩ := (leftShiftAddEquiv M N n a n' hn).surjective z
  simp only [leftShiftAddEquiv_apply, leftUnshift_leftShift, z.δ_leftShift a n' m' hn m hm',
    leftUnshift_units_smul, smul_smul, Int.units_mul_self, one_smul]

/--
@isnad1 id=eq.0h7v.s8.1b0adbf33021 from=translated src=- shape=743ba495 vocab=24430dd1
-/
@[simp]
theorem δ_shift (a m : ℤ) : δ n m (z.shift a) = koszulSign a • (δ n m z).shift a := by
  by_cases hnm : n + 1 = m
  · ext X x
    apply (shift.unmk a).injective
    simp only [δ_apply _ _ hnm, shift_apply, units_smul_apply, map_sub, shift.unmk_d,
      shift.unmk_units_smul, shift.unmk_mk, map_units_smul, _root_.smul_sub,
      smul_smul]
    rw [mul_comm]
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm, shift_zero, _root_.smul_zero]

end Differential

/-! ### Left and right shifts -/

section LeftRight

variable {n : ℤ} (z : Cochain M N n)

end LeftRight

end Cochain

namespace Cocycle

open DG.CatModule.Cochain

variable {M N : CatModule.{w} C} {n : ℤ}

/-- The cocycle `Cocycle M (shift a N) n'` attached to `z : Cocycle M N n` when
`n' + a = n`.-/
@[simps!]
def rightShift (z : Cocycle M N n) (a n' : ℤ) (hn' : n' + a = n) :
    Cocycle M (CatModule.shift a N) n' :=
  Cocycle.mk ((z : Cochain M N n).rightShift a n' hn') _ rfl (by
    simp only [δ_rightShift _ a n' (n' + 1) hn' (n + 1) (by omega), δ_eq_zero, rightShift_zero,
      _root_.smul_zero])

/-- The cocycle `Cocycle M N n` attached to `z : Cocycle M (shift a N) n'` when
`n' + a = n`.-/
@[simps!]
def rightUnshift {n' a : ℤ} (z : Cocycle M (CatModule.shift a N) n') (n : ℤ) (hn : n' + a = n) :
    Cocycle M N n :=
  Cocycle.mk ((z : Cochain M (CatModule.shift a N) n').rightUnshift n hn) _ rfl (by
    rw [δ_rightUnshift _ n hn (n + 1) (n + 1 - a) (by omega), δ_eq_zero, rightUnshift_zero,
      _root_.smul_zero])

/-- The cocycle `Cocycle (shift a M) N n'` attached to `z : Cocycle M N n` when
`n + a = n'`.-/
@[simps!]
def leftShift (z : Cocycle M N n) (a n' : ℤ) (hn' : n + a = n') :
    Cocycle (CatModule.shift a M) N n' :=
  Cocycle.mk ((z : Cochain M N n).leftShift a n' hn') _ rfl (by
    simp only [δ_leftShift _ a n' (n' + 1) hn' (n + 1) (by omega), δ_eq_zero, leftShift_zero,
      _root_.smul_zero])

/-- The cocycle `Cocycle M N n` attached to `z : Cocycle (shift a M) N n'` when
`n + a = n'`.-/
@[simps!]
def leftUnshift {n' a : ℤ} (z : Cocycle (CatModule.shift a M) N n') (n : ℤ) (hn : n + a = n') :
    Cocycle M N n :=
  Cocycle.mk ((z : Cochain (CatModule.shift a M) N n').leftUnshift n hn) _ rfl (by
    rw [δ_leftUnshift _ n hn (n + 1) (n + 1 + a) rfl, δ_eq_zero, leftUnshift_zero,
      _root_.smul_zero])

/-- The cocycle `Cocycle (shift a M) (shift a N) n` attached to `z : Cocycle M N n`.-/
@[simps!]
def shift (z : Cocycle M N n) (a : ℤ) : Cocycle (CatModule.shift a M) (CatModule.shift a N) n :=
  Cocycle.mk ((z : Cochain M N n).shift a) _ rfl
    (by simp only [δ_shift, δ_eq_zero, shift_zero, _root_.smul_zero])

end Cocycle

end CatModule

end DG
