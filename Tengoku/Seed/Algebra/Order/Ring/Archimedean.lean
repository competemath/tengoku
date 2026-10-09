/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang, Violeta Hernández Palacios
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Archimedean.Class
public import Tengoku.Seed.Algebra.Order.Group.DenselyOrdered
public import Tengoku.Seed.Algebra.Order.Ring.Basic
public import Tengoku.Seed.Algebra.Order.Hom.Ring
public import Tengoku.Seed.RingTheory.Valuation.Basic
public import Tengoku.Seed.Algebra.Order.Archimedean.Basic

/-!
# Archimedean classes of a linearly ordered ring

The archimedean classes of a linearly ordered ring can be given the structure of an `AddCommMonoid`,
by defining

* `0 = mk 1`
* `mk x + mk y = mk (x * y)`

For a linearly ordered field, we can define a negative as

* `-mk x = mk x⁻¹`

which turns them into a `LinearOrderedAddCommGroupWithTop`.

## Implementation notes

We give Archimedean class an additive structure, rather than a multiplicative one, for the following
reasons:

* In the ring version of Hahn embedding theorem, the subtype `FiniteArchimedeanClass R` of non-top
  elements in `ArchimedeanClass R` naturally becomes the additive abelian group for the ring
  `ℝ⟦FiniteArchimedeanClass R⟧`.
* The order we defined on `ArchimedeanClass R` matches the order on `AddValuation`, rather than the
  one on `Valuation`.
-/

@[expose] public section

variable {R S : Type*} [LinearOrder R] [LinearOrder S]

namespace ArchimedeanClass
section Ring
variable [CommRing R]

section IsOrderedRing
variable [IsStrictOrderedRing R]

instance : Zero (ArchimedeanClass R) where
  zero := mk 1

/--
@isnad1 id=eq.0h1v.s6.bc353091837d from=seed src=0 shape=e251427b vocab=9bc7c132
-/
@[simp] theorem mk_one : mk (1 : R) = 0 := rfl

/--
@isnad1 id=ne.0h1v.s7.4813a53e9a72 from=seed src=0 shape=c9aff670 vocab=25c99fa3
-/
@[simp] lemma top_ne_zero : (⊤ : ArchimedeanClass R) ≠ 0 := by simp [← mk_one]
/--
@isnad1 id=ne.0h1v.s7.88bf78f48f9f from=seed src=0 shape=cebe7671 vocab=25c99fa3
-/
@[simp] lemma zero_ne_top : 0 ≠ (⊤ : ArchimedeanClass R) := top_ne_zero.symm

private theorem mk_mul_le_of_le {x₁ y₁ x₂ y₂ : R} (hx : mk x₁ ≤ mk x₂) (hy : mk y₁ ≤ mk y₂) :
    mk (x₁ * y₁) ≤ mk (x₂ * y₂) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  use m * n
  convert mul_le_mul hm hn (abs_nonneg _) (nsmul_nonneg (abs_nonneg _) _) <;>
    simp_rw [ArchimedeanOrder.val_of, abs_mul]
  ring

/-- Multiplication in `R` transfers to addition in `ArchimedeanClass R`. -/
instance : Add (ArchimedeanClass R) where
  add := lift₂ (fun x y ↦ .mk <| x * y) fun _ _ _ _ hx hy ↦ by
    exact (mk_mul_le_of_le hx.le hy.le).antisymm (mk_mul_le_of_le hx.ge hy.ge)

/--
@isnad1 id=eq.0h3v.s7.e79368ef31cb from=seed src=0 shape=1318b0ef vocab=bc21e515
-/
@[simp] theorem mk_mul (x y : R) : mk (x * y) = mk x + mk y := rfl

instance : SMul ℕ (ArchimedeanClass R) where
  smul n := lift (fun x ↦ mk (x ^ n)) fun x y h ↦ by
    induction n with
    | zero => simp
    | succ n IH => simp_rw [pow_succ, mk_mul, IH, h]

/--
@isnad1 id=eq.0h3v.s6.9ce1128a64d7 from=seed src=0 shape=4de4739d vocab=6cc8726b
-/
@[simp] theorem mk_pow (n : ℕ) (x : R) : mk (x ^ n) = n • mk x := rfl

instance : AddCommMagma (ArchimedeanClass R) where
  add_comm x y := by
    induction x with | mk x
    induction y with | mk y
    rw [← mk_mul, mul_comm, mk_mul]

private theorem zero_add' (x : ArchimedeanClass R) : 0 + x = x := by
  induction x with | mk x
  rw [← mk_one, ← mk_mul, one_mul]

private theorem add_assoc' (x y z : ArchimedeanClass R) : x + y + z = x + (y + z) := by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  simp_rw [← mk_mul, mul_assoc]

instance : AddCommMonoid (ArchimedeanClass R) where
  add_assoc := private add_assoc'
  zero_add := private zero_add'
  add_zero x := private add_comm x _ ▸ zero_add' x
  nsmul_zero x := by induction x with | mk x => rw [← mk_pow, pow_zero, mk_one]
  nsmul_succ n x := by induction x with | mk x => rw [← mk_pow, pow_succ, mk_mul, mk_pow]

instance : IsOrderedAddMonoid (ArchimedeanClass R) where
  add_le_add_left x y h z := by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    rw [← mk_mul, ← mk_mul]
    exact mk_mul_le_of_le h le_rfl

/--
@isnad1 id=isaddreg.1h2v.s6.4de95777cbb1 from=seed src=0 shape=23c84f62 vocab=7d7e2416
-/
lemma isAddRegular_mk {x : R} (hx : x ≠ 0) : IsAddRegular (mk x) := by
  rw [← isAddLeftRegular_iff_isAddRegular]
  rintro y z hyz
  induction y with | mk y =>
  induction z with | mk z =>
  simpa [← mk_mul, mk_eq_mk, mul_left_comm _ (|x|), abs_pos.2 hx] using hyz

noncomputable instance : LinearOrderedAddCommMonoidWithTop (ArchimedeanClass R) where
  top_add' x := by induction x with | mk x => rw [← mk_zero, ← mk_mul, zero_mul]
  isAddLeftRegular_of_ne_top x := by induction x with | mk x => simp +contextual [isAddRegular_mk]

variable (R) in
/-- `ArchimedeanClass.mk` defines an `AddValuation` on the ring `R`. -/
noncomputable def addValuation : AddValuation R (ArchimedeanClass R) := AddValuation.of mk
  rfl rfl min_le_mk_add mk_mul

/--
@isnad1 id=eq.0h2v.s6.0f3cb0269ed4 from=seed src=0 shape=2c5bc943 vocab=124ae002
-/
@[simp] theorem addValuation_apply (a : R) : addValuation R a = mk a := rfl

variable {S : Type*} [LinearOrder S] [CommRing S] [IsStrictOrderedRing S]

/--
@isnad1 id=eq.0h3v.s9.b413d3179578 from=seed src=0 shape=2bddbc2b vocab=fe80f716
-/
@[simp]
theorem orderHom_zero (f : S →+o R) : orderHom f 0 = mk (f 1) := by
  rw [← mk_one, orderHom_mk]

/--
@isnad1 id=eq.1h2v.s6.c3b250b88a38 from=seed src=0 shape=6aa86c01 vocab=286ff2d5
-/
@[simp]
theorem mk_eq_zero_of_archimedean [Archimedean S] {x : S} (h : x ≠ 0) : mk x = 0 :=
  mk_eq_mk_of_archimedean h one_ne_zero

theorem eq_zero_or_top_of_archimedean [Archimedean S] (x : ArchimedeanClass S) : x = 0 ∨ x = ⊤ := by
  induction x with | mk x
  obtain rfl | h := eq_or_ne x 0 <;> simp_all

/-- See `mk_map_of_archimedean'` for a version taking `M →+*o R`.
@isnad1 id=eq.1h4v.s8.767097876cd3 from=seed src=0 shape=d5954b4d vocab=6ec12426
-/
theorem mk_map_of_archimedean [Archimedean S] (f : S →+o R) {x : S} (h : x ≠ 0) :
    mk (f x) = mk (f 1) := by
  rw [← orderHom_mk, mk_eq_zero_of_archimedean h, orderHom_zero]

/-- See `mk_map_of_archimedean` for a version taking `M →+o R`.
@isnad1 id=eq.1h4v.s8.52b8ade437cc from=seed src=0 shape=60264282 vocab=8809c19e
-/
theorem mk_map_of_archimedean' [Archimedean S] (f : S →+*o R) {x : S} (h : x ≠ 0) :
    mk (f x) = 0 := by
  simpa using mk_map_of_archimedean f.toOrderAddMonoidHom h

/--
@isnad1 id=le.0h5v.s8.81f672450a83 from=seed src=0 shape=09aa0ba5 vocab=f184906c
-/
theorem mk_le_mk_add_of_archimedean [Archimedean S] (f : S →+*o R) (x : R) (y : S) :
    mk x ≤ mk (f y) + mk x := by
  obtain rfl | hy := eq_or_ne y 0
  · simp
  · rw [mk_map_of_archimedean' f hy, zero_add]

/--
@isnad1 id=le.0h5v.s8.fd7b793b051a from=seed src=0 shape=550a999c vocab=f184906c
-/
theorem mk_le_add_mk_of_archimedean [Archimedean S] (f : S →+*o R) (x : R) (y : S) :
    mk x ≤ mk x + mk (f y) := by
  rw [add_comm]
  exact mk_le_mk_add_of_archimedean f x y

/--
@isnad1 id=le.0h4v.s8.aaa84ad70169 from=seed src=0 shape=cc56b982 vocab=42a89314
-/
theorem mk_map_nonneg_of_archimedean [Archimedean S] (f : S →+*o R) (y : S) : 0 ≤ mk (f y) := by
  simpa using mk_le_mk_add_of_archimedean f 1 y

/--
@isnad1 id=lt.2h5v.s8.0f9420b7350e from=seed src=0 shape=5a13dffe vocab=5384467a
-/
theorem lt_of_pos_of_archimedean [Archimedean S] (f : S →+*o R)
    {x : R} (hx : 0 < mk x) {y : S} (hy : 0 < y) : x < f y := by
  apply lt_of_mk_lt_mk_of_nonneg
  · rwa [mk_map_of_archimedean' f hy.ne']
  · simpa using f.monotone' hy.le

/--
@isnad1 id=lt.2h5v.s8.fef19e731c97 from=seed src=0 shape=1905b649 vocab=5384467a
-/
theorem lt_of_neg_of_archimedean [Archimedean S] (f : S →+*o R)
    {x : R} (hx : 0 < mk x) {y : S} (hy : y < 0) : f y < x := by
  apply lt_of_mk_lt_mk_of_nonpos
  · rwa [mk_map_of_archimedean' f hy.ne]
  · simpa using f.monotone' hy.le

/--
@isnad1 id=eq.1h2v.s6.82724f570317 from=seed src=0 shape=3ab2ec70 vocab=5edd65d0
-/
@[simp]
theorem mk_intCast {n : ℤ} (h : n ≠ 0) : mk (n : S) = 0 := by
  obtain _ | _ := subsingleton_or_nontrivial S
  · exact Subsingleton.allEq ..
  · exact mk_map_of_archimedean' ⟨Int.castRingHom S, fun _ ↦ by simp⟩ h

/--
@isnad1 id=le.0h2v.s7.21f79b6f78c2 from=seed src=0 shape=3d1906a3 vocab=0d67e05a
-/
theorem mk_intCast_nonneg (n : ℤ) : 0 ≤ mk (n : S) := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  · rw [mk_intCast hn]

/--
@isnad1 id=eq.1h2v.s6.0da66a35027c from=seed src=0 shape=3ab2ec70 vocab=1efcd305
-/
@[simp]
theorem mk_natCast {n : ℕ} : n ≠ 0 → mk (n : S) = 0 :=
  mod_cast mk_intCast (n := n)

/--
@isnad1 id=eq.0h2v.s6.726c7060aaf5 from=seed src=0 shape=8b6cf1fd vocab=6f80e2e5
-/
@[simp]
theorem mk_ofNat {n : ℕ} [n.AtLeastTwo] : mk (ofNat(n) : S) = 0 :=
  mod_cast mk_intCast (n := n) (mod_cast NeZero.ne n)

/--
@isnad1 id=le.0h2v.s7.d8a4752a5ed8 from=seed src=0 shape=3d1906a3 vocab=1963942d
-/
theorem mk_natCast_nonneg (n : ℕ) : 0 ≤ mk (n : S) :=
  mod_cast mk_intCast_nonneg n

/--
@isnad1 id=ex.1h2v.s7.6bc5613b9989 from=seed src=0 shape=85dc3b45 vocab=1963942d
-/
theorem exists_nat_ge_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℕ, x ≤ n := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, le_of_abs_le ?_⟩
  simpa using hn

/--
@isnad1 id=ex.1h2v.s7.e1b21098aa63 from=seed src=0 shape=186d9218 vocab=9842e7fc
-/
theorem exists_nat_gt_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℕ, x < n := by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg hx
  refine ⟨n + 1, hn.trans_lt ?_⟩
  simp

/--
@isnad1 id=ex.1h2v.s7.cf0313397b92 from=seed src=0 shape=85dc3b45 vocab=0d67e05a
-/
theorem exists_int_ge_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℤ, x ≤ n := by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg hx
  exact ⟨n, mod_cast hn⟩

/--
@isnad1 id=ex.1h2v.s7.a6ca4b0440dc from=seed src=0 shape=186d9218 vocab=78fe57c4
-/
theorem exists_int_gt_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℤ, x < n := by
  obtain ⟨n, hn⟩ := exists_nat_gt_of_mk_nonneg hx
  exact ⟨n, mod_cast hn⟩

/--
@isnad1 id=ex.1h2v.s7.e7fa7ca44ce5 from=seed src=0 shape=f1fa5563 vocab=0d67e05a
-/
theorem exists_int_le_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℤ, n ≤ x := by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg (mk_neg x ▸ hx)
  use -n
  simpa [neg_le]

/--
@isnad1 id=ex.1h2v.s7.54b7e66fb3f3 from=seed src=0 shape=b3ff0990 vocab=78fe57c4
-/
theorem exists_int_lt_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℤ, n < x := by
  obtain ⟨n, hn⟩ := exists_nat_gt_of_mk_nonneg (mk_neg x ▸ hx)
  use -n
  simpa [neg_lt]

/--
@isnad1 id=le.2h6v.s8.b30fae695668 from=seed src=0 shape=960eb086 vocab=42a89314
-/
theorem mk_nonneg_of_le_of_le_of_archimedean [Archimedean S] (f : S →+*o R) {x : R} {r s : S}
    (hr : f r ≤ x) (hs : x ≤ f s) : 0 ≤ mk x := by
  apply (min_le_mk_of_le_of_le hr hs).trans'
  simp [mk_map_nonneg_of_archimedean]

end IsOrderedRing

section IsStrictOrderedRing
variable [IsStrictOrderedRing R]

/--
@isnad1 id=eq.2h4v.s8.e23c3bce1296 from=seed src=0 shape=81613387 vocab=3276250c
-/
theorem add_left_cancel_of_ne_top {x y z : ArchimedeanClass R} (hx : x ≠ ⊤) (h : x + y = x + z) :
    y = z := by
  simp_all

/--
@isnad1 id=eq.2h4v.s8.f7041f0f2952 from=seed src=0 shape=ef4c60f2 vocab=3276250c
-/
theorem add_right_cancel_of_ne_top {x y z : ArchimedeanClass R} (hx : x ≠ ⊤) (h : y + x = z + x) :
    y = z := by
  simp_rw [← add_comm x] at h
  exact add_left_cancel_of_ne_top hx h

/--
@isnad1 id=iff.1h5v.s8.d7ea6fdcc67c from=seed src=0 shape=0f476db4 vocab=dd5ff249
-/
theorem mk_le_mk_iff_denselyOrdered [Ring S] [IsStrictOrderedRing S]
    [DenselyOrdered R] [Archimedean R] {x y : S} (f : R →+* S) (hf : StrictMono f) :
    mk x ≤ mk y ↔ ∃ q : R, 0 < f q ∧ f q * |y| ≤ |x| := by
  have H {q} : 0 < f q ↔ 0 < q := by simpa using hf.lt_iff_lt (a := 0)
  constructor
  · rintro ⟨(_ | n), hn⟩
    · simp_all [exists_zero_lt]
    · obtain ⟨q, hq₀, hq⟩ := exists_nsmul_lt_of_pos (one_pos (α := R)) (n + 1)
      refine ⟨q, H.2 hq₀, le_of_mul_le_mul_left ?_ n.cast_add_one_pos⟩
      simpa [← mul_assoc] using mul_le_mul (hf hq).le hn (abs_nonneg y) (by simp)
  · rintro ⟨q, hq₀, hq⟩
    have hq₀' := H.1 hq₀
    obtain ⟨n, hn⟩ := exists_lt_nsmul hq₀' 1
    refine ⟨n, le_of_mul_le_mul_left ?_ hq₀⟩
    have h : 0 ≤ f (n • q) := by
      rw [← f.map_zero]
      exact hf.monotone (nsmul_nonneg hq₀'.le n)
    simpa [mul_comm, mul_assoc] using mul_le_mul (hf hn).le hq (mul_nonneg hq₀.le (abs_nonneg y)) h

end IsStrictOrderedRing
end Ring

section Field
variable [Field R] [IsOrderedRing R]

instance : Neg (ArchimedeanClass R) where
  neg := lift (fun x ↦ mk x⁻¹) fun x y h ↦ by
    obtain rfl | hx := eq_or_ne x 0
    · simp_all
    obtain rfl | hy := eq_or_ne y 0
    · simp_all
    have hx' : mk x ≠ ⊤ := by simpa using hx
    apply add_left_cancel_of_ne_top hx'
    nth_rw 2 [h]
    simp [← mk_mul, hx, hy]

/--
@isnad1 id=eq.0h2v.s6.d83324edab53 from=seed src=0 shape=457b981d vocab=63b7ba2b
-/
@[simp] theorem mk_inv (x : R) : mk x⁻¹ = -mk x := rfl

instance : SMul ℤ (ArchimedeanClass R) where
  smul n := lift (fun x ↦ mk (x ^ n)) fun x y h ↦ by
    obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simp [h]

/--
@isnad1 id=eq.0h3v.s6.6e2dcad18650 from=seed src=0 shape=4de4739d vocab=e9565624
-/
@[simp] theorem mk_zpow (n : ℤ) (x : R) : mk (x ^ n) = n • mk x := rfl

private theorem zsmul_succ' (n : ℕ) (x : ArchimedeanClass R) :
    (n.succ : ℤ) • x = (n : ℤ) • x + x := by
  induction x with | mk x
  rw [← mk_zpow, Nat.cast_succ]
  obtain rfl | hx := eq_or_ne x 0
  · simp [zero_zpow _ n.cast_add_one_ne_zero]
  · rw [zpow_add_one₀ hx, mk_mul, mk_zpow]

noncomputable instance : LinearOrderedAddCommGroupWithTop (ArchimedeanClass R) where
  neg_top := by simp [← mk_zero, ← mk_inv]
  top_add' := by simp
  add_neg_cancel_of_ne_top x h := by
    induction x with | mk x
    simp [← mk_inv, ← mk_mul, mul_inv_cancel₀ (mk_eq_top_iff.not.1 h)]
  zsmul_zero' x := by induction x with | mk x => rw [← mk_zpow, zpow_zero, mk_one]
  zsmul_succ' := by exact zsmul_succ'
  zsmul_neg' n x := by
    induction x with | mk x
    rw [← mk_zpow, zpow_negSucc, pow_succ, zsmul_succ', mk_inv, mk_mul, ← zpow_natCast, mk_zpow]

/--
@isnad1 id=eq.0h3v.s7.540b7a02b94c from=seed src=0 shape=1318b0ef vocab=ee1b24bc
-/
@[simp]
theorem mk_div (x y : R) : mk (x / y) = mk x - mk y := by
  rw [div_eq_mul_inv, mk_mul, mk_inv, sub_eq_add_neg]

/--
@isnad1 id=eq.1h2v.s6.48d42684dd30 from=seed src=0 shape=3ab2ec70 vocab=7bc43036
-/
@[simp]
theorem mk_ratCast {q : ℚ} (h : q ≠ 0) : mk (q : R) = 0 := by
  simpa using mk_map_of_archimedean ⟨(Rat.castHom R).toAddMonoidHom, fun _ ↦ by simp⟩ h

/--
@isnad1 id=le.0h2v.s7.54d0c719016e from=seed src=0 shape=3d1906a3 vocab=71e2b711
-/
theorem mk_ratCast_nonneg (q : ℚ) : 0 ≤ mk (q : R) := by
  obtain rfl | hn := eq_or_ne q 0
  · simp
  · rw [mk_ratCast hn]

/--
@isnad1 id=iff.0h3v.s7.f936a522e497 from=seed src=0 shape=d0aef1fc vocab=2a1675c8
-/
theorem mk_le_mk_iff_ratCast {x y : R} : mk x ≤ mk y ↔ ∃ q : ℚ, 0 < q ∧ q * |y| ≤ |x| := by
  simpa using mk_le_mk_iff_denselyOrdered (Rat.castHom _) Rat.cast_strictMono (x := x)

end Field
end ArchimedeanClass
