/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import Tengoku

/-!
# Euclidean composition algebras

A **Euclidean composition algebra** is a real vector space `C` carrying a unital, not
necessarily associative or commutative, bilinear product, together with a symmetric
positive-definite bilinear form `B` whose associated quadratic form `N x = B x x` is
*multiplicative*: `N (x * y) = N x * N y`.

The four examples are `ℝ`, `ℂ`, `ℍ`, `𝕆` (`Composition/Instances.lean`), and Hurwitz's
theorem says there are no others. This file is the ground floor: the class, and the
identity toolkit that every later argument runs on.

## Design

* The form is carried as a **symmetric bilinear map** `B : C →ₗ[ℝ] C →ₗ[ℝ] ℝ` rather than as
  a `Mathlib` `QuadraticForm`. Over `ℝ` the two are interchangeable (`2` is invertible), and
  the substantive arguments below are polarisation arguments, i.e. are *about* the bilinear
  form. Carrying `B` directly removes an API layer from the middle of those proofs.
* The ambient algebra is `[NonAssocRing C] [Module ℝ C] [IsScalarTower ℝ C C]
  [SMulCommClass ℝ C C]`: unital, distributive, `ℝ`-bilinear multiplication, **no
  associativity and no commutativity**. `Algebra ℝ C` is not usable here — it presupposes
  associativity.
* `B` is a class field. There is at most one composition-algebra structure of interest per
  carrier, so class inference is the right vehicle and it keeps `ip`/`nf` argument-inferred.

## Main results

Everything below is derived from the four class fields alone.

* `ip_mul_left_left`, `ip_mul_right_right`, `ip_exchange` — the three polarisations of the
  composition law. `ip_exchange` is the workhorse: `⟪xy, wz⟫ + ⟪wy, xz⟫ = 2⟪x,w⟫⟪y,z⟫`.
* `ip_mul_adj_left`, `ip_mul_adj_right` — conjugation is the adjoint of multiplication:
  `⟪xy, z⟫ = ⟪y, x* z⟫` and `⟪xy, z⟫ = ⟪x, z y*⟫`.
* `sq_eq` — **every element is quadratic**: `x * x = 2⟪x,1⟫ • x - N x • 1`. This is the
  single most useful consequence; `mul_cstar_self`, `cstar_mul_self` and both alternativity
  laws come off it directly.
* `cstar_mul` — conjugation is an anti-automorphism.
* `left_alternative`, `right_alternative` — `x (x y) = (x x) y` and `(y x) x = y (x x)`.
* `pure_mul_pure_add` — for `x, y` orthogonal to `1`, `x y + y x = -2⟪x,y⟫ • 1`; in
  particular a unit imaginary squares to `-1`.

## Scope

Substrate for the two Hurwitz theorems. It states neither of them.
-/

@[expose] public section

universe u

/-- A **Euclidean composition algebra**: a unital, `ℝ`-bilinear, not necessarily associative
product together with a symmetric positive-definite bilinear form whose quadratic form is
multiplicative. -/
class CompositionAlgebra (C : Type u) [NonAssocRing C] [Module ℝ C]
    [IsScalarTower ℝ C C] [SMulCommClass ℝ C C] where
  /-- The defining bilinear form. -/
  B : C →ₗ[ℝ] C →ₗ[ℝ] ℝ
  /-- The form is symmetric. -/
  B_symm : ∀ x y, B x y = B y x
  /-- The form is positive definite. -/
  B_pos : ∀ x : C, x ≠ 0 → 0 < B x x
  /-- The **composition law**: the associated quadratic form is multiplicative. -/
  B_comp : ∀ x y : C, B (x * y) (x * y) = B x x * B y y

namespace CompositionAlgebra

variable {C : Type u} [NonAssocRing C] [Module ℝ C]
  [IsScalarTower ℝ C C] [SMulCommClass ℝ C C] [CompositionAlgebra C]

/-- The inner product `⟪x, y⟫` of a composition algebra. -/
def ip (x y : C) : ℝ := B x y

/-- The norm form `N x = ⟪x, x⟫`. Positive definite, and multiplicative by `comp`. -/
def nf (x : C) : ℝ := B x x

/--
@isnad1 id=eq.0h2v.s7.5c7237b2acbb from=translated src=- shape=f2fe6097 vocab=06fd03f0
-/
theorem nf_eq_ip (x : C) : nf x = ip x x := rfl

/--
@isnad1 id=eq.0h3v.s7.28b3a65c4335 from=translated src=- shape=8230c641 vocab=76168681
-/
theorem ip_symm (x y : C) : ip x y = ip y x := B_symm x y

/--
@isnad1 id=eq.0h4v.s8.9e2738cd654f from=translated src=- shape=cd9c7144 vocab=6b63006e
-/
@[simp] theorem ip_add_left (x y z : C) : ip (x + y) z = ip x z + ip y z := by simp [ip]
/--
@isnad1 id=eq.0h4v.s8.465aed56248b from=translated src=- shape=362b360e vocab=6b63006e
-/
@[simp] theorem ip_add_right (x y z : C) : ip x (y + z) = ip x y + ip x z := by simp [ip]
/--
@isnad1 id=eq.0h4v.s8.6709a39b117e from=translated src=- shape=cd9c7144 vocab=2687a148
-/
@[simp] theorem ip_sub_left (x y z : C) : ip (x - y) z = ip x z - ip y z := by simp [ip]
/--
@isnad1 id=eq.0h4v.s8.4772aa39c137 from=translated src=- shape=362b360e vocab=2687a148
-/
@[simp] theorem ip_sub_right (x y z : C) : ip x (y - z) = ip x y - ip x z := by simp [ip]
/--
@isnad1 id=eq.0h4v.s8.5baf9129e8be from=translated src=- shape=68550930 vocab=458998a0
-/
@[simp] theorem ip_smul_left (r : ℝ) (x y : C) : ip (r • x) y = r * ip x y := by simp [ip]
/--
@isnad1 id=eq.0h4v.s8.627641bd7314 from=translated src=- shape=70653cdd vocab=458998a0
-/
@[simp] theorem ip_smul_right (r : ℝ) (x y : C) : ip x (r • y) = r * ip x y := by simp [ip]
/--
@isnad1 id=eq.0h2v.s8.e6096f2d3ecd from=translated src=- shape=04dd8f33 vocab=76168681
-/
@[simp] theorem ip_zero_left (y : C) : ip (0 : C) y = 0 := by simp [ip]
/--
@isnad1 id=eq.0h2v.s8.2d48db9c29b2 from=translated src=- shape=e8d1cace vocab=76168681
-/
@[simp] theorem ip_zero_right (x : C) : ip x (0 : C) = 0 := by simp [ip]
/--
@isnad1 id=eq.0h3v.s8.9f39c94d5baa from=translated src=- shape=5a1f9e12 vocab=2e59e1ce
-/
@[simp] theorem ip_neg_left (x y : C) : ip (-x) y = -ip x y := by simp [ip]
/--
@isnad1 id=eq.0h3v.s8.2a9dc51f7e27 from=translated src=- shape=25446938 vocab=2e59e1ce
-/
@[simp] theorem ip_neg_right (x y : C) : ip x (-y) = -ip x y := by simp [ip]

/--
@isnad1 id=le.0h2v.s7.4065af12422a from=translated src=- shape=5237f2dd vocab=417174d7
-/
theorem nf_nonneg (x : C) : 0 ≤ nf x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [nf]
  · exact le_of_lt (B_pos x hx)

/--
@isnad1 id=lt.1h2v.s8.8a94729c96d1 from=translated src=- shape=c41f6bea vocab=19efc499
-/
theorem nf_pos {x : C} (hx : x ≠ 0) : 0 < nf x := B_pos x hx

/--
@isnad1 id=iff.0h2v.s8.47fd33a5e276 from=translated src=- shape=6aa9da6a vocab=2007a2a0
-/
theorem nf_eq_zero_iff {x : C} : nf x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact absurd h (ne_of_gt (B_pos x hx))
  · rintro rfl; simp [nf]

/--
@isnad1 id=eq.0h2v.s8.cb21fdd26e25 from=translated src=- shape=e4a5d871 vocab=894eec55
-/
@[simp] theorem nf_neg (x : C) : nf (-x) = nf x := by
  simp only [nf_eq_ip, ip_neg_left, ip_neg_right, neg_neg]

/--
@isnad1 id=eq.0h3v.s8.37a748eaa1d3 from=translated src=- shape=6f83ab05 vocab=8dce8d80
-/
theorem nf_smul (r : ℝ) (x : C) : nf (r • x) = r ^ 2 * nf x := by
  simp only [nf_eq_ip, ip_smul_left, ip_smul_right]
  ring

/--
@isnad1 id=eq.0h3v.s8.5db3ad71f10e from=translated src=- shape=de99673e vocab=c18bda55
-/
theorem nf_add (x y : C) : nf (x + y) = nf x + 2 * ip x y + nf y := by
  simp only [nf, ip, map_add, LinearMap.add_apply]
  rw [B_symm y x]; ring

/--
@isnad1 id=eq.0h3v.s8.941f9163a96f from=translated src=- shape=08f4b437 vocab=2f67c7cc
-/
theorem nf_sub (x y : C) : nf (x - y) = nf x - 2 * ip x y + nf y := by
  simp only [nf_eq_ip, ip_sub_left, ip_sub_right, ip_symm y x]
  ring

/-- The **composition law**, in `nf` form.
@isnad1 id=eq.0h3v.s8.7698ded5703e from=translated src=- shape=5cfd2f47 vocab=d357f687
-/
theorem comp (x y : C) : nf (x * y) = nf x * nf y := B_comp x y

/-- Positive definiteness as nondegeneracy. -/
theorem eq_zero_of_ip_eq_zero {v : C} (h : ∀ z, ip v z = 0) : v = 0 := by
  by_contra hv
  exact absurd (h v) (ne_of_gt (B_pos v hv))

/-- The form separates points: this is how every identity below is proved. -/
theorem eq_of_ip_eq {u v : C} (h : ∀ z, ip u z = ip v z) : u = v := by
  have hz : u - v = 0 := eq_zero_of_ip_eq_zero (fun z => by rw [ip_sub_left, h z]; ring)
  linear_combination (norm := module) hz

/-! ### The three polarisations of the composition law -/

/-- First polarisation: `⟪x y, x z⟫ = N x ⟪y, z⟫`.
@isnad1 id=eq.0h4v.s8.265af7038a35 from=translated src=- shape=04bf9f02 vocab=3126a09b
-/
theorem ip_mul_left_left (x y z : C) : ip (x * y) (x * z) = nf x * ip y z := by
  have h := comp x (y + z)
  rw [mul_add, nf_add, nf_add, comp, comp] at h
  linarith

/-- Second polarisation: `⟪x z, y z⟫ = ⟪x, y⟫ N z`.
@isnad1 id=eq.0h4v.s8.5432d24af414 from=translated src=- shape=622e41e6 vocab=3126a09b
-/
theorem ip_mul_right_right (x y z : C) : ip (x * z) (y * z) = ip x y * nf z := by
  have h := comp (x + y) z
  rw [add_mul, nf_add, nf_add, comp, comp] at h
  linarith

/-- Third polarisation (the **exchange identity**):
`⟪x y, w z⟫ + ⟪w y, x z⟫ = 2 ⟪x, w⟫ ⟪y, z⟫`.

Almost everything in this file is a specialisation of this one identity.
@isnad1 id=eq.0h5v.s8.c8a22542e92b from=translated src=- shape=c72aa769 vocab=e18f9a87
-/
theorem ip_exchange (x y w z : C) :
    ip (x * y) (w * z) + ip (w * y) (x * z) = 2 * ip x w * ip y z := by
  have h := ip_mul_left_left (x + w) y z
  rw [add_mul, add_mul, nf_add] at h
  have h1 := ip_mul_left_left x y z
  have h2 := ip_mul_left_left w y z
  simp only [ip_add_left, ip_add_right] at h
  linarith

/-! ### Conjugation -/

/-- The conjugation `x* = 2⟪x, 1⟫ • 1 - x`, i.e. reflection in the line `ℝ ∙ 1`. -/
def cstar (x : C) : C := (2 * ip x 1) • (1 : C) - x

/--
@isnad1 id=eq.0h2v.s8.99d3f231c339 from=translated src=- shape=8c8f9d9b vocab=63813052
-/
theorem cstar_apply (x : C) : cstar x = (2 * ip x 1) • (1 : C) - x := rfl

/--
@isnad1 id=eq.0h3v.s8.2d88e9e84b10 from=translated src=- shape=0ba29a8b vocab=d082301d
-/
theorem cstar_add (x y : C) : cstar (x + y) = cstar x + cstar y := by
  simp only [cstar_apply, ip_add_left]
  module

/--
@isnad1 id=eq.0h3v.s8.0d00b6f9faef from=translated src=- shape=72d339fc vocab=a9ba69db
-/
theorem cstar_smul (r : ℝ) (x : C) : cstar (r • x) = r • cstar x := by
  simp only [cstar_apply, ip_smul_left]
  module

/--
@isnad1 id=eq.0h1v.s8.b0304c31b28e from=translated src=- shape=664c0171 vocab=bca9b1e3
-/
@[simp] theorem cstar_zero : cstar (0 : C) = 0 := by
  simp only [cstar_apply, ip_zero_left]
  module

/--
@isnad1 id=eq.0h2v.s8.19a430bfe973 from=translated src=- shape=b45b56fb vocab=d2a87049
-/
theorem cstar_neg (x : C) : cstar (-x) = -cstar x := by
  simp only [cstar_apply, ip_neg_left]
  module

/--
@isnad1 id=eq.0h3v.s8.a30ef0b13c3a from=translated src=- shape=0ba29a8b vocab=d18083b6
-/
theorem cstar_sub (x y : C) : cstar (x - y) = cstar x - cstar y := by
  simp only [cstar_apply, ip_sub_left]
  module

/-- `N 1 = 1`: the unit is a unit vector.
@isnad1 id=eq.0h1v.s8.3e5658a5a4b7 from=translated src=- shape=fe34abe0 vocab=2f241f2c
-/
theorem nf_one [Nontrivial C] : nf (1 : C) = 1 := by
  have h := comp (1 : C) 1
  rw [one_mul] at h
  have hpos : 0 < nf (1 : C) := B_pos 1 one_ne_zero
  nlinarith

/--
@isnad1 id=eq.0h1v.s8.a76ed07bdc69 from=translated src=- shape=c76af1e4 vocab=c89d3d46
-/
@[simp] theorem ip_one_one [Nontrivial C] : ip (1 : C) 1 = 1 := nf_one

/--
@isnad1 id=eq.0h1v.s8.1f41f5a4b6a8 from=translated src=- shape=bd60de26 vocab=1cddadfc
-/
@[simp] theorem cstar_one [Nontrivial C] : cstar (1 : C) = 1 := by
  simp only [cstar_apply, ip_one_one]
  module

/--
@isnad1 id=eq.0h2v.s8.af12a56c5950 from=translated src=- shape=7f15e5dc vocab=27001c2f
-/
theorem ip_cstar_one [Nontrivial C] (x : C) : ip (cstar x) 1 = ip x 1 := by
  simp only [cstar_apply, ip_sub_left, ip_smul_left, ip_one_one]
  ring

/--
@isnad1 id=eq.0h2v.s7.26c622138b7c from=translated src=- shape=0b8f2c53 vocab=1cddadfc
-/
@[simp] theorem cstar_cstar [Nontrivial C] (x : C) : cstar (cstar x) = x := by
  have h : ip (cstar x) (1 : C) = ip x 1 := ip_cstar_one x
  change (2 * ip (cstar x) 1) • (1 : C) - cstar x = x
  rw [h, cstar_apply]
  abel

/--
@isnad1 id=eq.0h2v.s8.18b3f15f5c06 from=translated src=- shape=19fde8f5 vocab=74f21387
-/
theorem nf_cstar [Nontrivial C] (x : C) : nf (cstar x) = nf x := by
  simp only [nf_eq_ip, cstar_apply, ip_sub_left, ip_sub_right, ip_smul_left, ip_smul_right,
    ip_one_one, ip_symm (1 : C) x]
  ring

/-! ### Conjugation is the adjoint of multiplication -/

/-- `⟪x y, z⟫ = ⟪y, x* z⟫`.
@isnad1 id=eq.0h4v.s8.6291fed8b363 from=translated src=- shape=33499905 vocab=b863bdb7
-/
theorem ip_mul_adj_left (x y z : C) : ip (x * y) z = ip y (cstar x * z) := by
  have h := ip_exchange x y 1 z
  rw [one_mul, one_mul] at h
  have hz : cstar x * z = (2 * ip x 1) • z - x * z := by
    simp [cstar_apply, sub_mul, smul_mul_assoc]
  rw [hz, ip_sub_right, ip_smul_right]
  linarith

/-- `⟪x y, z⟫ = ⟪x, z y*⟫`.
@isnad1 id=eq.0h4v.s8.d3bd5c294693 from=translated src=- shape=3be11828 vocab=b863bdb7
-/
theorem ip_mul_adj_right (x y z : C) : ip (x * y) z = ip x (z * cstar y) := by
  have h := ip_exchange x y z 1
  rw [mul_one, mul_one] at h
  have hz : z * cstar y = (2 * ip y 1) • z - z * y := by
    simp [cstar_apply, mul_sub, mul_smul_comm]
  rw [hz, ip_sub_right, ip_smul_right, ip_symm (z * y) x] at *
  linarith [ip_symm x z]

/-- `⟪x, z x⟫ = ⟪1, z⟫ N x`.
@isnad1 id=eq.0h3v.s8.eaf875159abf from=translated src=- shape=01e7d571 vocab=3126a09b
-/
theorem ip_self_mul (x z : C) : ip x (z * x) = ip 1 z * nf x := by
  have h := ip_exchange 1 x z x
  simp only [one_mul] at h
  rw [ip_symm (z * x) x, ← nf_eq_ip] at h
  linarith

/-- `⟪x y, 1⟫ = 2⟪x,1⟫⟪y,1⟫ - ⟪x,y⟫`: the real part of a product.
@isnad1 id=eq.0h3v.s8.4fc575d323ca from=translated src=- shape=c2d8b66b vocab=63161e0b
-/
theorem ip_mul_one (x y : C) : ip (x * y) 1 = 2 * ip x 1 * ip y 1 - ip x y := by
  have h := ip_exchange x y 1 1
  simp only [one_mul, mul_one] at h
  rw [ip_symm y x] at h
  linarith

/-! ### Every element is quadratic -/

/-- **Every element of a composition algebra satisfies a real quadratic equation**:
`x * x = 2⟪x, 1⟫ • x - N x • 1`.
@isnad1 id=eq.0h2v.s8.fdf6e3d144ec from=translated src=- shape=cfee3d1a vocab=e0614163
-/
theorem sq_eq (x : C) : x * x = (2 * ip x 1) • x - (nf x) • (1 : C) := by
  refine eq_of_ip_eq (fun z => ?_)
  rw [ip_mul_adj_right]
  have h1 : z * cstar x = (2 * ip x 1) • z - z * x := by
    simp [cstar_apply, mul_sub, mul_smul_comm]
  rw [h1, ip_sub_right, ip_smul_right, ip_self_mul]
  simp only [ip_sub_left, ip_smul_left]
  rw [ip_symm 1 z]
  ring

/-- `x x* = N x • 1`.
@isnad1 id=eq.0h2v.s8.85ede4268ead from=translated src=- shape=2eae70be vocab=604c4521
-/
theorem mul_cstar_self (x : C) : x * cstar x = (nf x) • (1 : C) := by
  have h : x * cstar x = (2 * ip x 1) • x - x * x := by
    simp [cstar_apply, mul_sub, mul_smul_comm]
  rw [h, sq_eq]; abel

/-- `x* x = N x • 1`.
@isnad1 id=eq.0h2v.s8.171c9b36ac71 from=translated src=- shape=35be3eef vocab=604c4521
-/
theorem cstar_mul_self (x : C) : cstar x * x = (nf x) • (1 : C) := by
  have h : cstar x * x = (2 * ip x 1) • x - x * x := by
    simp [cstar_apply, sub_mul, smul_mul_assoc]
  rw [h, sq_eq]; abel

/-- The polarised quadratic relation:
`x y + y x = 2⟪x,1⟫ • y + 2⟪y,1⟫ • x - 2⟪x,y⟫ • 1`.
@isnad1 id=eq.0h3v.s9.352aeec6006c from=translated src=- shape=fa5a6554 vocab=c37c840c
-/
theorem mul_add_mul (x y : C) :
    x * y + y * x = (2 * ip x 1) • y + (2 * ip y 1) • x - (2 * ip x y) • (1 : C) := by
  have h := sq_eq (x + y)
  rw [mul_add, add_mul, add_mul, sq_eq x, sq_eq y, nf_add] at h
  simp only [ip_add_left] at h
  linear_combination (norm := module) h

/-- Conjugation is an **anti-automorphism**: `(x y)* = y* x*`.
@isnad1 id=eq.0h3v.s8.c1a081299667 from=translated src=- shape=a412a587 vocab=52c1f393
-/
theorem cstar_mul (x y : C) : cstar (x * y) = cstar y * cstar x := by
  have hm := mul_add_mul x y
  have h1 := ip_mul_one x y
  have hxy : cstar y * cstar x
      = (2 * ip y 1 * (2 * ip x 1)) • (1 : C) - (2 * ip y 1) • x - (2 * ip x 1) • y + y * x := by
    simp only [cstar_apply, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      ]
    module
  rw [hxy, cstar_apply, h1]
  linear_combination (norm := module) -hm

/-! ### Alternativity -/

/-- **Left alternativity**: `x (x y) = (x x) y`.
@isnad1 id=eq.0h3v.s8.33b5cfd709e6 from=translated src=- shape=92cb37b2 vocab=10311368
-/
theorem left_alternative (x y : C) : x * (x * y) = (x * x) * y := by
  refine eq_of_ip_eq (fun z => ?_)
  rw [ip_mul_adj_left]
  have h1 : cstar x * z = (2 * ip x 1) • z - x * z := by
    simp [cstar_apply, sub_mul, smul_mul_assoc]
  rw [h1, ip_sub_right, ip_smul_right, ip_mul_left_left, sq_eq x]
  simp only [sub_mul, smul_mul_assoc, one_mul, ip_sub_left, ip_smul_left]

/-- **Right alternativity**: `(y x) x = y (x x)`.
@isnad1 id=eq.0h3v.s8.b7d23c20053f from=translated src=- shape=28d303cb vocab=10311368
-/
theorem right_alternative (x y : C) : (y * x) * x = y * (x * x) := by
  refine eq_of_ip_eq (fun z => ?_)
  rw [ip_mul_adj_right]
  have h1 : z * cstar x = (2 * ip x 1) • z - z * x := by
    simp [cstar_apply, mul_sub, mul_smul_comm]
  rw [h1, ip_sub_right, ip_smul_right, ip_mul_right_right, sq_eq x]
  simp only [mul_sub, mul_smul_comm, mul_one, ip_sub_left, ip_smul_left]
  ring

/-! ### Imaginary elements -/

/-- `x` is **imaginary** (pure) when it is orthogonal to the unit. -/
def IsPure (x : C) : Prop := ip x 1 = 0

/--
@isnad1 id=eq.1h2v.s8.5ae8883a3b24 from=translated src=- shape=967ac504 vocab=8c72ad57
-/
theorem cstar_of_pure {x : C} (hx : IsPure x) : cstar x = -x := by
  simp only [cstar_apply, IsPure] at *
  rw [hx]
  module

/-- A pure element squares to a nonpositive real multiple of the unit.
@isnad1 id=eq.1h2v.s8.7de901566c94 from=translated src=- shape=09a765c8 vocab=7a77de02
-/
theorem sq_of_pure {x : C} (hx : IsPure x) : x * x = -(nf x) • (1 : C) := by
  rw [sq_eq x, hx]
  module

/-- Two pure elements anticommute up to their inner product:
`x y + y x = -2⟪x, y⟫ • 1`. This is the Clifford relation.
@isnad1 id=eq.2h3v.s8.2398c8c4f9ed from=translated src=- shape=192dde94 vocab=bf7423bd
-/
theorem pure_mul_pure_add {x y : C} (hx : IsPure x) (hy : IsPure y) :
    x * y + y * x = -(2 * ip x y) • (1 : C) := by
  rw [mul_add_mul x y, hx, hy]
  module

/-- The imaginary part of `x`. -/
def impart (x : C) : C := x - (ip x 1) • (1 : C)

/--
@isnad1 id=ispure.0h2v.s7.baf36228e6e1 from=translated src=- shape=1d72cf7b vocab=4efe499c
-/
theorem isPure_impart [Nontrivial C] (x : C) : IsPure (impart x) := by
  simp only [IsPure, impart, ip_sub_left, ip_smul_left, ip_one_one]
  ring

/--
@isnad1 id=eq.0h2v.s8.28c9bfda01ef from=translated src=- shape=9e10640d vocab=cbed1197
-/
theorem impart_add_re (x : C) : (ip x 1) • (1 : C) + impart x = x := by
  simp only [impart]; abel

end CompositionAlgebra
