/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Core.GradedBasis
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialSupport
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Signature
import Tengoku.Seed.Algebra.Ring.MinimalAxioms
import Tengoku.Seed.LinearAlgebra.Basis.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Numerical intersection data for the blow-up of `P²` at two points

The first model in this repository of Picard rank greater than two.  For
`X = Bl_{p,q} P²` the numerical divisor lattice is

```text
N¹(X) = ℤH ⊕ ℤE₁ ⊕ ℤE₂,   H² = 1,  E₁² = E₂² = -1,
```

with all other products zero, so the intersection form is `diag(1, -1, -1)`:
signature `(1, 2)`.  This is the smallest example in the Mizuno--Yoshida family
in which `ω^⊥` is a genuine negative definite **plane** rather than a point,
which is what makes it worth building.

## Why rank three and not rank two

`SmoothQuadric.lean` already has Picard rank two, but its form is hyperbolic
and its `ω^⊥` is a line.  `RankOneRealization.lean` has `ω^⊥ = 0`, so
`DivisorSpace.HodgeDefinite` there is vacuous in its definiteness clause.  Here
the clause has content: `blowUpHodgeDefinite` is the reverse Cauchy--Schwarz
inequality for `diag(1,-1,-1)`, and it is proved, not supplied.  That is the
first time in this library that the Hodge input to the support property of
`Stability/DivisorialSupport.lean` is discharged by a real argument.

## The ring

The rational intersection ring is `ℚ ⊕ N¹_ℚ ⊕ ℚ` with

```text
(a, v, s)(a', v', s') = (aa', av' + a'v, as' + a's + v·v').
```

It is built here as a bespoke five-field carrier rather than as a quotient of a
polynomial ring, because the graded basis `1, H, E₁, E₂, pt` then holds by
`decide` on each pair instead of needing a normal form for an ideal.  The
nested-dual-number trick of `SmoothQuadric.lean` does not extend: it produces a
hyperbolic form, and `diag(1,-1,-1)` is not hyperbolic.

## The lattice, and why `ch₂` is reparametrized

`ch₂` is a half-integer here, exactly as on `P²`.  For `D = aH + bE₁ + cE₂` the
line bundle `O(D)` has `ch₂ = (a² - b² - c²)/2`.  Coordinates `(r, a, b, c, v)`
therefore record

```text
ch₂ = (a + b + c)/2 + v,
```

which is the shift that makes `χ = r + 2a + b + c + v` integral, the same device
`ProjectivePlane.lean` uses with `ch₂ = c/2 + v`.

## What is not claimed

The carrier is not identified with `K_num(X)` for a geometric blow-up, and no
Chern-character map from coherent sheaves is constructed.  Ampleness enters only
as the numerical condition `∫(ω²) > 0`; the actual ample cone
`a > b + c, b > 0, c > 0` is recorded but not required by any theorem below.
-/

open Submodule Set
open DerivedAlgGeo.LinearAlgebra
open CategoryTheory.Triangulated.WeakStabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

namespace AlgebraicGeometry.Numerical.Examples.BlowUpPlane

noncomputable section

/-! ### The rational intersection ring -/

/-- The rational intersection ring of `Bl_{p,q} P²`, in the basis
`1, H, E₁, E₂, pt`.-/
@[ext]
structure Ring where
  /-- The coefficient of `1`.-/
  const : ℚ
  /-- The coefficient of `H`.-/
  hCoeff : ℚ
  /-- The coefficient of `E₁`.-/
  e₁Coeff : ℚ
  /-- The coefficient of `E₂`.-/
  e₂Coeff : ℚ
  /-- The coefficient of the point class.-/
  ptCoeff : ℚ

namespace Ring

instance : Zero Ring := ⟨⟨0, 0, 0, 0, 0⟩⟩
instance : One Ring := ⟨⟨1, 0, 0, 0, 0⟩⟩
instance : Add Ring :=
  ⟨fun x y => ⟨x.const + y.const, x.hCoeff + y.hCoeff, x.e₁Coeff + y.e₁Coeff,
    x.e₂Coeff + y.e₂Coeff, x.ptCoeff + y.ptCoeff⟩⟩
instance : Neg Ring :=
  ⟨fun x => ⟨-x.const, -x.hCoeff, -x.e₁Coeff, -x.e₂Coeff, -x.ptCoeff⟩⟩

/-- The intersection product: `diag(1, -1, -1)` on the divisor coordinates,
landing in the point class.-/
instance : Mul Ring :=
  ⟨fun x y =>
    ⟨x.const * y.const,
      x.const * y.hCoeff + y.const * x.hCoeff,
      x.const * y.e₁Coeff + y.const * x.e₁Coeff,
      x.const * y.e₂Coeff + y.const * x.e₂Coeff,
      x.const * y.ptCoeff + y.const * x.ptCoeff
        + x.hCoeff * y.hCoeff - x.e₁Coeff * y.e₁Coeff - x.e₂Coeff * y.e₂Coeff⟩⟩

/--
@isnad1 id=eq.0h0v.s3.69beb58ca3e6 from=translated src=- shape=1ac31801 vocab=58f55cfa
-/
@[simp] theorem zero_const : (0 : Ring).const = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.c2bcc27fe93e from=translated src=- shape=1ac31801 vocab=243cff78
-/
@[simp] theorem zero_hCoeff : (0 : Ring).hCoeff = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.3488d79f143d from=translated src=- shape=1ac31801 vocab=0b4e911f
-/
@[simp] theorem zero_e₁Coeff : (0 : Ring).e₁Coeff = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.7932c0a0d1da from=translated src=- shape=1ac31801 vocab=1d0bbb93
-/
@[simp] theorem zero_e₂Coeff : (0 : Ring).e₂Coeff = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.dcb00db46143 from=translated src=- shape=1ac31801 vocab=13f55b47
-/
@[simp] theorem zero_ptCoeff : (0 : Ring).ptCoeff = 0 := rfl

/--
@isnad1 id=eq.0h0v.s3.ef409b9f3287 from=translated src=- shape=1ac31801 vocab=58f55cfa
-/
@[simp] theorem one_const : (1 : Ring).const = 1 := rfl
/--
@isnad1 id=eq.0h0v.s3.83a7d34fb18c from=translated src=- shape=1ac31801 vocab=243cff78
-/
@[simp] theorem one_hCoeff : (1 : Ring).hCoeff = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.822e55925575 from=translated src=- shape=1ac31801 vocab=0b4e911f
-/
@[simp] theorem one_e₁Coeff : (1 : Ring).e₁Coeff = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.e6c2a627c0e2 from=translated src=- shape=1ac31801 vocab=1d0bbb93
-/
@[simp] theorem one_e₂Coeff : (1 : Ring).e₂Coeff = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.9b2c8c354081 from=translated src=- shape=1ac31801 vocab=13f55b47
-/
@[simp] theorem one_ptCoeff : (1 : Ring).ptCoeff = 0 := rfl

/--
@isnad1 id=eq.0h2v.s4.2195b328ea6e from=translated src=- shape=0438c7a3 vocab=41418ef4
-/
@[simp] theorem add_const (x y : Ring) : (x + y).const = x.const + y.const := rfl
/--
@isnad1 id=eq.0h2v.s4.4b5c8a817b26 from=translated src=- shape=0438c7a3 vocab=e8076a0a
-/
@[simp] theorem add_hCoeff (x y : Ring) : (x + y).hCoeff = x.hCoeff + y.hCoeff := rfl
/--
@isnad1 id=eq.0h2v.s4.53a23c0019fe from=translated src=- shape=0438c7a3 vocab=5cf56536
-/
@[simp] theorem add_e₁Coeff (x y : Ring) : (x + y).e₁Coeff = x.e₁Coeff + y.e₁Coeff := rfl
/--
@isnad1 id=eq.0h2v.s4.e0962c78e224 from=translated src=- shape=0438c7a3 vocab=038b12c1
-/
@[simp] theorem add_e₂Coeff (x y : Ring) : (x + y).e₂Coeff = x.e₂Coeff + y.e₂Coeff := rfl
/--
@isnad1 id=eq.0h2v.s4.347e1e845eb4 from=translated src=- shape=0438c7a3 vocab=a5c39a2b
-/
@[simp] theorem add_ptCoeff (x y : Ring) : (x + y).ptCoeff = x.ptCoeff + y.ptCoeff := rfl

/--
@isnad1 id=eq.0h1v.s3.df79be1f4bf0 from=translated src=- shape=5a02da31 vocab=554c9a21
-/
@[simp] theorem neg_const (x : Ring) : (-x).const = -x.const := rfl
/--
@isnad1 id=eq.0h1v.s3.ba382a83f35f from=translated src=- shape=5a02da31 vocab=f0a8c19e
-/
@[simp] theorem neg_hCoeff (x : Ring) : (-x).hCoeff = -x.hCoeff := rfl
/--
@isnad1 id=eq.0h1v.s3.bb2598bf23c0 from=translated src=- shape=5a02da31 vocab=982ea8c6
-/
@[simp] theorem neg_e₁Coeff (x : Ring) : (-x).e₁Coeff = -x.e₁Coeff := rfl
/--
@isnad1 id=eq.0h1v.s3.49434f5a3312 from=translated src=- shape=5a02da31 vocab=0f84ee43
-/
@[simp] theorem neg_e₂Coeff (x : Ring) : (-x).e₂Coeff = -x.e₂Coeff := rfl
/--
@isnad1 id=eq.0h1v.s3.7e934004c152 from=translated src=- shape=5a02da31 vocab=828c21a2
-/
@[simp] theorem neg_ptCoeff (x : Ring) : (-x).ptCoeff = -x.ptCoeff := rfl

/--
@isnad1 id=eq.0h2v.s4.fba1139e5cfb from=translated src=- shape=0438c7a3 vocab=1d6c8d57
-/
@[simp] theorem mul_const (x y : Ring) : (x * y).const = x.const * y.const := rfl
/--
@isnad1 id=eq.0h2v.s5.e833301198d2 from=translated src=- shape=317ac3c9 vocab=d4b432ec
-/
@[simp] theorem mul_hCoeff (x y : Ring) :
    (x * y).hCoeff = x.const * y.hCoeff + y.const * x.hCoeff := rfl
/--
@isnad1 id=eq.0h2v.s5.d4e50c13727d from=translated src=- shape=317ac3c9 vocab=20830237
-/
@[simp] theorem mul_e₁Coeff (x y : Ring) :
    (x * y).e₁Coeff = x.const * y.e₁Coeff + y.const * x.e₁Coeff := rfl
/--
@isnad1 id=eq.0h2v.s5.8aa9c7c53c83 from=translated src=- shape=317ac3c9 vocab=e2885f8a
-/
@[simp] theorem mul_e₂Coeff (x y : Ring) :
    (x * y).e₂Coeff = x.const * y.e₂Coeff + y.const * x.e₂Coeff := rfl
/--
@isnad1 id=eq.0h2v.s6.afff54850d98 from=translated src=- shape=a5bfe300 vocab=6a63e034
-/
@[simp] theorem mul_ptCoeff (x y : Ring) :
    (x * y).ptCoeff = x.const * y.ptCoeff + y.const * x.ptCoeff
      + x.hCoeff * y.hCoeff - x.e₁Coeff * y.e₁Coeff - x.e₂Coeff * y.e₂Coeff := rfl

instance : CommRing Ring :=
  CommRing.ofMinimalAxioms
    (fun a b c => by ext <;> simp <;> ring)
    (fun a => by ext <;> simp)
    (fun a => by ext <;> simp)
    (fun a b c => by ext <;> simp <;> ring)
    (fun a b => by ext <;> simp <;> ring)
    (fun a => by ext <;> simp)
    (fun a b c => by ext <;> simp <;> ring)

/-- The rational scalars, as a ring map.-/
def ofRat : ℚ →+* Ring where
  toFun q := ⟨q, 0, 0, 0, 0⟩
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp
  map_zero' := rfl
  map_add' _ _ := by ext <;> simp

instance : Algebra ℚ Ring := ofRat.toAlgebra

/--
@isnad1 id=eq.0h1v.s6.4dc859de82f7 from=translated src=- shape=51b3238f vocab=786e5267
-/
theorem algebraMap_eq (q : ℚ) : algebraMap ℚ Ring q = ⟨q, 0, 0, 0, 0⟩ := rfl

/--
@isnad1 id=eq.0h1v.s5.ca434769d96b from=translated src=- shape=0773184a vocab=d3818154
-/
@[simp] theorem algebraMap_const (q : ℚ) : (algebraMap ℚ Ring q).const = q := rfl
/--
@isnad1 id=eq.0h1v.s5.49679368063d from=translated src=- shape=8d8c43c2 vocab=efc41b26
-/
@[simp] theorem algebraMap_hCoeff (q : ℚ) : (algebraMap ℚ Ring q).hCoeff = 0 := rfl
/--
@isnad1 id=eq.0h1v.s5.691d6b11eaa8 from=translated src=- shape=8d8c43c2 vocab=140d3adc
-/
@[simp] theorem algebraMap_e₁Coeff (q : ℚ) : (algebraMap ℚ Ring q).e₁Coeff = 0 := rfl
/--
@isnad1 id=eq.0h1v.s5.c2c89d2f9511 from=translated src=- shape=8d8c43c2 vocab=d6886587
-/
@[simp] theorem algebraMap_e₂Coeff (q : ℚ) : (algebraMap ℚ Ring q).e₂Coeff = 0 := rfl
/--
@isnad1 id=eq.0h1v.s5.fe761ebde482 from=translated src=- shape=8d8c43c2 vocab=883ea626
-/
@[simp] theorem algebraMap_ptCoeff (q : ℚ) : (algebraMap ℚ Ring q).ptCoeff = 0 := rfl

/--
@isnad1 id=eq.0h2v.s5.61072e941cd5 from=translated src=- shape=0438c7a3 vocab=492b658c
-/
@[simp] theorem sub_const (x y : Ring) : (x - y).const = x.const - y.const := by
  rw [sub_eq_add_neg, add_const, neg_const, ← sub_eq_add_neg]
/--
@isnad1 id=eq.0h2v.s5.ef8887a7c159 from=translated src=- shape=0438c7a3 vocab=1c14ff84
-/
@[simp] theorem sub_hCoeff (x y : Ring) : (x - y).hCoeff = x.hCoeff - y.hCoeff := by
  rw [sub_eq_add_neg, add_hCoeff, neg_hCoeff, ← sub_eq_add_neg]
/--
@isnad1 id=eq.0h2v.s5.784bc9d3e9ac from=translated src=- shape=0438c7a3 vocab=94673b50
-/
@[simp] theorem sub_e₁Coeff (x y : Ring) : (x - y).e₁Coeff = x.e₁Coeff - y.e₁Coeff := by
  rw [sub_eq_add_neg, add_e₁Coeff, neg_e₁Coeff, ← sub_eq_add_neg]
/--
@isnad1 id=eq.0h2v.s5.aac3aa379313 from=translated src=- shape=0438c7a3 vocab=d47b9ef0
-/
@[simp] theorem sub_e₂Coeff (x y : Ring) : (x - y).e₂Coeff = x.e₂Coeff - y.e₂Coeff := by
  rw [sub_eq_add_neg, add_e₂Coeff, neg_e₂Coeff, ← sub_eq_add_neg]
/--
@isnad1 id=eq.0h2v.s5.b27bd7ceb852 from=translated src=- shape=0438c7a3 vocab=440c32ef
-/
@[simp] theorem sub_ptCoeff (x y : Ring) : (x - y).ptCoeff = x.ptCoeff - y.ptCoeff := by
  rw [sub_eq_add_neg, add_ptCoeff, neg_ptCoeff, ← sub_eq_add_neg]

/--
@isnad1 id=eq.0h2v.s5.9d58e1527a43 from=translated src=- shape=803e8aba vocab=9ae5f5bf
-/
@[simp] theorem smul_const (q : ℚ) (x : Ring) : (q • x).const = q * x.const := by
  rw [Algebra.smul_def, algebraMap_eq]; simp
/--
@isnad1 id=eq.0h2v.s5.047617433af5 from=translated src=- shape=803e8aba vocab=6830d668
-/
@[simp] theorem smul_hCoeff (q : ℚ) (x : Ring) : (q • x).hCoeff = q * x.hCoeff := by
  rw [Algebra.smul_def, algebraMap_eq]; simp
/--
@isnad1 id=eq.0h2v.s5.0120c43bc938 from=translated src=- shape=803e8aba vocab=823cb311
-/
@[simp] theorem smul_e₁Coeff (q : ℚ) (x : Ring) : (q • x).e₁Coeff = q * x.e₁Coeff := by
  rw [Algebra.smul_def, algebraMap_eq]; simp
/--
@isnad1 id=eq.0h2v.s5.dbd2b70e9b30 from=translated src=- shape=803e8aba vocab=dd2a31fa
-/
@[simp] theorem smul_e₂Coeff (q : ℚ) (x : Ring) : (q • x).e₂Coeff = q * x.e₂Coeff := by
  rw [Algebra.smul_def, algebraMap_eq]; simp
/--
@isnad1 id=eq.0h2v.s5.0c3476d6c436 from=translated src=- shape=803e8aba vocab=67041c1c
-/
@[simp] theorem smul_ptCoeff (q : ℚ) (x : Ring) : (q • x).ptCoeff = q * x.ptCoeff := by
  rw [Algebra.smul_def, algebraMap_eq]; simp

end Ring

/-! ### The named classes -/

/-- The hyperplane class pulled back from `P²`.-/
def hQ : Ring := ⟨0, 1, 0, 0, 0⟩

/-- The first exceptional class.-/
def e₁Q : Ring := ⟨0, 0, 1, 0, 0⟩

/-- The second exceptional class.-/
def e₂Q : Ring := ⟨0, 0, 0, 1, 0⟩

/-- The point class.-/
def pointQ : Ring := ⟨0, 0, 0, 0, 1⟩

/--
@isnad1 id=eq.0h0v.s3.143a11ad51e9 from=translated src=- shape=b0ae1d2b vocab=194ed18a
-/
@[simp] theorem hQ_const : hQ.const = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.405be8f4b65f from=translated src=- shape=b0ae1d2b vocab=2c7ed410
-/
@[simp] theorem hQ_hCoeff : hQ.hCoeff = 1 := rfl
/--
@isnad1 id=eq.0h0v.s3.0a6b5d9ecac5 from=translated src=- shape=b0ae1d2b vocab=5fd19b1f
-/
@[simp] theorem hQ_e₁Coeff : hQ.e₁Coeff = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.db55b599747c from=translated src=- shape=b0ae1d2b vocab=26e35e2f
-/
@[simp] theorem hQ_e₂Coeff : hQ.e₂Coeff = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.1112d7623d4e from=translated src=- shape=b0ae1d2b vocab=d13b15ca
-/
@[simp] theorem hQ_ptCoeff : hQ.ptCoeff = 0 := rfl

/--
@isnad1 id=eq.0h0v.s3.22169a7aa0cd from=translated src=- shape=b0ae1d2b vocab=d7d8c44a
-/
@[simp] theorem e₁Q_const : e₁Q.const = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.e82bc769c5ca from=translated src=- shape=b0ae1d2b vocab=2468d82d
-/
@[simp] theorem e₁Q_hCoeff : e₁Q.hCoeff = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.fbb343655005 from=translated src=- shape=b0ae1d2b vocab=8587be41
-/
@[simp] theorem e₁Q_e₁Coeff : e₁Q.e₁Coeff = 1 := rfl
/--
@isnad1 id=eq.0h0v.s3.9c2ef79754ea from=translated src=- shape=b0ae1d2b vocab=f03a7126
-/
@[simp] theorem e₁Q_e₂Coeff : e₁Q.e₂Coeff = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.05f89981366f from=translated src=- shape=b0ae1d2b vocab=4820e8ba
-/
@[simp] theorem e₁Q_ptCoeff : e₁Q.ptCoeff = 0 := rfl

/--
@isnad1 id=eq.0h0v.s3.cf3ddb795d3e from=translated src=- shape=b0ae1d2b vocab=f6e768d9
-/
@[simp] theorem e₂Q_const : e₂Q.const = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.912f7aeab244 from=translated src=- shape=b0ae1d2b vocab=23cbb44a
-/
@[simp] theorem e₂Q_hCoeff : e₂Q.hCoeff = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.2f094fe71353 from=translated src=- shape=b0ae1d2b vocab=f39705fa
-/
@[simp] theorem e₂Q_e₁Coeff : e₂Q.e₁Coeff = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.f1d233dd9f63 from=translated src=- shape=b0ae1d2b vocab=e1ed355e
-/
@[simp] theorem e₂Q_e₂Coeff : e₂Q.e₂Coeff = 1 := rfl
/--
@isnad1 id=eq.0h0v.s3.e88a3ea0e9b0 from=translated src=- shape=b0ae1d2b vocab=e1441fa4
-/
@[simp] theorem e₂Q_ptCoeff : e₂Q.ptCoeff = 0 := rfl

/--
@isnad1 id=eq.0h0v.s3.f39ab78f5fae from=translated src=- shape=b0ae1d2b vocab=982cd792
-/
@[simp] theorem pointQ_const : pointQ.const = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.314cb52c8ac8 from=translated src=- shape=b0ae1d2b vocab=630fe928
-/
@[simp] theorem pointQ_hCoeff : pointQ.hCoeff = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.f4d1cac39dd9 from=translated src=- shape=b0ae1d2b vocab=7e8373d9
-/
@[simp] theorem pointQ_e₁Coeff : pointQ.e₁Coeff = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.6a7be6b1fcd7 from=translated src=- shape=b0ae1d2b vocab=52511688
-/
@[simp] theorem pointQ_e₂Coeff : pointQ.e₂Coeff = 0 := rfl
/--
@isnad1 id=eq.0h0v.s3.718aa9889242 from=translated src=- shape=b0ae1d2b vocab=68f57a3b
-/
@[simp] theorem pointQ_ptCoeff : pointQ.ptCoeff = 1 := rfl

/--
@isnad1 id=eq.0h0v.s3.dbb72bd1473b from=translated src=- shape=8f076a7f vocab=a91f033d
-/
@[simp] theorem hQ_mul_hQ : hQ * hQ = pointQ := by ext <;> simp [hQ, pointQ]
/--
@isnad1 id=eq.0h0v.s3.79d35c93c922 from=translated src=- shape=9fff8687 vocab=e57fb20f
-/
@[simp] theorem e₁Q_mul_e₁Q : e₁Q * e₁Q = -pointQ := by ext <;> simp [e₁Q, pointQ]
/--
@isnad1 id=eq.0h0v.s3.3326379fc26f from=translated src=- shape=9fff8687 vocab=431b47a2
-/
@[simp] theorem e₂Q_mul_e₂Q : e₂Q * e₂Q = -pointQ := by ext <;> simp [e₂Q, pointQ]
/--
@isnad1 id=eq.0h0v.s4.745fcbdee646 from=translated src=- shape=33aceabd vocab=f2319411
-/
@[simp] theorem hQ_mul_e₁Q : hQ * e₁Q = 0 := by ext <;> simp [hQ, e₁Q]
/--
@isnad1 id=eq.0h0v.s4.413dc0a63ba6 from=translated src=- shape=33aceabd vocab=f2319411
-/
@[simp] theorem e₁Q_mul_hQ : e₁Q * hQ = 0 := by ext <;> simp [hQ, e₁Q]
/--
@isnad1 id=eq.0h0v.s4.5e4ba569b145 from=translated src=- shape=33aceabd vocab=f9054855
-/
@[simp] theorem hQ_mul_e₂Q : hQ * e₂Q = 0 := by ext <;> simp [hQ, e₂Q]
/--
@isnad1 id=eq.0h0v.s4.dbbd0d05fd94 from=translated src=- shape=33aceabd vocab=f9054855
-/
@[simp] theorem e₂Q_mul_hQ : e₂Q * hQ = 0 := by ext <;> simp [hQ, e₂Q]
/--
@isnad1 id=eq.0h0v.s4.75a240079b9e from=translated src=- shape=33aceabd vocab=696ebec4
-/
@[simp] theorem e₁Q_mul_e₂Q : e₁Q * e₂Q = 0 := by ext <;> simp [e₁Q, e₂Q]
/--
@isnad1 id=eq.0h0v.s4.b44d28d23c26 from=translated src=- shape=33aceabd vocab=696ebec4
-/
@[simp] theorem e₂Q_mul_e₁Q : e₂Q * e₁Q = 0 := by ext <;> simp [e₁Q, e₂Q]
/--
@isnad1 id=eq.0h0v.s4.d26846f2d258 from=translated src=- shape=33aceabd vocab=a91f033d
-/
@[simp] theorem hQ_mul_pointQ : hQ * pointQ = 0 := by ext <;> simp [hQ, pointQ]
/--
@isnad1 id=eq.0h0v.s4.c5e3126d11c3 from=translated src=- shape=33aceabd vocab=a91f033d
-/
@[simp] theorem pointQ_mul_hQ : pointQ * hQ = 0 := by ext <;> simp [hQ, pointQ]
/--
@isnad1 id=eq.0h0v.s4.028313771bef from=translated src=- shape=33aceabd vocab=99e06ec9
-/
@[simp] theorem e₁Q_mul_pointQ : e₁Q * pointQ = 0 := by ext <;> simp [e₁Q, pointQ]
/--
@isnad1 id=eq.0h0v.s4.c1cf441f5ae9 from=translated src=- shape=33aceabd vocab=99e06ec9
-/
@[simp] theorem pointQ_mul_e₁Q : pointQ * e₁Q = 0 := by ext <;> simp [e₁Q, pointQ]
/--
@isnad1 id=eq.0h0v.s4.25d1bb6848ef from=translated src=- shape=33aceabd vocab=3a27058b
-/
@[simp] theorem e₂Q_mul_pointQ : e₂Q * pointQ = 0 := by ext <;> simp [e₂Q, pointQ]
/--
@isnad1 id=eq.0h0v.s4.fb5943cb636d from=translated src=- shape=33aceabd vocab=3a27058b
-/
@[simp] theorem pointQ_mul_e₂Q : pointQ * e₂Q = 0 := by ext <;> simp [e₂Q, pointQ]
/--
@isnad1 id=eq.0h0v.s4.277bbccd2ffd from=translated src=- shape=73cd6f0b vocab=657bbd44
-/
@[simp] theorem pointQ_mul_pointQ : pointQ * pointQ = 0 := by ext <;> simp [pointQ]

/-! ### The graded basis -/

/-- Coordinates in the ordered basis `1, H, E₁, E₂, pt`.-/
def coordEquiv : Ring ≃ₗ[ℚ] (Fin 5 → ℚ) where
  toFun x := ![x.const, x.hCoeff, x.e₁Coeff, x.e₂Coeff, x.ptCoeff]
  invFun x := ⟨x 0, x 1, x 2, x 3, x 4⟩
  left_inv _ := rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl
  map_add' _ _ := by
    funext i
    fin_cases i <;> simp
  map_smul' _ _ := by
    funext i
    fin_cases i <;> simp

/-- The product basis `1, H, E₁, E₂, pt`.-/
def basis : Module.Basis (Fin 5) ℚ Ring := Module.Basis.ofEquivFun coordEquiv

/-- Codimension weights on the product basis.-/
def weight : Fin 5 → ℕ := ![0, 1, 1, 1, 2]

/--
@isnad1 id=eq.0h0v.s6.4efeedc087e0 from=translated src=- shape=85d10564 vocab=146c7c88
-/
@[simp] theorem basis_zero : basis 0 = 1 := by
  apply coordEquiv.injective; funext i; fin_cases i <;> simp [basis, coordEquiv]
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)
/--
@isnad1 id=eq.0h0v.s6.78ad0ee6f27d from=translated src=- shape=aa291ac9 vocab=b8aa6105
-/
@[simp] theorem basis_one : basis 1 = hQ := by
  apply coordEquiv.injective; funext i; fin_cases i <;> simp [basis, coordEquiv, hQ]
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)
/--
@isnad1 id=eq.0h0v.s6.075ec81d81a7 from=translated src=- shape=aa291ac9 vocab=ccd10ee7
-/
@[simp] theorem basis_two : basis 2 = e₁Q := by
  apply coordEquiv.injective; funext i; fin_cases i <;> simp [basis, coordEquiv, e₁Q]
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)
/--
@isnad1 id=eq.0h0v.s6.e5c68d7590e6 from=translated src=- shape=aa291ac9 vocab=359e71a5
-/
@[simp] theorem basis_three : basis 3 = e₂Q := by
  apply coordEquiv.injective; funext i; fin_cases i <;> simp [basis, coordEquiv, e₂Q]
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)
/--
@isnad1 id=eq.0h0v.s6.7fe2f7c436ad from=translated src=- shape=aa291ac9 vocab=36e4bc45
-/
@[simp] theorem basis_four : basis 4 = pointQ := by
  apply coordEquiv.injective; funext i; fin_cases i <;> simp [basis, coordEquiv, pointQ]
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/--
@isnad1 id=le.0h1v.s4.ea8a14dae304 from=translated src=- shape=b73a83c4 vocab=37f9b07d
-/
theorem weight_le_two (i : Fin 5) : weight i ≤ 2 := by fin_cases i <;> decide

/--
@isnad1 id=eq.0h0v.s4.4aac3eb93d30 from=translated src=- shape=3ffd5d8e vocab=93f96678
-/
@[simp] theorem weight_zero : weight 0 = 0 := rfl
/--
@isnad1 id=eq.0h0v.s4.a707596dcb7f from=translated src=- shape=3ffd5d8e vocab=93f96678
-/
@[simp] theorem weight_one : weight 1 = 1 := rfl
/--
@isnad1 id=eq.0h0v.s4.941ae6d3c942 from=translated src=- shape=3ffd5d8e vocab=93f96678
-/
@[simp] theorem weight_two : weight 2 = 1 := rfl
/--
@isnad1 id=eq.0h0v.s4.562f1512bd4e from=translated src=- shape=3ffd5d8e vocab=93f96678
-/
@[simp] theorem weight_three : weight 3 = 1 := rfl
/--
@isnad1 id=eq.0h0v.s4.f1818aa1787d from=translated src=- shape=3ffd5d8e vocab=93f96678
-/
@[simp] theorem weight_four : weight 4 = 2 := rfl

/-- Integration extracts the coefficient of the point class.-/
def degree : Ring →ₗ[ℚ] ℚ where
  toFun x := x.ptCoeff
  map_add' _ _ := rfl
  map_smul' _ _ := by simp

/--
@isnad1 id=eq.0h1v.s6.ae01131060da from=translated src=- shape=9fcea169 vocab=1e75b9b3
-/
@[simp] theorem degree_apply (x : Ring) : degree x = x.ptCoeff := rfl

/--
@isnad1 id=eq.1h1v.s7.9db00f37e58d from=translated src=- shape=748767e7 vocab=ba4a4902
-/
theorem degree_basis_of_ne (i : Fin 5) (hi : weight i ≠ 2) : degree (basis i) = 0 := by
  fin_cases i
  · simp
  · simp [hQ]
  · simp [e₁Q]
  · simp [e₂Q]
  · exact absurd rfl hi

/-! ### Membership of the named classes -/

/--
@isnad1 id=mem.0h0v.s7.f8ac738e5628 from=translated src=- shape=4d4e58a0 vocab=19992285
-/
theorem hQ_mem : hQ ∈ gradedPiece (basis : Fin 5 → Ring) weight 1 := by
  simpa using (mem_gradedPiece (b := (basis : Fin 5 → Ring)) (w := weight) 1)

/--
@isnad1 id=mem.0h0v.s7.040a142c651f from=translated src=- shape=4d4e58a0 vocab=a6ac8172
-/
theorem e₁Q_mem : e₁Q ∈ gradedPiece (basis : Fin 5 → Ring) weight 1 := by
  simpa using (mem_gradedPiece (b := (basis : Fin 5 → Ring)) (w := weight) 2)

/--
@isnad1 id=mem.0h0v.s7.a8488e62cb09 from=translated src=- shape=4d4e58a0 vocab=8ede752a
-/
theorem e₂Q_mem : e₂Q ∈ gradedPiece (basis : Fin 5 → Ring) weight 1 := by
  simpa using (mem_gradedPiece (b := (basis : Fin 5 → Ring)) (w := weight) 3)

/--
@isnad1 id=mem.0h0v.s7.9912e97f4bcc from=translated src=- shape=4d4e58a0 vocab=171d3c44
-/
theorem pointQ_mem : pointQ ∈ gradedPiece (basis : Fin 5 → Ring) weight 2 := by
  simpa using (mem_gradedPiece (b := (basis : Fin 5 → Ring)) (w := weight) 4)

/--
@isnad1 id=mem.0h0v.s7.fef919f95597 from=translated src=- shape=8d3d57e8 vocab=7d72dcce
-/
theorem one_mem : (1 : Ring) ∈ gradedPiece (basis : Fin 5 → Ring) weight 0 := by
  simpa using (mem_gradedPiece (b := (basis : Fin 5 → Ring)) (w := weight) 0)

/-- The multiplicative grading, checked on the twenty-five basis pairs.
@isnad1 id=mem.0h2v.s8.d6a808c7b951 from=translated src=- shape=bcd73aee vocab=bd42759d
-/
theorem basis_mul_mem (p q : Fin 5) :
    basis p * basis q ∈ gradedPiece (basis : Fin 5 → Ring) weight (weight p + weight q) := by
  fin_cases p <;> fin_cases q <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, basis_zero, basis_one, basis_two,
      basis_three, basis_four, one_mul, mul_one, hQ_mul_hQ, e₁Q_mul_e₁Q, e₂Q_mul_e₂Q,
      hQ_mul_e₁Q, e₁Q_mul_hQ, hQ_mul_e₂Q, e₂Q_mul_hQ, e₁Q_mul_e₂Q, e₂Q_mul_e₁Q,
      hQ_mul_pointQ, pointQ_mul_hQ, e₁Q_mul_pointQ, pointQ_mul_e₁Q, e₂Q_mul_pointQ,
      pointQ_mul_e₂Q, pointQ_mul_pointQ, weight_zero, weight_one, weight_two, weight_three,
      weight_four] <;>
    first
      | exact one_mem
      | exact hQ_mem
      | exact e₁Q_mem
      | exact e₂Q_mem
      | exact pointQ_mem
      | exact Submodule.neg_mem _ pointQ_mem
      | exact Submodule.zero_mem _

/-- The rational numerical intersection ring of the two-point blow-up.-/
@[reducible]
def numericalRing : NumericalRingData 2 Ring :=
  NumericalRingData.ofGradedBasis 2 basis weight weight_le_two one_mem
    basis_mul_mem degree degree_basis_of_ne

/-! ### The numerical lattice -/

/-- Numerical classes in the coordinates `(r, a, b, c, v)`, with
`ch₁ = aH + bE₁ + cE₂` and `ch₂ = (a + b + c)/2 + v`.-/
abbrev NumericalClass : Type := Fin 5 → ℤ

/-- The Chern-character components in the blow-up intersection ring.-/
def chComp (E : NumericalClass) : ℕ → Ring
  | 0 => algebraMap ℚ Ring ((E 0 : ℚ))
  | 1 => (E 1 : ℚ) • hQ + (E 2 : ℚ) • e₁Q + (E 3 : ℚ) • e₂Q
  | 2 => (((E 1 : ℚ) + (E 2 : ℚ) + (E 3 : ℚ)) / 2 + (E 4 : ℚ)) • pointQ
  | _ + 3 => 0

/--
@isnad1 id=mem.0h2v.s6.6249832656ba from=translated src=- shape=4f5c0a93 vocab=f17e538b
-/
theorem chComp_mem (E : NumericalClass) (i : ℕ) : chComp E i ∈ numericalRing.piece i := by
  match i with
  | 0 => exact numericalRing.algebraMap_mem_piece_zero _
  | 1 =>
      exact Submodule.add_mem _
        (Submodule.add_mem _ (Submodule.smul_mem _ _ hQ_mem) (Submodule.smul_mem _ _ e₁Q_mem))
        (Submodule.smul_mem _ _ e₂Q_mem)
  | 2 => exact Submodule.smul_mem _ _ pointQ_mem
  | _ + 3 => exact Submodule.zero_mem _

/--
@isnad1 id=eq.0h3v.s5.00a6d614f661 from=translated src=- shape=897af36f vocab=c746a655
-/
theorem chComp_add (E F : NumericalClass) (i : ℕ) :
    chComp (E + F) i = chComp E i + chComp F i := by
  match i with
  | 0 =>
      simp only [chComp, Pi.add_apply, Int.cast_add, map_add]
  | 1 =>
      simp only [chComp, Pi.add_apply]
      push_cast
      module
  | 2 =>
      simp only [chComp, Pi.add_apply]
      push_cast
      rw [← add_smul]
      congr 1
      ring
  | _ + 3 =>
      simp only [chComp]
      rw [add_zero]

/-! ### Todd class, Euler characteristic, and the variety -/

/-- The Todd class of the two-point blow-up: `td₁ = -K/2 = (3H - E₁ - E₂)/2` and
`td₂ = pt`, so `∫td₂ = χ(O_X) = 1`.-/
def toddComp : ℕ → Ring
  | 0 => 1
  | 1 => (3 / 2 : ℚ) • hQ - (1 / 2 : ℚ) • e₁Q - (1 / 2 : ℚ) • e₂Q
  | 2 => pointQ
  | _ + 3 => 0

/--
@isnad1 id=mem.0h1v.s6.0d73e4ec3cf0 from=translated src=- shape=e5381633 vocab=8db46002
-/
theorem toddComp_mem (i : ℕ) : toddComp i ∈ numericalRing.piece i := by
  match i with
  | 0 => exact numericalRing.one_mem_piece_zero
  | 1 =>
      exact Submodule.sub_mem _
        (Submodule.sub_mem _ (Submodule.smul_mem _ _ hQ_mem) (Submodule.smul_mem _ _ e₁Q_mem))
        (Submodule.smul_mem _ _ e₂Q_mem)
  | 2 => exact pointQ_mem
  | _ + 3 => exact Submodule.zero_mem _

/-- The total Chern character in the five explicit coordinates.
@isnad1 id=eq.0h1v.s7.1ebf8b42652d from=translated src=- shape=86d568b2 vocab=5f89e92f
-/
theorem ch_sum (E : NumericalClass) :
    (∑ i ∈ Finset.range (2 + 1), chComp E i) =
      ⟨(E 0 : ℚ), (E 1 : ℚ), (E 2 : ℚ), (E 3 : ℚ),
        ((E 1 : ℚ) + (E 2 : ℚ) + (E 3 : ℚ)) / 2 + (E 4 : ℚ)⟩ := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ext <;> simp only [chComp, Ring.algebraMap_const, Ring.algebraMap_hCoeff,
      Ring.algebraMap_e₁Coeff, Ring.algebraMap_e₂Coeff, Ring.algebraMap_ptCoeff, Ring.add_const, Ring.add_hCoeff, Ring.add_e₁Coeff, Ring.add_e₂Coeff,
      Ring.add_ptCoeff, Ring.smul_const, Ring.smul_hCoeff, Ring.smul_e₁Coeff,
      Ring.smul_e₂Coeff, Ring.smul_ptCoeff,
      hQ_const, hQ_hCoeff, hQ_e₁Coeff, hQ_e₂Coeff, hQ_ptCoeff,
      e₁Q_const, e₁Q_hCoeff, e₁Q_e₁Coeff, e₁Q_e₂Coeff, e₁Q_ptCoeff,
      e₂Q_const, e₂Q_hCoeff, e₂Q_e₁Coeff, e₂Q_e₂Coeff, e₂Q_ptCoeff,
      pointQ_const, pointQ_hCoeff, pointQ_e₁Coeff, pointQ_e₂Coeff, pointQ_ptCoeff] <;> ring

/-- The total Todd class in the five explicit coordinates.
@isnad1 id=eq.0h0v.s6.84e052f4d076 from=translated src=- shape=ae742f17 vocab=dc3bc649
-/
theorem todd_sum :
    (∑ j ∈ Finset.range (2 + 1), toddComp j) =
      ⟨(1 : ℚ), (3 / 2 : ℚ), (-1 / 2 : ℚ), (-1 / 2 : ℚ), (1 : ℚ)⟩ := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ext <;> simp [toddComp] <;> ring

/-- The Euler characteristic in the chosen integral coordinates.-/
def chi : NumericalClass →+ ℤ :=
  AddMonoidHom.mk'
    (fun E => E 0 + 2 * E 1 + E 2 + E 3 + E 4)
    (by
      intro E F
      show (E + F) 0 + 2 * (E + F) 1 + (E + F) 2 + (E + F) 3 + (E + F) 4 = _
      show E 0 + F 0 + 2 * (E 1 + F 1) + (E 2 + F 2) + (E 3 + F 3) + (E 4 + F 4) = _
      ring)

/-- **The model.** The blow-up of `P²` at two points, of Picard rank three.-/
@[reducible]
def numericalVariety : NumericalVarietyData 2 Ring NumericalClass where
  ring := numericalRing
  rank := AddMonoidHom.mk' (fun E => E 0) (by intro E F; rfl)
  chComp := chComp
  chComp_mem := chComp_mem
  chComp_zero := fun _ => rfl
  chComp_add := chComp_add
  toddComp := toddComp
  toddComp_mem := toddComp_mem
  toddComp_zero := rfl
  chi := chi

/-- The presentation satisfies Hirzebruch--Riemann--Roch:
`χ = r + 2a + b + c + v`.
@isnad1 id=satisfie.0h0v.s5.cbb25ca743e2 from=translated src=- shape=8c01f280 vocab=1f40c3f4
-/
theorem numericalVariety_satisfiesHRR : numericalVariety.SatisfiesHRR := by
  refine ⟨fun E => ?_⟩
  change ((E 0 + 2 * E 1 + E 2 + E 3 + E 4 : ℤ) : ℚ) =
    degree ((∑ i ∈ Finset.range (2 + 1), chComp E i) *
      (∑ j ∈ Finset.range (2 + 1), toddComp j))
  rw [ch_sum, todd_sum, degree_apply, Ring.mul_ptCoeff]
  push_cast
  ring

/-! ### Polarizations -/

/-- A rational divisor class `aH + bE₁ + cE₂`.-/
def polarizationClass (a b c : ℚ) : Ring := a • hQ + b • e₁Q + c • e₂Q

/--
@isnad1 id=mem.0h3v.s6.f452e122c596 from=translated src=- shape=e7f5f55f vocab=652640b9
-/
theorem polarizationClass_mem (a b c : ℚ) : polarizationClass a b c ∈ numericalRing.piece 1 :=
  Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.smul_mem _ _ hQ_mem) (Submodule.smul_mem _ _ e₁Q_mem))
    (Submodule.smul_mem _ _ e₂Q_mem)

/-- Not a `simp` lemma: `degree_apply` is already `simp` and rewrites the
left-hand side to a `ptCoeff` projection first, so the normal-form linter
rejects the attribute.
@isnad1 id=eq.0h3v.s7.7315a4c700f6 from=translated src=- shape=cdb3f5f4 vocab=2ac9ad3b
-/
theorem degree_polarizationClass_sq (a b c : ℚ) :
    numericalRing.degree (polarizationClass a b c ^ 2) = a ^ 2 - b ^ 2 - c ^ 2 := by
  change degree (polarizationClass a b c ^ 2) = _
  rw [pow_two, degree_apply, Ring.mul_ptCoeff]
  simp [polarizationClass]
  ring

/-- **The ample cone of the two-point blow-up**, recorded for the reader:
`aH - bE₁ - cE₂` is ample exactly when `b > 0`, `c > 0` and `a > b + c`.  No
theorem below needs it; the numerical condition that matters is `∫(ω²) > 0`.-/
def IsAmpleCoefficients (a b c : ℚ) : Prop := 0 < b ∧ 0 < c ∧ b + c < a

/-- A polarization from coefficients of positive square.-/
def polarization (a b c : ℚ) (h : 0 < a ^ 2 - b ^ 2 - c ^ 2) :
    Polarization numericalVariety.ring where
  cls := polarizationClass a b c
  cls_mem := polarizationClass_mem a b c
  degree_pow_pos := by rw [degree_polarizationClass_sq]; exact h

/-- The anticanonical polarization `-K = 3H - E₁ - E₂`, of square `7`.-/
def antiCanonicalPolarization : Polarization numericalVariety.ring :=
  polarization 3 (-1) (-1) (by norm_num)

/-! ### The real divisor space -/

/-- Real numerical divisor classes, in the basis `H, E₁, E₂`.-/
abbrev Divisor : Type := ℝ × ℝ × ℝ

/-- The intersection form `diag(1, -1, -1)`.-/
def intersectionForm : LinearMap.BilinForm ℝ Divisor :=
  LinearMap.mk₂ ℝ (fun x y => x.1 * y.1 - x.2.1 * y.2.1 - x.2.2 * y.2.2)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by simp; ring) (fun _ _ _ => by simp; ring)

/--
@isnad1 id=eq.0h2v.s9.41abb775bc70 from=translated src=- shape=b0a91187 vocab=26bc3639
-/
@[simp]
theorem intersectionForm_apply (x y : Divisor) :
    intersectionForm x y = x.1 * y.1 - x.2.1 * y.2.1 - x.2.2 * y.2.2 := rfl

/-- The rank-three real divisor space of the two-point blow-up.-/
def divisorSpace : DivisorSpace Divisor where
  intersection := intersectionForm
  intersection_symm := ⟨by intro x y; simp; ring⟩

/--
@isnad1 id=eq.0h2v.s7.7d34096cffe9 from=translated src=- shape=463fe0dd vocab=9bae82d6
-/
@[simp]
theorem divisorSpace_pair (x y : Divisor) :
    divisorSpace.pair x y = x.1 * y.1 - x.2.1 * y.2.1 - x.2.2 * y.2.2 := rfl

/-! ### The realization -/

/--
@isnad1 id=eq.0h0v.s7.7372976fd7f2 from=translated src=- shape=020dfd9a vocab=2a6f8c6d
-/
theorem weightOne_preimage : weight ⁻¹' ({1} : Set ℕ) = ({1, 2, 3} : Set (Fin 5)) := by
  ext i
  fin_cases i <;> simp [weight]

/-- The codimension-one piece is the rational span of `H, E₁, E₂`.
@isnad1 id=eq.0h0v.s7.139231f4be19 from=translated src=- shape=67d12ec0 vocab=49e01d25
-/
theorem pieceOne_eq_span :
    gradedPiece (basis : Fin 5 → Ring) weight 1 =
      Submodule.span ℚ ({hQ, e₁Q, e₂Q} : Set Ring) := by
  rw [gradedPiece, weightOne_preimage, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_singleton, basis_one, basis_two, basis_three]

/-- Every class of codimension one has vanishing constant term.  This is the
only fact about the piece the realization needs.
@isnad1 id=eq.1h1v.s7.1ae5ea5149b2 from=translated src=- shape=103c646c vocab=3a77394f
-/
theorem const_eq_zero_of_mem_pieceOne {x : Ring}
    (hx : x ∈ gradedPiece (basis : Fin 5 → Ring) weight 1) : x.const = 0 := by
  rw [pieceOne_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl <;> rfl
  | zero => rfl
  | add a b _ _ ha hb => simp [ha, hb]
  | smul q a _ ha => simp [ha]

/-- The realization of a rational divisor class in the basis `H, E₁, E₂`.-/
def divisorClass : numericalRing.piece 1 →+ Divisor :=
  AddMonoidHom.mk'
    (fun x => ((x.1.hCoeff : ℝ), (x.1.e₁Coeff : ℝ), (x.1.e₂Coeff : ℝ)))
    (by
      intro x y
      ext <;> simp)

/--
@isnad1 id=eq.0h1v.s10.d23862dee713 from=translated src=- shape=109f5678 vocab=b9bc3e2b
-/
@[simp]
theorem divisorClass_apply (x : numericalRing.piece 1) :
    divisorClass x = ((x.1.hCoeff : ℝ), (x.1.e₁Coeff : ℝ), (x.1.e₂Coeff : ℝ)) := rfl

/--
@isnad1 id=eq.0h2v.s11.c0b4c33e579f from=translated src=- shape=cebfd54d vocab=1ae9cce1
-/
theorem divisorClass_map_rat_smul (q : ℚ) (x : numericalRing.piece 1) :
    divisorClass (q • x) = (q : ℝ) • divisorClass x := by
  ext <;> simp [divisorClass]

/--
@isnad1 id=eq.0h2v.s11.e1f571d1e1fe from=translated src=- shape=2cf78a91 vocab=947ca716
-/
theorem divisorClass_intersection (x y : numericalRing.piece 1) :
    divisorSpace.pair (divisorClass x) (divisorClass y) =
      ((numericalRing.degree (x.1 * y.1) : ℚ) : ℝ) := by
  have hx := const_eq_zero_of_mem_pieceOne x.2
  have hy := const_eq_zero_of_mem_pieceOne y.2
  show (x.1.hCoeff : ℝ) * (y.1.hCoeff : ℝ) - (x.1.e₁Coeff : ℝ) * (y.1.e₁Coeff : ℝ)
      - (x.1.e₂Coeff : ℝ) * (y.1.e₂Coeff : ℝ) = _
  show _ = ((degree (x.1 * y.1) : ℚ) : ℝ)
  rw [degree_apply, Ring.mul_ptCoeff, hx, hy]
  push_cast
  ring

/-- **The real divisor realization of the two-point blow-up.**-/
def numericalRealization :
    Surface.NumericalRealization numericalVariety.ring (D := Divisor) where
  divisorSpace := divisorSpace
  divisorClass := divisorClass
  map_rat_smul := divisorClass_map_rat_smul
  intersection_eq := divisorClass_intersection

/--
@isnad1 id=eq.0h0v.s6.3556499b8d17 from=translated src=- shape=02811bfd vocab=3a31f9db
-/
@[simp]
theorem numericalRealization_divisorSpace :
    numericalRealization.divisorSpace = divisorSpace := rfl

/--
@isnad1 id=eq.1h3v.s7.b14681745058 from=translated src=- shape=54dd9472 vocab=2d94b468
-/
@[simp]
theorem numericalRealization_polarization (a b c : ℚ) (h : 0 < a ^ 2 - b ^ 2 - c ^ 2) :
    numericalRealization.realizePolarization (polarization a b c h) =
      ((a : ℝ), (b : ℝ), (c : ℝ)) := by
  show divisorClass ⟨polarizationClass a b c, polarizationClass_mem a b c⟩ = _
  ext <;> simp [divisorClass, polarizationClass]

/-! ### The Hodge index theorem in signature `(1, 2)` -/

/-- **Hodge definiteness on the two-point blow-up is exactly positivity of
`ω²`.**

This is the reverse Cauchy--Schwarz inequality for `diag(1, -1, -1)`: if
`ω² > 0` and `x ⊥ ω` with `x ≠ 0`, then `x² < 0`.  Unlike the rank-one models,
the definiteness clause here has content, because `ω^⊥` is a plane.

It is proved, not supplied.  That is what makes the support property of
`Stability/DivisorialSupport.lean` depend on Bogomolov--Gieseker alone on this
surface.
@isnad1 id=hodgedef.1h1v.s6.71123c936660 from=translated src=- shape=0771fce2 vocab=e223ff31
-/
theorem hodgeDefinite {w : Divisor} (hw : 0 < divisorSpace.pair w w) :
    divisorSpace.HodgeDefinite w where
  H_square_pos := hw
  neg_definite x hx hxne := by
    obtain ⟨p, q, r⟩ := w
    obtain ⟨x₁, x₂, x₃⟩ := x
    have hw' : 0 < p * p - q * q - r * r := hw
    have hx' : p * x₁ - q * x₂ - r * x₃ = 0 := hx
    show x₁ * x₁ - x₂ * x₂ - x₃ * x₃ < 0
    have hp2 : 0 < p * p := by nlinarith [mul_self_nonneg q, mul_self_nonneg r]
    by_cases hz : x₂ = 0 ∧ x₃ = 0
    · exfalso
      obtain ⟨h2, h3⟩ := hz
      subst h2
      subst h3
      have hp : p ≠ 0 := by
        intro h
        rw [h] at hp2
        simp at hp2
      have hx1 : x₁ = 0 := by
        have hpx : p * x₁ = 0 := by linarith
        exact (mul_eq_zero.mp hpx).resolve_left hp
      exact hxne (by simp [hx1])
    · have hpos : 0 < x₂ * x₂ + x₃ * x₃ := by
        rcases not_and_or.mp hz with h | h
        · have := mul_self_pos.mpr h
          nlinarith [mul_self_nonneg x₃]
        · have := mul_self_pos.mpr h
          nlinarith [mul_self_nonneg x₂]
      have he : p * x₁ = q * x₂ + r * x₃ := by linarith
      have hsq : (p * x₁) * (p * x₁) = (q * x₂ + r * x₃) * (q * x₂ + r * x₃) := by rw [he]
      have hcs : (q * x₂ + r * x₃) * (q * x₂ + r * x₃)
          ≤ (q * q + r * r) * (x₂ * x₂ + x₃ * x₃) := by
        nlinarith [mul_self_nonneg (q * x₃ - r * x₂)]
      nlinarith [hsq, hcs, hpos, hw', hp2]

/-- The realized anticanonical polarization has square `7`, so it is a Hodge
class in the sense above.
@isnad1 id=hodgedef.0h0v.s6.4956023cd634 from=translated src=- shape=2b19f338 vocab=db99f8b1
-/
theorem hodgeDefinite_antiCanonical :
    divisorSpace.HodgeDefinite
      (numericalRealization.realizePolarization antiCanonicalPolarization) := by
  apply hodgeDefinite
  rw [antiCanonicalPolarization, numericalRealization_polarization]
  norm_num

/-- **The real Mukai extension of the two-point blow-up has signature
`(2, 3)`.**

`hodgeDefinite` is exactly the input `hasSignatureTwo_of_hodgeDefinite` wants,
so every period-domain theorem — the negative definiteness on the orthogonal
complement of a positive plane, the wall-finiteness statements, the orientation
cocycle — is available here from `ω² > 0` alone.
@isnad1 id=hassigna.1h1v.s7.e131afa84a6b from=translated src=- shape=b71b4066 vocab=e19d65bc
-/
theorem hasSignatureTwo {w : Divisor} (hw : 0 < divisorSpace.pair w w) :
    PeriodDomain.HasSignatureTwo (Mukai.realForm divisorSpace.intersection) :=
  DivisorSpace.hasSignatureTwo_of_hodgeDefinite (hodgeDefinite hw)

/-! ### The support property, needing Bogomolov--Gieseker alone -/

/-- **On the two-point blow-up the support property reduces to
Bogomolov--Gieseker.**

`hasQuadraticSupportProperty_semistable` takes two supplied inputs.  Here the
Hodge input is discharged by `hodgeDefinite`, so the only hypothesis left is a
`BogomolovGiesekerData` and positivity of `ω²`.  That is the payoff of building
a model whose intersection form has signature `(1, 2)`.
@isnad1 id=hasquadr.2h4v.s9.7dff6b23b8ee from=translated src=- shape=ccac6b96 vocab=2d1eecd8
-/
theorem hasQuadraticSupportProperty
    (P : Polarization numericalVariety.ring)
    (B : BogomolovGiesekerData numericalVariety P)
    (Q : StabilityParameters Divisor) (hQ : 0 < divisorSpace.pair Q.omega Q.omega)
    {C : ℝ} (hC : 0 ≤ C) :
    Support.HasQuadraticSupportProperty
      (divisorSpace.realCentralCharge Q)
      (numericalRealization.chernCharacter.toRealExtension ''
        {E : NumericalClass | B.Semistable E}) :=
  numericalRealization.hasQuadraticSupportProperty_semistable P B Q (hodgeDefinite hQ) hC

/-- The same conclusion in the norm-bound formulation.
@isnad1 id=hassuppo.2h4v.s9.1c70f244434e from=translated src=- shape=ccac6b96 vocab=c94a9856
-/
theorem hasSupportProperty
    (P : Polarization numericalVariety.ring)
    (B : BogomolovGiesekerData numericalVariety P)
    (Q : StabilityParameters Divisor) (hQ : 0 < divisorSpace.pair Q.omega Q.omega)
    {C : ℝ} (hC : 0 ≤ C) :
    Support.HasSupportProperty
      (divisorSpace.realCentralCharge Q)
      (numericalRealization.chernCharacter.toRealExtension ''
        {E : NumericalClass | B.Semistable E}) :=
  numericalRealization.hasSupportProperty_semistable P B Q (hodgeDefinite hQ) hC

end

end AlgebraicGeometry.Numerical.Examples.BlowUpPlane
