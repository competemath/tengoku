/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Tengoku

public import Tengoku.LeanPool.LeanPool.EcTateLean.FieldTheory.PerfectClosure
import Tengoku.LeanPool.LeanPool.EcTateLean.Algebra.Ring.Basic

/-!
# LeanPool.EcTateLean.Algebra.EllipticCurve.Model

Imported Lean Pool material for `LeanPool.EcTateLean.Algebra.EllipticCurve.Model`.
-/

@[expose] public section
-- import Aesop

-- TODO cleanup variables, sections assumption strength

--#print AddCommGroup.toDivisionCommMonoid -- TODO a way to tell if this works

/-- A model of a (possibly singular) elliptic curve is given
by `a` invariants $$a₁, a₂, a₃, a₄, a₆$$ which represent the curve
$$
y^2 + a₁ xy + a₃ y = x^ 3 + a₂ x ^ 2 + a₄ x + a₆
$$
-/
structure Model (R : Type u) [CommRing R] where
  /-- The `a₁` coefficient of the Weierstrass model. -/
  a1 : R
  /-- The `a₂` coefficient of the Weierstrass model. -/
  a2 : R
  /-- The `a₃` coefficient of the Weierstrass model. -/
  a3 : R
  /-- The `a₄` coefficient of the Weierstrass model. -/
  a4 : R
  /-- The `a₆` coefficient of the Weierstrass model. -/
  a6 : R
deriving Inhabited, DecidableEq

namespace Model
variable {R : Type u} [CommRing R]

instance [Repr R] : Repr (Model R) :=
  ⟨fun (e : Model R) _ => repr (e.a1, e.a2, e.a3, e.a4, e.a6)⟩

/-- The `b₂` invariant of a Weierstrass model. -/
def b2 (e : Model R) : R := e.a1 * e.a1 + 4 * e.a2

/-- The `b₄` invariant of a Weierstrass model. -/
def b4 (e : Model R) : R := e.a1 * e.a3 + 2 * e.a4

/-- The `b₆` invariant of a Weierstrass model. -/
def b6 (e : Model R) : R := e.a3 * e.a3 + 4 * e.a6

/-- The `b₈` invariant of a Weierstrass model. -/
def b8 (e : Model R) : R :=
  e.a1*e.a1*e.a6 - e.a1*e.a3*e.a4 + 4*e.a2*e.a6 + e.a2*e.a3*e.a3 - e.a4*e.a4

/-- The `b₅` invariant of a Weierstrass model (from Connell). -/
def b5 (e : Model R) : R := e.a1 * e.a4 - 2 * e.a2 * e.a3

/-- The `b₇` invariant of a Weierstrass model (from Connell). -/
def b7 (e : Model R) : R := e.a1 * (e.a3 ^ 2 - 12 * e.a6) + 8 * e.a3 * e.a4

/--
@isnad1 id=eq.0h2v.s6.0dbcee95a27f from=translated src=- shape=ac6e87fa vocab=4b0fa748
-/
lemma b8_identity (e : Model R) : 4*e.b8 = e.b2*e.b6 - e.b4 ^ 2 := by
  simp only [b2, b4, b6, b8]
  ring

/-- The `c₄` invariant of a Weierstrass model. -/
def c4 (e : Model R) : R := e.b2 ^ 2 - 24*e.b4

/-- The `c₆` invariant of a Weierstrass model. -/
def c6 (e : Model R) : R := -e.b2 ^ 3 + 36*e.b2*e.b4 - 216*e.b6

/-- The discriminant of a Weierstrass model. -/
def discr (e : Model R) : R :=
  -e.b2 * e.b2 * e.b8 - 8 * e.b4 ^ 3 - 27 * e.b6 * e.b6 + 9 * e.b2 * e.b4 * e.b6

/--
@isnad1 id=eq.0h2v.s6.01370c1ed1db from=translated src=- shape=b8eb398c vocab=76e84451
-/
lemma discr_identity (e : Model R) : 1728 * e.discr = e.c4 ^ 3 - e.c6 ^ 2 := by
  simp only [c4, c6, discr, mul_sub, mul_add]
  rw [(by ring : 1728 * (-e.b2 * e.b2 * e.b8) = -432 * e.b2 * e.b2 * (4 * e.b8))]
  rw [b8_identity]
  ring

-- TODO rename
/-- A change of coordinates `(u, r, s, t)` of a Weierstrass model, with `u` a
unit and `r`, `s`, `t` ring elements. -/
structure urstTransform (R : Type _) [Ring R] where
  /-- The scaling unit of the change of coordinates. -/
  u : Rˣ
  /-- The `x`-translation of the change of coordinates. -/
  r : R
  /-- The `xy`-shear of the change of coordinates. -/
  s : R
  /-- The `y`-translation of the change of coordinates. -/
  t : R

namespace urstTransform
instance instMulURSTTransform : Mul (urstTransform R) where
  mul f g := ⟨f.u * g.u, f.r + f.u * g.r, f.s + f.u * g.s, f.t + f.u * g.t⟩
/--
@isnad1 id=eq.0h3v.s8.00a9833363e9 from=translated src=- shape=c5edf64b vocab=0ae6affd
-/
lemma mul_def (f g : urstTransform R) :
  f * g = ⟨f.u * g.u, f.r + f.u * g.r, f.s + f.u * g.s, f.t + f.u * g.t⟩ := rfl
instance : One (urstTransform R) where
  one := ⟨1, 0, 0, 0⟩
/--
@isnad1 id=eq.0h1v.s6.e5783000b60a from=translated src=- shape=448fb1e2 vocab=8b0930da
-/
lemma one_def : (1 : urstTransform R) = ⟨1, 0, 0, 0⟩ := rfl

instance : Monoid (urstTransform R) where
  mul_one := by
    intros
    simp [urstTransform.mul_def, urstTransform.one_def]
  one_mul := by
    intros
    simp [urstTransform.mul_def, urstTransform.one_def]
  mul_assoc := by
    intros
    simp only [urstTransform.mul_def, mk.injEq]
    refine ⟨mul_assoc _ _ _, ?_, ?_, ?_⟩ <;> push_cast <;> ring
instance : Inv (urstTransform R) where
  inv f := ⟨f.u⁻¹, -f.u⁻¹ * f.r, -f.u⁻¹ * f.s, -f.u⁻¹ * f.t⟩
/--
@isnad1 id=eq.0h2v.s8.4d6d52db25dd from=translated src=- shape=5439a30a vocab=a2ae69be
-/
lemma inv_def (f : urstTransform R) :
  f⁻¹ = ⟨f.u⁻¹, -f.u⁻¹ * f.r, -f.u⁻¹ * f.s, -f.u⁻¹ * f.t⟩ := rfl

instance : Group (urstTransform R) where
  inv_mul_cancel := by
    intros
    simp [urstTransform.mul_def, urstTransform.one_def, urstTransform.inv_def]
  mul_one := by
    simp_all
  one_mul := by
    simp_all
  mul_assoc := by
    intros
    simp only [urstTransform.mul_def, mk.injEq]
    refine ⟨mul_assoc _ _ _, ?_, ?_, ?_⟩ <;> push_cast <;> ring

end urstTransform

-- TODO maybe define as a subgroup?
/-- The change-of-coordinates transformations with trivial scaling unit `u = 1`. -/
def rstTransform := {urst : urstTransform R // urst.u = 1}

--TODO instance Group
/-- The Weierstrass model obtained from `e` by the change of coordinates
`(1, r, s, t)`. -/
def rstIso (r s t : R) (e : Model R) : Model R :=
{ a1 := e.a1 + 2*s
  a2 := e.a2 - s*e.a1 + 3*r - s*s
  a3 := e.a3 + r*e.a1 + 2*t
  a4 := e.a4 - s*e.a3 + 2*r*e.a2 - (t+r*s)*e.a1 + 3*r*r - 2*s*t
  a6 := e.a6 + r*e.a4 + r*r*e.a2 + r*r*r - t*(e.a3 + t + r*e.a1) }

/--
@isnad1 id=eq.0h5v.s6.b435aca054a0 from=translated src=- shape=d79dc223 vocab=355f35cd
-/
lemma rst_b2 (r s t : R) (e : Model R) : (rstIso r s t e).b2 = e.b2 + 12*r := by
  simp [rstIso, b2]
  ring

/--
@isnad1 id=eq.0h5v.s6.5b41c11dd6b7 from=translated src=- shape=eb342149 vocab=3ec0fc58
-/
lemma rst_b4 (r s t : R) (e : Model R) :
  (rstIso r s t e).b4 = e.b4 + r * (e.b2 + 6 * r) := by
  simp only [rstIso, b2, b4]
  ring

/--
@isnad1 id=eq.0h5v.s7.e145743c56ee from=translated src=- shape=a59bd0ba vocab=5148b8e0
-/
lemma rst_b6 (r s t : R) (e : Model R) :
  (rstIso r s t e).b6 = e.b6 + 2*r*e.b4 + r*r*e.b2 + 4*r*r*r := by
  simp only [rstIso, b2, b4, b6]
  ring

/--
@isnad1 id=eq.0h5v.s8.8f802dd29906 from=translated src=- shape=1951f693 vocab=7afe6e5a
-/
lemma rst_b8 (r s t : R) (e : Model R) :
  (rstIso r s t e).b8 = e.b8 + 3*r*e.b6 + 3*r*r*e.b4 + r*r*r*e.b2 + 3*r*r*r*r := by
  simp only [rstIso, b2, b4, b6, b8]
  ring

/--
@isnad1 id=eq.0h5v.s4.6ba91cec6c8e from=translated src=- shape=954a5757 vocab=c88e68cb
-/
@[simp]
lemma rst_c4 (r s t : R) (e : Model R) :
  (rstIso r s t e).c4 = e.c4 := by
  simp only [rstIso, b2, b4, c4]
  ring

/--
@isnad1 id=eq.0h5v.s4.bfadc58300d4 from=translated src=- shape=954a5757 vocab=9a59d4a1
-/
@[simp]
lemma rst_c6 (r s t : R) (e : Model R) :
  (rstIso r s t e).c6 = e.c6 := by
  simp only [rstIso, b2, b4, b6, c6]
  ring

/--
@isnad1 id=eq.0h5v.s4.cdebde21ad5d from=translated src=- shape=954a5757 vocab=54daff71
-/
lemma rst_discr (r s t : R) (e : Model R) : (rstIso r s t e).discr = e.discr := by
  simp only [discr, rst_b2, rst_b4, rst_b6, rst_b8]
  simp only [mul_add]
  rw [(by ring :
    (-(b2 e + 12 * r) * b2 e + -(b2 e + 12 * r) * (12 * r)) * b8 e =
      -(b2 e ^ 2 * b8 e) + (- (3 * r) * b2 e + -(b2 e + 12 * r) * (3 * r)) * (4 * b8 e))]
  rw [b8_identity]
  ring

variable {S : Type u} [CommRing S] (f : R →+* S)

/-- Pushes a Weierstrass model forward along a ring homomorphism `f`. -/
@[simps]
def map : Model R → Model S := fun e => ⟨f e.a1, f e.a2, f e.a3, f e.a4, f e.a6⟩

/--
@isnad1 id=eq.0h4v.s6.91e2e6ff544a from=translated src=- shape=67e1482b vocab=331d7b1e
-/
@[simp] lemma map_b2 : (map f e).b2 = f e.b2 := by simp [Model.b2, map_ofNat]
/--
@isnad1 id=eq.0h4v.s6.86c089119686 from=translated src=- shape=67e1482b vocab=d43c2da1
-/
@[simp] lemma map_b4 : (map f e).b4 = f e.b4 := by simp [Model.b4, map_ofNat]
/--
@isnad1 id=eq.0h4v.s6.0b8d36c9d507 from=translated src=- shape=67e1482b vocab=9030c7a8
-/
@[simp] lemma map_b5 : (map f e).b5 = f e.b5 := by simp [Model.b5, map_ofNat]
/--
@isnad1 id=eq.0h4v.s6.6406922737fc from=translated src=- shape=67e1482b vocab=4d31db67
-/
@[simp] lemma map_b6 : (map f e).b6 = f e.b6 := by simp [Model.b6, map_ofNat]
/--
@isnad1 id=eq.0h4v.s6.d5fb83818987 from=translated src=- shape=67e1482b vocab=79266e63
-/
@[simp] lemma map_b7 : (map f e).b7 = f e.b7 := by simp [Model.b7, map_ofNat]
/--
@isnad1 id=eq.0h4v.s6.2083d5f03288 from=translated src=- shape=67e1482b vocab=e7d5fab4
-/
@[simp] lemma map_b8 : (map f e).b8 = f e.b8 := by simp [Model.b8, map_ofNat]

/--
@isnad1 id=eq.0h4v.s6.5999e3b5e458 from=translated src=- shape=67e1482b vocab=b673274d
-/
@[simp] lemma map_c4 : (map f e).c4 = f e.c4 := by simp [Model.c4, map_ofNat]
/--
@isnad1 id=eq.0h4v.s6.6c9e2cb801e8 from=translated src=- shape=67e1482b vocab=e3739ca7
-/
@[simp] lemma map_c6 : (map f e).c6 = f e.c6 := by simp [Model.c6, map_ofNat]

/--
@isnad1 id=eq.0h4v.s6.f46ccdba79cf from=translated src=- shape=67e1482b vocab=1834b236
-/
@[simp] lemma map_discr : (map f e).discr = f e.discr := by simp [Model.discr, map_ofNat]

/-- The Weierstrass polynomial of `e` evaluated at a point `P = (x, y)`, i.e.
the difference of the two sides of the Weierstrass equation. -/
def weierstrass (e : Model R) (P : R × R) : R :=
  P.2 ^ 2 + e.a1 * P.1 * P.2 + e.a3 * P.2 - (P.1 ^ 3 + e.a2 * P.1 ^ 2 + e.a4 * P.1 + e.a6)

--partial derivation library?

/-- The partial derivative of the Weierstrass polynomial with respect to `x`,
evaluated at `P`. -/
def dweierstrassDx (e : Model R) (P : R × R) : R :=
  e.a1 * P.2 - (3 * P.1 ^ 2 + 2 * e.a2 * P.1 + e.a4)

/-- The partial derivative of the Weierstrass polynomial with respect to `y`,
evaluated at `P`. -/
def dweierstrassDy (e : Model R) (P : R × R) : R :=
  2 * P.2 + e.a1 * P.1 + e.a3

/--
@isnad1 id=eq.0h5v.s7.19ea6d77ed9b from=translated src=- shape=f30d98ab vocab=af22c18f
-/
@[simp]
lemma weierstrass_map (e : Model R) (P : R × R) : weierstrass (e.map f) (P.map f f) =
  f (weierstrass e P) := by simp [weierstrass]

/--
@isnad1 id=eq.0h5v.s7.642e245b3794 from=translated src=- shape=f30d98ab vocab=215e3711
-/
@[simp]
lemma dweierstrassDx_map (e : Model R) (P : R × R) : dweierstrassDx (e.map f) (P.map f f) =
  f (dweierstrassDx e P) := by simp [dweierstrassDx, map_ofNat]

/--
@isnad1 id=eq.0h5v.s7.fae71e1b1978 from=translated src=- shape=f30d98ab vocab=85fa26ab
-/
@[simp]
lemma dweierstrassDy_map (e : Model R) (P : R × R) : dweierstrassDy (e.map f) (P.map f f) =
  f (dweierstrassDy e P) := by simp [dweierstrassDy, map_ofNat]

/--
The discriminant equals (minus) the standard order-`a6` generator of the elimination ideal
of the Weierstrass and partial-derivative polynomials. This identity (verified with
`Singular.jl`, part of `OSCAR`) is the negative of the `a6`-resultant polynomial below.
@isnad1 id=eq.0h2v.s11.d6f48acb7277 from=translated src=- shape=22eb3f5a vocab=e71927d2
-/
lemma discr_eq_neg_singular (e : Model R) : e.discr = -(
  e.a1^4*e.a2*e.a3^2 - e.a1^5*e.a3*e.a4 + e.a1^6*e.a6 + 8*e.a1^2*e.a2^2*e.a3^2 - e.a1^3*e.a3^3
    - 8*e.a1^3*e.a2*e.a3*e.a4 - e.a1^4*e.a4^2 + 12*e.a1^4*e.a2*e.a6 + 16*e.a2^3*e.a3^2
    - 36*e.a1*e.a2*e.a3^3 - 16*e.a1*e.a2^2*e.a3*e.a4 + 30*e.a1^2*e.a3^2*e.a4 - 8*e.a1^2*e.a2*e.a4^2
    + 48*e.a1^2*e.a2^2*e.a6 - 36*e.a1^3*e.a3*e.a6 + 27*e.a3^4 - 72*e.a2*e.a3^2*e.a4
    - 16*e.a2^2*e.a4^2 + 96*e.a1*e.a3*e.a4^2 + 64*e.a2^3*e.a6 - 144*e.a1*e.a2*e.a3*e.a6
    - 72*e.a1^2*e.a4*e.a6 + 64*e.a4^3 + 216*e.a3^2*e.a6 - 288*e.a2*e.a4*e.a6 + 432*e.a6^2) := by
  simp only [discr, b2, b4, b6, b8]
  ring

/--
@isnad1 id=eq.0h3v.s13.49295299d04c from=translated src=- shape=3afd0cd4 vocab=9b9a6b66
-/
lemma discr_in_jacobian_ideal (e : Model R) (P : R × R) : e.discr =
  -((48*P.1*P.2*e.a2^2 +24*e.a1*e.a2*e.a6 +216*P.2*e.a6 +P.2*e.a1^6 +11*P.2*e.a1^4*e.a2
      +P.1*e.a1^4*e.a3 +38*P.1*e.a1^2*e.a2*e.a3 +8*e.a1^2*e.a2^2*e.a3
  +e.a1^4*e.a2*e.a3 +40*P.2*e.a1^2*e.a2^2 +32*P.2*e.a2^3 +24*P.1*P.2*e.a1*e.a3 +30*P.1^2*e.a2*e.a3
      +3*P.1*e.a1^3*e.a4 +60*P.1^2*e.a1*e.a4 +30*P.1^2*e.a1^2*e.a3
  +31*e.a1^2*e.a3*e.a4 +144*P.2^2*e.a3 +198*P.2*e.a3^2 +27*e.a3^3 +60*e.a1*e.a4^2 +36*P.1*e.a1*e.a6
      +76*P.1*e.a2^2*e.a3 +16*e.a2^3*e.a3 +84*P.1*e.a1*e.a2*e.a4
  -(36*e.a3*e.a6 +P.1^2*e.a1^5 +P.1*e.a1^5*e.a2 +P.1*P.2*e.a1^4 +9*P.1^2*e.a1^3*e.a2
      +10*P.1*e.a1^3*e.a2^2 +e.a1^5*e.a4 +6*P.2^2*e.a1^3 +8*P.1*P.2*e.a1^2*e.a2
  +24*P.1^2*e.a1*e.a2^2 +32*P.1*e.a1*e.a2^3 +35*P.2*e.a1^3*e.a3 +e.a1^3*e.a3^2 +9*e.a1^3*e.a2*e.a4
      +48*P.2^2*e.a1*e.a2 +134*P.2*e.a1*e.a2*e.a3 +27*P.1*e.a1*e.a3^2 +36*e.a1*e.a2*e.a3^2
  +58*P.2*e.a1^2*e.a4 +24*e.a1*e.a2^2*e.a4 +144*P.1*P.2*e.a4 +120*P.2*e.a2*e.a4 +168*P.1*e.a3*e.a4
      +34*e.a2*e.a3*e.a4))*(dweierstrassDy e P)
  +(e.a1^2*e.a3^2 +12*e.a1^2*e.a6 +16*e.a2^2*e.a4 +32*P.1*e.a2^3 +e.a1^4*e.a4 +144*P.1*e.a6
      +48*e.a2*e.a6 +P.1*e.a1^4*e.a2 +84*P.1*e.a3^2 +56*P.2*e.a1*e.a4 +8*e.a1^2*e.a2*e.a4
      +28*P.2*e.a1^2*e.a3 +52*P.2*e.a2*e.a3
  +96*P.1*P.2*e.a3 +8*P.1*e.a1^2*e.a2^2 +38*e.a2*e.a3^2 +32*P.1^2*e.a2^2
  -(2*P.1*e.a1^3*e.a3 +112*P.1*e.a2*e.a4 +e.a1^3*e.a2*e.a3 +36*e.a1*e.a3*e.a4 +96*P.1^2*e.a4
      +32*P.1*P.2*e.a1*e.a2 +32*P.2*e.a1*e.a2^2 +64*e.a4^2
  +4*P.1*P.2*e.a1^3 +10*P.2*e.a1^3*e.a2 +P.2*e.a1^5 +8*e.a1*e.a2^2*e.a3
      +46*P.1*e.a1*e.a2*e.a3))*(dweierstrassDx e P)
  +(60*e.a1^2*e.a4 +288*P.1*e.a4 +240*e.a2*e.a4 +12*P.2*e.a1^3 +36*e.a1^3*e.a3 +96*P.2*e.a1*e.a2
      +168*e.a1*e.a2*e.a3
  -(432*e.a6 +e.a1^6 +288*P.2*e.a3 +252*e.a3^2 +12*e.a1^4*e.a2 +48*e.a1^2*e.a2^2 +96*P.1*e.a2^2
      +64*e.a2^3))*(weierstrass e P))
 := by
  rw [discr_eq_neg_singular]
  simp only [weierstrass, dweierstrassDx, dweierstrassDy]
  ring

/-- The change of variables on points induced by the change of coordinates
`(1, r, s, t)`. -/
def varChange (r s t : R) (P' : R × R) : R × R :=
  (P'.1 + r, P'.2 + s * P'.1 + t)

/--
@isnad1 id=eq.0h8v.s6.64424e7bf0d9 from=translated src=- shape=b443f9ed vocab=1adc2001
-/
@[simp]
lemma varChange_comp (r s t : R) (r' s' t' : R) (P : R × R) :
  varChange r s t (varChange r' s' t' P) = varChange (r + r') (s + s') (t + t' + s * r') P := by
  simp only [varChange, Prod.mk.injEq]
  apply And.intro <;> ring

/--
@isnad1 id=eq.0h2v.s5.1b4cc103baaf from=translated src=- shape=3a5593b2 vocab=581bfc5e
-/
@[simp]
lemma varChange_zero (P : R × R) : varChange (0 : R) 0 0 P = P := by simp [varChange]

-- TODO probably these proofs should be more conceptual

/--
@isnad1 id=eq.0h6v.s5.50af664a2769 from=translated src=- shape=997b310b vocab=83bbecae
-/
theorem weierstrass_iso_eq_varChange (e : Model R) (P : R × R) :
  weierstrass (rstIso r s t e) P = weierstrass e (varChange r s t P) := by
  simp only [weierstrass, rstIso, varChange]
  ring

/--
@isnad1 id=eq.0h6v.s6.32b1e7e7f7ed from=translated src=- shape=fe955f7d vocab=f740a54d
-/
theorem dweierstrassDx_iso_eq_varChange (e : Model R) (P : R × R) :
  dweierstrassDx (rstIso r s t e) P =
  dweierstrassDx e (varChange r s t P) + s * dweierstrassDy e (varChange r s t P) := by
  simp only [dweierstrassDx, dweierstrassDy, rstIso, varChange]
  ring

/--
@isnad1 id=eq.0h6v.s5.1d33fc9644fb from=translated src=- shape=997b310b vocab=02691290
-/
theorem dweierstrassDy_iso_eq_varChange (e : Model R) (P : R × R) :
  dweierstrassDy (rstIso r s t e) P = dweierstrassDy e (varChange r s t P) := by
  simp only [dweierstrassDy, rstIso, varChange]
  ring

/-- The change of coordinates `(1, r, s, t)` applied to `e`, with the triple
`rst = (r, s, t)` packaged as a single argument. -/
def rstTriple (e : Model R) (rst : R × R × R) : Model R :=
  rstIso rst.fst rst.snd.fst rst.snd.snd e

/--
@isnad1 id=eq.0h5v.s5.1cb9699d6ebf from=translated src=- shape=127843f8 vocab=fcbd0c50
-/
lemma rstIso_to_triple (e : Model R) (r s t : R) : rstIso r s t e = rstTriple e (r, s, t) := rfl

end Model

/-- A Weierstrass model with nonzero discriminant, i.e. a nonsingular elliptic
curve. -/
structure ValidModel (R : Type u) [CommRing R] extends Model R where
  /-- The discriminant of the underlying model is nonzero. -/
  discr_not_zero : toModel.discr ≠ 0

namespace ValidModel
variable {R : Type u} [CommRing R]
instance [Repr R] : Repr (ValidModel R) := ⟨fun (e : ValidModel R) _ => repr e.toModel⟩

/-- The valid model obtained from `e` by the change of coordinates `(1, r, s, t)`. -/
@[simps!]
def rstIso (r s t : R) (e : ValidModel R) : ValidModel R := {
  toModel := Model.rstIso r s t e.toModel,
  discr_not_zero := by
    rw [Model.rst_discr]
    exact e.discr_not_zero }

/--
@isnad1 id=eq.0h5v.s5.0ec61330d4c5 from=translated src=- shape=9f72a76d vocab=2ddc0c42
-/
@[simp]
lemma rst_discr_valid (r s t : R) (e : ValidModel R) : (rstIso r s t e).discr = e.discr :=
  Model.rst_discr r s t e.toModel

--more [simp] lemmas
/--
@isnad1 id=eq.0h4v.s5.cf891595b082 from=translated src=- shape=51c3c07e vocab=4139257e
-/
lemma rt_of_a1 (e : ValidModel R) (r t : R) : (rstIso r 0 t e).a1 = e.a1 :=
by simp only [rstIso, Model.rstIso, mul_zero, add_zero]

/--
@isnad1 id=eq.0h3v.s5.8c337b671ef5 from=translated src=- shape=e702372f vocab=4fe69579
-/
lemma t_of_a2 (e : ValidModel R) (t : R) : (rstIso 0 0 t e).a2 = e.a2 :=
by simp only [rstIso, Model.rstIso, zero_mul, sub_zero, mul_zero, add_zero]

/--
@isnad1 id=eq.0h3v.s6.1e6ed46a98e5 from=translated src=- shape=f1dc6d3c vocab=9b90fd80
-/
lemma r_of_a2 (e : ValidModel R) (r : R) : (rstIso r 0 0 e).a2 = e.a2 + 3 * r :=
by simp only [rstIso, Model.rstIso, zero_mul, sub_zero, mul_zero, add_zero]

/--
@isnad1 id=eq.0h3v.s6.46e5ee7e83ae from=translated src=- shape=a16df32a vocab=a4b87358
-/
lemma t_of_a3 (e : ValidModel R) (t : R) : (rstIso 0 0 t e).a3 = e.a3 + 2 * t :=
by simp only [rstIso, Model.rstIso, zero_mul, sub_zero, mul_zero, add_zero]

/--
@isnad1 id=eq.0h3v.s6.5d6644d28f31 from=translated src=- shape=c6bb7ed1 vocab=b36a55ea
-/
lemma r_of_a3 (e : ValidModel R) (r : R) : (rstIso r 0 0 e).a3 = e.a3 + r * e.a1 :=
by simp only [rstIso, Model.rstIso, zero_mul, sub_zero, mul_zero, add_zero]

/--
@isnad1 id=eq.0h3v.s6.2035a53dc5d2 from=translated src=- shape=72bb55fd vocab=2f8ad4ca
-/
lemma t_of_a4 (e : ValidModel R) (t : R) : (rstIso 0 0 t e).a4 = e.a4 - t * e.a1 :=
by simp only [rstIso, Model.rstIso, zero_mul, sub_zero, mul_zero, add_zero]

/--
@isnad1 id=eq.0h3v.s7.f1096a2b96aa from=translated src=- shape=85ccd9b0 vocab=555959d9
-/
lemma r_of_a4 (e : ValidModel R) (r : R) : (rstIso r 0 0 e).a4 = e.a4 + 2 * r * e.a2 + 3 * r ^ 2 :=
by simp only [rstIso, Model.rstIso, zero_mul,
  sub_zero, mul_zero, add_zero, mul_assoc, ←pow_two r]

/--
@isnad1 id=eq.0h3v.s7.7913338bb569 from=translated src=- shape=baa52b7f vocab=3d95dd04
-/
lemma t_of_a6 (e : ValidModel R) (t : R) : (rstIso 0 0 t e).a6 = e.a6 - t * e.a3 - t ^ 2 :=
by simp only [rstIso, Model.rstIso, zero_mul, mul_zero,
  add_zero, mul_add, ←pow_two t, sub_eq_add_neg, neg_add, ←add_assoc]

/--
@isnad1 id=eq.0h3v.s7.8a73677130c1 from=translated src=- shape=60649960 vocab=108c8815
-/
lemma r_of_a6 (e : ValidModel R) (r : R) :
  (rstIso r 0 0 e).a6 = e.a6 + r * e.a4 + r ^ 2 * e.a2 + r ^ 3 :=
by simp only [rstIso, Model.rstIso, zero_mul, sub_zero,
  mul_zero, add_zero, mul_assoc, pow_two r, pow_succ r]

/--
@isnad1 id=eq.0h4v.s6.406de4b54eff from=translated src=- shape=ec662a6f vocab=17a1dd92
-/
lemma st_of_a1 (e : ValidModel R) (s t : R) : (rstIso 0 s t e).a1 = e.a1 + 2 * s :=
by simp only [rstIso, Model.rstIso, mul_zero]

/--
@isnad1 id=eq.0h4v.s7.594c0552afed from=translated src=- shape=1c3005f7 vocab=fd581f6c
-/
lemma st_of_a2 (e : ValidModel R) (s t : R) : (rstIso 0 s t e).a2 = e.a2 - s * e.a1 - s ^ 2 :=
by simp only [rstIso, Model.rstIso, mul_zero, add_zero, mul_assoc, ←pow_two s]

/--
@isnad1 id=eq.0h4v.s6.497ffeeef5cc from=translated src=- shape=80862e54 vocab=a4b87358
-/
lemma st_of_a3 (e : ValidModel R) (s t : R) : (rstIso 0 s t e).a3 = e.a3 + 2 * t :=
by simp only [rstIso, Model.rstIso, mul_zero, add_zero, mul_assoc, zero_mul]

/--
@isnad1 id=eq.0h4v.s7.5ffcb99d110b from=translated src=- shape=1e19d706 vocab=e7aea16b
-/
lemma st_of_a4 (e : ValidModel R) (s t : R) :
  (rstIso 0 s t e).a4 = e.a4 - s * e.a3 - t * e.a1 - 2 * s * t :=
by simp only [rstIso, Model.rstIso, mul_zero, add_zero, mul_assoc, zero_mul]

/--
@isnad1 id=eq.0h4v.s7.49b11e7a448d from=translated src=- shape=a65eb211 vocab=3d95dd04
-/
lemma st_of_a6 (e : ValidModel R) (s t : R) : (rstIso 0 s t e).a6 = e.a6 - t * e.a3 - t ^ 2 :=
by simp only [rstIso, Model.rstIso, mul_zero,
  add_zero, mul_assoc, ←pow_two t, zero_mul, mul_add, sub_sub]

/--
@isnad1 id=eq.0h4v.s5.1191cf304b81 from=translated src=- shape=fdf4e943 vocab=ff8f49f5
-/
lemma st_of_b8 (e : ValidModel R) (s t : R) : (rstIso 0 s t e).b8 = e.b8 := by
  simp only [rstIso, Model.rst_b8, mul_zero, add_zero, zero_mul]

/-- The change of coordinates `(1, r, s, t)` applied to the valid model `e`, with
the triple `rst = (r, s, t)` packaged as a single argument. -/
def rstTriple (e : ValidModel R) (rst : R × R × R) : ValidModel R :=
  rstIso rst.fst rst.snd.fst rst.snd.snd e

/--
@isnad1 id=eq.0h5v.s5.296b9b400e2a from=translated src=- shape=127843f8 vocab=149a79a9
-/
lemma rstIso_to_triple (e : ValidModel R) (r s t : R) : rstIso r s t e = rstTriple e (r, s, t) :=
rfl

end ValidModel

namespace Model

variable {K : Type u} [CommRing K]

/-- A point `P` is a singular point of the model `e` when the Weierstrass
polynomial and both of its partial derivatives vanish at `P`. -/
def isSingularPoint (e : Model K) (P : K × K) : Prop :=
weierstrass e P = 0 ∧ dweierstrassDx e P = 0 ∧ dweierstrassDy e P = 0

/--
@isnad1 id=eq.1h3v.s5.eb247d5f0010 from=translated src=- shape=6279594d vocab=3a8f4a1d
-/
lemma discr_eq_zero_of_singular (e : Model K) {P} (h : isSingularPoint e P) :
  e.discr = 0 := by
  rcases h with ⟨h₁, h₂, h₃⟩
  rw [discr_in_jacobian_ideal, h₁, h₂, h₃, mul_zero,
    mul_zero, mul_zero, add_zero, add_zero, neg_eq_zero]

variable [IsDomain K]

/--
@isnad1 id=iff.1h2v.s6.1b687ac47eee from=translated src=- shape=1dcffa69 vocab=f47bd14f
-/
lemma c4_zero_iff_a1_zero_of_char_two (e : Model K) (h : ringChar K = 2) :
  e.c4 = 0 ↔ e.a1 = 0 := by
  have hchar' : (ringChar K : K) = 2 := by simp [h]
  have hchar'' : (2 : K) = 0 := by simp [← hchar']
  -- TODO use the nicer mod strategy from cubic roots here or a tactic
  rw [c4, b2, show (24 : K) = 2 * 12 by norm_num, show (4 : K) = 2 * 2 by norm_num,
    hchar'', ← pow_two]
  simp_all

/--
@isnad1 id=iff.1h2v.s6.48d27ba94430 from=translated src=- shape=1dcffa69 vocab=bb4b7a5c
-/
lemma c4_zero_iff_b2_zero_of_char_three (e : Model K) (h : ringChar K = 3) :
  e.c4 = 0 ↔ e.b2 = 0 := by
  have hchar' : (ringChar K : K) = 3 := by simp [h]
  have hchar'' : (3 : K) = 0 := by simp [← hchar']
  rw [c4, show (24 : K) = 3 * 8 by norm_num, hchar'']
  simp_all

-- TODO is this actually an iff
/--
@isnad1 id=eq.3h2v.s6.52eec09d967c from=translated src=- shape=741cbef8 vocab=68b958f8
-/
lemma a3_zero_of_a1_zero_of_disc_zero_of_char_two
  (e : Model K) (h : ringChar K = 2) (hdisc : e.discr = 0) (ha1 : e.a1 = 0) :
  e.a3 = 0 := by
  have hchar' : (ringChar K : K) = 2 := by simp [h]
  have hchar'' : (2 : K) = 0 := by simp [← hchar']
  rw [discr, b2, b4, b6, b8, ha1,
    show (8 : K) = 2 * 4 by norm_num, show (4 : K) = 2 * 2 by norm_num, show (27 : K) = 2 * 13
        + 1 by norm_num, hchar''] at hdisc
  simp_all

-- TODO is this actually an iff discr
/--
@isnad1 id=eq.3h2v.s6.fea6ed879e20 from=translated src=- shape=741cbef8 vocab=e4ec1224
-/
lemma b4_zero_of_b2_zero_of_disc_zero_of_char_three
  (e : Model K) (h : ringChar K = 3) (hdisc : e.discr = 0) (hb2 : e.b2 = 0) :
  e.b4 = 0 := by
  have hchar' : (ringChar K : K) = 3 := by simp [h]
  have hchar'' : (3 : K) = 0 := by simp [← hchar']
  rw [discr, hb2,
    show (27 : K) = 3 * 9 by norm_num,
    show (8 : K) = 3 * 3 - 1 by norm_num,
    hchar''] at hdisc
  simpa using hdisc

namespace Field
variable {K : Type u} [Field K]

open ECTate ECTate.PerfectRing

open Classical in
/--
Proposition 1.5.4 of Elliptic Curve Handbook, Ian Connell February, 1999,
https://www.math.rug.nl/~top/ian.pdf
-/
noncomputable
def singularPoint [PerfectRing K] (e : Model K) : K × K :=
  if e.c4 = 0 then
    match ringChar K with
    | 2 => (pthRoot e.a4, pthRoot (e.a2 * e.a4 + e.a6))
    | 3 => (pthRoot (-(e.a3 ^ 2) - e.a6), e.a1 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a3)
    | _ => (-e.b2 / 12, -(-e.a1 * e.b2 / 12 + e.a3) / 2)
  else
    ((18 * e.b6 - e.b2 * e.b4) / e.c4, (e.b2 * e.b5 + 3 * e.b7) / e.c4)

/--
@isnad1 id=eq.2h2v.s6.a9d992345475 from=translated src=- shape=444606fa vocab=18c215f1
-/
lemma ringChar_eq_of_Prime [Nat.AtLeastTwo n] (hn : @OfNat.ofNat K n _ = 0) (hnp : Nat.Prime n) :
  ringChar K = n := by
  rw [← Nat.cast_ofNat, ringChar.spec] at hn
  cases (Nat.dvd_prime hnp).mp hn with
  | inl h =>
    have hh := CharP.char_is_prime_or_zero K (ringChar K)
    rw [h] at hh
    exact absurd hh (by simp [Nat.not_prime_one])
  | inr h =>
    assumption

-- TODO a field should be a division comm monoid

-- TODO maybe rewrite to take an explicit point

/--
@isnad1 id=issingul.1h2v.s5.1335bab543b1 from=translated src=- shape=ac6ba6c4 vocab=a4bb34bc
-/
lemma isSingularPoint_singularPoint [PerfectRing K] (e : Model K) (h : e.discr = 0) :
  isSingularPoint e (singularPoint e) := by
  rw [singularPoint]
  split_ifs with hc4
  · have hc6 : c6 e = 0 := by
      simpa [h, hc4, pow_succ, mul_eq_zero] using discr_identity e
    split
    -- case _ hchar => TODO get this working, but its subtly different
    · rw [isSingularPoint]
      have hchar : ringChar K = 2 := by assumption
      have hchar' : (ringChar K : K) = 2 := by simp [hchar]
      have hchar'' : (2 : K) = 0 := by simp [← hchar']
      have hcharne : ringChar K ≠ 0 := by simp [hchar]
      have ha1 : e.a1 = 0 := by simpa [c4_zero_iff_a1_zero_of_char_two e hchar] using hc4
      have ha3 : e.a3 = 0 := a3_zero_of_a1_zero_of_disc_zero_of_char_two e hchar h ha1
      refine ⟨?_, ?_, ?_⟩
      · rw [weierstrass]
        simp only [ha1, ha3, zero_mul, add_zero]
        rw [show 3 = 2 + 1 by norm_num]
        rw [pow_succ _ 2]
        rw [← hchar, pthRoot_pow_char hcharne]
        rw [pthRoot_pow_char hcharne]
        ring_nf
        simp [hchar'']
      · rw [dweierstrassDx]
        simp only [ha1, zero_mul, hchar'', add_zero, zero_sub, neg_add_rev]
        rw [← hchar, pthRoot_pow_char hcharne, ← sub_eq_add_neg]
        simp only [sub_eq_iff_eq_add, zero_add]
        rw [show (3 : K) = 2 * 2 - 1 by norm_num]
        simp_all
      · simp [dweierstrassDy, ha1, ha3, hchar'']
    · rw [isSingularPoint]
      have hchar : ringChar K = 3 := by assumption
      have hcharne : ringChar K ≠ 0 := by simp [hchar]
      have hchar' : (ringChar K : K) = 3 := by simp [hchar]
      have hchar'' : (3 : K) = 0 := by simp [← hchar']
      have hb2 : e.b2 = 0 := by simpa [c4_zero_iff_b2_zero_of_char_three e hchar] using hc4
      have hb4 : e.b4 = 0 := b4_zero_of_b2_zero_of_disc_zero_of_char_three e hchar h hb2
      rw [b2] at hb2 -- TODO get versions that elim one b
      rw [b4] at hb4
      refine ⟨?_, ?_, ?_⟩
      · rw [weierstrass]
        rw [← hchar, pthRoot_pow_char hcharne]
        simp only
        rw [show
          (e.a1 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a3) ^ 2 +
          e.a1 * pthRoot (-(e.a3 ^ 2) - e.a6) * (e.a1 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a3) +
          e.a3 * (e.a1 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a3) -
          (-(e.a3 ^ 2) - e.a6 + e.a2 * pthRoot (-(e.a3 ^ 2) - e.a6) ^ 2
              + e.a4 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a6) =
          (2 * e.a1 ^ 2 - e.a2) * pthRoot (-(e.a3 ^ 2) - e.a6) ^ 2 +
          (4 * e.a1 * e.a3 - e.a4) * pthRoot (-(e.a3 ^ 2) - e.a6) +
          3 * e.a3 ^ 2
          by ring]
        have hfac2 : 2 * e.a1 ^ 2 - e.a2 = 0 := by
          linear_combination (norm := (ring_nf; simp [hchar''])) -hb2
        have hfac4 : 4 * e.a1 * e.a3 - e.a4 = 0 := by
          rw [show (2 : K) = -1 by rw [← add_zero (-1), ← hchar'']; norm_num] at hb4
          rw [show (4 : K) = 1 by rw [← add_zero 1, ← hchar'']; norm_num]
          simp only [neg_mul, one_mul] at hb4
          simp [sub_eq_add_neg, hb4]
        simp_all
      · rw [dweierstrassDx]
        rw [hchar'', zero_mul, zero_add]
        simp only
        rw [show e.a1 * (e.a1 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a3)
            - (2 * e.a2 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a4) =
                 (e.a1 * e.a1 - 2 * e.a2) * pthRoot (-(e.a3 ^ 2) - e.a6) + (e.a1 * e.a3 - e.a4)
          by ring]
        rw [show (2 : K) = -1 by rw [← add_zero (-1), ← hchar'']; norm_num] at hb4
        rw [show (4 : K) =
            -2 by rw [← add_zero (-2), ← zero_mul (2 : K), ← hchar'']; norm_num] at hb2
        simp only [neg_mul, one_mul, ← sub_eq_add_neg] at hb4 hb2
        rw [hb4, hb2, zero_mul, zero_add]
      · rw [dweierstrassDy]
        simp only
        rw [show 2 * (e.a1 * pthRoot (-(e.a3 ^ 2) - e.a6) + e.a3)
            + e.a1 * pthRoot (- (e.a3 ^ 2) - e.a6) + e.a3 = 3 * ((e.a1 * pthRoot (-(e.a3 ^ 2)
                - e.a6)) + e.a3) by ring]
        rw [hchar'', zero_mul]
    · rename_i hn2 hn3
      rw [isSingularPoint]
      -- have hb4 : e.b2 ^ 2 = 24 * e.b4 := sorry
      have h2 : (2 : K) ≠ 0 := fun hh => hn2 (ringChar_eq_of_Prime (n := 2) hh Nat.prime_two)
      have h3 : (3 : K) ≠ 0 := fun hh => hn3 (ringChar_eq_of_Prime (n := 3) hh Nat.prime_three)
      have h12 : (12 : K) ≠ 0 := by
        rw [show (12 : K) = 2 * 2 * 3 by norm_num]
        simp_all
      refine ⟨?_, ?_, ?_⟩
      · simp only [weierstrass]
        field_simp
        simp only [mul_zero]
        rw [← mul_zero (8 : K), ← hc6]
        simp only [c6, b2, b4, b6]
        ring
      · simp only [dweierstrassDx]
        field_simp
        simp only [mul_zero]
        rw [← mul_zero (6 : K), ← hc4]
        simp only [c4, b2, b4]
        ring
      · simp only [dweierstrassDy]
        field_simp
        ring
  · rw [isSingularPoint]
    refine ⟨?_, ?_, ?_⟩
    · simp only [weierstrass]
      field_simp
      simp only [mul_zero]
      rw [b5, b7, c4, b2, b4, b6]
      rw [← mul_zero (e.a1^6 + 12*e.a1^4*e.a2 + 48*e.a1^2*e.a2^2 - 36*e.a1^3*e.a3 + 64*e.a2^3
        - 144*e.a1*e.a2*e.a3 - 72*e.a1^2*e.a4 + 216*e.a3^2 - 288*e.a2*e.a4 + 864*e.a6),
        ← h, discr_eq_neg_singular]
      ring
    · simp only [dweierstrassDx]
      field_simp
      simp only [mul_zero]
      rw [b5, b7, c4, b2, b4, b6]
      rw [← mul_zero (36 : K), ← h, discr_eq_neg_singular]
      ring
    · simp only [dweierstrassDy]
      field_simp
      simp only [mul_zero]
      rw [b5, b7, c4, b2, b4, b6]
      ring

/--
Proposition 1.5.4 of Elliptic Curve Handbook, Ian Connell February, 1999,
https://www.math.rug.nl/~top/ian.pdf
-/
noncomputable
def moveSingularPointToOriginTriple [PerfectRing K] (e : Model K) : K × K × K :=
⟨(singularPoint e).1, 0, (singularPoint e).2⟩

/-- The model obtained from `e` by the change of coordinates that moves its
singular point to the origin. -/
noncomputable
def moveSingularPointToOriginIso [PerfectRing K] (e : Model K) : Model K :=
rstTriple e (moveSingularPointToOriginTriple e)

/--
@isnad1 id=issingul.1h5v.s6.41fc42708a3c from=translated src=- shape=56b04858 vocab=f499fd23
-/
lemma move_singularPoint (e : Model K) (r t : K) {P : K × K} (h : isSingularPoint e P) :
  isSingularPoint (rstIso r 0 t e) (varChange (-r) 0 (-t) P) := by
  rw [isSingularPoint, weierstrass_iso_eq_varChange,
    dweierstrassDx_iso_eq_varChange, zero_mul, add_zero,
    dweierstrassDy_iso_eq_varChange, varChange_comp]
  simpa

/--
@isnad1 id=issingul.1h2v.s6.a6ccc8c96b91 from=translated src=- shape=6cb20d61 vocab=98fa7376
-/
lemma move_singularPoint_to_origin [PerfectRing K] (e : Model K) (h : e.discr = 0) :
  isSingularPoint (moveSingularPointToOriginIso e) (0, 0) := by
  rw [moveSingularPointToOriginIso, rstTriple, moveSingularPointToOriginTriple]
  convert move_singularPoint e (singularPoint e).fst (singularPoint e).snd
    (isSingularPoint_singularPoint e h) using 2 <;> -- TODO convert does too much here
  simp [varChange]

/--
@isnad1 id=issingul.1h2v.s6.fd15a53e68a6 from=translated src=- shape=4b7a4eab vocab=f6cfb99b
-/
lemma move_singularPoint_to_origin' [PerfectRing K] (e : Model K) :
  (∃ P, isSingularPoint e P) →
    isSingularPoint (moveSingularPointToOriginIso e) (0, 0) := by
  rintro ⟨P, hP⟩
  exact move_singularPoint_to_origin e (discr_eq_zero_of_singular e hP)

end Field

end Model
