/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Data.Complex.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Families of additive complex charges

This file owns the dimension- and geometry-independent charge-family root.  A
`ChargeFamily P N` is only a family of additive maps `N →+ ℂ`, indexed by an
arbitrary parameter type `P`.  It contains no heart, slicing, support property,
wall locus, Chern character, or scheme.

`reindex` changes parameters and `pullback` changes the additive class
presentation. `zeroLocus` names charge vanishing without calling it a wall.
Real-linear postcomposition and complex rescaling also belong here because they
act on charges before any wall or phase is considered.

The declarations keep their established `...Wall` namespace so the source
cutover preserves public names.  The path records the mathematical owner; wall
equations are downstream in `StabilityCondition/Walls/Alignment.lean`.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

universe u v w x

variable {P : Type u} {Q : Type v}
variable {N : Type w} {M : Type x}
variable [AddCommGroup N] [AddCommGroup M]

/-- A parameterized family of additive complex central charges.

This is numerical data only: it deliberately does not contain a heart, a
slicing, support-property data, or a topology on the parameter space.-/
structure ChargeFamily (P : Type u) (N : Type v) [AddCommGroup N] where
  /-- The central charge at a parameter value.-/
  charge : P → N →+ ℂ

namespace ChargeFamily

variable (Z : ChargeFamily P N)

/-- The parameters where the charge of one class vanishes. This is generally
two real equations, not a codimension-one numerical alignment wall.-/
def zeroLocus (v : N) : Set P := {p | Z.charge p v = 0}

/--
@isnad1 id=iff.0h5v.s6.c3f4c92f179d from=translated src=- shape=5ff073f0 vocab=6fefecfb
-/
@[simp]
theorem mem_zeroLocus (p : P) (v : N) :
    p ∈ Z.zeroLocus v ↔ Z.charge p v = 0 := Iff.rfl

/--
@isnad1 id=eq.1h4v.s5.fb1e45cf3397 from=translated src=- shape=930f960d vocab=3f58715f
-/
@[ext]
theorem ext {Z W : ChargeFamily P N}
    (h : ∀ p, Z.charge p = W.charge p) : Z = W := by
  cases Z
  cases W
  congr
  funext p
  exact h p

/-- Change the parameter space of a charge family.-/
def reindex (f : Q → P) : ChargeFamily Q N where
  charge q := Z.charge (f q)

/-- Pull a charge family back along an additive map of numerical class
carriers.-/
def pullback (f : M →+ N) : ChargeFamily P M where
  charge p := (Z.charge p).comp f

/--
@isnad1 id=eq.0h6v.s6.ea364479c985 from=translated src=- shape=4df320b0 vocab=c2e47958
-/
@[simp]
theorem reindex_charge (f : Q → P) (q : Q) :
    (Z.reindex f).charge q = Z.charge (f q) := rfl

/--
@isnad1 id=eq.0h7v.s7.ab49b50258eb from=translated src=- shape=10b4393e vocab=dd6fb7e9
-/
@[simp]
theorem pullback_charge (f : M →+ N) (p : P) (v : M) :
    (Z.pullback f).charge p v = Z.charge p (f v) := rfl

/-- Simultaneously changing parameters and pulling back classes evaluates by
composition in the two independent inputs.
@isnad1 id=eq.0h9v.s7.f7578688de11 from=translated src=- shape=e752b67a vocab=9418d5e2
-/
theorem reindex_pullback_charge (f : Q → P) (g : M →+ N) (q : Q) (v : M) :
    ((Z.reindex f).pullback g).charge q v = Z.charge (f q) (g v) := rfl

/-- Reindexing pulls a charge-zero locus back along the parameter map.
@isnad1 id=eq.0h6v.s5.1b1610fb1ea3 from=translated src=- shape=af5c8dda vocab=2fc45ae6
-/
theorem reindex_zeroLocus (f : Q → P) (v : N) :
    (Z.reindex f).zeroLocus v = f ⁻¹' Z.zeroLocus v := rfl

/-- Pullback of classes compares the corresponding charge-zero loci.
@isnad1 id=eq.0h6v.s6.9fbc3c372eb0 from=translated src=- shape=a01ecd4d vocab=7951421a
-/
theorem pullback_zeroLocus (f : M →+ N) (v : M) :
    (Z.pullback f).zeroLocus v = Z.zeroLocus (f v) := rfl

/--
@isnad1 id=eq.0h3v.s4.15b653a8cb8e from=translated src=- shape=ee26da8b vocab=9e912d11
-/
@[simp]
theorem reindex_id : Z.reindex id = Z := rfl

/--
@isnad1 id=eq.0h7v.s5.076a7780d77e from=translated src=- shape=6e08140f vocab=7b0b581e
-/
theorem reindex_reindex {R : Type*} (f : Q → P) (g : R → Q) :
    (Z.reindex f).reindex g = Z.reindex (f ∘ g) := rfl

/--
@isnad1 id=eq.0h3v.s5.a9acbda138ed from=translated src=- shape=bc515720 vocab=f35dbcb6
-/
@[simp]
theorem pullback_id : Z.pullback (AddMonoidHom.id N) = Z := rfl

/--
@isnad1 id=eq.0h7v.s7.e22e9c3bb3cf from=translated src=- shape=f7c1a8d8 vocab=808e4e60
-/
theorem pullback_pullback {L : Type*} [AddCommGroup L] (f : M →+ N) (g : L →+ M) :
    (Z.pullback f).pullback g = Z.pullback (f.comp g) := rfl

/-- Reindexing and pullback act on independent inputs, so they commute.
@isnad1 id=eq.0h7v.s6.dad99274c203 from=translated src=- shape=9abe0dfa vocab=1fed2248
-/
theorem pullback_reindex (f : Q → P) (g : M →+ N) :
    (Z.pullback g).reindex f = (Z.reindex f).pullback g := rfl

/-- The real part of the central charge of a class.-/
def re (p : P) (v : N) : ℝ := (Z.charge p v).re

/-- The imaginary part of the central charge of a class.-/
def im (p : P) (v : N) : ℝ := (Z.charge p v).im

/--
@isnad1 id=eq.0h4v.s5.a9a0100bc752 from=translated src=- shape=699c3c6d vocab=19375d87
-/
@[simp]
theorem re_zero (p : P) : Z.re p 0 = 0 := by simp [re]

/--
@isnad1 id=eq.0h4v.s5.e19a387907c3 from=translated src=- shape=699c3c6d vocab=9c84578d
-/
@[simp]
theorem im_zero (p : P) : Z.im p 0 = 0 := by simp [im]

/--
@isnad1 id=eq.0h6v.s6.199a30b72b65 from=translated src=- shape=928a0f6d vocab=1bbd82de
-/
@[simp]
theorem re_add (p : P) (v w : N) :
    Z.re p (v + w) = Z.re p v + Z.re p w := by simp [re]

/--
@isnad1 id=eq.0h6v.s6.2388f57651ce from=translated src=- shape=928a0f6d vocab=13cd000f
-/
@[simp]
theorem im_add (p : P) (v w : N) :
    Z.im p (v + w) = Z.im p v + Z.im p w := by simp [im]

/--
@isnad1 id=eq.0h5v.s5.3d6e2a19c987 from=translated src=- shape=4591d65d vocab=c69321f4
-/
@[simp]
theorem re_neg (p : P) (v : N) : Z.re p (-v) = -Z.re p v := by simp [re]

/--
@isnad1 id=eq.0h5v.s5.2b9ea939575e from=translated src=- shape=4591d65d vocab=6ab68f24
-/
@[simp]
theorem im_neg (p : P) (v : N) : Z.im p (-v) = -Z.im p v := by simp [im]

/--
@isnad1 id=eq.0h6v.s6.f5d9987bb600 from=translated src=- shape=20721e1c vocab=174f476d
-/
@[simp]
theorem re_zsmul (p : P) (n : ℤ) (v : N) :
    Z.re p (n • v) = n • Z.re p v := by simp [re]

/--
@isnad1 id=eq.0h6v.s6.c04fc4e088f5 from=translated src=- shape=20721e1c vocab=f18acab3
-/
@[simp]
theorem im_zsmul (p : P) (n : ℤ) (v : N) :
    Z.im p (n • v) = n • Z.im p v := by simp [im]

/-- The determinant of a real-linear endomorphism of `ℂ`, computed in the basis
`1, I`.-/
def realDet (g : ℂ →ₗ[ℝ] ℂ) : ℝ :=
  (g 1).re * (g Complex.I).im - (g 1).im * (g Complex.I).re

/-- A real-linear map of `ℂ` is determined by its values on `1` and `I`.
@isnad1 id=eq.0h2v.s9.55e42ec850c0 from=translated src=- shape=63894a4c vocab=c6b64de6
-/
theorem map_eq_smul_add_smul (g : ℂ →ₗ[ℝ] ℂ) (z : ℂ) :
    g z = z.re • g 1 + z.im • g Complex.I := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul]

/-- Post-compose every charge of a family with a real-linear map of `ℂ`.-/
def linearAct (g : ℂ →ₗ[ℝ] ℂ) : ChargeFamily P N where
  charge p := g.toAddMonoidHom.comp (Z.charge p)

/--
@isnad1 id=eq.0h6v.s8.2d2f7a3a7c30 from=translated src=- shape=b83f7a17 vocab=f5006930
-/
@[simp]
theorem linearAct_charge (g : ℂ →ₗ[ℝ] ℂ) (p : P) (v : N) :
    (Z.linearAct g).charge p v = g (Z.charge p v) := rfl

/-- Rescale every charge by a complex scalar.-/
def smul (c : ℂ) : ChargeFamily P N := Z.linearAct (LinearMap.mulLeft ℝ c)

/--
@isnad1 id=eq.0h6v.s7.ed8f6677f2ba from=translated src=- shape=1c634ff2 vocab=55b2ccb2
-/
@[simp]
theorem smul_charge (c : ℂ) (p : P) (v : N) :
    (Z.smul c).charge p v = c * Z.charge p v := rfl

/-- Multiplication by `c` has determinant `‖c‖²` as a real-linear map.
@isnad1 id=eq.0h1v.s6.2af0561d6c86 from=translated src=- shape=38ee9fea vocab=7260e8ce
-/
@[simp]
theorem realDet_mulLeft (c : ℂ) :
    realDet (LinearMap.mulLeft ℝ c) = Complex.normSq c := by
  simp only [realDet, LinearMap.mulLeft_apply, mul_one, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.normSq_apply]
  ring

end ChargeFamily

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
