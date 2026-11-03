/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Family
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Alignment and signed-ray loci of parameterized charge families

`CentralCharge/Family.lean` owns `ChargeFamily`, reindexing, pullback and
postcomposition. This downstream file adds the determinant-alignment value and
separates its zero locus from the positive-ray condition used to read equal
phase.

For two classes `v,w`, their universal alignment equation is the determinant

`Re Z(v) Im Z(w) - Im Z(v) Re Z(w) = 0`.

The parameter type remains unconstrained. `positiveRayLocus` includes the
nonvanishing and positive-sign data that the determinant equation alone omits.
Actual destabilization still needs semistable objects and categorical
existence data; none is asserted here.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

open scoped ComplexConjugate

universe u v w x

variable {P : Type u} {Q : Type v}
variable {N : Type w} {M : Type x}
variable [AddCommGroup N] [AddCommGroup M]

namespace ChargeFamily

variable (Z : ChargeFamily P N)

/-- The universal numerical alignment expression for two classes.-/
def alignmentValue (p : P) (v w : N) : ℝ :=
  Z.re p v * Z.im p w - Z.im p v * Z.re p w

/-- The numerical alignment locus of two classes in the parameter space.

This is the determinant-zero locus where the two charges are
real-linearly dependent. It
is the whole parameter space when `w` is an integral multiple of `v`
(`alignmentLocus_self`, `alignmentLocus_add_zsmul_right`) and wherever `Z(v) = 0`.
It therefore does not by itself express equal phase or destabilization.-/
def alignmentLocus (v w : N) : Set P := {p | Z.alignmentValue p v w = 0}

/-- The locus where two nonzero charges lie on the same positive real ray.

The explicit nonvanishing and positive scalar are the hypotheses omitted by
the determinant alignment equation. This is the numerical equal-phase
adapter; it still carries no semistable objects and is not an actual wall.-/
def positiveRayLocus (v w : N) : Set P :=
  {p | Z.charge p v ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ Z.charge p w = (r : ℂ) * Z.charge p v}

/--
@isnad1 id=iff.0h6v.s5.252429495ab4 from=translated src=- shape=10d978ff vocab=390cce8a
-/
@[simp]
theorem mem_alignmentLocus (p : P) (v w : N) :
    p ∈ Z.alignmentLocus v w ↔ Z.alignmentValue p v w = 0 := Iff.rfl

/--
@isnad1 id=iff.0h6v.s7.7d3391a23cf5 from=translated src=- shape=8f293f51 vocab=5d5170ed
-/
theorem mem_positiveRayLocus (p : P) (v w : N) :
    p ∈ Z.positiveRayLocus v w ↔
      Z.charge p v ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ Z.charge p w = (r : ℂ) * Z.charge p v :=
  Iff.rfl

/-- Positive-ray alignment implies determinant alignment. The converse needs
the nonzero and sign conditions recorded by `positiveRayLocus`.
@isnad1 id=le.0h5v.s5.2cf52f687706 from=translated src=- shape=e5e50482 vocab=a19d5584
-/
theorem positiveRayLocus_subset_alignmentLocus (v w : N) :
    Z.positiveRayLocus v w ⊆ Z.alignmentLocus v w := by
  rintro p ⟨-, r, -, hr⟩
  rw [mem_alignmentLocus, alignmentValue]
  simp only [re, im]
  rw [hr]
  simp
  ring

/-- Charge-zero parameters are automatically in every alignment locus with
that class. This is exactly why alignment cannot by itself mean equal phase.
@isnad1 id=le.0h5v.s5.fd6611caddd5 from=translated src=- shape=66676535 vocab=5030e706
-/
theorem zeroLocus_subset_alignmentLocus_left (v w : N) :
    Z.zeroLocus v ⊆ Z.alignmentLocus v w := by
  intro p hp
  rw [mem_alignmentLocus, alignmentValue]
  have hz := (mem_zeroLocus Z p v).mp hp
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.zero_re, Complex.zero_im] at hre him
  simp only [re, im]
  rw [hre, him]
  ring

/-- The same containment for a zero charge in the second class.
@isnad1 id=le.0h5v.s5.0ee70ca17e64 from=translated src=- shape=0c63fa17 vocab=5030e706
-/
theorem zeroLocus_subset_alignmentLocus_right (v w : N) :
    Z.zeroLocus w ⊆ Z.alignmentLocus v w := by
  intro p hp
  rw [mem_alignmentLocus, alignmentValue]
  have hz := (mem_zeroLocus Z p w).mp hp
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [Complex.zero_re, Complex.zero_im] at hre him
  simp only [re, im]
  rw [hre, him]
  ring

/-- The determinant alignment expression is the negative imaginary part of
`Z(v) * conj (Z(w))`.
@isnad1 id=eq.0h6v.s7.9e0e48401f6a from=translated src=- shape=663d1f94 vocab=bc805045
-/
theorem alignmentValue_eq_neg_im_mul_conj (p : P) (v w : N) :
    Z.alignmentValue p v w =
      -((Z.charge p v) * conj (Z.charge p w)).im := by
  simp only [alignmentValue, re, im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/--
@isnad1 id=eq.0h5v.s5.862904073981 from=translated src=- shape=84b3ebae vocab=a8375535
-/
@[simp]
theorem alignmentValue_self (p : P) (v : N) : Z.alignmentValue p v v = 0 := by
  simp only [alignmentValue]
  ring

/--
@isnad1 id=eq.0h4v.s4.b45cdade043e from=translated src=- shape=b3528197 vocab=b490b9d9
-/
@[simp]
theorem alignmentLocus_self (v : N) : Z.alignmentLocus v v = Set.univ := by
  ext p
  simp

/--
@isnad1 id=eq.0h6v.s5.b27ca09773da from=translated src=- shape=f7e05cad vocab=db5fcfa2
-/
theorem alignmentValue_swap (p : P) (v w : N) :
    Z.alignmentValue p w v = -Z.alignmentValue p v w := by
  simp only [alignmentValue]
  ring

/--
@isnad1 id=eq.0h5v.s5.dda0a95315d4 from=translated src=- shape=f8115afd vocab=f7bcc48a
-/
theorem alignmentLocus_swap (v w : N) : Z.alignmentLocus w v = Z.alignmentLocus v w := by
  ext p
  change Z.alignmentValue p w v = 0 ↔ Z.alignmentValue p v w = 0
  rw [alignmentValue_swap, neg_eq_zero]

/--
@isnad1 id=eq.0h5v.s5.dc8fe06bf4dd from=translated src=- shape=0fdf090c vocab=a8375535
-/
@[simp]
theorem alignmentValue_zero_left (p : P) (w : N) : Z.alignmentValue p 0 w = 0 := by
  simp [alignmentValue]

/--
@isnad1 id=eq.0h5v.s5.ceff25e4065c from=translated src=- shape=4fd89c20 vocab=a8375535
-/
@[simp]
theorem alignmentValue_zero_right (p : P) (v : N) : Z.alignmentValue p v 0 = 0 := by
  simp [alignmentValue]

/--
@isnad1 id=eq.0h7v.s6.59adb4b7f339 from=translated src=- shape=57aac9f9 vocab=6ee815b2
-/
theorem alignmentValue_add_left (p : P) (v₁ v₂ w : N) :
    Z.alignmentValue p (v₁ + v₂) w =
      Z.alignmentValue p v₁ w + Z.alignmentValue p v₂ w := by
  simp only [alignmentValue, re_add, im_add]
  ring

/--
@isnad1 id=eq.0h7v.s6.a19d57e1239b from=translated src=- shape=f01500b8 vocab=6ee815b2
-/
theorem alignmentValue_add_right (p : P) (v w₁ w₂ : N) :
    Z.alignmentValue p v (w₁ + w₂) =
      Z.alignmentValue p v w₁ + Z.alignmentValue p v w₂ := by
  simp only [alignmentValue, re_add, im_add]
  ring

/--
@isnad1 id=eq.0h6v.s5.60b2fba5eb75 from=translated src=- shape=db82e505 vocab=db5fcfa2
-/
theorem alignmentValue_neg_left (p : P) (v w : N) :
    Z.alignmentValue p (-v) w = -Z.alignmentValue p v w := by
  simp only [alignmentValue, re_neg, im_neg]
  ring

/--
@isnad1 id=eq.0h6v.s5.488a8e709baa from=translated src=- shape=1ddff32d vocab=db5fcfa2
-/
theorem alignmentValue_neg_right (p : P) (v w : N) :
    Z.alignmentValue p v (-w) = -Z.alignmentValue p v w := by
  simp only [alignmentValue, re_neg, im_neg]
  ring

/--
@isnad1 id=eq.0h6v.s5.3a491eaa202e from=translated src=- shape=15ee7d3d vocab=2bd8084e
-/
@[simp]
theorem alignmentValue_zsmul_right (p : P) (n : ℤ) (v : N) :
    Z.alignmentValue p v (n • v) = 0 := by
  simp only [alignmentValue, re_zsmul, im_zsmul]
  ring

/-- An alignment locus depends on the competitor only modulo integral multiples of the
reference class.
@isnad1 id=eq.0h7v.s6.6148ccb84ed3 from=translated src=- shape=45862f62 vocab=1f44d38e
-/
theorem alignmentValue_add_zsmul_right (p : P) (n : ℤ) (v w : N) :
    Z.alignmentValue p v (w + n • v) = Z.alignmentValue p v w := by
  rw [alignmentValue_add_right, alignmentValue_zsmul_right, add_zero]

/--
@isnad1 id=eq.0h6v.s6.578e64267da7 from=translated src=- shape=b3e1bd50 vocab=4dd833ed
-/
theorem alignmentLocus_add_zsmul_right (n : ℤ) (v w : N) :
    Z.alignmentLocus v (w + n • v) = Z.alignmentLocus v w := by
  ext p
  simp only [mem_alignmentLocus, alignmentValue_add_zsmul_right]

/-- Compatibility version for a nonnegative integral multiple.
@isnad1 id=eq.0h7v.s6.77b23d0e1d59 from=translated src=- shape=45862f62 vocab=6f7a282a
-/
theorem alignmentValue_add_nsmul_right (p : P) (n : ℕ) (v w : N) :
    Z.alignmentValue p v (w + n • v) = Z.alignmentValue p v w := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, ← add_assoc, alignmentValue_add_right, ih, alignmentValue_self, add_zero]

/-- **The determinant law.**  `alignmentValue` is the determinant of the `2 × 2`
matrix of real and imaginary parts of the two charges, so post-composing with a
real-linear map multiplies it by that map's determinant.
@isnad1 id=eq.0h7v.s6.02cbb6abc1d0 from=translated src=- shape=0f954b51 vocab=d2e941fb
-/
theorem alignmentValue_linearAct (g : ℂ →ₗ[ℝ] ℂ) (p : P) (v w : N) :
    (Z.linearAct g).alignmentValue p v w = realDet g * Z.alignmentValue p v w := by
  simp only [alignmentValue, re, im, linearAct_charge, realDet]
  rw [map_eq_smul_add_smul g (Z.charge p v), map_eq_smul_add_smul g (Z.charge p w)]
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero]
  ring

/-- An invertible real-linear change of charge leaves every numerical alignment locus
where it was.
@isnad1 id=eq.1h6v.s6.ad04a1977dfc from=translated src=- shape=bb53c5e0 vocab=d67b4746
-/
theorem alignmentLocus_linearAct {g : ℂ →ₗ[ℝ] ℂ} (hg : realDet g ≠ 0) (v w : N) :
    (Z.linearAct g).alignmentLocus v w = Z.alignmentLocus v w := by
  ext p
  simp only [mem_alignmentLocus, alignmentValue_linearAct, mul_eq_zero]
  exact or_iff_right hg

/-- Rescaling the charges by `c` scales every alignment expression by `‖c‖²`.
@isnad1 id=eq.0h7v.s6.334c433b040f from=translated src=- shape=a0b2f337 vocab=6e598197
-/
theorem alignmentValue_smul (c : ℂ) (p : P) (v w : N) :
    (Z.smul c).alignmentValue p v w = Complex.normSq c * Z.alignmentValue p v w := by
  rw [smul, alignmentValue_linearAct, realDet_mulLeft]

/-- **Numerical walls are invariant under rescaling the central charge.**
@isnad1 id=eq.1h6v.s5.18c4cdc583f7 from=translated src=- shape=0ac2e774 vocab=1f220b25
-/
theorem alignmentLocus_smul {c : ℂ} (hc : c ≠ 0) (v w : N) :
    (Z.smul c).alignmentLocus v w = Z.alignmentLocus v w :=
  Z.alignmentLocus_linearAct (by
    rw [realDet_mulLeft]
    exact fun h => hc (Complex.normSq_eq_zero.mp h)) v w

/-- Reindexing a charge family pulls its alignment locus back as a set.
@isnad1 id=eq.0h7v.s5.78a156d1a795 from=translated src=- shape=0be30fc8 vocab=db58343b
-/
theorem reindex_alignmentLocus (f : Q → P) (v w : N) :
    (Z.reindex f).alignmentLocus v w = f ⁻¹' Z.alignmentLocus v w := rfl

/-- Pullback of numerical classes preserves the alignment expression.
@isnad1 id=eq.0h8v.s7.ca431e949b66 from=translated src=- shape=59fdcafb vocab=b3b0bad7
-/
@[simp]
theorem pullback_alignmentValue (f : M →+ N) (p : P) (v w : M) :
    (Z.pullback f).alignmentValue p v w = Z.alignmentValue p (f v) (f w) := rfl

/-- Pullback of numerical classes identifies the corresponding alignment loci.
@isnad1 id=eq.0h7v.s7.12ea5b3ac6f1 from=translated src=- shape=6c0a88f0 vocab=2f8bae50
-/
theorem pullback_alignmentLocus (f : M →+ N) (v w : M) :
    (Z.pullback f).alignmentLocus v w = Z.alignmentLocus (f v) (f w) := rfl

end ChargeFamily

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
