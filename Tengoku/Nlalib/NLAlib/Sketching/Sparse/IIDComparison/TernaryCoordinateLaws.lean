/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.SparseStackLaw
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.FockModel.TernaryJacobi
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.MomentMethod.MomentParameters
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite iid sparse-coordinate laws

Literal ternary vector laws, support probability, and reciprocal support corrections.
Ported from `SparseFockFormal.SparseIIDCoupling` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

open scoped InnerProductSpace

namespace NLAlib.SparseSketch

noncomputable section

/-- The unscaled value of one iid coordinate `Y_a`.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def yValue : TernaryOutcome → ℝ
  | .neg => -1
  | .zero => 0
  | .pos => 1

/-- The nonzero outcome associated with a Rademacher sign.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def outcomeOfSign : Sign → TernaryOutcome
  | .plus => .pos
  | .minus => .neg

/-- Embedding a sign into the ternary outcomes retains its real signed value.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.636914eb05f6 from=translated src=- shape=7718e021 vocab=a0c79b18
-/
@[simp] theorem yValue_outcomeOfSign (e : Sign) :
    yValue (outcomeOfSign e) = e.val := by
  cases e <;> rfl

/-- Negation of a ternary atom.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def negateOutcome : TernaryOutcome → TernaryOutcome
  | .neg => .pos
  | .zero => .zero
  | .pos => .neg

/-- Negating a ternary outcome twice returns the original outcome.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.437cb7d80fdb from=translated src=- shape=47dcad53 vocab=51fe569d
-/
@[simp] theorem negateOutcome_involutive (z : TernaryOutcome) :
    negateOutcome (negateOutcome z) = z := by cases z <;> rfl

/-- Negating a ternary outcome negates its real coordinate value.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.596697b82f11 from=translated src=- shape=d2189a58 vocab=dc816263
-/
@[simp] theorem yValue_negateOutcome (z : TernaryOutcome) :
    yValue (negateOutcome z) = -yValue z := by cases z <;> norm_num [yValue, negateOutcome]

/-- Flip a Rademacher sign.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def flipSign : Sign → Sign
  | .plus => .minus
  | .minus => .plus

/-- Flipping a sign twice returns the original sign.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.c69632124d6c from=translated src=- shape=47dcad53 vocab=0336b6ac
-/
@[simp] theorem flipSign_involutive (e : Sign) : flipSign (flipSign e) = e := by
  cases e <;> rfl

/-- Embedding a flipped sign is the negation of the embedded original sign.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h1v.s3.0dfde068fd88 from=translated src=- shape=0ebce511 vocab=f7cac393
-/
@[simp] theorem outcomeOfSign_flipSign (e : Sign) :
    outcomeOfSign (flipSign e) = negateOutcome (outcomeOfSign e) := by
  cases e <;> rfl

/-- An iid vector `Y ∈ {-1,0,1}^b`.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
abbrev YVector (b : ℕ) := Fin b → TernaryOutcome

/-- The independent-coordinate law of `Y`.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def yVectorLaw (b : ℕ) (hb : 0 < b) : FiniteLaw (YVector b) :=
  FiniteLaw.independentProduct (fun _ : Fin b => ternaryLaw b hb)

/-- The iid vector-law weight is the product of its coordinate masses.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h2v.s5.2eda4ff71d9d from=translated src=- shape=c6c2df0f vocab=105be32b
-/
@[simp] theorem yVectorLaw_weight {b : ℕ} (hb : 0 < b) (y : YVector b) :
    (yVectorLaw b hb).weight y = ∏ a, mass b (y a) := rfl

/-- The all-zero iid vector.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def zeroY (b : ℕ) : YVector b := fun _ => .zero

/-- The finite nonzero support.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def support {b : ℕ} (y : YVector b) : Finset (Fin b) :=
  Finset.univ.filter fun a => y a ≠ .zero

/-- A coordinate belongs to iid support precisely when its outcome is nonzero.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=iff.0h3v.s5.f48d2dc6d799 from=translated src=- shape=934feca4 vocab=852d29b2
-/
@[simp] theorem mem_support {b : ℕ} (y : YVector b) (a : Fin b) :
    a ∈ support y ↔ y a ≠ .zero := by simp [support]

/-- Number of nonzero coordinates.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def supportSize {b : ℕ} (y : YVector b) : ℕ := (support y).card

/-- An iid vector has empty support precisely when it is the zero vector.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=iff.0h2v.s4.586d166505d9 from=translated src=- shape=7a8ab2f5 vocab=04a95945
-/
theorem supportSize_eq_zero_iff {b : ℕ} (y : YVector b) :
    supportSize y = 0 ↔ y = zeroY b := by
  constructor
  · intro h
    apply funext
    intro a
    have hempty : support y = ∅ := Finset.card_eq_zero.mp h
    have hnot : a ∉ support y := by simp [hempty]
    have : ¬y a ≠ .zero := by simpa [mem_support] using hnot
    simpa [zeroY] using not_ne_iff.mp this
  · rintro rfl
    simp [supportSize, support, zeroY]

/-- The zero-vector probability `p₀=(1-1/b)^b`.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def p0 (b : ℕ) : ℝ := (1 - 1 / (b : ℝ)) ^ b

/-- The zero iid vector has the defined zero-support probability.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.1h1v.s5.487161014874 from=translated src=- shape=4e25f016 vocab=4c497fbf
-/
theorem zeroY_weight {b : ℕ} (hb : 0 < b) :
    (yVectorLaw b hb).weight (zeroY b) = p0 b := by
  simp [yVectorLaw_weight, zeroY, mass, p0]

/-- The zero-support probability is nonnegative.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.1h1v.s4.a02c15ed2ee4 from=translated src=- shape=f8216502 vocab=85317059
-/
theorem p0_nonneg {b : ℕ} (hb : 0 < b) : 0 ≤ p0 b := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbase : (0 : ℝ) ≤ 1 - 1 / (b : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one (by positivity : (0 : ℝ) < b)).2 hbR
  exact pow_nonneg hbase _

/-- The zero-support probability is strictly below one at positive block size.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=lt.1h1v.s4.6901601b0ce9 from=translated src=- shape=01574b0e vocab=4f5d9b47
-/
theorem p0_lt_one {b : ℕ} (hb : 0 < b) : p0 b < 1 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hbase0 : (0 : ℝ) ≤ 1 - 1 / (b : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one hbR).2 (by exact_mod_cast hb)
  have hbase1 : (1 : ℝ) - 1 / (b : ℝ) < 1 := by
    have : (0 : ℝ) < 1 / (b : ℝ) := one_div_pos.mpr hbR
    linarith
  exact pow_lt_one₀ hbase0 hbase1 (Nat.ne_of_gt hb)

/-- The elementary exponential estimate omitted in the prose proof.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.1h1v.s4.b91d26e5f79a from=translated src=- shape=f3700b64 vocab=e176f855
-/
theorem p0_le_exp_neg_one {b : ℕ} (hb : 0 < b) :
    p0 b ≤ Real.exp (-1) := by
  have h1b : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  simpa [p0] using
    (Real.one_sub_div_pow_le_exp_neg (n := b) (t := (1 : ℝ)) h1b)

/-- The exact coupling rescaling `c_b=(1-p₀)⁻¹`.

Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def cB (b : ℕ) : ℝ := (1 - p0 b)⁻¹

/-- The nonempty-support probability is positive at positive block size.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=lt.1h1v.s5.3b2ff0555135 from=translated src=- shape=2b5ed7c5 vocab=63950089
-/
theorem one_sub_p0_pos {b : ℕ} (hb : 0 < b) : 0 < 1 - p0 b := by
  linarith [p0_lt_one hb]

/-- The reciprocal nonempty-support correction is at least one.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.1h1v.s4.2a94e12ccd01 from=translated src=- shape=f8216502 vocab=52abdafa
-/
theorem one_le_cB {b : ℕ} (hb : 0 < b) : 1 ≤ cB b := by
  rw [cB, one_le_inv₀ (one_sub_p0_pos hb)]
  linarith [p0_nonneg hb]

/-- The finite-block support correction is bounded by the universal support-gap constant.
Source: ported from `SparseFockFormal.SparseIIDCoupling`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.1h1v.s4.c23cb7264c89 from=translated src=- shape=d6dc4f2d vocab=b51a51b8
-/
theorem cB_le_cStar {b : ℕ} (hb : 0 < b) : cB b ≤ convexOrderConstant := by
  rw [cB, convexOrderConstant]
  apply inv_anti₀ expGap_pos
  linarith [p0_le_exp_neg_one hb]

end

end NLAlib.SparseSketch
