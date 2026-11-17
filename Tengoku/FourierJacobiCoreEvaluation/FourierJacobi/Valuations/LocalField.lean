import Tengoku.Seed.NumberTheory.LocalField.Basic
import Tengoku.Seed.Algebra.Order.GroupWithZero.Canonical
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A normalized extended integer valuation on the actual local field

The canonical value-group order isomorphism in mathlib is transported to an
additive valuation with values in `WithTop ℤ`. Its value at zero is infinity.
This connects general local fields to the `AddValuation` matrix bridge.
-/

noncomputable section
open scoped WithZero

namespace FourierJacobi.Valuations

/-- Negative logarithm with infinity at zero, unlike `WithZero.log`'s junk
value at zero.-/
def extendedNegLog (x : ℤᵐ⁰) : WithTop ℤ :=
  WithZero.expRecOn x ⊤ (fun n => ((-n : ℤ) : WithTop ℤ))

/--
@isnad1 id=eq.0h0v.s4.af17cb67448f from=translated src=- shape=ee3f1261 vocab=ff769618
-/
@[simp] theorem extendedNegLog_zero : extendedNegLog 0 = ⊤ := rfl
/--
@isnad1 id=eq.0h1v.s3.ffd1361db75a from=translated src=- shape=81c7590b vocab=7a78efbd
-/
@[simp] theorem extendedNegLog_exp (n : ℤ) :
    extendedNegLog (WithZero.exp n) = ((-n : ℤ) : WithTop ℤ) := rfl

/--
@isnad1 id=eq.0h0v.s5.ddab92cbef99 from=translated src=- shape=ebff1a2e vocab=0420d977
-/
@[simp] theorem extendedNegLog_one : extendedNegLog 1 = 0 := by
  change ((-(0 : ℤ) : ℤ) : WithTop ℤ) = 0
  simp only [neg_zero, WithTop.coe_zero]

/--
@isnad1 id=eq.0h2v.s5.330455ca1cc3 from=translated src=- shape=e7fba083 vocab=0b3f02e9
-/
theorem extendedNegLog_mul (x y : ℤᵐ⁰) :
    extendedNegLog (x * y) = extendedNegLog x + extendedNegLog y := by
  induction x using WithZero.expRecOn with
  | zero => simp
  | exp a =>
    induction y using WithZero.expRecOn with
    | zero => simp
    | exp b =>
      rw [← WithZero.exp_add]
      change ((-(a + b) : ℤ) : WithTop ℤ) = ((-a : ℤ) : WithTop ℤ) + ((-b : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_add]
      congr 1
      omega

/--
@isnad1 id=antitone.0h0v.s5.cee115a31c58 from=translated src=- shape=905eff27 vocab=b53f9d4e
-/
theorem extendedNegLog_antitone : Antitone extendedNegLog := by
  intro x y h
  induction x using WithZero.expRecOn with
  | zero => simp
  | exp a =>
    induction y using WithZero.expRecOn with
    | zero => simp at h
    | exp b =>
      change ((-b : ℤ) : WithTop ℤ) ≤ ((-a : ℤ) : WithTop ℤ)
      exact WithTop.coe_le_coe.mpr (neg_le_neg (WithZero.exp_le_exp.mp h))

/--
@isnad1 id=eq.0h2v.s5.870567cfb38b from=translated src=- shape=d2858b53 vocab=2f98ebc7
-/
theorem extendedNegLog_max (x y : ℤᵐ⁰) :
    extendedNegLog (max x y) = min (extendedNegLog x) (extendedNegLog y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, min_eq_right (extendedNegLog_antitone h)]
  · rw [max_eq_left h, min_eq_left (extendedNegLog_antitone h)]

/--
@isnad1 id=iff.0h1v.s6.cdb3ee32cf33 from=translated src=- shape=6134d49e vocab=ae28628f
-/
theorem extendedNegLog_nonnegative (x : ℤᵐ⁰) :
    0 ≤ extendedNegLog x ↔ x ≤ 1 := by
  induction x using WithZero.expRecOn with
  | zero => simp
  | exp n =>
    change ((0 : ℤ) : WithTop ℤ) ≤ ((-n : ℤ) : WithTop ℤ) ↔
      WithZero.exp n ≤ WithZero.exp (0 : ℤ)
    rw [WithTop.coe_le_coe, WithZero.exp_le_exp]
    omega

section LocalField
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The general local field's normalized multiplicative discrete valuation.-/
def discreteValuation : Valuation K ℤᵐ⁰ :=
  Valuation.congr (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
    (ValuativeRel.valuation K)

/--
@isnad1 id=surjecti.0h1v.s6.8d648f456d50 from=translated src=- shape=5592768f vocab=02f6735a
-/
theorem discreteValuation_surjective : Function.Surjective (discreteValuation K) :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).surjective.comp
    ValuativeRel.valuation_surjective

/-- The paper's extended additive convention on the actual field.-/
def localFieldValuation : AddValuation K (WithTop ℤ) :=
  AddValuation.of (fun x => extendedNegLog (discreteValuation K x))
    (by simp) (by simp)
    (fun x y => by
      rw [← extendedNegLog_max]
      exact extendedNegLog_antitone ((discreteValuation K).map_add x y))
    (fun x y => by rw [map_mul, extendedNegLog_mul])

/--
@isnad1 id=eq.0h1v.s6.4918d78d8733 from=translated src=- shape=6ad68462 vocab=b49ba6f0
-/
@[simp] theorem localFieldValuation_zero : localFieldValuation K 0 = ⊤ :=
  (localFieldValuation K).map_zero

/-- Finite additive valuations are obtained exactly at nonzero field elements.
@isnad1 id=iff.0h2v.s6.72e006c8af8d from=translated src=- shape=62e12c2c vocab=b49ba6f0
-/
theorem localFieldValuation_ne_top (x : K) :
    localFieldValuation K x ≠ ⊤ ↔ x ≠ 0 :=
  (localFieldValuation K).ne_top_iff

/--
@isnad1 id=surjecti.0h1v.s6.2aec99f73165 from=translated src=- shape=4df0d8e9 vocab=5dc2dd78
-/
theorem localFieldValuation_surjective : Function.Surjective (localFieldValuation K) := by
  intro n
  induction n using WithTop.recTopCoe with
  | top => exact ⟨0, localFieldValuation_zero K⟩
  | coe n =>
    obtain ⟨x, hx⟩ := discreteValuation_surjective K (WithZero.exp (-n))
    refine ⟨x, ?_⟩
    change extendedNegLog (discreteValuation K x) = (n : WithTop ℤ)
    rw [hx]
    change ((-(-n) : ℤ) : WithTop ℤ) = (n : WithTop ℤ)
    rw [neg_neg]

/-- The nonnegative valuation locus is the actual valuation ring.
@isnad1 id=iff.0h2v.s7.1eb503a6ec83 from=translated src=- shape=9e1b5a0d vocab=592e0c48
-/
theorem localFieldValuation_nonnegative_iff (x : K) :
    0 ≤ localFieldValuation K x ↔ x ∈ (ValuativeRel.valuation K).integer := by
  change 0 ≤ extendedNegLog (discreteValuation K x) ↔ ValuativeRel.valuation K x ≤ 1
  rw [extendedNegLog_nonnegative]
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
    (ValuativeRel.valuation K x) ≤ 1 ↔ _
  rw [← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)]
  exact map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)

end LocalField
end FourierJacobi.Valuations
