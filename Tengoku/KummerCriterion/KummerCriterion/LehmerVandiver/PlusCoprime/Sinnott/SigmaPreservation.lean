module

public import Tengoku.KummerCriterion.KummerCriterion.LehmerVandiver.PrimaryUnits.Part1
import Tengoku.KummerCriterion.KummerCriterion.TotallyRealSubfield.ZetaPrime
import Tengoku.Seed.Analysis.SpecialFunctions.Bernstein

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# σ-preservation of `cyclotomicUnitsSubgroup`

The complex-conjugation automorphism `σ = unitsComplexConj K` of
`(𝓞 K)ˣ` preserves the cyclotomic-units subgroup `C`. The key
algebraic identity is

 `σ(cyclotomicUnit p K k) = ζ^{p+1-k} · cyclotomicUnit p K k` in `𝓞 K`,

which exhibits `σ(cyclotomicUnit k)` as a torsion-times-generator
element of `C`.

This uses:
* The defining identity `(ζ-1) · cyclotomicUnit k = ζ^k - 1`.
* `σ(ζ) = ζ^{p-1}` (`complexConj_apply_zeta`).
* The fact that `ζ-1` is a non-zero divisor.

This is a key building block for **Step (E)** of the Sinnott / Cor 8.19
bridge construction.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension

namespace KummerCriterion

namespace LehmerVandiver

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

/-- **σ-conjugate of `(ζ - 1)`**: `σ(ζ - 1) = ζ^{p-1} - 1`.

Direct from `complexConj_apply_zeta`.
@isnad1 id=eq.0h2v.s9.b19492308251 from=translated src=- shape=74035c1d vocab=b2cc4c82
-/
theorem ringOfIntegersComplexConj_zeta_sub_one :
    ringOfIntegersComplexConj K (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) =
      ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ (p - 1) - 1 := by
  rw [map_sub, map_one]
  congr 1
  change ringOfIntegersComplexConj K (zeta_spec p ℚ K).toInteger =
    (zeta_spec p ℚ K).toInteger ^ (p - 1)
  exact complexConj_apply_zeta (p := p) (K := K)

/-- **σ-conjugate of `ζ^k - 1`**: `σ(ζ^k - 1) = ζ^{(p-1)·k} - 1 = (ζ^{p-1})^k - 1`.
@isnad1 id=eq.0h3v.s9.11b4500d9dfd from=translated src=- shape=ca9617e4 vocab=b2cc4c82
-/
theorem ringOfIntegersComplexConj_zeta_pow_sub_one (k : ℕ) :
    ringOfIntegersComplexConj K (((zeta_spec p ℚ K).unit' : 𝓞 K) ^ k - 1) =
      (((zeta_spec p ℚ K).unit' : 𝓞 K) ^ (p - 1)) ^ k - 1 := by
  rw [map_sub, map_one, map_pow]
  congr 2
  change ringOfIntegersComplexConj K (zeta_spec p ℚ K).toInteger =
    (zeta_spec p ℚ K).toInteger ^ (p - 1)
  exact complexConj_apply_zeta (p := p) (K := K)

omit [IsCMField K] in
/-- **Reduce `(p-1)·k` mod `p`**: `ζ^{(p-1)·k} = ζ^{p-k}` for `1 ≤ k ≤ p-1`.

Computation in `𝓞 K`: `(p-1)·k = pk - k`, and `ζ^{pk} = (ζ^p)^k = 1^k = 1`, so
`ζ^{(p-1)·k} = ζ^{pk}·ζ^{-k} = ζ^{-k} = ζ^{p-k}`.
@isnad1 id=eq.1h3v.s8.9a081732103a from=translated src=- shape=fa697669 vocab=8021608a
-/
theorem zeta_pow_pred_pow_eq (k : ℕ) (hk_le : k ≤ p) :
    (((zeta_spec p ℚ K).unit' : 𝓞 K) ^ (p - 1)) ^ k =
      ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ (p - k) := by
  have hp_pow : ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ p = 1 := by
    have := (zeta_spec p ℚ K).unit'_pow
    exact congrArg (fun u : (𝓞 K)ˣ => (u : 𝓞 K)) this
  have h1 : (((zeta_spec p ℚ K).unit' : 𝓞 K) ^ (p - 1)) ^ k *
      ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ k = 1 := by
    rw [← mul_pow, ← pow_succ, Nat.sub_add_cancel hp.out.one_le, hp_pow, one_pow]
  have h2 : ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ (p - k) *
      ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ k = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hk_le, hp_pow]
  have hzeta_unit : IsUnit (((zeta_spec p ℚ K).unit' : 𝓞 K) ^ k) :=
    ((zeta_spec p ℚ K).unit'.isUnit).pow k
  exact mul_right_cancel₀ hzeta_unit.ne_zero (h1.trans h2.symm)

/-- **σ-image of `cyclotomicUnit k`** (1 ≤ k ≤ p-1): the key identity

 `(ζ-1) · cyclotomicUnit(p-1) · σ(cyclotomicUnit k) = (ζ-1) · cyclotomicUnit(p-k)`.

Both sides equal `ζ^{p-k} - 1` after canceling `(ζ-1)`:
* LHS = `(ζ^{p-1}-1) · σ(cyclotomicUnit k)` [defining identity]
 = `σ((ζ-1) · cyclotomicUnit k)` [σ ring hom]
 = `σ(ζ^k - 1)` [defining identity]
 = `(ζ^{p-1})^k - 1 = ζ^{p-k} - 1` [reduction mod p].
* RHS = `(ζ-1) · cyclotomicUnit(p-k) = ζ^{p-k} - 1` [defining identity].
@isnad1 id=eq.1h3v.s9.22cd7bb0466c from=translated src=- shape=77694139 vocab=87f2cbf2
-/
theorem zeta_sub_one_mul_cyclotomicUnit_pred_mul_complexConj_cyclotomicUnit_eq
    (k : ℕ) (hk_le : k ≤ p) :
    (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) * cyclotomicUnit p K (p - 1) *
        ringOfIntegersComplexConj K (cyclotomicUnit p K k) =
      (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) * cyclotomicUnit p K (p - k) := by
  have hLHS : (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) * cyclotomicUnit p K (p - 1) *
      ringOfIntegersComplexConj K (cyclotomicUnit p K k) =
        (((zeta_spec p ℚ K).unit' : 𝓞 K) ^ (p - 1) - 1) *
          ringOfIntegersComplexConj K (cyclotomicUnit p K k) := by
    rw [zeta_sub_one_mul_cyclotomicUnit]
  rw [hLHS]
  rw [← ringOfIntegersComplexConj_zeta_sub_one (p := p) (K := K),
      ← map_mul, zeta_sub_one_mul_cyclotomicUnit,
      ringOfIntegersComplexConj_zeta_pow_sub_one,
      zeta_pow_pred_pow_eq (p := p) (K := K) k hk_le]
  rw [zeta_sub_one_mul_cyclotomicUnit]

/-- **σ-image clean form** (1 ≤ k ≤ p-1): cancelling `(ζ-1)`
key identity gives

 `cyclotomicUnit(p-1) · σ(cyclotomicUnit k) = cyclotomicUnit(p-k)`

in `𝓞 K`. This expresses `σ(cyclotomicUnit k)` as a quotient of two
cyclotomic units (both in `cyclotomicUnitsSubgroup`), establishing
σ-preservation of the subgroup.
@isnad1 id=eq.1h3v.s9.c43cba4ba77a from=translated src=- shape=09a72a69 vocab=1d3d7723
-/
theorem cyclotomicUnit_pred_mul_complexConj_cyclotomicUnit_eq
    (k : ℕ) (hk_le : k ≤ p) :
    cyclotomicUnit p K (p - 1) *
        ringOfIntegersComplexConj K (cyclotomicUnit p K k) =
      cyclotomicUnit p K (p - k) := by
  have hzeta_sub_one_ne_zero : (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) ≠ 0 :=
    (zeta_spec p ℚ K).zeta_sub_one_prime'.ne_zero
  have h_eq := zeta_sub_one_mul_cyclotomicUnit_pred_mul_complexConj_cyclotomicUnit_eq
    (p := p) (K := K) k hk_le
  have h_eq' : (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) *
      (cyclotomicUnit p K (p - 1) *
        ringOfIntegersComplexConj K (cyclotomicUnit p K k)) =
      (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) * cyclotomicUnit p K (p - k) := by
    rw [← mul_assoc]; exact h_eq
  exact mul_left_cancel₀ hzeta_sub_one_ne_zero h_eq'

end Sinnott

end LehmerVandiver

end KummerCriterion

end
