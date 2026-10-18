/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.RingTheory.FormalGroup.Basic
import Tengoku.Seed.RingTheory.PowerSeries.Substitution
import Tengoku.Seed.RingTheory.PowerSeries.Order

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Multiplication-by-`n` on a formal group

Let `F` be a one-dimensional formal group law over a commutative ring `R`, with group operation
`z₁ ⊕ z₂ = F(z₁, z₂)` on power series of zero constant coefficient.  This file constructs the
**multiplication-by-`n` power series** `[n](z)` (`n : ℕ`), the one-variable series representing the
map `z ↦ n • z`, defined by iterating the formal group addition:
`[0](z) = 0`, `[n+1](z) = F([n](z), z)`.

We prove:
* `constantCoeff ([n]) = 0` and the linear coefficient `coeff 1 ([n]) = (n : R)`
  (so `[n](z) = n·z + O(z²)`);
* when `(n : R)` is a unit, `[n]` has a two-sided compositional (substitution) inverse — the map
  `z ↦ [n](z)` is bijective on series of zero constant coefficient.

This is the invertibility input consumed by the group `Ê(𝔪)` of a formal group over a complete
local ring (Silverman AEC IV.3, VII.2.2): for `m` prime to the residue characteristic `p`, `(m : A)`
is a unit in the DVR `A`, so `[m]` is compositionally invertible, hence `[m] : Ê(𝔪) → Ê(𝔪)` is
bijective and `Ê(𝔪)` is uniquely `m`-divisible (no nontrivial prime-to-`p` torsion).  Only positive
`m` is needed there, so this ℕ-indexed series suffices.

⚠️ **The `ℤ`-extension has landed, and it did not need the hypothesis this file used to price it
against.**  This paragraph used to end *"; the extension to `m : ℤ` (via the additive inverse
series) is handled once the `AddCommGroup` structure on `FormalGroup.Point` is available."*  It is
`EllipticCurves.FormalGroup.MulByZ`, which has this file in its `EllipticCurves`-import closure:
`FormalGroup.mulByZ : ℤ → PowerSeries R` with `[-m](z) := i([m](z))` for `i = F.formalInv` — the
additive inverse series named above — together with `FormalGroup.zsmul_val_eq_mulByZ_subst` and
`FormalGroup.zsmul_eq_zero_iff_mulByZ_subst`.

⚠️ And the named precondition was **stronger than what the extension used**, which is the part worth
keeping: `AddCommGroup (F.Point σ)` carries `[F.IsComm]`, whereas `AddGroup (F.Point σ)` — which is
what `mulByZ` consumes, for its `zsmul` — is unconditional.  `MulByZ`'s own header says so.  So the
ℕ-indexing here was never a commutativity restriction, and this file's `EllipticCurves`-import
closure stays **0**: the pointer above is prose, not an import.

The compositional inverse is Mathlib's `PowerSeries.substInvOfIsUnit`, which needs exactly
`constantCoeff P = 0` and `IsUnit (P.coeff 1)`.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.2, IV.3, VII.2.
-/

open MvPowerSeries Finsupp

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

/-- Formal-group addition of two one-variable power series `a`, `b` (of zero constant coefficient):
`a ⊕ b = F(a, b)`, via substitution of `a`, `b` into the two-variable law `F`. -/
noncomputable def fgAdd (a b : PowerSeries R) : PowerSeries R :=
  F.toPowerSeries.subst ![a, b]

/-- `![a, b]` has the substitution admissibility needed to substitute into `F`, provided `a` and `b`
have zero constant coefficient. -/
theorem hasSubst_cons {a b : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0)
    (hb : PowerSeries.constantCoeff b = 0) :
    MvPowerSeries.HasSubst ![a, b] := by
  have ha' : MvPowerSeries.constantCoeff a = 0 := ha
  have hb' : MvPowerSeries.constantCoeff b = 0 := hb
  refine hasSubst_of_constantCoeff_nilpotent fun s => ?_
  fin_cases s <;> simp [ha', hb']

/-- The formal-group sum of two series of zero constant coefficient again has zero constant
coefficient. -/
@[simp]
theorem constantCoeff_fgAdd {a b : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0)
    (hb : PowerSeries.constantCoeff b = 0) :
    PowerSeries.constantCoeff (F.fgAdd a b) = 0 := by
  -- `F(a,b)` has zero constant coefficient because `F` does and `a`, `b` do.
  have ha' : MvPowerSeries.constantCoeff a = 0 := ha
  have hb' : MvPowerSeries.constantCoeff b = 0 := hb
  refine MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_cons ha hb) (fun s => ?_)
    F.zero_constantCoeff
  fin_cases s <;> simp [ha', hb']

/-- If `a`, `b` have zero constant term and `2 ≤ m + k`, then the degree-1 coefficient of
`a ^ m * b ^ k` vanishes: the product is divisible by `X²` (since `X ∣ a` and `X ∣ b`). -/
theorem coeff_one_pow_mul_pow {a b : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0)
    (hb : PowerSeries.constantCoeff b = 0) {m k : ℕ} (h : 2 ≤ m + k) :
    PowerSeries.coeff 1 (a ^ m * b ^ k) = 0 := by
  have hdvd : (PowerSeries.X : PowerSeries R) ^ 2 ∣ a ^ m * b ^ k := by
    refine dvd_trans (pow_dvd_pow _ h) ?_
    rw [pow_add]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr ha) m)
      (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr hb) k)
  exact PowerSeries.X_pow_dvd_iff.mp hdvd 1 (by norm_num)

/-- **Linear coefficient of the formal-group sum.**  Because `F(X, Y) = X + Y + (deg ≥ 2)` and
`a`, `b` have order `≥ 1`, only the linear terms `X` and `Y` of `F` (coefficients `1`, by
`lin_coeff_X`/`lin_coeff_Y`) contribute to the degree-1 coefficient of `F(a, b)`; the degree `≥ 2`
monomials of `F` produce order `≥ 2` when `a`, `b` are substituted. -/
theorem coeff_one_fgAdd {a b : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0)
    (hb : PowerSeries.constantCoeff b = 0) :
    PowerSeries.coeff (R := R) 1 (F.fgAdd a b) =
      PowerSeries.coeff (R := R) 1 a + PowerSeries.coeff (R := R) 1 b := by
  -- Strategy: `MvPowerSeries.coeff_subst` writes the coefficient as a `finsum` over exponent
  -- vectors `d : Fin 2 →₀ ℕ` of `(coeff d F) • coeff₁ (a ^ d 0 * b ^ d 1)`.  The summand vanishes
  -- unless `d 0 + d 1 = 1` (for `d = 0` the product is `1`, coeff₁ = 0; for `d 0 + d 1 ≥ 2` the
  -- product `a^(d 0) b^(d 1)` is divisible by `X²` since `X ∣ a`, `X ∣ b`, so coeff₁ = 0).  The two
  -- surviving terms are `d = single 0 1` (giving `lin_coeff_X • coeff₁ a = coeff₁ a`) and
  -- `d = single 1 1` (giving `lin_coeff_Y • coeff₁ b = coeff₁ b`).
  classical
  -- The `d.prod` factor simplifies to `a ^ d 0 * b ^ d 1`.
  have hprod : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => ![a, b] s ^ e) = a ^ d 0 * b ^ d 1 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp
  -- `single 0 1 ≠ single 1 1`.
  have hne_single : (single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ single 1 1 := by
    intro h
    have := DFunLike.congr_fun h 0
    simp at this
  -- The summand has support contained in `{single 0 1, single 1 1}`.
  have hsupp : Function.support (fun d : Fin 2 →₀ ℕ =>
      MvPowerSeries.coeff d F.toPowerSeries •
        MvPowerSeries.coeff (single () 1) (a ^ d 0 * b ^ d 1)) ⊆
      ↑({single 0 1, single 1 1} : Finset (Fin 2 →₀ ℕ)) := by
    intro d hd
    simp only [Function.mem_support] at hd
    have hne : MvPowerSeries.coeff (single () 1) (a ^ d 0 * b ^ d 1) ≠ 0 := by
      intro h
      exact hd (by rw [h, smul_zero])
    rw [PowerSeries.coeff_coeToMvPowerSeries] at hne
    have hsum : d 0 + d 1 = 1 := by
      by_contra hs
      rcases Nat.lt_or_ge (d 0 + d 1) 1 with hlt | hge
      · have h0 : d 0 = 0 := by omega
        have h1 : d 1 = 0 := by omega
        rw [h0, h1, pow_zero, pow_zero, mul_one, PowerSeries.coeff_one] at hne
        simp at hne
      · exact hne (coeff_one_pow_mul_pow ha hb (by omega))
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    have hd01 : (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1) := by omega
    rcases hd01 with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact Or.inl (Finsupp.ext fun i => by fin_cases i <;> simp [h0, h1])
    · exact Or.inr (Finsupp.ext fun i => by fin_cases i <;> simp [h0, h1])
  unfold fgAdd
  rw [← PowerSeries.coeff_coeToMvPowerSeries,
    MvPowerSeries.coeff_subst (hasSubst_cons ha hb) F.toPowerSeries (single () 1)]
  simp only [hprod]
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp, Finset.sum_pair hne_single]
  simp [F.lin_coeff_X, F.lin_coeff_Y, PowerSeries.coeff_coeToMvPowerSeries]

/-- The multiplication-by-`n` power series `[n](z)` of the formal group `F`: `[0](z) = 0` and
`[n+1](z) = F([n](z), z)`. -/
noncomputable def mulByN (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => F.fgAdd (mulByN F n) PowerSeries.X

@[simp]
theorem mulByN_zero : F.mulByN 0 = 0 := rfl

theorem mulByN_succ (n : ℕ) : F.mulByN (n + 1) = F.fgAdd (F.mulByN n) PowerSeries.X := rfl

@[simp]
theorem mulByN_one : F.mulByN 1 = PowerSeries.X := by
  -- `[1](z) = F(0, z) = z` : substituting `0` into the first slot leaves the second unchanged.
  rw [mulByN_succ, mulByN_zero]
  unfold fgAdd
  exact F.zero_add PowerSeries.HasSubst.X'

/-- `[n](z)` has zero constant coefficient. -/
@[simp]
theorem constantCoeff_mulByN (n : ℕ) : PowerSeries.constantCoeff (F.mulByN n) = 0 := by
  induction n with
  | zero => simp [mulByN]
  | succ k ih => rw [mulByN_succ]; exact F.constantCoeff_fgAdd ih PowerSeries.constantCoeff_X

/-- **The linear coefficient of `[n](z)` is `n`.**  Hence `[n](z) = n·z + O(z²)`. -/
@[simp]
theorem coeff_one_mulByN (n : ℕ) : PowerSeries.coeff (R := R) 1 (F.mulByN n) = (n : R) := by
  induction n with
  | zero => simp [mulByN]
  | succ k ih =>
    rw [mulByN_succ, F.coeff_one_fgAdd (F.constantCoeff_mulByN k) PowerSeries.constantCoeff_X, ih,
      PowerSeries.coeff_one_X]
    push_cast
    ring

/-- `[n](z)` is substitution-admissible. -/
theorem hasSubst_mulByN (n : ℕ) : PowerSeries.HasSubst (F.mulByN n) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (F.constantCoeff_mulByN n)

section Invertible

variable {F} {n : ℕ}

/-- When `(n : R)` is a unit, the multiplication-by-`n` series `[n]` has a compositional
(substitution) inverse `[n]⁻¹`, i.e. a power series with `[n]([n]⁻¹(z)) = z` and
`[n]⁻¹([n](z)) = z`.
This is Mathlib's `substInvOfIsUnit`, applicable because `constantCoeff [n] = 0` and
`coeff 1 [n] = n` is a unit. -/
noncomputable def mulByNInv (hn : IsUnit (n : R)) : PowerSeries R :=
  PowerSeries.substInvOfIsUnit (F.mulByN n) (by rw [F.coeff_one_mulByN]; exact hn)

theorem subst_mulByNInv_right (hn : IsUnit (n : R)) :
    (F.mulByN n).subst (mulByNInv (F := F) hn) = PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_right (F.mulByN n) (F.constantCoeff_mulByN n) _

theorem subst_mulByNInv_left (hn : IsUnit (n : R)) :
    (mulByNInv (F := F) hn).subst (F.mulByN n) = PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_left (F.mulByN n) (F.constantCoeff_mulByN n) _

theorem constantCoeff_mulByNInv (hn : IsUnit (n : R)) :
    PowerSeries.constantCoeff (mulByNInv (F := F) hn) = 0 :=
  PowerSeries.constantCoeff_substInvOfIsUnit (F.mulByN n) _

theorem hasSubst_mulByNInv (hn : IsUnit (n : R)) :
    PowerSeries.HasSubst (mulByNInv (F := F) hn) :=
  PowerSeries.HasSubst.substInvOfIsUnit (F.mulByN n) _

/-- **Bijectivity of `[n]` under substitution.**  When `(n : R)` is a unit, substitution by `[n]`,
`s ↦ [n].subst s`, is a bijection of the set of substitution-admissible power series, with inverse
`s ↦ [n]⁻¹.subst s`.  This is the series-level statement behind the bijectivity of
`[n] : Ê(𝔪) → Ê(𝔪)`. -/
theorem subst_mulByN_bijective (hn : IsUnit (n : R)) {s : PowerSeries R}
    (hs : PowerSeries.HasSubst s) :
    (F.mulByN n).subst ((mulByNInv (F := F) hn).subst s) = s ∧
    (mulByNInv (F := F) hn).subst ((F.mulByN n).subst s) = s := by
  -- Two applications of `subst_comp_subst` with the left/right inverse identities and `subst_X`.
  refine ⟨?_, ?_⟩
  · rw [← PowerSeries.subst_comp_subst_apply (hasSubst_mulByNInv (F := F) hn) hs,
      subst_mulByNInv_right hn, PowerSeries.subst_X hs]
  · rw [← PowerSeries.subst_comp_subst_apply (hasSubst_mulByN F n) hs, subst_mulByNInv_left hn,
      PowerSeries.subst_X hs]

end Invertible

end FormalGroup
