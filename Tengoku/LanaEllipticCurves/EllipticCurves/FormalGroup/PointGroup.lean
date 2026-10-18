/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.RingTheory.FormalGroup.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The formal inverse and the group of points of a formal group law

For a one dimensional formal group law `F : FormalGroup R` (in the sense of
`Mathlib.RingTheory.FormalGroup.Basic`) we construct the *formal inverse* power series
`i(X) = F.formalInv ∈ R⟦X⟧` characterised by
`F(X, i(X)) = 0`, and upgrade the additive monoid structure on `F.Point σ` (from `Basic.lean`)
to an `AddGroup` (and to an `AddCommGroup` when `F` is commutative).

The construction of `formalInv` is a specialisation of the `PowerSeries.substInv` development.
Because `F(X, Y) = X + Y + (higher order)` the diagonal coefficient solving `F(X, i(X)) = 0`
coefficientwise is the bare `+Y` term, whose coefficient is `1` (`FormalGroup.lin_coeff_Y`); hence,
unlike `substInv`, **no** invertibility hypothesis is needed — one simply negates.

## Main definitions / results

* `FormalGroup.formalInv` : the formal inverse power series `i(X)`.
* `FormalGroup.subst_formalInv` : `F(X, i(X)) = 0`.
* `FormalGroup.point_add_neg` : `F(h, i(h)) = 0` for any substitutable `h`.
* `instance : Neg (F.Point σ)`, `instance : AddGroup (F.Point σ)`,
  `instance [F.IsComm] : AddCommGroup (F.Point σ)`.

## References
* [Silverman, *The Arithmetic of Elliptic Curves*, IV.2][silverman2009]
-/

open MvPowerSeries Finsupp

noncomputable section

variable {R : Type*} [CommRing R] {σ : Type*}

/-- If `X ∣ B`, `X ∣ B'`, `X ^ n ∣ B - B'` and `k ≥ 2`, then `X ^ (n+1) ∣ B ^ k - B' ^ k`:
the geometric cofactor of `B ^ k - B' ^ k` is divisible by `X`, contributing one extra factor. -/
theorem PowerSeries.X_pow_succ_dvd_pow_sub_pow {B B' : PowerSeries R}
    (hB : (PowerSeries.X : PowerSeries R) ∣ B) (hB' : (PowerSeries.X : PowerSeries R) ∣ B')
    {n k : ℕ} (hk : 2 ≤ k) (hd : (PowerSeries.X : PowerSeries R) ^ n ∣ B - B') :
    (PowerSeries.X : PowerSeries R) ^ (n + 1) ∣ B ^ k - B' ^ k := by
  have hcof : (PowerSeries.X : PowerSeries R) ∣
      ∑ i ∈ Finset.range k, B ^ i * B' ^ (k - 1 - i) := by
    refine Finset.dvd_sum (fun i _ => ?_)
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      rw [pow_zero, one_mul]
      exact dvd_pow hB' (by omega)
    · exact (dvd_pow hB (by omega)).mul_right _
  rw [← geom_sum₂_mul B B' k, show n + 1 = 1 + n from by omega, pow_add, pow_one]
  exact mul_dvd_mul hcof hd

/-- In an additive monoid, a right inverse (`a + -a = 0` for all `a`) is automatically a left
inverse. -/
theorem neg_add_cancel_of_add_neg_cancel {M : Type*} [AddMonoid M] [Neg M]
    (h : ∀ a : M, a + -a = 0) (a : M) : -a + a = 0 := by
  calc -a + a = -a + a + (-a + - -a) := by rw [h (-a), add_zero]
    _ = -a + (a + -a) + - -a := by simp only [add_assoc]
    _ = -a + - -a := by rw [h a, add_zero]
    _ = 0 := h (-a)

namespace FormalGroup

/-- Coefficient recursion for the formal inverse power series.  The degree-`(n+2)` coefficient is
forced by the vanishing of the degree-`(n+2)` coefficient of `F(X, partial)`, using that the
diagonal (bare `+Y`) coefficient of `F` is `1`. -/
noncomputable def formalInvFun (F : FormalGroup R) : ℕ → R
  | 0 => 0
  | 1 => -1
  | (n + 2) => - PowerSeries.coeff (n + 2)
      (F.toPowerSeries.subst
        ![PowerSeries.X, ∑ i : Fin (n + 2),
          PowerSeries.C (formalInvFun F i.1) * PowerSeries.X ^ i.1])

@[simp] lemma formalInvFun_zero (F : FormalGroup R) : formalInvFun F 0 = 0 := by
  simp only [formalInvFun]

@[simp] lemma formalInvFun_one (F : FormalGroup R) : formalInvFun F 1 = -1 := by
  simp only [formalInvFun]

/-- `HasSubst` for `![X, B]` when `B` has zero constant coefficient. -/
lemma hasSubst_X_cons {B : PowerSeries R} (hB : PowerSeries.constantCoeff B = 0) :
    MvPowerSeries.HasSubst ![PowerSeries.X (R := R), B] := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => ?_)
  fin_cases s
  · exact PowerSeries.constantCoeff_X (R := R)
  · exact hB

/-- The partial sum `∑_{i ≤ m} i_i X^i` of the formal-inverse series. -/
noncomputable def partialInv (F : FormalGroup R) (m : ℕ) : PowerSeries R :=
  ∑ i : Fin (m + 1), PowerSeries.C (formalInvFun F i.1) * PowerSeries.X ^ i.1

/-- The formal inverse power series `i(X)`. -/
noncomputable def formalInv (F : FormalGroup R) : PowerSeries R :=
  PowerSeries.mk (formalInvFun F)

lemma coeff_formalInv (F : FormalGroup R) (i : ℕ) :
    PowerSeries.coeff i (formalInv F) = formalInvFun F i := by
  rw [formalInv, PowerSeries.coeff_mk]

@[simp] lemma constantCoeff_formalInv (F : FormalGroup R) :
    PowerSeries.constantCoeff (formalInv F) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_formalInv, formalInvFun_zero]

lemma coeff_one_formalInv (F : FormalGroup R) : PowerSeries.coeff 1 (formalInv F) = -1 := by
  rw [coeff_formalInv, formalInvFun_one]

lemma hasSubst_formalInv (F : FormalGroup R) : PowerSeries.HasSubst (formalInv F) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_formalInv F)

lemma subst_X_zero_eq_Xzero (F : FormalGroup R) :
    F.toPowerSeries.subst ![PowerSeries.X, (0 : PowerSeries R)] = F.Xzero := rfl

/-- Definitional unfolding of `formalInvFun` at `n + 2`, phrased through `partialInv`. -/
lemma formalInvFun_add_two (F : FormalGroup R) (n : ℕ) :
    formalInvFun F (n + 2) = - PowerSeries.coeff (n + 2)
      (F.toPowerSeries.subst ![PowerSeries.X, partialInv F (n + 1)]) := by
  rw [partialInv]
  simp only [formalInvFun]

lemma coeff_partialInv (F : FormalGroup R) (m i : ℕ) :
    PowerSeries.coeff i (partialInv F m) = if i ≤ m then formalInvFun F i else 0 := by
  rw [partialInv, map_sum]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Fin.sum_univ_eq_sum_range (fun j => if i = j then formalInvFun F j else 0) (m + 1),
    Finset.sum_ite_eq (Finset.range (m + 1)) i (formalInvFun F)]
  simp

@[simp] lemma constantCoeff_partialInv (F : FormalGroup R) (m : ℕ) :
    PowerSeries.constantCoeff (partialInv F m) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_partialInv, ite_eq_left (Nat.zero_le m),
    formalInvFun_zero]

section Increment

variable (F : FormalGroup R)

/-- The degree-`n` coefficient of `F(X, B)` written as a finite sum over bidegrees. -/
lemma coeff_subst_X_cons {B : PowerSeries R}
    (hsB : MvPowerSeries.HasSubst ![PowerSeries.X (R := R), B]) (n : ℕ) :
    PowerSeries.coeff n (F.toPowerSeries.subst ![PowerSeries.X, B]) =
      ∑ᶠ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F.toPowerSeries *
        PowerSeries.coeff n (PowerSeries.X ^ d 0 * B ^ d 1) := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst hsB]
  refine finsum_congr (fun d => ?_)
  rw [smul_eq_mul]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
  simp [PowerSeries.coeff]

/-- The finite-support witness for the bidegree sum of `coeff_subst_X_cons`. -/
lemma hasFiniteSupport_coeff_subst_X_cons {B : PowerSeries R}
    (hsB : MvPowerSeries.HasSubst ![PowerSeries.X (R := R), B]) (n : ℕ) :
    Function.HasFiniteSupport (fun d : Fin 2 →₀ ℕ => MvPowerSeries.coeff d F.toPowerSeries *
        PowerSeries.coeff n (PowerSeries.X ^ d 0 * B ^ d 1)) := by
  have h := MvPowerSeries.coeff_subst_finite hsB F.toPowerSeries (Finsupp.single () n)
  have heq : (fun d : Fin 2 →₀ ℕ => MvPowerSeries.coeff d F.toPowerSeries •
        MvPowerSeries.coeff (Finsupp.single () n)
          (d.prod fun s e => (![PowerSeries.X (R := R), B] s) ^ e))
      = (fun d : Fin 2 →₀ ℕ => MvPowerSeries.coeff d F.toPowerSeries *
          PowerSeries.coeff n (PowerSeries.X ^ d 0 * B ^ d 1)) := by
    funext d
    rw [smul_eq_mul]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp [PowerSeries.coeff]
  rwa [heq] at h

/-- Increment lemma: substituting into the second slot of `F(X, -)`, the degree-`n` coefficient
changes exactly by the difference of the degree-`n` coefficients of the arguments, provided the
two arguments agree in all lower degrees. -/
lemma coeff_subst_X_cons_sub {B B' : PowerSeries R}
    (hB : PowerSeries.constantCoeff B = 0) (hB' : PowerSeries.constantCoeff B' = 0)
    {n : ℕ} (hdvd : (PowerSeries.X : PowerSeries R) ^ n ∣ B - B') :
    PowerSeries.coeff n (F.toPowerSeries.subst ![PowerSeries.X, B]) =
      PowerSeries.coeff n (F.toPowerSeries.subst ![PowerSeries.X, B']) +
        (PowerSeries.coeff n B - PowerSeries.coeff n B') := by
  have hsB : MvPowerSeries.HasSubst ![PowerSeries.X (R := R), B] := hasSubst_X_cons hB
  have hsB' : MvPowerSeries.HasSubst ![PowerSeries.X (R := R), B'] := hasSubst_X_cons hB'
  rw [coeff_subst_X_cons F hsB, coeff_subst_X_cons F hsB', ← sub_eq_iff_eq_add',
    ← finsum_sub_distrib (hasFiniteSupport_coeff_subst_X_cons F hsB n)
      (hasFiniteSupport_coeff_subst_X_cons F hsB' n)]
  rw [finsum_eq_single _ (Finsupp.single 1 1)]
  · simp [F.lin_coeff_Y]
  · intro d hd
    suffices h : PowerSeries.coeff n (PowerSeries.X ^ d 0 * B ^ d 1)
        = PowerSeries.coeff n (PowerSeries.X ^ d 0 * B' ^ d 1) by rw [h, sub_self]
    rw [← sub_eq_zero, ← map_sub, ← mul_sub]
    have hdvd' : (PowerSeries.X : PowerSeries R) ^ (n + 1) ∣
        PowerSeries.X ^ d 0 * (B ^ d 1 - B' ^ d 1) := by
      rcases Nat.eq_zero_or_pos (d 0) with h0 | h0
      · rcases (show d 1 = 0 ∨ d 1 = 1 ∨ 2 ≤ d 1 from by omega) with h1 | h1 | h1
        · rw [h1]; simp
        · refine absurd (Finsupp.ext (fun a => ?_)) hd
          fin_cases a
          · simp [h0]
          · simp [h1]
        · rw [h0, pow_zero, one_mul]
          exact PowerSeries.X_pow_succ_dvd_pow_sub_pow (PowerSeries.X_dvd_iff.mpr hB)
            (PowerSeries.X_dvd_iff.mpr hB') h1 hdvd
      · have key : (PowerSeries.X : PowerSeries R) ^ n ∣ B ^ d 1 - B' ^ d 1 :=
          hdvd.trans (sub_dvd_pow_sub_pow B B' (d 1))
        rw [show n + 1 = 1 + n from by omega, pow_add]
        exact mul_dvd_mul (pow_dvd_pow _ h0) key
    exact PowerSeries.X_pow_dvd_iff.mp hdvd' n (Nat.lt_succ_self n)

end Increment

/-- The core identity: `F(X, i(X)) = 0`, where `i = formalInv F`. -/
theorem subst_formalInv (F : FormalGroup R) :
    F.toPowerSeries.subst ![PowerSeries.X, formalInv F] = 0 := by
  have hs : MvPowerSeries.HasSubst ![PowerSeries.X (R := R), formalInv F] :=
    hasSubst_X_cons (constantCoeff_formalInv F)
  refine PowerSeries.ext (fun n => ?_)
  rw [map_zero]
  obtain _ | _ | n := n
  · have h1 : PowerSeries.coeff 0 (F.toPowerSeries.subst ![PowerSeries.X, formalInv F])
        = PowerSeries.coeff 0 (F.toPowerSeries.subst ![PowerSeries.X, 0])
          + (PowerSeries.coeff 0 (formalInv F) - PowerSeries.coeff 0 0) :=
      coeff_subst_X_cons_sub F (constantCoeff_formalInv F) (map_zero _) (by simp)
    rw [h1, subst_X_zero_eq_Xzero, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      F.constantCoeff_Xzero, coeff_formalInv, formalInvFun_zero, map_zero]
    ring
  · have h1 : PowerSeries.coeff 1 (F.toPowerSeries.subst ![PowerSeries.X, formalInv F])
        = PowerSeries.coeff 1 (F.toPowerSeries.subst ![PowerSeries.X, 0])
          + (PowerSeries.coeff 1 (formalInv F) - PowerSeries.coeff 1 0) :=
      coeff_subst_X_cons_sub F (constantCoeff_formalInv F) (map_zero _)
        (by
          rw [sub_zero, pow_one]
          exact PowerSeries.X_dvd_iff.mpr (constantCoeff_formalInv F))
    rw [h1, subst_X_zero_eq_Xzero, F.coeff_one_Xzero, coeff_one_formalInv, map_zero]
    ring
  · have hdvd : (PowerSeries.X : PowerSeries R) ^ (n + 2)
        ∣ formalInv F - partialInv F (n + 1) := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro i hi
      rw [map_sub, coeff_formalInv, coeff_partialInv, ite_eq_left (by omega : i ≤ n + 1), sub_self]
    rw [coeff_subst_X_cons_sub F (constantCoeff_formalInv F) (constantCoeff_partialInv F (n + 1))
      hdvd]
    have hrec : PowerSeries.coeff (n + 2)
        (F.toPowerSeries.subst ![PowerSeries.X, partialInv F (n + 1)])
          = - formalInvFun F (n + 2) := by
      rw [formalInvFun_add_two]
      ring
    rw [hrec, coeff_formalInv, coeff_partialInv, ite_eq_right (by omega : ¬ n + 2 ≤ n + 1)]
    ring

/-- For any substitutable `h`, `F(h, i(h)) = 0`. -/
theorem point_add_neg (F : FormalGroup R) {h : MvPowerSeries σ R} (hh : PowerSeries.HasSubst h) :
    F.toPowerSeries.subst ![h, (formalInv F).subst h] = 0 := by
  have hs : MvPowerSeries.HasSubst ![PowerSeries.X (R := R), formalInv F] :=
    hasSubst_X_cons (constantCoeff_formalInv F)
  have key : PowerSeries.subst h (F.toPowerSeries.subst ![PowerSeries.X, formalInv F])
      = F.toPowerSeries.subst ![h, (formalInv F).subst h] := by
    rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hs hh.const]
    congr! 2 with s
    fin_cases s
    · simp [PowerSeries.X, MvPowerSeries.subst]
    · simp [PowerSeries.subst]
  rw [← key, subst_formalInv, ← PowerSeries.coe_substAlgHom hh, map_zero]

variable (F : FormalGroup R)

/-- **Negation on `F.Point σ`**, `x ↦ i(x)` for the formal inverse `i`.

⚠️ **Named rather than anonymous** (`#1277`).  An anonymous `instance` whose elaborated type
mentions no constant of this project gets `moduleToSuffix` appended by
`Lean.Elab.NameGen.mkBaseNameWithSuffix` — here `_ellipticCurves`, the lake library name — so the
auto-generated name was ``FormalGroup.instNegPoint_tengoku``.  That is not a
collision (the unsuffixed name exists nowhere); it is the library name leaking into the API, and it
would change if the library were renamed.  The name below is Lean's own generated name with the
suffix removed, so nothing else moves. -/
instance instNegPoint : Neg (F.Point σ) where
  neg x := ⟨(formalInv F).subst x.val, by
    have h := (hasSubst_formalInv F).comp x.prop
    rwa [PowerSeries.coe_substAlgHom x.prop] at h⟩

@[simp] lemma neg_apply (x : F.Point σ) :
    (-x).val = (formalInv F).subst x.val := rfl

/-- **`F.Point σ` is an additive group.**  The monoid structure together with `instNegPoint`;
`neg_add_cancel` comes from `point_add_neg`.

⚠️ Named rather than anonymous, for the reason given on `instNegPoint`: the auto-generated name
was `FormalGroup.instAddGroupPoint_tengoku`. -/
instance instAddGroupPoint : AddGroup (F.Point σ) :=
  { (inferInstance : AddMonoid (F.Point σ)), (inferInstance : Neg (F.Point σ)) with
    zsmul := zsmulRec
    neg_add_cancel := by
      have hrn : ∀ y : F.Point σ, y + -y = 0 := fun y => Subtype.ext (by
        simp only [add_apply, neg_apply, zero_apply]
        exact point_add_neg F y.prop)
      exact neg_add_cancel_of_add_neg_cancel hrn }

/-- **`F.Point σ` is an additive commutative group** when the law is commutative.

⚠️ Named rather than anonymous, for the reason given on `instNegPoint`: the auto-generated name
was `FormalGroup.instAddCommGroupPointOfIsComm_tengoku`. -/
instance instAddCommGroupPointOfIsComm [F.IsComm] : AddCommGroup (F.Point σ) :=
  { (inferInstance : AddGroup (F.Point σ)), (inferInstance : AddCommMonoid (F.Point σ)) with }

end FormalGroup
