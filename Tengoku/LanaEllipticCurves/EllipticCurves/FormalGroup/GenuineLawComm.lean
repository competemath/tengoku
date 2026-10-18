/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.GenuineLaw

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Commutativity of the genuine Weierstrass formal group law

The genuine bivariate power series `W.formalGroupZW : MvPowerSeries (Fin 2) R` of
`EllipticCurves.FormalGroup.GenuineLaw` is built entirely from the `(z, w)`-plane addition data
(slope `λ = Δ(w)`, intercept `ν`, Vieta third root `z₃'`, negation), all of which are **symmetric**
under the interchange `z₁ ↔ z₂`. This file records that symmetry, i.e. the **commutativity** of the
Weierstrass formal group law

`F(z₁, z₂) = F(z₂, z₁)`,

expressed as invariance under the variable swap `MvPowerSeries.rename (Equiv.swap 0 1)`.

The proof is the manifest symmetry of the construction:
* the slope `λ = Δ(w)` has `z₀^a z₁^b`-coefficient `w.coeff (a + b + 1)`, which depends only on the
  *sum* `a + b`, hence is swap-invariant (`formalWDividedDiff_swap`);
* the intercept `ν = w(z₁) − λ z₁` is swap-invariant because `w(z₂) − λ z₂ = w(z₁) − λ z₁`, which is
  the divided-difference regularity `(z₂ − z₁)·λ = w(z₂) − w(z₁)` (`formalGroupNu_swap`);
* the cubic data `A`, `B`, the Vieta third root `z₃'` and the negation denominator `D` are then
  swap-invariant by functoriality of the rename homomorphism together with the compatibility of the
  swap with `MvPowerSeries.invOfUnit` (`rename_swap_invOfUnit`);
* hence `F = −z₃' · D⁻¹` is swap-invariant (`formalGroupZW_comm`).

This is the mathematical core of the commutativity of the Weierstrass formal group law, delivered on
the genuine `(z, w)` construction (Silverman AEC IV.1, Theorem 1.1).

## ⚠️ Both things this file used to defer have landed, and one of them was never deferred

⚠️ **This paragraph used to read** *"Once the identification of `W.formalGroupZW` with the Laurent
`W.formalGroupLaurent` / `W.formalGroupSeries` lands (the sibling identification issue), the
commutativity of `W.formalGroupSeries` in the `FormalGroup.IsComm` form transfers immediately from
`formalGroupZW_comm`."*  It tied two different statements to one gate, and neither is future work.

* **The identification landed.**  `WeierstrassCurve.formalGroupSeries_eq_formalGroupZW`
  (`EllipticCurves.FormalGroup.GenuineLawTransfer`, issue #310) is a merged, unconditional theorem
  over every `CommRing R`.
* **The transfer to `W.formalGroupSeries` was done, in a file downstream of this one.**
  `WeierstrassCurve.formalGroupSeries_comm` (`EllipticCurves.FormalGroup.SeriesComm`) is
  `W.formalGroupSeries.subst ![X 1, X 0] = W.formalGroupSeries`, proved by rewriting with that
  identification and then with `formalGroupZW_subst_swap` — two rewrites, which is the *"transfers
  immediately"* the retired sentence predicted.  ⚠️ That file has this one in its
  `EllipticCurves`-import closure; the pointer could only ever go stale in this direction.
* ⚠️ **The `FormalGroup.IsComm` clause named the wrong gate.**  Every `IsComm` witness in this tree
  is built on `W.formalGroupZW` *directly*, out of `formalGroupZW_subst_swap`, on a bundle whose
  `toPowerSeries` is `W.formalGroupZW` by `rfl` — `formalGroupOfLogAdditivity_isComm`
  (`EllipticCurves.FormalGroup.GroupLawBundle`), `formalGroupOfRatAlgebra_isComm` and
  `formalGroup_isComm` (`EllipticCurves.FormalGroup.GroupLawBundleGeneral`).  The first of those
  lives in a file whose `EllipticCurves`-import closure is 14 modules and **does not contain**
  `EllipticCurves.FormalGroup.GenuineLawTransfer`, so it cannot see the identification at all.  The
  `IsComm` form was never gated on it; only the `formalGroupSeries` restatement was.

## Main results

* `WeierstrassCurve.formalGroupZW_comm` : `rename (swap 0 1) F = F`, i.e. `F(z₁,z₂) = F(z₂,z₁)`.
* `WeierstrassCurve.coeff_formalGroupZW_swap` : the coefficient form of commutativity.

## ⚠️ Three `@[simp]` attributes were removed here, and the lemmas kept (`#1278`)

The three private variable-swap lemmas `rename_swap_C`, `rename_swap_X_zero` and
`rename_swap_X_one` carried `@[simp]`, and the default simp set **already proves each of them** —
through `MvPowerSeries.rename_C`, and `MvPowerSeries.rename_X` with `Equiv.swap_apply_left` /
`Equiv.swap_apply_right`. Measured with Mathlib's `simpNF` environment linter, which had never been
run on this tree. All three are still used by name below; only the attribute went.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, Theorem 1.1.
-/

open MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-! ### The variable-swap homomorphism at the coefficient level -/

/-- The coefficients of a series renamed along a variable *equivalence* `e`: `rename e` reads off
coefficients along the inverse reindexing `e.symm`. -/
private lemma coeff_rename_of_equiv {σ τ : Type*} (e : σ ≃ τ) (p : MvPowerSeries σ R)
    (d : τ →₀ ℕ) :
    MvPowerSeries.coeff d (MvPowerSeries.rename (⇑e) p)
      = MvPowerSeries.coeff (Finsupp.equivMapDomain e.symm d) p := by
  have hemb : Finsupp.embDomain e.toEmbedding (Finsupp.equivMapDomain e.symm d) = d := by
    rw [Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding,
        ← Finsupp.equivMapDomain_eq_mapDomain, ← Finsupp.equivMapDomain_trans,
        Equiv.symm_trans_self, Finsupp.equivMapDomain_refl]
  have h := MvPowerSeries.coeff_embDomain_rename (R := R) e.toEmbedding p
              (Finsupp.equivMapDomain e.symm d)
  rw [hemb] at h
  rw [← h]
  simp only [Equiv.coe_toEmbedding]

/-- The variable swap fixes the divided difference: its `z₀^a z₁^b`-coefficient is `f.coeff
(a + b + 1)`, which depends only on the sum `a + b`. -/
private lemma rename_swap_dividedDiff (f : PowerSeries R) :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) (PowerSeries.dividedDiff f)
      = PowerSeries.dividedDiff f := by
  ext d
  have e0 : (Finsupp.equivMapDomain (Equiv.swap (0 : Fin 2) 1).symm d) 0 = d 1 := by
    rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm, Equiv.swap_apply_left]
  have e1 : (Finsupp.equivMapDomain (Equiv.swap (0 : Fin 2) 1).symm d) 1 = d 0 := by
    rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm, Equiv.swap_apply_right]
  rw [coeff_rename_of_equiv (Equiv.swap (0 : Fin 2) 1), PowerSeries.coeff_dividedDiff,
      PowerSeries.coeff_dividedDiff, e0, e1, Nat.add_comm (d 1) (d 0)]

/-- The variable swap commutes with `invOfUnit` when the constant coefficient is `1`. -/
private lemma rename_swap_invOfUnit (u : MvPowerSeries (Fin 2) R)
    (h : MvPowerSeries.constantCoeff u = 1) :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) (MvPowerSeries.invOfUnit u 1)
      = MvPowerSeries.invOfUnit
          (MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) u) 1 := by
  set S := MvPowerSeries.rename (R := R) (⇑(Equiv.swap (0 : Fin 2) 1)) with hS
  have hval : MvPowerSeries.constantCoeff u = ((1 : Rˣ) : R) := by rw [h, Units.val_one]
  have hsval : MvPowerSeries.constantCoeff (S u) = ((1 : Rˣ) : R) := by
    rw [hS, MvPowerSeries.constantCoeff_rename, h, Units.val_one]
  have h1 : S u * S (MvPowerSeries.invOfUnit u 1) = 1 := by
    rw [hS, ← map_mul, MvPowerSeries.mul_invOfUnit u 1 hval, map_one]
  have h2 : MvPowerSeries.invOfUnit (S u) 1 * S u = 1 :=
    MvPowerSeries.invOfUnit_mul _ 1 hsval
  calc S (MvPowerSeries.invOfUnit u 1)
      = (MvPowerSeries.invOfUnit (S u) 1 * S u) * S (MvPowerSeries.invOfUnit u 1) := by
        rw [h2, one_mul]
    _ = MvPowerSeries.invOfUnit (S u) 1 * (S u * S (MvPowerSeries.invOfUnit u 1)) := by
        rw [mul_assoc]
    _ = MvPowerSeries.invOfUnit (S u) 1 := by rw [h1, mul_one]

/-- The variable swap fixes constant power series. -/
private lemma rename_swap_C (r : R) :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) (MvPowerSeries.C r) = MvPowerSeries.C r :=
  MvPowerSeries.rename_C _ r

/-- The variable swap sends `z₁ ↦ z₂`. -/
private lemma rename_swap_X_zero :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) (MvPowerSeries.X 0)
      = (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) := by
  rw [MvPowerSeries.rename_X, Equiv.swap_apply_left]

/-- The variable swap sends `z₂ ↦ z₁`. -/
private lemma rename_swap_X_one :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) (MvPowerSeries.X 1)
      = (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) := by
  rw [MvPowerSeries.rename_X, Equiv.swap_apply_right]

variable (W : WeierstrassCurve R)

/-! ### Vanishing constant coefficients of the addition data -/

/-- The slope `λ` has vanishing constant coefficient. -/
private lemma constantCoeff_formalWDividedDiff' :
    MvPowerSeries.constantCoeff W.formalWDividedDiff = 0 := by
  rw [WeierstrassCurve.formalWDividedDiff, PowerSeries.constantCoeff_dividedDiff]
  exact PowerSeries.coeff_of_lt_order 1 (lt_of_lt_of_le (by norm_num) W.order_formalW)

/-- The embedding `w(z₁) = formalW.toMvPowerSeries 0` has vanishing constant coefficient. -/
private lemma constantCoeff_toMvPowerSeries_formalW_zero :
    MvPowerSeries.constantCoeff (W.formalW.toMvPowerSeries (0 : Fin 2)) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      show (0 : Fin 2 →₀ ℕ) = Finsupp.single (0 : Fin 2) 0 by simp,
      PowerSeries.coeff_toMvPowerSeries_single]
  exact PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by norm_num) W.order_formalW)

/-- The intercept `ν` has vanishing constant coefficient. -/
private lemma constantCoeff_formalGroupNu :
    MvPowerSeries.constantCoeff W.formalGroupNu = 0 := by
  rw [WeierstrassCurve.formalGroupNu, map_sub, map_mul, W.constantCoeff_formalWDividedDiff',
      W.constantCoeff_toMvPowerSeries_formalW_zero]
  simp

/-- The cubic subleading coefficient `B` has vanishing constant coefficient. -/
private lemma constantCoeff_formalGroupSub :
    MvPowerSeries.constantCoeff W.formalGroupSub = 0 := by
  rw [WeierstrassCurve.formalGroupSub]
  simp [map_add, map_mul, map_pow, MvPowerSeries.constantCoeff_C,
    W.constantCoeff_formalWDividedDiff', W.constantCoeff_formalGroupNu]

/-- The cubic leading coefficient `A` has constant coefficient `1` (a unit). -/
private lemma constantCoeff_formalGroupLead :
    MvPowerSeries.constantCoeff W.formalGroupLead = 1 := by
  rw [WeierstrassCurve.formalGroupLead]
  simp [map_add, map_mul, map_pow, map_one, MvPowerSeries.constantCoeff_C,
    W.constantCoeff_formalWDividedDiff']

/-- The Vieta third root `z₃'` has vanishing constant coefficient. -/
private lemma constantCoeff_formalThirdRoot :
    MvPowerSeries.constantCoeff W.formalThirdRoot = 0 := by
  rw [WeierstrassCurve.formalThirdRoot]
  simp [map_sub, map_neg, map_mul, MvPowerSeries.constantCoeff_X,
    W.constantCoeff_formalGroupSub]

/-- The negation denominator `D` has constant coefficient `1` (a unit). -/
private lemma constantCoeff_formalGroupDen :
    MvPowerSeries.constantCoeff W.formalGroupDen = 1 := by
  rw [WeierstrassCurve.formalGroupDen]
  simp [map_sub, map_mul, map_add, map_one, MvPowerSeries.constantCoeff_C,
    W.constantCoeff_formalThirdRoot, W.constantCoeff_formalWDividedDiff',
    W.constantCoeff_formalGroupNu]

/-! ### Swap-invariance of the addition data -/

/-- The slope `λ` is invariant under `z₁ ↔ z₂`. -/
theorem formalWDividedDiff_swap :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) W.formalWDividedDiff
      = W.formalWDividedDiff := by
  rw [WeierstrassCurve.formalWDividedDiff]
  exact rename_swap_dividedDiff W.formalW

/-- The variable swap sends the embedding `w(z₁)` to `w(z₂)`. -/
private lemma rename_swap_toMvPowerSeries_zero :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) (W.formalW.toMvPowerSeries (0 : Fin 2))
      = W.formalW.toMvPowerSeries (1 : Fin 2) := by
  ext d
  rw [coeff_rename_of_equiv (Equiv.swap (0 : Fin 2) 1)]
  set d' := Finsupp.equivMapDomain (Equiv.swap (0 : Fin 2) 1).symm d with hd'
  have hd'0 : d' 0 = d 1 := by
    rw [hd', Finsupp.equivMapDomain_apply, Equiv.symm_symm, Equiv.swap_apply_left]
  have hd'1 : d' 1 = d 0 := by
    rw [hd', Finsupp.equivMapDomain_apply, Equiv.symm_symm, Equiv.swap_apply_right]
  by_cases h0 : d 0 = 0
  · have hd : d = Finsupp.single (1 : Fin 2) (d 1) := by ext s; fin_cases s <;> simp [h0]
    have hd's : d' = Finsupp.single (0 : Fin 2) (d' 0) := by
      ext s; fin_cases s <;> simp [hd'1, h0]
    rw [hd's, PowerSeries.coeff_toMvPowerSeries_single, hd,
        PowerSeries.coeff_toMvPowerSeries_single, hd'0]
  · have hne_d : d ≠ Finsupp.single (1 : Fin 2) (d 1) := fun hcon => h0 (by
      have := congrArg (fun g => g 0) hcon; simpa using this)
    have hne_d' : d' ≠ Finsupp.single (0 : Fin 2) (d' 0) := fun hcon => h0 (by
      have := congrArg (fun g => g 1) hcon; rw [hd'1] at this; simpa using this)
    rw [PowerSeries.coeff_toMvPowerSeries_of_ne W.formalW 0 hne_d',
        PowerSeries.coeff_toMvPowerSeries_of_ne W.formalW 1 hne_d]

/-- The intercept `ν` is invariant under `z₁ ↔ z₂` (via divided-difference regularity). -/
theorem formalGroupNu_swap :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) W.formalGroupNu = W.formalGroupNu := by
  simp only [WeierstrassCurve.formalGroupNu, map_sub, map_mul,
    W.rename_swap_toMvPowerSeries_zero, W.formalWDividedDiff_swap, rename_swap_X_zero]
  linear_combination -W.formalWDividedDiff_spec

/-- The cubic leading coefficient `A` is invariant under `z₁ ↔ z₂`. -/
theorem formalGroupLead_swap :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) W.formalGroupLead = W.formalGroupLead := by
  simp only [WeierstrassCurve.formalGroupLead, map_add, map_mul, map_pow, map_one,
    rename_swap_C, W.formalWDividedDiff_swap]

/-- The cubic subleading coefficient `B` is invariant under `z₁ ↔ z₂`. -/
theorem formalGroupSub_swap :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) W.formalGroupSub = W.formalGroupSub := by
  simp only [WeierstrassCurve.formalGroupSub, map_add, map_mul, map_pow, map_ofNat,
    rename_swap_C, W.formalWDividedDiff_swap, W.formalGroupNu_swap]

/-- The variable swap fixes `invOfUnit A 1`. -/
private lemma rename_swap_invOfUnit_formalGroupLead :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) (MvPowerSeries.invOfUnit W.formalGroupLead 1)
      = MvPowerSeries.invOfUnit W.formalGroupLead 1 := by
  rw [rename_swap_invOfUnit W.formalGroupLead W.constantCoeff_formalGroupLead,
      W.formalGroupLead_swap]

/-- The Vieta third root `z₃'` is invariant under `z₁ ↔ z₂`. -/
theorem formalThirdRoot_swap :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) W.formalThirdRoot = W.formalThirdRoot := by
  simp only [WeierstrassCurve.formalThirdRoot, map_sub, map_neg, map_mul, W.formalGroupSub_swap,
    W.rename_swap_invOfUnit_formalGroupLead, rename_swap_X_zero, rename_swap_X_one]
  ring

/-- The negation denominator `D` is invariant under `z₁ ↔ z₂`. -/
theorem formalGroupDen_swap :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) W.formalGroupDen = W.formalGroupDen := by
  simp only [WeierstrassCurve.formalGroupDen, map_sub, map_mul, map_add, map_one,
    rename_swap_C, W.formalThirdRoot_swap, W.formalWDividedDiff_swap, W.formalGroupNu_swap]

/-- The variable swap fixes `invOfUnit D 1`. -/
private lemma rename_swap_invOfUnit_formalGroupDen :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) (MvPowerSeries.invOfUnit W.formalGroupDen 1)
      = MvPowerSeries.invOfUnit W.formalGroupDen 1 := by
  rw [rename_swap_invOfUnit W.formalGroupDen W.constantCoeff_formalGroupDen,
      W.formalGroupDen_swap]

/-! ### Commutativity of the formal group law -/

/-- **Commutativity of the Weierstrass formal group law.** The genuine bivariate power series
`F(z₁, z₂) = W.formalGroupZW` is invariant under the interchange `z₁ ↔ z₂`, i.e.
`F(z₁, z₂) = F(z₂, z₁)`. All of the `(z, w)`-plane addition data (`λ`, `ν`, `A`, `B`, `z₃'`, `D`) is
symmetric in the two formal points, so the negation `F = −z₃' · D⁻¹` is too.
(Silverman AEC IV.1, Theorem 1.1.) -/
theorem formalGroupZW_comm :
    MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) W.formalGroupZW = W.formalGroupZW := by
  simp only [WeierstrassCurve.formalGroupZW, map_mul, map_neg, W.formalThirdRoot_swap,
    W.rename_swap_invOfUnit_formalGroupDen]

/-- The coefficient form of commutativity: swapping the two exponents leaves every coefficient of
`F` unchanged. -/
theorem coeff_formalGroupZW_swap (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.equivMapDomain (Equiv.swap (0 : Fin 2) 1) d) W.formalGroupZW
      = MvPowerSeries.coeff d W.formalGroupZW := by
  have h := coeff_rename_of_equiv (Equiv.swap (0 : Fin 2) 1) W.formalGroupZW d
  rw [W.formalGroupZW_comm, Equiv.symm_swap] at h
  exact h.symm

end WeierstrassCurve
