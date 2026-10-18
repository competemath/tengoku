/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.MvPowerSeriesCurry
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.BivariateCoords
import Tengoku.LanaEllipticCurves.EllipticCurves.FormalGroup.DividedDifference

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The generator dictionary for the double-Laurent writer `embedDoubleLaurent`

The faithful writer `HahnSeries.embedDoubleLaurent : MvPowerSeries (Fin 2) R → (R⸨X⸩)⸨X⸩`
(`PowerSeriesBridge.lean`, ring-hom form `HahnSeries.embedDoubleLaurentRingHom`) is the inclusion of
genuine bivariate power series into the iterated Laurent ring, with convention *inner grading
`z₁` = `Fin 2` index `0`, outer grading `z₂` = index `1`*. This file records how it acts on the
generators — the connective lemmas any change-of-coordinates identification of the two Weierstrass
formal group law constructions needs (issue #300):

* `embedDoubleLaurent_C` : the constant `MvPowerSeries.C r` maps to the double constant
  `C (C r)`.
* `embedDoubleLaurent_X_zero` / `_X_one` : the two variables `X 0` / `X 1` map to the inner / outer
  uniformisers `C (single 1 1)` / `single 1 1` of `R⸨z₁⸩⸨z₂⸩`.
* `embedDoubleLaurent_toMvPowerSeries_zero` / `_one` : a univariate power series `f`, embedded on
  the `zᵢ`-axis via `PowerSeries.toMvPowerSeries`, maps to the inner / outer Laurent embedding of
  its coercion `(f : R⸨X⸩)`.

The Weierstrass specialisations `embedDoubleLaurent_biZ₁ / _biZ₂ / _biW₁ / _biW₂` land on
the bivariate coordinates of `BivariateCoords.lean`.

Every proof is mechanical `HahnSeries` coefficient bookkeeping, routed through the unconditional
left inverse `HahnSeries.embedDoubleLaurent_ofDoubleLaurent` on pole-free-in-both series.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
-/

open scoped LaurentSeries PowerSeries

namespace HahnSeries

variable {R : Type*} [CommRing R]

/-! ### The reduction to the reader `ofDoubleLaurent` -/

/-- To identify `embedDoubleLaurent gen` with a target Laurent series `target`, it suffices to check
that `target` is pole-free in both gradings and that the reader `ofDoubleLaurent` sends it back to
`gen`. This routes every generator computation through the unconditional left inverse
`embedDoubleLaurent_ofDoubleLaurent`. -/
theorem embedDoubleLaurent_of_ofDoubleLaurent
    {gen : MvPowerSeries (Fin 2) R} {target : (R⸨X⸩)⸨X⸩}
    (hout : ∀ n < 0, target.coeff n = 0)
    (hin : ∀ (n : ℤ), ∀ g < 0, (target.coeff n).coeff g = 0)
    (h : ofDoubleLaurent target = gen) : embedDoubleLaurent gen = target := by
  rw [← h, embedDoubleLaurent_ofDoubleLaurent hout hin]

/-! ### Finsupp support helpers on `Fin 2 →₀ ℕ` -/

private lemma finTwo_eq_single_zero_iff (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single 0 1 ↔ d 0 = 1 ∧ d 1 = 0 := by
  rw [Finsupp.ext_iff, Fin.forall_fin_two]; simp

private lemma finTwo_eq_single_one_iff (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single 1 1 ↔ d 0 = 0 ∧ d 1 = 1 := by
  rw [Finsupp.ext_iff, Fin.forall_fin_two]; simp

/-- On `Fin 2`, `d` is supported on the index-`0` axis iff its index-`1` component vanishes. -/
private lemma finTwo_eq_single_zero_axis_iff (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single 0 (d 0) ↔ d 1 = 0 := by
  rw [Finsupp.ext_iff, Fin.forall_fin_two]; simp

/-- On `Fin 2`, `d` is supported on the index-`1` axis iff its index-`0` component vanishes. -/
private lemma finTwo_eq_single_one_axis_iff (d : Fin 2 →₀ ℕ) :
    d = Finsupp.single 1 (d 1) ↔ d 0 = 0 := by
  rw [Finsupp.ext_iff, Fin.forall_fin_two]; simp

/-! ### The constant -/

/-- `embedDoubleLaurent (C r) = C (C r)`: the writer sends the `MvPowerSeries` constant to the
double `HahnSeries` constant. -/
theorem embedDoubleLaurent_C (r : R) :
    embedDoubleLaurent (MvPowerSeries.C r : MvPowerSeries (Fin 2) R)
      = HahnSeries.C (HahnSeries.C r) := by
  refine embedDoubleLaurent_of_ofDoubleLaurent (fun n hn => ?_) (fun n g hg => ?_)
    (ofDoubleLaurent_C₂ r)
  · rw [C_apply, coeff_single_of_ne (ne_of_lt hn)]
  · rw [C_apply]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [coeff_single_same, C_apply, coeff_single_of_ne (ne_of_lt hg)]
    · rw [coeff_single_of_ne hn, coeff_zero]

/-! ### The two variables -/

/-- `embedDoubleLaurent (X 0) = C (single 1 1)`: the inner variable maps to the inner uniformiser
of `R⸨z₁⸩⸨z₂⸩`. -/
theorem embedDoubleLaurent_X_zero :
    embedDoubleLaurent (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R)
      = HahnSeries.C (HahnSeries.single (1 : ℤ) (1 : R)) := by
  refine embedDoubleLaurent_of_ofDoubleLaurent (fun n hn => ?_) (fun n g hg => ?_) ?_
  · rw [C_apply, coeff_single_of_ne (ne_of_lt hn)]
  · rw [C_apply]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [coeff_single_same, coeff_single_of_ne (by omega : g ≠ 1)]
    · rw [coeff_single_of_ne hn, coeff_zero]
  · refine MvPowerSeries.ext fun d => ?_
    rw [coeff_ofDoubleLaurent, MvPowerSeries.coeff_X, C_apply]
    rcases eq_or_ne (d 1) 0 with h1 | h1
    · rw [coeff_single, ite_eq_left (by exact_mod_cast h1), coeff_single]
      rcases eq_or_ne (d 0) 1 with h0 | h0
      · rw [ite_eq_left (by exact_mod_cast h0), ite_eq_left ((finTwo_eq_single_zero_iff d).2 ⟨h0, h1⟩)]
      · rw [ite_eq_right (by exact_mod_cast h0),
          ite_eq_right (fun h => h0 ((finTwo_eq_single_zero_iff d).1 h).1)]
    · rw [coeff_single, ite_eq_right (by exact_mod_cast h1), coeff_zero,
        ite_eq_right (fun h => h1 ((finTwo_eq_single_zero_iff d).1 h).2)]

/-- `embedDoubleLaurent (X 1) = single 1 1`: the outer variable maps to the outer uniformiser. -/
theorem embedDoubleLaurent_X_one :
    embedDoubleLaurent (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)
      = HahnSeries.single (1 : ℤ) (1 : R⸨X⸩) := by
  refine embedDoubleLaurent_of_ofDoubleLaurent (fun n hn => ?_) (fun n g hg => ?_) ?_
  · rw [coeff_single_of_ne (show (n : ℤ) ≠ 1 by omega)]
  · rcases eq_or_ne n 1 with rfl | hn
    · rw [coeff_single_same, coeff_one, ite_eq_right (ne_of_lt hg)]
    · rw [coeff_single_of_ne hn, coeff_zero]
  · refine MvPowerSeries.ext fun d => ?_
    rw [coeff_ofDoubleLaurent, MvPowerSeries.coeff_X]
    rcases eq_or_ne (d 1) 1 with h1 | h1
    · rw [coeff_single, ite_eq_left (by exact_mod_cast h1), coeff_one]
      rcases eq_or_ne (d 0) 0 with h0 | h0
      · rw [ite_eq_left (by exact_mod_cast h0), ite_eq_left ((finTwo_eq_single_one_iff d).2 ⟨h0, h1⟩)]
      · rw [ite_eq_right (by exact_mod_cast h0),
          ite_eq_right (fun h => h0 ((finTwo_eq_single_one_iff d).1 h).1)]
    · rw [coeff_single, ite_eq_right (by exact_mod_cast h1), coeff_zero,
        ite_eq_right (fun h => h1 ((finTwo_eq_single_one_iff d).1 h).2)]

/-! ### The axis embeddings of a univariate power series -/

/-- `embedDoubleLaurent (f(z₁)) = (f : R⸨X⸩)` embedded as an inner constant: the `z₁`-axis
embedding `PowerSeries.toMvPowerSeries 0` of `f` maps to `C (f : R⸨X⸩)`. -/
theorem embedDoubleLaurent_toMvPowerSeries_zero (f : R⟦X⟧) :
    embedDoubleLaurent (f.toMvPowerSeries (0 : Fin 2)) = HahnSeries.C (f : R⸨X⸩) := by
  refine embedDoubleLaurent_of_ofDoubleLaurent (fun n hn => ?_) (fun n g hg => ?_) ?_
  · rw [C_apply, coeff_single_of_ne (ne_of_lt hn)]
  · rw [C_apply]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [coeff_single_same, PowerSeries.coeff_coe, ite_eq_left hg]
    · rw [coeff_single_of_ne hn, coeff_zero]
  · refine MvPowerSeries.ext fun d => ?_
    rw [coeff_ofDoubleLaurent, C_apply]
    rcases eq_or_ne (d 1) 0 with h1 | h1
    · have hrhs : MvPowerSeries.coeff d (f.toMvPowerSeries (0 : Fin 2))
          = PowerSeries.coeff (d 0) f := by
        conv_lhs => rw [(finTwo_eq_single_zero_axis_iff d).2 h1]
        rw [PowerSeries.coeff_toMvPowerSeries_single]
      rw [hrhs, coeff_single, ite_eq_left (by exact_mod_cast h1), PowerSeries.coeff_coe,
        ite_eq_right (by exact_mod_cast (Int.natCast_nonneg (d 0)).not_gt), Int.natAbs_natCast]
    · have hrhs : MvPowerSeries.coeff d (f.toMvPowerSeries (0 : Fin 2)) = 0 :=
        PowerSeries.coeff_toMvPowerSeries_of_ne _ _
          (fun h => h1 ((finTwo_eq_single_zero_axis_iff d).1 h))
      rw [hrhs, coeff_single, ite_eq_right (by exact_mod_cast h1), coeff_zero]

/-- `embedDoubleLaurent (f(z₂))` embedded along the outer variable: the `z₂`-axis embedding
`PowerSeries.toMvPowerSeries 1` of `f` maps to `map C` of its coercion `(f : R⸨X⸩)`. -/
theorem embedDoubleLaurent_toMvPowerSeries_one (f : R⟦X⟧) :
    embedDoubleLaurent (f.toMvPowerSeries (1 : Fin 2))
      = (f : R⸨X⸩).map (HahnSeries.C : R →+* R⸨X⸩) := by
  refine embedDoubleLaurent_of_ofDoubleLaurent (fun n hn => ?_) (fun n g hg => ?_) ?_
  · rw [map_coeff, PowerSeries.coeff_coe, ite_eq_left hn, map_zero]
  · rw [map_coeff, C_apply, coeff_single_of_ne (ne_of_lt hg)]
  · refine MvPowerSeries.ext fun d => ?_
    rw [coeff_ofDoubleLaurent, map_coeff, C_apply]
    rcases eq_or_ne (d 0) 0 with h0 | h0
    · have hrhs : MvPowerSeries.coeff d (f.toMvPowerSeries (1 : Fin 2))
          = PowerSeries.coeff (d 1) f := by
        conv_lhs => rw [(finTwo_eq_single_one_axis_iff d).2 h0]
        rw [PowerSeries.coeff_toMvPowerSeries_single]
      rw [hrhs, coeff_single, ite_eq_left (by exact_mod_cast h0), PowerSeries.coeff_coe,
        ite_eq_right (by exact_mod_cast (Int.natCast_nonneg (d 1)).not_gt), Int.natAbs_natCast]
    · have hrhs : MvPowerSeries.coeff d (f.toMvPowerSeries (1 : Fin 2)) = 0 :=
        PowerSeries.coeff_toMvPowerSeries_of_ne _ _
          (fun h => h0 ((finTwo_eq_single_one_axis_iff d).1 h))
      rw [hrhs, coeff_single, ite_eq_right (by exact_mod_cast h0)]

end HahnSeries

/-! ### Weierstrass specialisations to the bivariate coordinates -/

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- `embedDoubleLaurent (X 0) = z₁`: the inner variable maps to the inner uniformiser `biZ₁`. -/
theorem embedDoubleLaurent_biZ₁ :
    HahnSeries.embedDoubleLaurent (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) = W.biZ₁ := by
  rw [HahnSeries.embedDoubleLaurent_X_zero, biZ₁, cConstRingHom]

/-- `embedDoubleLaurent (X 1) = z₂`: the outer variable maps to the outer uniformiser `biZ₂`. -/
theorem embedDoubleLaurent_biZ₂ :
    HahnSeries.embedDoubleLaurent (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = W.biZ₂ := by
  rw [HahnSeries.embedDoubleLaurent_X_one, biZ₂]

/-- `embedDoubleLaurent (w(z₁)) = w₁`: the inner `w`-embedding maps to `biW₁`. -/
theorem embedDoubleLaurent_biW₁ :
    HahnSeries.embedDoubleLaurent (W.formalW.toMvPowerSeries (0 : Fin 2)) = W.biW₁ := by
  rw [HahnSeries.embedDoubleLaurent_toMvPowerSeries_zero W.formalW, biW₁, cConstRingHom]

/-- `embedDoubleLaurent (w(z₂)) = w₂`: the outer `w`-embedding maps to `biW₂`. -/
theorem embedDoubleLaurent_biW₂ :
    HahnSeries.embedDoubleLaurent (W.formalW.toMvPowerSeries (1 : Fin 2)) = W.biW₂ := by
  rw [HahnSeries.embedDoubleLaurent_toMvPowerSeries_one W.formalW, biW₂, cLaurentRingHom,
    HahnSeries.mapRingHom_apply]

end WeierstrassCurve
