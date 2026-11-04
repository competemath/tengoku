/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.RelativeRiemannRoch.GrRingB4

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# B7 (algebra): the map induced on `Gr` by a filtration-shifting linear map

`R₁`, `R₂` `ℚ`-algebras with ring filtrations `Φ₁`, `Φ₂`, `F : R₁ →ₗ[ℚ] R₂` with
`F (Φ₁.Fⁿ) ⊆ Φ₂.F^{n-d}` for an integer `d` (SGA6 VIII 3.2 for `F = f_!`, `d` the relative
dimension).  Then `F` induces `B7.fGr : Gr_{≤D₁}(R₁) → Gr_{≤D₂}(R₂)` (`D₂ + d ≤ D₁`) with
`fGr [a] = [F a]` for `a ∈ Φ₁.Fⁿ` (class in degree `n - d`), and `fGr [a] = 0` if `n < d`.
It is defined at the level of the Rees rings by the coefficient shift `∑ aₙ uⁿ ↦ ∑ F(aₙ) u^{n-d}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace B7

open B4 PowerSeries

section Push

variable {R₁ R₂ : Type*} [CommRing R₁] [Algebra ℚ R₁] [CommRing R₂] [Algebra ℚ R₂]
  {Φ₁ : RingFilt R₁} {Φ₂ : RingFilt R₂} (F : R₁ →ₗ[ℚ] R₂) (d : ℤ)

/-- the coefficient shift `∑ aₙ uⁿ ↦ ∑ F(aₙ) u^{n-d}`-/
def pushSeries (r : R₁⟦X⟧) : R₂⟦X⟧ :=
  PowerSeries.mk fun m => if 0 ≤ (m : ℤ) + d then F (coeff (((m : ℤ) + d).toNat) r) else 0

/--
@isnad1 id=eq.0h6v.s9.188293120631 from=translated src=- shape=2277f8b9 vocab=85a5485b
-/
theorem coeff_pushSeries (r : R₁⟦X⟧) (m : ℕ) :
    coeff m (pushSeries F d r) =
      if 0 ≤ (m : ℤ) + d then F (coeff (((m : ℤ) + d).toNat) r) else 0 := by
  simp [pushSeries]

variable (hF : ∀ (n : ℕ) (a : R₁), a ∈ Φ₁.F n → F a ∈ Φ₂.F (((n : ℤ) - d).toNat))

include hF in
/--
@isnad1 id=mem.1h8v.s9.c13e3343a52a from=translated src=- shape=da3e1215 vocab=6df91c53
-/
theorem pushSeries_mem (r : ReesPS Φ₁) : ∀ m, coeff m (pushSeries F d (r : R₁⟦X⟧)) ∈ Φ₂.F m := by
  intro m
  rw [coeff_pushSeries]
  split_ifs with h
  · have := hF (((m : ℤ) + d).toNat) _ (r.2 _)
    have e : ((((m : ℤ) + d).toNat : ℤ) - d).toNat = m := by omega
    rwa [e] at this
  · exact Ideal.zero_mem _

/-- the Rees-level push-forward-/
def reesPush : ReesPS Φ₁ →ₗ[ℚ] ReesPS Φ₂ where
  toFun r := ⟨pushSeries F d (r : R₁⟦X⟧), pushSeries_mem F d hF r⟩
  map_add' a b := by
    apply Subtype.ext
    ext m
    simp only [Subalgebra.coe_add, coeff_pushSeries, map_add]
    split_ifs <;> simp
  map_smul' c a := by
    apply Subtype.ext
    ext m
    show coeff m (pushSeries F d (c • (a : R₁⟦X⟧))) = c • coeff m (pushSeries F d (a : R₁⟦X⟧))
    rw [coeff_pushSeries, coeff_pushSeries]
    show (if 0 ≤ (m : ℤ) + d then F (c • coeff _ (a : R₁⟦X⟧)) else 0) = _
    split_ifs
    · rw [map_smul]
    · rw [smul_zero]

/--
@isnad1 id=eq.1h8v.s11.4f67e00293c0 from=translated src=- shape=829e32de vocab=1519104c
-/
theorem reesPush_coeff (r : ReesPS Φ₁) (m : ℕ) :
    coeff m ((reesPush F d hF r : ReesPS Φ₂) : R₂⟦X⟧) =
      if 0 ≤ (m : ℤ) + d then F (coeff (((m : ℤ) + d).toNat) (r : R₁⟦X⟧)) else 0 :=
  coeff_pushSeries F d _ m

include hF in
/--
@isnad1 id=mem.3h9v.s11.0938ab24a39b from=translated src=- shape=724804b7 vocab=411214b4
-/
theorem reesPush_mem_ideal {D₁ D₂ : ℕ} (hD : (D₂ : ℤ) + d ≤ D₁) {r : ReesPS Φ₁}
    (hr : r ∈ ReesIdeal Φ₁ D₁) : reesPush F d hF r ∈ ReesIdeal Φ₂ D₂ := by
  intro m hm
  rw [reesPush_coeff]
  split_ifs with h
  · have hn : ((m : ℤ) + d).toNat ≤ D₁ := by omega
    have := hF (((m : ℤ) + d).toNat + 1) _ (hr _ hn)
    have e : (((((m : ℤ) + d).toNat + 1 : ℕ) : ℤ) - d).toNat = m + 1 := by omega
    rwa [e] at this
  · exact Ideal.zero_mem _

/-- **The map `Gr(F)`** induced by `F` on the truncated associated graded rings.-/
def fGr {D₁ D₂ : ℕ} (hD : (D₂ : ℤ) + d ≤ D₁) : GrT Φ₁ D₁ →ₗ[ℚ] GrT Φ₂ D₂ :=
  (Submodule.Quotient.restrictScalarsEquiv ℚ (ReesIdeal Φ₂ D₂)).toLinearMap ∘ₗ
    (Submodule.mapQ _ _ (reesPush F d hF) (fun r hr => reesPush_mem_ideal F d hF hD hr)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv ℚ (ReesIdeal Φ₁ D₁)).symm.toLinearMap

/--
@isnad1 id=eq.2h9v.s13.282e190039d2 from=translated src=- shape=ba242dc9 vocab=7284b61b
-/
theorem fGr_mk {D₁ D₂ : ℕ} (hD : (D₂ : ℤ) + d ≤ D₁) (r : ReesPS Φ₁) :
    fGr F d hF hD (Ideal.Quotient.mk (ReesIdeal Φ₁ D₁) r : ReesPS Φ₁ ⧸ ReesIdeal Φ₁ D₁) =
      (Ideal.Quotient.mk (ReesIdeal Φ₂ D₂) (reesPush F d hF r) : ReesPS Φ₂ ⧸ ReesIdeal Φ₂ D₂) :=
  rfl

/--
@isnad1 id=eq.2h8v.s10.9cbb844cea03 from=translated src=- shape=7c89e749 vocab=e84c8728
-/
theorem reesPush_gclPS_of_le {n : ℕ} (hnd : d ≤ n) (a : Φ₁.F n) :
    reesPush F d hF (gclPS n a) = gclPS (((n : ℤ) - d).toNat) ⟨F a, hF n a a.2⟩ := by
  apply Subtype.ext
  ext m
  rw [reesPush_coeff]
  show _ = coeff m (C (F (a : R₁)) * X ^ (((n : ℤ) - d).toNat))
  rw [coeff_C_mul_X_pow]
  show (if 0 ≤ (m : ℤ) + d then F (coeff _ (C (a : R₁) * X ^ n)) else 0) = _
  rw [coeff_C_mul_X_pow]
  by_cases h : 0 ≤ (m : ℤ) + d
  · rw [ite_eq_left h]
    by_cases hmn : m = ((n : ℤ) - d).toNat
    · have : ((m : ℤ) + d).toNat = n := by omega
      rw [ite_eq_left this, ite_eq_left hmn]
    · have : ¬ ((m : ℤ) + d).toNat = n := by omega
      rw [ite_eq_right this, ite_eq_right hmn, map_zero]
  · rw [ite_eq_right h]
    have : ¬ m = ((n : ℤ) - d).toNat := by omega
    rw [ite_eq_right this]

/--
@isnad1 id=eq.2h8v.s10.346a35f651d2 from=translated src=- shape=7724e0fb vocab=8ef81847
-/
theorem reesPush_gclPS_of_lt {n : ℕ} (hnd : (n : ℤ) < d) (a : Φ₁.F n) :
    reesPush F d hF (gclPS n a) = 0 := by
  apply Subtype.ext
  ext m
  rw [reesPush_coeff]
  show _ = coeff m (0 : R₂⟦X⟧)
  rw [map_zero]
  split_ifs with h
  · show F (coeff _ (C (a : R₁) * X ^ n)) = 0
    rw [coeff_C_mul_X_pow, ite_eq_right (by omega), map_zero]
  · rfl

/-- `Gr(F) [a] = [F a]` (degree `n - d`) for `d ≤ n`
@isnad1 id=eq.3h10v.s9.eb95620dbb92 from=translated src=- shape=ed3fc367 vocab=cf554fc9
-/
theorem fGr_gcl_of_le {D₁ D₂ : ℕ} (hD : (D₂ : ℤ) + d ≤ D₁) {n : ℕ} (hnd : d ≤ n) (a : Φ₁.F n) :
    fGr F d hF hD (gcl D₁ n a) = gcl D₂ (((n : ℤ) - d).toNat) ⟨F a, hF n a a.2⟩ := by
  show fGr F d hF hD (Ideal.Quotient.mk (ReesIdeal Φ₁ D₁) (gclPS n a) :
    ReesPS Φ₁ ⧸ ReesIdeal Φ₁ D₁) = _
  rw [fGr_mk, reesPush_gclPS_of_le F d hF hnd]
  rfl

/-- `Gr(F) [a] = 0` for `n < d`
@isnad1 id=eq.3h10v.s9.d4fef7772092 from=translated src=- shape=b0ecc171 vocab=fe9baa89
-/
theorem fGr_gcl_of_lt {D₁ D₂ : ℕ} (hD : (D₂ : ℤ) + d ≤ D₁) {n : ℕ} (hnd : (n : ℤ) < d)
    (a : Φ₁.F n) : fGr F d hF hD (gcl D₁ n a) = 0 := by
  show fGr F d hF hD (Ideal.Quotient.mk (ReesIdeal Φ₁ D₁) (gclPS n a) :
    ReesPS Φ₁ ⧸ ReesIdeal Φ₁ D₁) = _
  rw [fGr_mk, reesPush_gclPS_of_lt F d hF hnd]
  exact map_zero (Ideal.Quotient.mk (ReesIdeal Φ₂ D₂))

end Push

end B7
