/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.BooleanAnalysis.Fibers.Internal
public import Tengoku

/-!
# Density and coordinate-resampling identities

Uniform cube densities normalize probability masses. Completing a selected
pattern identifies the fraction of a fiber with its resampling probability.
These identities connect Korten's entropy and light-patterns lemmas.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
@isnad1 id=eq.0h3v.s7.96f16b2fa946 from=translated src=- shape=50e46de2 vocab=1a6e0bdf
-/
theorem expect_restrict_coordinates_internal (s : ι → Bool) (f : ({i // s i = true} → Bool) → ℝ) :
    (𝔼 x : ι → Bool, f (fun i => x i)) = 𝔼 x, f x := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => s i = true) (fun _ => Bool)
  rw [← Fintype.expect_equiv e.symm (fun z => f (fun i => e.symm z i)) _
    (fun _ => rfl)]
  rw [← univ_product_univ, expect_product]
  have he (a : {i // s i = true} → Bool) (b : {i // s i ≠ true} → Bool) :
      (fun i : {i // s i = true} => e.symm (a, b) i) = a := by
    funext i
    simp [e, Equiv.piEquivPiSubtypeProd, i.property]
  simp_rw [he, Fintype.expect_const]

omit [Fintype ι] [DecidableEq ι] in
/--
@isnad1 id=eq.0h4v.s5.9f4852dd1448 from=translated src=- shape=b977dcd5 vocab=5ab4a6ff
-/
theorem resample_eq_completePattern_internal (s x y : ι → Bool) :
    resample s x y = completePattern s x (fun i => y i) := by
  funext i
  by_cases hi : s i = true <;> simp [resample, completePattern, hi]

/--
@isnad1 id=eq.0h4v.s7.5faa11d07592 from=translated src=- shape=4c803172 vocab=1265f998
-/
theorem coordinateDensity_eq_expect_internal (X : Finset (ι → Bool)) (s x : ι → Bool) :
    coordinateDensity X s x = 𝔼 y, if resample s x y ∈ X then (1 : ℝ) else 0 := by
  simp_rw [resample_eq_completePattern_internal]
  rw [expect_restrict_coordinates_internal s
    (fun z => if completePattern s x z ∈ X then (1 : ℝ) else 0)]
  simp [coordinateDensity, coordinateFiber, Fintype.expect_eq_sum_div_card]

/--
@isnad1 id=eq.1h2v.s6.05a61fd6583c from=translated src=- shape=600c64b6 vocab=cf92f447
-/
theorem expect_uniformDensity_internal {X : Finset (ι → Bool)} (hX : X.Nonempty) :
    (𝔼 x, uniformDensity X x) = 1 := by
  unfold uniformDensity
  rw [Fintype.expect_eq_sum_div_card, ← mul_sum, sum_uniformMass_internal hX]
  simp

omit [DecidableEq ι] in
/--
@isnad1 id=le.2h4v.s5.79210b917058 from=translated src=- shape=e19711db vocab=e11c6113
-/
theorem uniformDensity_le_rpow_internal {X : Finset (ι → Bool)} (hX : X.Nonempty)
    {k : ℝ} (hk : uniformDeficit X ≤ k) (x : ι → Bool) :
    uniformDensity X x ≤ (2 : ℝ) ^ k := by
  have hproduct : (2 : ℝ) ^ Fintype.card ι * (2 : ℝ) ^ (k - Fintype.card ι) =
      (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  exact (mul_le_mul_of_nonneg_left (uniformMass_le_rpow_internal hX hk x) (by positivity)).trans_eq
    hproduct

omit [DecidableEq ι] in
/--
@isnad1 id=eq.1h3v.s6.ce8b4259159f from=translated src=- shape=37e14dfc vocab=38eba970
-/
theorem uniformDensity_eq_deficit_internal {X : Finset (ι → Bool)} (hX : X.Nonempty)
    (z : ι → Bool) :
    uniformDensity X z = (2 : ℝ) ^ uniformDeficit X * (if z ∈ X then 1 else 0) := by
  by_cases hz : z ∈ X
  · simp only [uniformDensity, uniformMass, ite_eq_left hz, mul_one, mul_one_div]
    rw [card_eq_rpow_sub_uniformDeficit_internal hX, ← Real.rpow_natCast,
      ← Real.rpow_sub (by norm_num)]
    congr 1
    ring
  · simp [uniformDensity, uniformMass, hz]

end Complexity.BooleanAnalysis
