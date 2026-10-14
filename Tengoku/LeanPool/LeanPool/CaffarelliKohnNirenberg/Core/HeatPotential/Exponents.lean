/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku

/-!
# Exponents

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

noncomputable section

namespace CKN.Core.HeatPotential

/--
@isnad1 id=eq.1h2v.s6.673d2226d11f from=translated src=- shape=b251189b vocab=b3e101fc
-/
lemma heat_morrey_theta_zero_identity {γ θ₀ : ℝ}
    (hθ₀ : 1 / θ₀ = (2 - γ) / 5) :
    2 - 5 / θ₀ = γ := by
  rw [div_eq_mul_inv] at hθ₀ ⊢
  nlinarith only [hθ₀]

/--
@isnad1 id=eq.1h2v.s6.ce6dae3bddd9 from=translated src=- shape=b251189b vocab=b3e101fc
-/
lemma heat_morrey_theta_one_identity {γ θ₁ : ℝ}
    (hθ₁ : 1 / θ₁ = (1 - γ) / 5) :
    1 - 5 / θ₁ = γ := by
  rw [div_eq_mul_inv] at hθ₁ ⊢
  nlinarith only [hθ₁]

/--
@isnad1 id=lt.1h1v.s5.77b72bbd0e1d from=translated src=- shape=b6e2f968 vocab=9bc4a636
-/
lemma heat_morrey_geometric_ratio_lt_one {γ : ℝ}
    (hγ : γ < 1) :
    (2 : ℝ) ^ (γ - 1) < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hγ])

/--
@isnad1 id=le.0h1v.s5.5c55fcea0f7a from=translated src=- shape=a81a58b7 vocab=66814e92
-/
lemma heat_morrey_geometric_ratio_nonneg {γ : ℝ} :
    0 ≤ (2 : ℝ) ^ (γ - 1) := by
  positivity

/--
@isnad1 id=eq.1h1v.s6.adfc03553cde from=translated src=- shape=ddc6b11e vocab=80a4718d
-/
lemma heat_morrey_geometric_series {γ : ℝ} (hγ : γ < 1) :
    ∑' j : ℕ, (2 : ℝ) ^ ((j : ℝ) * (γ - 1)) =
      (1 - (2 : ℝ) ^ (γ - 1))⁻¹ := by
  let q : ℝ := (2 : ℝ) ^ (γ - 1)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact heat_morrey_geometric_ratio_lt_one hγ
  have hsum := hasSum_geometric_of_lt_one hq0 hq1
  have hterm : (fun j : ℕ => (2 : ℝ) ^ ((j : ℝ) * (γ - 1))) =
      (fun j : ℕ => q ^ j) := by
    funext j
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hterm]
  simpa [q] using hsum.tsum_eq

end CKN.Core.HeatPotential
