import Tengoku.Seed.Analysis.Normed.Module.Basic
import Tengoku.Seed.Analysis.Normed.Module.RieszLemma
import Tengoku.Seed.LinearAlgebra.Multilinear.Basic
import Tengoku.Seed.Order.ConditionallyCompleteLattice.Basic
import Tengoku.Seed.Algebra.Order.Archimedean.Real.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Diagonal norms of continuous algebraic homogeneous polynomials

The diagonal `p x = b (x, …, x)` of an `n`-linear map `b` (not assumed continuous) vanishes at
zero when `n ≥ 1` and is homogeneous of degree `n`. If `p` is continuous at zero, then
`‖p x‖ ≤ D ‖x‖ ^ n` for some `D`, and the diagonal norm `sInf {D ≥ 0 | ∀ x, ‖p x‖ ≤ D ‖x‖ ^ n}`
is itself such a constant. Used in the proof of Proposition I.2.
-/

namespace AlgebraicPolynomialCZero

variable {K E Z : Type*} [NontriviallyNormedField K] [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup Z] [NormedSpace K Z] {n : ℕ}

/-- The diagonal of a multilinear map is homogeneous of degree `n`.
@isnad1 id=eq.0h7v.s9.20181cd45d09 from=translated src=- shape=4d3dcc8e vocab=76802e19
-/
theorem diag_smul (b : MultilinearMap K (fun _ : Fin n => E) Z) (c : K) (x : E) :
    b (fun _ => c • x) = c ^ n • b (fun _ => x) := by
  rw [MultilinearMap.map_smul_univ b (fun _ => c) (fun _ => x), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- The diagonal of a multilinear map of positive degree vanishes at zero.
@isnad1 id=eq.1h5v.s8.ee6da058926c from=translated src=- shape=f238a178 vocab=33783269
-/
theorem diag_zero (b : MultilinearMap K (fun _ : Fin n => E) Z) (hn : 1 ≤ n) :
    b (fun _ => (0 : E)) = 0 :=
  b.map_coord_zero (⟨0, hn⟩ : Fin n) rfl

/-- A homogeneous map of degree `n` that is continuous at zero and vanishes there is bounded by a
multiple of `‖x‖ ^ n`.
@isnad1 id=ex.3h5v.s8.aff5397860c3 from=translated src=- shape=4d1dbbd1 vocab=bb3da5c7
-/
theorem exists_diag_bound {p : E → Z} (hp : ContinuousAt p 0) (h0 : p 0 = 0)
    (hhom : ∀ (c : K) x, p (c • x) = c ^ n • p x) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖p x‖ ≤ D * ‖x‖ ^ n := by
  obtain ⟨δ, δpos, hδ⟩ := Metric.continuousAt_iff.mp hp 1 one_pos
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
  refine ⟨(δ⁻¹ * ‖c‖) ^ n, by positivity, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    rw [h0, norm_zero]
    positivity
  obtain ⟨d, hd, hdx, -, hd'⟩ := rescale_to_shell hc δpos hx
  have h1 : ‖p (d • x)‖ < 1 := by
    simpa [h0, dist_eq_norm] using hδ (x := d • x) (by simpa [dist_eq_norm] using hdx)
  have hpx : p x = (d ^ n)⁻¹ • p (d • x) := by
    rw [hhom, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hd), one_smul]
  rw [hpx, norm_smul, norm_inv, norm_pow]
  calc (‖d‖ ^ n)⁻¹ * ‖p (d • x)‖ ≤ (‖d‖ ^ n)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h1.le (by positivity)
    _ = ‖d‖⁻¹ ^ n := by rw [mul_one, inv_pow]
    _ ≤ (δ⁻¹ * ‖c‖ * ‖x‖) ^ n := pow_le_pow_left₀ (by positivity) hd' n
    _ = (δ⁻¹ * ‖c‖) ^ n * ‖x‖ ^ n := by rw [mul_pow]

/-- The diagonal norm is nonnegative.
@isnad1 id=le.0h4v.s6.b5c684162860 from=translated src=- shape=8f21d30f vocab=28f23c68
-/
theorem diagNorm_nonneg (p : E → Z) :
    0 ≤ sInf {D : ℝ | 0 ≤ D ∧ ∀ x, ‖p x‖ ≤ D * ‖x‖ ^ n} :=
  Real.sInf_nonneg fun _ hD => hD.1

/-- When some admissible constant exists, the diagonal norm is itself admissible.
@isnad1 id=le.2h5v.s7.52dda8966e27 from=translated src=- shape=f248a5e7 vocab=28f23c68
-/
theorem norm_le_diagNorm_mul {p : E → Z} (h0 : p 0 = 0)
    (hne : ∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖p x‖ ≤ D * ‖x‖ ^ n) (x : E) :
    ‖p x‖ ≤ sInf {D : ℝ | 0 ≤ D ∧ ∀ x, ‖p x‖ ≤ D * ‖x‖ ^ n} * ‖x‖ ^ n := by
  by_cases hx : x = 0
  · subst hx
    rw [h0, norm_zero]
    exact mul_nonneg (diagNorm_nonneg p) (pow_nonneg (norm_nonneg _) _)
  have hpos : 0 < ‖x‖ ^ n := pow_pos (norm_pos_iff.mpr hx) n
  rw [← div_le_iff₀ hpos]
  exact le_csInf hne fun D hD => (div_le_iff₀ hpos).mpr (hD.2 x)

end AlgebraicPolynomialCZero
