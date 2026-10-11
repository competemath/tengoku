import Tengoku.OpenaiMath.OAI.Combinatorics.SparsestCut.DirectionAsymptotics

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.DirectionFamily
open Directions DirectionInterpolation DirectionAsymptotics GaussianTools FiniteNets
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

lemma normBounds_of_not_bad {g : Fin N → E} (hg : g ∉ normBad) (i : Fin N) :
    (m : ℝ)/4 ≤ ‖g i‖^2 ∧ ‖g i‖^2 ≤ 4*(m : ℝ) := by
  constructor
  · by_contra h; exact hg ⟨i, Or.inl (lt_of_not_ge h)⟩
  · by_contra h; exact hg ⟨i, Or.inr (lt_of_not_ge h)⟩

lemma inner_empiricalSin (g : Fin N → E) (v w : E) :
    inner ℝ (empiricalSin g w - Real.exp (-‖w‖^2/2) • w) v =
      (∑ i, inner ℝ (g i) v * Real.sin (inner ℝ (g i) w))/(N : ℝ) -
      inner ℝ w v * Real.exp (-‖w‖^2/2) := by
  simp only [empiricalSin, inner_sub_left, inner_smul_left, conj_trivial,
    sum_inner, div_eq_mul_inv]
  congr 1
  · rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · ring

lemma net_fourier_scalar (hm : 0 < m) {g : Fin N → E} (hg : g ∉ normBad)
    {u : ℝ} (v w : E) (hv : ‖v‖ = 1) (hf : g ∉ fourierBad u v w) :
    |inner ℝ (empiricalSin g w - Real.exp (-‖w‖^2/2) • w) v| ≤
      u + 16*Real.exp (-(m : ℝ)/12) := by
  have hsample (i : Fin N) : fourierSummand v w (g i) =
      inner ℝ (g i) v * Real.sin (inner ℝ (g i) w) := by
    dsimp only [fourierSummand, covarianceSummand, truncate]
    exact Set.indicator_of_mem (show g i ∈ {z : E | ‖z‖^2 ≤ 4*(m : ℝ)} from
      (normBounds_of_not_bad hg i).2) _
  have hdev : |(∑ i, fourierSummand v w (g i))/(N : ℝ) -
      ∫ z, fourierSummand v w z ∂stdGaussian E| ≤ u := le_of_not_gt hf
  simp_rw [hsample] at hdev
  rw [inner_empiricalSin]
  have hb := truncation_fourier_bias (show 1 ≤ m by omega) v w hv
  exact (abs_sub_le _ (∫ z, fourierSummand v w z ∂stdGaussian E) _).trans (add_le_add hdev hb)

lemma net_covariance_scalar {g : Fin N → E} (hg : g ∉ normBad)
    (v : E) (hv : ‖v‖ = 1) (hf : g ∉ covarianceBad v) :
    |empiricalCov g v - 1| ≤ 1/8 + 16*Real.exp (-(m : ℝ)/12) := by
  have hsample (i : Fin N) : covarianceSummand v (g i) = (inner ℝ v (g i))^2 := by
    dsimp only [fourierSummand, covarianceSummand, truncate]
    exact Set.indicator_of_mem (show g i ∈ {z : E | ‖z‖^2 ≤ 4*(m : ℝ)} from
      (normBounds_of_not_bad hg i).2) _
  have hdev : |(∑ i, covarianceSummand v (g i))/(N : ℝ) -
      ∫ z, covarianceSummand v z ∂stdGaussian E| ≤ 1/8 := le_of_not_gt hf
  simp_rw [hsample] at hdev
  exact (abs_sub_le _ (∫ z, covarianceSummand v z ∂stdGaussian E) _).trans
    (add_le_add hdev (truncation_covariance_bias v hv))

lemma source_nets (hm : 2 ≤ m) : ∃ V W : Finset E,
    (∀ v ∈ V, ‖v‖ = 1) ∧
    (V.card : ℝ) ≤ Real.exp (6*(m : ℝ)^2) ∧
    (W.card : ℝ) ≤ Real.exp (48*(m : ℝ)^2) ∧
    (∀ v : E, ‖v‖ = 1 → ∃ v' ∈ V, ‖v-v'‖ ≤ 1/(m : ℝ)^3) ∧
    (∀ w : E, ‖w‖ ≤ (m : ℝ)^42 → ∃ w' ∈ W, ‖w-w'‖ ≤ 1/(m : ℝ)^3) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hδ : (0 : ℝ) < 1/(m : ℝ)^4 := by positivity
  have hid : (m : ℝ) * (1/(m : ℝ)^4) = 1/(m : ℝ)^3 := by field_simp
  obtain ⟨V,hV,hVc,hVnet⟩ := exists_coordinate_net (K := m^4) hδ {v : E | ‖v‖ = 1} (by
    intro v hv
    change ‖v‖ = 1 at hv
    rw [hv, Nat.cast_pow]
    simp [hm0.ne'])
  obtain ⟨W,hW,hWc,hWnet⟩ := exists_coordinate_net (K := m^46) hδ {w : E | ‖w‖ ≤ (m : ℝ)^42} (by
    intro w hw
    change ‖w‖ ≤ (m : ℝ)^42 at hw
    have he : (((m^46 : ℕ) : ℝ))*(1/(m : ℝ)^4) = (m : ℝ)^42 := by push_cast; field_simp
    rwa [he])
  refine ⟨V,W,hV,?_,?_,?_,?_⟩
  · exact (Nat.cast_le.mpr hVc).trans (by simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, show (4+2 : ℝ) = 6 by norm_num] using grid_card_bound m 4 hm)
  · exact (Nat.cast_le.mpr hWc).trans (by simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, show (46+2 : ℝ) = 48 by norm_num] using grid_card_bound m 46 hm)
  · intro v hv; simpa only [hid] using hVnet v hv
  · intro w hw; simpa only [hid] using hWnet w hw

lemma badCount_le_of_imp {A B : Set (Fin N → E)} (g : Fin S → Fin N → E)
    (h : ∀ s, g s ∈ A → g s ∈ B) : badCount A g ≤ badCount B g := by
  classical
  apply Finset.card_le_card
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact h s hs

lemma good_chart_interpolation {N S : ℕ} (g : Fin S → Fin N → E)
    (hg : ∀ s, g s ∉ normBad) {v v' : E} {ρ q q' : ℝ}
    (hd : ‖v-v'‖ ≤ ρ) (hq : q+2*Real.sqrt m*ρ ≤ q') :
    badCount (projectionBad q' v) g ≤ badCount (projectionBad q v') g := by
  apply badCount_le_of_imp g
  intro s hs
  by_contra hn
  obtain ⟨i,hi⟩ := hs
  have hp : |inner ℝ v' (g s i)| ≤ q := by
    by_contra h; exact hn ⟨i,lt_of_not_ge h⟩
  have hgn : ‖g s i‖ ≤ 2*Real.sqrt m := by
    have := (normBounds_of_not_bad (hg s) i).2
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m), Real.sqrt_nonneg (m : ℝ), norm_nonneg (g s i)]
  have hh := (projection_interpolate hgn (by positivity) hd hp).trans hq
  exact not_lt_of_ge hh hi

structure Family (m : ℕ) where
  g : Fin (m^3) → Fin (m^6) → EuclideanSpace ℝ (Fin m)
  norms : ∀ s i, Real.sqrt m/2 ≤ ‖g s i‖ ∧ ‖g s i‖ ≤ 2*Real.sqrt m
  nonparallel : ∀ s a b, a ≠ b → ∀ t : ℝ, g s a ≠ t • g s b
  covariance : ∀ s v, ‖v‖ = 1 → 1/2 ≤ empiricalCov (g s) v ∧ empiricalCov (g s) v ≤ 2
  fourier : ∀ s w, ‖w‖ ≤ (m : ℝ)^42 →
    ‖empiricalSin (g s) w - Real.exp (-‖w‖^2/2) • w‖ ≤ 2/Real.sqrt m
  good : ∀ v, ‖v‖ = 1 →
    (badCount (projectionBad (11*Real.sqrt (Real.log m)) v) g : ℝ) ≤ ((m^3 : ℕ) : ℝ)/2

end UniformSparsestCut.DirectionFamily

end

end OAI
