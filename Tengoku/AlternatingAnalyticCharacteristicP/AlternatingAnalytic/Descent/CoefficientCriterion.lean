import Tengoku.Seed.Analysis.Analytic.Constructions
import Tengoku.Seed.Analysis.Normed.Operator.LinearIsometry
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.ClosedSubspaceCoefficients

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The coefficient descent criterion (Theorem 3.1)

Let `j : W → Z` be a linear isometry and suppose `j (f (x₀ + h)) = ∑ b_n(h, …, h)` on the ball
`‖h‖ < R`, with `sup ‖b_n‖ Rⁿ < ∞`. If the range of `j` is closed, every diagonal `b_n(h, …, h)`
lies in `j(W)`. In general, `f` is analytic at `x₀` iff the diagonals of `b` have `W`-valued
bounded multilinear representatives with a positive radius. No completeness is assumed.
-/

noncomputable section

open scoped NNReal ENNReal

namespace AlternatingAnalytic.CoefficientCriterion

variable {K : Type*} [NontriviallyNormedField K]
  {P W Z : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  [NormedAddCommGroup W] [NormedSpace K W] [NormedAddCommGroup Z] [NormedSpace K Z]

/-- A geometric bound `sup ‖p n‖ Rⁿ < ∞` gives radius at least `R`.
@isnad1 id=le.2h5v.s8.6b15f3ceb4db from=translated src=- shape=83279589 vocab=2dab9f77
-/
theorem le_radius_of_bddAbove {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (p : FormalMultilinearSeries K E F) {R : ℝ}
    (hR : 0 ≤ R) (hbound : BddAbove (Set.range fun n => ‖p n‖ * R ^ n)) :
    ENNReal.ofReal R ≤ p.radius := by
  obtain ⟨C, hC⟩ := hbound
  exact p.le_radius_of_bound C (r := R.toNNReal) fun n => by
    rw [Real.coe_toNNReal _ hR]; exact hC ⟨n, rfl⟩

/-- An ambient expansion on the ball of radius `R` is a power series expansion of `j ∘ f`.
@isnad1 id=hasfpowe.3h9v.s9.58749d3096aa from=translated src=- shape=f1695c2c vocab=fac3309f
-/
theorem hasFPowerSeriesOnBall_comp (j : W →ₗᵢ[K] Z) (f : P → W) (x₀ : P)
    (b : FormalMultilinearSeries K P Z) {R : ℝ} (hR : 0 < R)
    (hbound : BddAbove (Set.range fun n => ‖b n‖ * R ^ n))
    (hexp : ∀ h : P, ‖h‖ < R → HasSum (fun n => b n (fun _ => h)) (j (f (x₀ + h)))) :
    HasFPowerSeriesOnBall (j ∘ f) b x₀ (ENNReal.ofReal R) where
  r_le := le_radius_of_bddAbove b hR.le hbound
  r_pos := ENNReal.ofReal_pos.mpr hR
  hasSum := fun {y} hy => by
    refine hexp y ?_
    rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm,
      ENNReal.ofReal_lt_ofReal_iff hR] at hy

/-- Theorem 3.1(1): every diagonal of an ambient expansion lies in `j(W)`.
@isnad1 id=mem.4h11v.s10.75ba5c748afe from=translated src=- shape=6de13acf vocab=22b2393c
-/
theorem diagonal_mem_range (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    (f : P → W) (x₀ : P) (b : FormalMultilinearSeries K P Z) (R : ℝ) (hR : 0 < R)
    (hbound : BddAbove (Set.range fun n => ‖b n‖ * R ^ n))
    (hexp : ∀ h : P, ‖h‖ < R → HasSum (fun n => b n (fun _ => h)) (j (f (x₀ + h)))) :
    ∀ (n : ℕ) (h : P), b n (fun _ => h) ∈ Set.range j := by
  intro n h
  have hb := (hasFPowerSeriesOnBall_comp j f x₀ b hR hbound hexp).hasFPowerSeriesAt
  have hW : IsClosed ((LinearMap.range j.toLinearMap : Submodule K Z) : Set Z) := by
    rw [LinearMap.coe_range]; exact hj
  have := HasFPowerSeriesAt.diagonal_mem_closedSubspace _ hW hb
    (Filter.Eventually.of_forall fun y => ⟨f y, rfl⟩) n h
  simpa using this

/-- Two expansions of `j ∘ f` at `x₀` have the same diagonals.
@isnad1 id=eq.2h11v.s9.4983f2c6d9ef from=translated src=- shape=172191e5 vocab=4a9dfdad
-/
theorem diagonal_eq_of_hasFPowerSeriesAt (j : W →ₗᵢ[K] Z) {f : P → W} {x₀ : P}
    {b : FormalMultilinearSeries K P Z} {p : FormalMultilinearSeries K P W}
    (hb : HasFPowerSeriesAt (j ∘ f) b x₀) (hp : HasFPowerSeriesAt f p x₀) (n : ℕ) (h : P) :
    j (p n (fun _ => h)) = b n (fun _ => h) := by
  have hjp : HasFPowerSeriesAt (j ∘ f)
      (j.toContinuousLinearMap.compFormalMultilinearSeries p) x₀ := by
    obtain ⟨r, hr⟩ := hp
    exact ⟨r, j.toContinuousLinearMap.comp_hasFPowerSeriesOnBall hr⟩
  have h0 := (sub_self (j ∘ f) ▸ hb.sub hjp).apply_eq_zero n h
  rw [FormalMultilinearSeries.sub_apply, sub_apply, sub_eq_zero,
    ContinuousLinearMap.compFormalMultilinearSeries_apply] at h0
  exact h0.symm

/-- Theorem 3.1(2): `f` is analytic at `x₀` if and only if the ambient diagonals have
`W`-valued bounded multilinear representatives with a positive common radius.
@isnad1 id=iff.3h9v.s10.e02260e769a9 from=translated src=- shape=fa0ed978 vocab=468a87d4
-/
theorem analyticAt_iff (j : W →ₗᵢ[K] Z)
    (f : P → W) (x₀ : P) (b : FormalMultilinearSeries K P Z) (R : ℝ) (hR : 0 < R)
    (hbound : BddAbove (Set.range fun n => ‖b n‖ * R ^ n))
    (hexp : ∀ h : P, ‖h‖ < R → HasSum (fun n => b n (fun _ => h)) (j (f (x₀ + h)))) :
    AnalyticAt K f x₀ ↔
      ∃ (q : FormalMultilinearSeries K P W) (r : ℝ), 0 < r ∧
        (∀ (n : ℕ) (h : P), j (q n (fun _ => h)) = b n (fun _ => h)) ∧
        BddAbove (Set.range fun n => ‖q n‖ * r ^ n) := by
  have hb := (hasFPowerSeriesOnBall_comp j f x₀ b hR hbound hexp).hasFPowerSeriesAt
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨r, hr0, hrp⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.radius_pos
    obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius hrp
    exact ⟨p, r, by exact_mod_cast hr0, diagonal_eq_of_hasFPowerSeriesAt j hb hp,
      ⟨C, by rintro _ ⟨n, rfl⟩; exact hC n⟩⟩
  · rintro ⟨q, r, hr, hq, hqb⟩
    refine ⟨q, ENNReal.ofReal (min r R),
      { r_le := (ENNReal.ofReal_le_ofReal (min_le_left r R)).trans
          (le_radius_of_bddAbove q hr.le hqb)
        r_pos := ENNReal.ofReal_pos.mpr (lt_min hr hR)
        hasSum := fun {y} hy => ?_ }⟩
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm,
      ENNReal.ofReal_lt_ofReal_iff (lt_min hr hR)] at hy
    rw [← j.isEmbedding.isInducing.hasSum_iff]
    simpa [Function.comp_def, hq] using hexp y (hy.trans_le (min_le_right r R))

end AlternatingAnalytic.CoefficientCriterion
