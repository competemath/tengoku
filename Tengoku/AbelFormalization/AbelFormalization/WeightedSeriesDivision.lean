import Tengoku.AbelFormalization.AbelFormalization.WeightedSeriesBanach
import Tengoku.AbelFormalization.AbelFormalization.BanachDivision
import Tengoku.Seed.Topology.Algebra.InfiniteSum.ENNReal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Convergent coefficient-tail division

Coefficient tails preserve weighted absolute summability and are bounded
linear operators on the actual weighted-series Banach algebra. They divide
the corresponding coordinate monomials exactly. Neumann division therefore
applies to series whose weighted coefficient distance from that monomial is
small enough. The remainder has no coefficients of sufficiently high degree
in the selected coordinate.

The conclusions concern weighted convergent coefficient series. Identifying
these series with analytic germs and obtaining the required smallness from
analytic regularity are separate obligations.
-/

noncomputable section

namespace AbelFormalization

variable {σ : Type*}

/--
@isnad1 id=eq.0h4v.s5.ae65a342d274 from=translated src=- shape=8c06bd98 vocab=03642aa1
-/
@[simp]
theorem multiRadiusWeight_single (ρ : σ → ℝ) (i : σ) (n : ℕ) :
    multiRadiusWeight ρ (Finsupp.single i n) = ρ i ^ n :=
  Finsupp.prod_single_index (pow_zero _)

/-- Every monomial has finite weighted coefficient support.
@isnad1 id=weighted.0h4v.s6.b85022035c5c from=translated src=- shape=f1a67d37 vocab=07966cbe
-/
theorem weightedCoeffSummable_monomial (ρ : σ → ℝ) (d : σ →₀ ℕ) (c : ℝ) :
    WeightedCoeffSummable ρ (MvPowerSeries.monomial d c) := by
  classical
  apply summable_of_ne_finset_zero (s := {d})
  intro k hk
  have hkd : k ≠ d := by simpa only [Finset.mem_singleton] using hk
  simp [MvPowerSeries.coeff_monomial, hkd]

/--
@isnad1 id=eq.0h4v.s6.1f6ab90afdbd from=translated src=- shape=44affd58 vocab=220ec296
-/
@[simp]
theorem weightedCoeffNorm_monomial (ρ : σ → ℝ) (d : σ →₀ ℕ) (c : ℝ) :
    weightedCoeffNorm ρ (MvPowerSeries.monomial d c) = ‖c‖ * multiRadiusWeight ρ d := by
  classical
  unfold weightedCoeffNorm
  rw [tsum_eq_single d (fun k hk => by simp [MvPowerSeries.coeff_monomial, hk])]
  simp [MvPowerSeries.coeff_monomial_same]

/-- The formal coefficient tail by an arbitrary multiindex.-/
def mvPowerSeriesTail (d : σ →₀ ℕ) : MvPowerSeries σ ℝ →ₗ[ℝ] MvPowerSeries σ ℝ where
  toFun f := fun k => MvPowerSeries.coeff (k + d) f
  map_add' f g := by
    apply MvPowerSeries.ext
    intro k
    exact map_add (MvPowerSeries.coeff (k + d)) f g
  map_smul' c f := by
    apply MvPowerSeries.ext
    intro k
    exact MvPowerSeries.coeff_smul f (k + d) c

/--
@isnad1 id=eq.0h4v.s8.99810cd32702 from=translated src=- shape=f097b3c1 vocab=58d51965
-/
@[simp]
theorem coeff_mvPowerSeriesTail (d k : σ →₀ ℕ) (f : MvPowerSeries σ ℝ) :
    MvPowerSeries.coeff k (mvPowerSeriesTail d f) = MvPowerSeries.coeff (k + d) f := rfl

/-- Shifting the coefficient index removes exactly the monomial's weight.
@isnad1 id=eq.1h5v.s8.8fcd0fe1a844 from=translated src=- shape=4c9f046d vocab=20ef4d13
-/
theorem weightedCoeff_tail_identity (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (d k : σ →₀ ℕ) (f : MvPowerSeries σ ℝ) :
    ‖MvPowerSeries.coeff k (mvPowerSeriesTail d f)‖ * multiRadiusWeight ρ k =
      (‖MvPowerSeries.coeff (k + d) f‖ * multiRadiusWeight ρ (k + d)) /
        multiRadiusWeight ρ d := by
  rw [coeff_mvPowerSeriesTail, multiRadiusWeight_add, ← mul_assoc,
    mul_div_cancel_right₀ _ (multiRadiusWeight_pos hρ d).ne']

/-- Absolute summability of a coefficient tail follows by injectively
reindexing the original absolutely summable family.
@isnad1 id=weighted.2h4v.s7.77e068700880 from=translated src=- shape=b27700e1 vocab=fda24ad5
-/
theorem weightedCoeffSummable_tail (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (d : σ →₀ ℕ) {f : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f) :
    WeightedCoeffSummable ρ (mvPowerSeriesTail d f) := by
  have ht := hf.comp_injective (add_left_injective d)
  have hd := ht.div_const (multiRadiusWeight ρ d)
  apply hd.congr
  intro k
  exact (weightedCoeff_tail_identity ρ hρ d k f).symm

/-- The coefficient-tail bound, before passage to the Banach algebra.
@isnad1 id=le.2h4v.s7.455ab3c52dcc from=translated src=- shape=8d8c0865 vocab=dea4dca8
-/
theorem weightedCoeffNorm_tail_le (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (d : σ →₀ ℕ) {f : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f) :
    weightedCoeffNorm ρ (mvPowerSeriesTail d f) ≤
      weightedCoeffNorm ρ f / multiRadiusWeight ρ d := by
  unfold weightedCoeffNorm
  simp_rw [weightedCoeff_tail_identity ρ hρ d]
  rw [tsum_div_const]
  apply div_le_div_of_nonneg_right _ (multiRadiusWeight_pos hρ d).le
  exact tsum_comp_le_tsum_of_inj hf
    (fun k => mul_nonneg (norm_nonneg _) (multiRadiusWeight_pos hρ k).le)
    (add_left_injective d)

/-- The coefficient tail as a linear operator on weighted summable series.-/
def weightedSeriesTailLinear (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (d : σ →₀ ℕ) :
    WeightedSeries ρ hρ →ₗ[ℝ] WeightedSeries ρ hρ where
  toFun f := ⟨mvPowerSeriesTail d f.val, weightedCoeffSummable_tail ρ hρ d f.property⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add (mvPowerSeriesTail d) f.val g.val
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (mvPowerSeriesTail d) c f.val

/-- Division by a monomial on coefficient tails is a bounded real-linear map.-/
def weightedSeriesTailCLM (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (d : σ →₀ ℕ) :
    WeightedSeries ρ hρ →L[ℝ] WeightedSeries ρ hρ :=
  (weightedSeriesTailLinear ρ hρ d).mkContinuous (1 / multiRadiusWeight ρ d) fun f => by
    rw [weightedSeries_norm_eq, weightedSeries_norm_eq]
    calc
      _ ≤ weightedCoeffNorm ρ f.val / multiRadiusWeight ρ d :=
        weightedCoeffNorm_tail_le ρ hρ d f.property
      _ = _ := by ring

/--
@isnad1 id=eq.1h5v.s11.11c471aa5f86 from=translated src=- shape=b3ccd30f vocab=01278b64
-/
@[simp]
theorem weightedSeriesTailCLM_coeff (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (d k : σ →₀ ℕ) (f : WeightedSeries ρ hρ) :
    MvPowerSeries.coeff k (weightedSeriesTailCLM ρ hρ d f).val =
      MvPowerSeries.coeff (k + d) f.val := rfl

/-- A monomial as an element of the actual Banach algebra.-/
def weightedSeriesMonomial (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (d : σ →₀ ℕ) (c : ℝ) :
    WeightedSeries ρ hρ :=
  ⟨MvPowerSeries.monomial d c, weightedCoeffSummable_monomial ρ d c⟩

/--
@isnad1 id=eq.1h4v.s8.b647668fe8be from=translated src=- shape=de947d6b vocab=4e21c5b0
-/
@[simp]
theorem weightedSeriesMonomial_norm (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (d : σ →₀ ℕ) (c : ℝ) :
    ‖weightedSeriesMonomial ρ hρ d c‖ = ‖c‖ * multiRadiusWeight ρ d := by
  rw [weightedSeries_norm_eq]
  exact weightedCoeffNorm_monomial ρ d c

/-- The coordinate variable as a weighted summable power series.-/
def weightedSeriesX (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (i : σ) : WeightedSeries ρ hρ :=
  weightedSeriesMonomial ρ hρ (Finsupp.single i 1) 1

/--
@isnad1 id=eq.1h3v.s6.ae882fd0ec9c from=translated src=- shape=babd808d vocab=908d605f
-/
@[simp]
theorem weightedSeriesX_val (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) (i : σ) :
    (weightedSeriesX ρ hρ i).val = MvPowerSeries.X i := rfl

end AbelFormalization
