import Tengoku.Lmlf.LMLF.ODE.Hypergeometric
import Tengoku.Lmlf.LMLF.ODE.HolomorphicSecondOrder
import Tengoku.Seed.Analysis.Complex.Convex
import Tengoku.Seed.Analysis.Convex.Contractible

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The principal Gauss hypergeometric function

This file continues the regularized local Gauss series to the plane cut along `[1, ∞)`. The
construction uses two slit-plane IVPs and glues them to the local series on the unit disk. All
chart geometry and choices remain private; the public characterization is agreement with the
whole local-series germ.
-/

open Filter Metric Set
open scoped ComplexOrder Topology

namespace LMLF.Definitions

/-- The principal Gauss domain, the complex plane cut along the real ray `[1, ∞)`.-/
def gaussHypergeometricDomain : Set ℂ := (Set.Ici (1 : ℂ))ᶜ

/-- Coordinate description of the principal Gauss domain.-/
@[simp] theorem mem_gaussHypergeometricDomain_iff (z : ℂ) :
    z ∈ gaussHypergeometricDomain ↔ z.im ≠ 0 ∨ z.re < 1 := by
  simp only [gaussHypergeometricDomain, Set.mem_compl_iff, Set.mem_Ici, Complex.le_def]
  constructor
  · intro h
    by_cases hz : z.im = 0
    · exact Or.inr (lt_of_not_ge fun hle ↦ h ⟨hle, by simpa using hz.symm⟩)
    · exact Or.inl hz
  · rintro (hz | hz) h
    · exact hz (by simpa using h.2.symm)
    · exact (not_le_of_gt hz) h.1

/-- The principal Gauss domain is open.-/
theorem isOpen_gaussHypergeometricDomain : IsOpen gaussHypergeometricDomain :=
  isClosed_Ici.isOpen_compl

private def gaussChartA : Set ℂ :=
  (Set.Iic (0 : ℂ))ᶜ ∩ gaussHypergeometricDomain

private def gaussChartB : Set ℂ :=
  (Set.Ici (0 : ℂ))ᶜ

private def gaussSeriesDisk : Set ℂ := Metric.ball 0 1

private def gaussUpperHalfPlane : Set ℂ := {z | 0 < z.im}

private def gaussLowerHalfPlane : Set ℂ := {z | z.im < 0}

private theorem isOpen_gaussChartA : IsOpen gaussChartA :=
  isClosed_Iic.isOpen_compl.inter isOpen_gaussHypergeometricDomain

private theorem isOpen_gaussChartB : IsOpen gaussChartB :=
  isClosed_Ici.isOpen_compl

private theorem isOpen_gaussSeriesDisk : IsOpen gaussSeriesDisk := Metric.isOpen_ball

private theorem starConvex_gaussHypergeometricDomain :
    StarConvex ℝ (0 : ℂ) gaussHypergeometricDomain := by
  exact starConvex_compl_Ici (by norm_num : (0 : ℂ) < 1)

private theorem zero_mem_gaussHypergeometricDomain :
    (0 : ℂ) ∈ gaussHypergeometricDomain := by
  simp

/-- The principal Gauss domain is simply connected.-/
theorem isSimplyConnected_gaussHypergeometricDomain :
    IsSimplyConnected gaussHypergeometricDomain := by
  let _ : ContractibleSpace gaussHypergeometricDomain :=
    starConvex_gaussHypergeometricDomain.contractibleSpace
      ⟨0, zero_mem_gaussHypergeometricDomain⟩
  exact SimplyConnectedSpace.ofContractible gaussHypergeometricDomain

private theorem half_mem_gaussChartA : (1 / 2 : ℂ) ∈ gaussChartA := by
  norm_num [gaussChartA, gaussHypergeometricDomain, Complex.le_def, div_eq_mul_inv]

private theorem neg_half_mem_gaussChartB : (-1 / 2 : ℂ) ∈ gaussChartB := by
  norm_num [gaussChartB, Complex.le_def, div_eq_mul_inv]

private theorem half_mem_gaussSeriesDisk : (1 / 2 : ℂ) ∈ gaussSeriesDisk := by
  norm_num [gaussSeriesDisk, div_eq_mul_inv]

private theorem neg_half_mem_gaussSeriesDisk : (-1 / 2 : ℂ) ∈ gaussSeriesDisk := by
  norm_num [gaussSeriesDisk, div_eq_mul_inv]

private theorem starConvex_gaussChartA : StarConvex ℝ (1 / 2 : ℂ) gaussChartA := by
  exact (starConvex_compl_Iic (by norm_num : (0 : ℂ) < 1 / 2)).inter
    (starConvex_compl_Ici (by norm_num : (1 / 2 : ℂ) < 1))

private theorem starConvex_gaussChartB : StarConvex ℝ (-1 / 2 : ℂ) gaussChartB := by
  exact starConvex_compl_Ici (by norm_num : (-1 / 2 : ℂ) < 0)

private theorem isSimplyConnected_gaussChartA : IsSimplyConnected gaussChartA := by
  let _ : ContractibleSpace gaussChartA :=
    starConvex_gaussChartA.contractibleSpace ⟨_, half_mem_gaussChartA⟩
  exact SimplyConnectedSpace.ofContractible gaussChartA

private theorem isSimplyConnected_gaussChartB : IsSimplyConnected gaussChartB := by
  let _ : ContractibleSpace gaussChartB :=
    starConvex_gaussChartB.contractibleSpace ⟨_, neg_half_mem_gaussChartB⟩
  exact SimplyConnectedSpace.ofContractible gaussChartB

private theorem starConvex_gaussChartADisk :
    StarConvex ℝ (1 / 2 : ℂ) (gaussChartA ∩ gaussSeriesDisk) :=
  starConvex_gaussChartA.inter
    ((convex_ball (0 : ℂ) 1).starConvex half_mem_gaussSeriesDisk)

private theorem starConvex_gaussChartBDisk :
    StarConvex ℝ (-1 / 2 : ℂ) (gaussChartB ∩ gaussSeriesDisk) :=
  starConvex_gaussChartB.inter
    ((convex_ball (0 : ℂ) 1).starConvex neg_half_mem_gaussSeriesDisk)

private theorem isSimplyConnected_gaussChartADisk :
    IsSimplyConnected (gaussChartA ∩ gaussSeriesDisk) := by
  let _ : ContractibleSpace ↥(gaussChartA ∩ gaussSeriesDisk) :=
    starConvex_gaussChartADisk.contractibleSpace
      ⟨_, half_mem_gaussChartA, half_mem_gaussSeriesDisk⟩
  exact SimplyConnectedSpace.ofContractible ↥(gaussChartA ∩ gaussSeriesDisk)

private theorem isSimplyConnected_gaussChartBDisk :
    IsSimplyConnected (gaussChartB ∩ gaussSeriesDisk) := by
  let _ : ContractibleSpace ↥(gaussChartB ∩ gaussSeriesDisk) :=
    starConvex_gaussChartBDisk.contractibleSpace
      ⟨_, neg_half_mem_gaussChartB, neg_half_mem_gaussSeriesDisk⟩
  exact SimplyConnectedSpace.ofContractible ↥(gaussChartB ∩ gaussSeriesDisk)

private theorem gaussChartA_subset_domain : gaussChartA ⊆ gaussHypergeometricDomain :=
  fun _ hz ↦ hz.2

private theorem gaussChartB_subset_domain : gaussChartB ⊆ gaussHypergeometricDomain := by
  intro z hz
  rw [mem_gaussHypergeometricDomain_iff]
  simp only [gaussChartB, Set.mem_compl_iff, Set.mem_Ici, Complex.le_def] at hz
  by_cases hi : z.im = 0
  · right
    have hnre : ¬0 ≤ z.re := fun hre ↦ hz ⟨hre, hi.symm⟩
    exact lt_trans (lt_of_not_ge hnre) zero_lt_one
  · exact Or.inl hi

private theorem gaussSeriesDisk_subset_domain : gaussSeriesDisk ⊆ gaussHypergeometricDomain := by
  intro z hz
  rw [mem_gaussHypergeometricDomain_iff]
  by_cases hi : z.im = 0
  · right
    have hre : |z.re| < 1 := by
      have hle := Complex.abs_re_le_norm z
      exact lt_of_le_of_lt hle (by simpa [gaussSeriesDisk] using hz)
    exact lt_of_le_of_lt (le_abs_self z.re) hre
  · exact Or.inl hi

private theorem gaussCharts_cover_punctured :
    gaussChartA ∪ gaussChartB = gaussHypergeometricDomain \ {0} := by
  ext z
  constructor
  · rintro (hz | hz)
    · refine ⟨hz.2, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hzero
      subst z
      exact hz.1 (by simp)
    · refine ⟨gaussChartB_subset_domain hz, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hzero
      subst z
      exact hz (by simp)
  · rintro ⟨hzD, hz0⟩
    by_cases hzB : z ∈ gaussChartB
    · exact Or.inr hzB
    · left
      refine ⟨?_, hzD⟩
      simp only [Set.mem_compl_iff, Set.mem_Iic, Complex.le_def]
      intro hzle
      have hzIci : z ∈ Set.Ici (0 : ℂ) := by
        simp only [Set.mem_Ici, Complex.le_def]
        have him : z.im = 0 := hzle.2
        refine ⟨?_, him.symm⟩
        by_contra hn
        have hlt : z.re < 0 := lt_of_not_ge hn
        have : z ∈ gaussChartB := by
          simp only [gaussChartB, Set.mem_compl_iff, Set.mem_Ici, Complex.le_def]
          exact fun h ↦ (not_le_of_gt hlt) h.1
        exact hzB this
      have hzre0 : z.re = 0 := le_antisymm hzle.1 hzIci.1
      apply hz0
      apply Complex.ext
      · simpa using hzre0
      · simpa using hzle.2

private theorem gaussThreeSets_cover :
    gaussSeriesDisk ∪ gaussChartA ∪ gaussChartB = gaussHypergeometricDomain := by
  ext z
  constructor
  · rintro ((hz | hz) | hz)
    · exact gaussSeriesDisk_subset_domain hz
    · exact gaussChartA_subset_domain hz
    · exact gaussChartB_subset_domain hz
  · intro hz
    by_cases hz0 : z = 0
    · subst z
      exact Or.inl (by simp [gaussSeriesDisk])
    · have hp : z ∈ gaussHypergeometricDomain \ {0} := ⟨hz, by simpa⟩
      rw [← gaussCharts_cover_punctured] at hp
      rcases hp with hzA | hzB
      · exact Or.inl (Or.inr hzA)
      · exact Or.inr hzB

private theorem gaussChart_inter_eq_halfPlanes :
    gaussChartA ∩ gaussChartB = gaussUpperHalfPlane ∪ gaussLowerHalfPlane := by
  ext z
  simp only [gaussChartA, gaussChartB, gaussUpperHalfPlane, gaussLowerHalfPlane,
    Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Iic, Set.mem_Ici,
    Complex.le_def, Set.mem_union, gaussHypergeometricDomain]
  constructor
  · rintro ⟨⟨hIic, _⟩, hIci⟩
    by_cases hi : z.im = 0
    · exfalso
      by_cases hre : z.re ≤ 0
      · exact hIic ⟨hre, hi⟩
      · exact hIci ⟨le_of_not_ge hre, hi.symm⟩
    · rcases lt_or_gt_of_ne hi with hneg | hpos
      · exact Or.inr hneg
      · exact Or.inl hpos
  · rintro (hpos | hneg)
    · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> intro h
      · exact (ne_of_gt hpos) h.2
      · exact (ne_of_gt hpos) h.2.symm
      · exact (ne_of_gt hpos) h.2.symm
    · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> intro h
      · exact (ne_of_lt hneg) h.2
      · exact (ne_of_lt hneg) h.2.symm
      · exact (ne_of_lt hneg) h.2.symm

private def gaussDenominator (z : ℂ) : ℂ := z * (1 - z)

private noncomputable def gaussFirstCoefficient (a b c : ℂ) (z : ℂ) : ℂ :=
  (c - (a + b + 1) * z) / gaussDenominator z

private noncomputable def gaussZeroCoefficient (a b : ℂ) (z : ℂ) : ℂ :=
  -(a * b) / gaussDenominator z

private theorem gaussDenominator_ne_zero_of_mem_domain_of_ne_zero
    {z : ℂ} (hzD : z ∈ gaussHypergeometricDomain) (hz0 : z ≠ 0) :
    gaussDenominator z ≠ 0 := by
  have hz1 : z ≠ 1 := by
    intro hz
    subst z
    exact hzD (by norm_num [gaussHypergeometricDomain, Complex.le_def])
  simp [gaussDenominator, hz0, sub_ne_zero.mpr hz1.symm]

private theorem gaussDenominator_ne_zero_of_mem_chartA
    {z : ℂ} (hz : z ∈ gaussChartA) : gaussDenominator z ≠ 0 := by
  apply gaussDenominator_ne_zero_of_mem_domain_of_ne_zero hz.2
  intro hz0
  subst z
  exact hz.1 (by simp)

private theorem gaussDenominator_ne_zero_of_mem_chartB
    {z : ℂ} (hz : z ∈ gaussChartB) : gaussDenominator z ≠ 0 := by
  apply gaussDenominator_ne_zero_of_mem_domain_of_ne_zero (gaussChartB_subset_domain hz)
  intro hz0
  subst z
  exact hz (by simp)

private theorem gaussFirstCoefficient_analyticOnNhd_chartA (a b c : ℂ) :
    AnalyticOnNhd ℂ (gaussFirstCoefficient a b c) gaussChartA := by
  apply (analyticOnNhd_const.sub ((analyticOnNhd_const.add analyticOnNhd_const).mul
    analyticOnNhd_id)).div
    (analyticOnNhd_id.mul (analyticOnNhd_const.sub analyticOnNhd_id))
  exact fun z hz ↦ gaussDenominator_ne_zero_of_mem_chartA hz

private theorem gaussFirstCoefficient_analyticOnNhd_chartB (a b c : ℂ) :
    AnalyticOnNhd ℂ (gaussFirstCoefficient a b c) gaussChartB := by
  apply (analyticOnNhd_const.sub ((analyticOnNhd_const.add analyticOnNhd_const).mul
    analyticOnNhd_id)).div
    (analyticOnNhd_id.mul (analyticOnNhd_const.sub analyticOnNhd_id))
  exact fun z hz ↦ gaussDenominator_ne_zero_of_mem_chartB hz

private theorem gaussZeroCoefficient_analyticOnNhd_chartA (a b : ℂ) :
    AnalyticOnNhd ℂ (gaussZeroCoefficient a b) gaussChartA := by
  apply analyticOnNhd_const.div
    (analyticOnNhd_id.mul (analyticOnNhd_const.sub analyticOnNhd_id))
  exact fun z hz ↦ gaussDenominator_ne_zero_of_mem_chartA hz

private theorem gaussZeroCoefficient_analyticOnNhd_chartB (a b : ℂ) :
    AnalyticOnNhd ℂ (gaussZeroCoefficient a b) gaussChartB := by
  apply analyticOnNhd_const.div
    (analyticOnNhd_id.mul (analyticOnNhd_const.sub analyticOnNhd_id))
  exact fun z hz ↦ gaussDenominator_ne_zero_of_mem_chartB hz

private theorem regularizedSeries_normalizedCandidate
    (a b c : ℂ) {z : ℂ} (hz : z ∈ gaussSeriesDisk)
    (hd : gaussDenominator z ≠ 0) :
    HasDerivAt (deriv (regularizedGaussHypergeometricSeriesSum a b c))
      (-(gaussFirstCoefficient a b c z *
          deriv (regularizedGaussHypergeometricSeriesSum a b c) z +
        gaussZeroCoefficient a b z * regularizedGaussHypergeometricSeriesSum a b c z)) z := by
  have hderiv :=
    ((regularizedGaussHypergeometricSeriesSum_analyticOnNhd a b c).deriv z hz).differentiableAt
      |>.hasDerivAt
  apply hderiv.congr_deriv
  have hlocal := LMLF.ODE.regularizedGaussHypergeometricSeriesSum_gaussEquation
    (a := a) (b := b) (c := c) (z := z) (by simpa [gaussSeriesDisk] using hz)
  simp only [gaussFirstCoefficient, gaussZeroCoefficient]
  field_simp [gaussDenominator, hd]
  unfold gaussDenominator
  linear_combination hlocal

private theorem exists_gaussChartA_solution (a b c : ℂ) :
    ∃ w : ℂ → ℂ,
      AnalyticOnNhd ℂ w gaussChartA ∧
      w (1 / 2) = regularizedGaussHypergeometricSeriesSum a b c (1 / 2) ∧
      HasDerivAt w (deriv (regularizedGaussHypergeometricSeriesSum a b c) (1 / 2)) (1 / 2) ∧
      (∀ z ∈ gaussChartA,
        HasDerivAt (deriv w)
          (-(gaussFirstCoefficient a b c z * deriv w z +
            gaussZeroCoefficient a b z * w z)) z) ∧
      ∀ v : ℂ → ℂ, AnalyticOnNhd ℂ v gaussChartA →
        v (1 / 2) = regularizedGaussHypergeometricSeriesSum a b c (1 / 2) →
        HasDerivAt v (deriv (regularizedGaussHypergeometricSeriesSum a b c) (1 / 2)) (1 / 2) →
        (∀ z ∈ gaussChartA,
          HasDerivAt (deriv v)
            (-(gaussFirstCoefficient a b c z * deriv v z +
              gaussZeroCoefficient a b z * v z)) z) →
        Set.EqOn w v gaussChartA := by
  exact LMLF.ODE.exists_unique_holomorphicSecondOrderLinear
    isOpen_gaussChartA isSimplyConnected_gaussChartA
    (gaussFirstCoefficient_analyticOnNhd_chartA a b c)
    (gaussZeroCoefficient_analyticOnNhd_chartA a b)
    half_mem_gaussChartA _ _

private theorem exists_gaussChartB_solution (a b c : ℂ) :
    ∃ w : ℂ → ℂ,
      AnalyticOnNhd ℂ w gaussChartB ∧
      w (-1 / 2) = regularizedGaussHypergeometricSeriesSum a b c (-1 / 2) ∧
      HasDerivAt w (deriv (regularizedGaussHypergeometricSeriesSum a b c) (-1 / 2)) (-1 / 2) ∧
      (∀ z ∈ gaussChartB,
        HasDerivAt (deriv w)
          (-(gaussFirstCoefficient a b c z * deriv w z +
            gaussZeroCoefficient a b z * w z)) z) ∧
      ∀ v : ℂ → ℂ, AnalyticOnNhd ℂ v gaussChartB →
        v (-1 / 2) = regularizedGaussHypergeometricSeriesSum a b c (-1 / 2) →
        HasDerivAt v (deriv (regularizedGaussHypergeometricSeriesSum a b c) (-1 / 2)) (-1 / 2) →
        (∀ z ∈ gaussChartB,
          HasDerivAt (deriv v)
            (-(gaussFirstCoefficient a b c z * deriv v z +
              gaussZeroCoefficient a b z * v z)) z) →
        Set.EqOn w v gaussChartB := by
  exact LMLF.ODE.exists_unique_holomorphicSecondOrderLinear
    isOpen_gaussChartB isSimplyConnected_gaussChartB
    (gaussFirstCoefficient_analyticOnNhd_chartB a b c)
    (gaussZeroCoefficient_analyticOnNhd_chartB a b)
    neg_half_mem_gaussChartB _ _

private noncomputable def gaussChartASolution (a b c : ℂ) : ℂ → ℂ :=
  Classical.choose (exists_gaussChartA_solution a b c)

private noncomputable def gaussChartBSolution (a b c : ℂ) : ℂ → ℂ :=
  Classical.choose (exists_gaussChartB_solution a b c)

private theorem gaussChartASolution_eqOn_seriesDisk (a b c : ℂ) :
    Set.EqOn (gaussChartASolution a b c)
      (regularizedGaussHypergeometricSeriesSum a b c) (gaussChartA ∩ gaussSeriesDisk) := by
  let U := gaussChartA ∩ gaussSeriesDisk
  obtain ⟨u, huAnalytic, hu0, huDeriv, huOde, huUnique⟩ :=
    LMLF.ODE.exists_unique_holomorphicSecondOrderLinear
      (isOpen_gaussChartA.inter isOpen_gaussSeriesDisk)
      isSimplyConnected_gaussChartADisk
      ((gaussFirstCoefficient_analyticOnNhd_chartA a b c).mono inter_subset_left)
      ((gaussZeroCoefficient_analyticOnNhd_chartA a b).mono inter_subset_left)
      ⟨half_mem_gaussChartA, half_mem_gaussSeriesDisk⟩
      (regularizedGaussHypergeometricSeriesSum a b c (1 / 2))
      (deriv (regularizedGaussHypergeometricSeriesSum a b c) (1 / 2))
  have hA := Classical.choose_spec (exists_gaussChartA_solution a b c)
  have huA : Set.EqOn u (gaussChartASolution a b c) U :=
    huUnique _ (hA.1.mono inter_subset_left) hA.2.1 hA.2.2.1
      (fun z hz ↦ hA.2.2.2.1 z hz.1)
  have hRAnalytic : AnalyticOnNhd ℂ (regularizedGaussHypergeometricSeriesSum a b c) U :=
    (regularizedGaussHypergeometricSeriesSum_analyticOnNhd a b c).mono inter_subset_right
  have hRDeriv : HasDerivAt (regularizedGaussHypergeometricSeriesSum a b c)
      (deriv (regularizedGaussHypergeometricSeriesSum a b c) (1 / 2)) (1 / 2) :=
    (hRAnalytic (1 / 2) ⟨half_mem_gaussChartA, half_mem_gaussSeriesDisk⟩).differentiableAt
      |>.hasDerivAt
  have huR : Set.EqOn u (regularizedGaussHypergeometricSeriesSum a b c) U :=
    huUnique _ hRAnalytic rfl hRDeriv fun z hz ↦
      regularizedSeries_normalizedCandidate a b c hz.2
        (gaussDenominator_ne_zero_of_mem_chartA hz.1)
  exact fun z hz ↦ (huA hz).symm.trans (huR hz)

private theorem gaussChartBSolution_eqOn_seriesDisk (a b c : ℂ) :
    Set.EqOn (gaussChartBSolution a b c)
      (regularizedGaussHypergeometricSeriesSum a b c) (gaussChartB ∩ gaussSeriesDisk) := by
  let U := gaussChartB ∩ gaussSeriesDisk
  obtain ⟨u, huAnalytic, hu0, huDeriv, huOde, huUnique⟩ :=
    LMLF.ODE.exists_unique_holomorphicSecondOrderLinear
      (isOpen_gaussChartB.inter isOpen_gaussSeriesDisk)
      isSimplyConnected_gaussChartBDisk
      ((gaussFirstCoefficient_analyticOnNhd_chartB a b c).mono inter_subset_left)
      ((gaussZeroCoefficient_analyticOnNhd_chartB a b).mono inter_subset_left)
      ⟨neg_half_mem_gaussChartB, neg_half_mem_gaussSeriesDisk⟩
      (regularizedGaussHypergeometricSeriesSum a b c (-1 / 2))
      (deriv (regularizedGaussHypergeometricSeriesSum a b c) (-1 / 2))
  have hB := Classical.choose_spec (exists_gaussChartB_solution a b c)
  have huB : Set.EqOn u (gaussChartBSolution a b c) U :=
    huUnique _ (hB.1.mono inter_subset_left) hB.2.1 hB.2.2.1
      (fun z hz ↦ hB.2.2.2.1 z hz.1)
  have hRAnalytic : AnalyticOnNhd ℂ (regularizedGaussHypergeometricSeriesSum a b c) U :=
    (regularizedGaussHypergeometricSeriesSum_analyticOnNhd a b c).mono inter_subset_right
  have hRDeriv : HasDerivAt (regularizedGaussHypergeometricSeriesSum a b c)
      (deriv (regularizedGaussHypergeometricSeriesSum a b c) (-1 / 2)) (-1 / 2) :=
    (hRAnalytic (-1 / 2) ⟨neg_half_mem_gaussChartB, neg_half_mem_gaussSeriesDisk⟩).differentiableAt
      |>.hasDerivAt
  have huR : Set.EqOn u (regularizedGaussHypergeometricSeriesSum a b c) U :=
    huUnique _ hRAnalytic rfl hRDeriv fun z hz ↦
      regularizedSeries_normalizedCandidate a b c hz.2
        (gaussDenominator_ne_zero_of_mem_chartB hz.1)
  exact fun z hz ↦ (huB hz).symm.trans (huR hz)

private theorem gaussChartASolution_analyticOnNhd (a b c : ℂ) :
    AnalyticOnNhd ℂ (gaussChartASolution a b c) gaussChartA :=
  (Classical.choose_spec (exists_gaussChartA_solution a b c)).1

private theorem gaussChartBSolution_analyticOnNhd (a b c : ℂ) :
    AnalyticOnNhd ℂ (gaussChartBSolution a b c) gaussChartB :=
  (Classical.choose_spec (exists_gaussChartB_solution a b c)).1

private theorem gaussChartASolution_normalizedEquation (a b c : ℂ) :
    ∀ z ∈ gaussChartA,
      HasDerivAt (deriv (gaussChartASolution a b c))
        (-(gaussFirstCoefficient a b c z * deriv (gaussChartASolution a b c) z +
          gaussZeroCoefficient a b z * gaussChartASolution a b c z)) z :=
  (Classical.choose_spec (exists_gaussChartA_solution a b c)).2.2.2.1

private theorem gaussChartBSolution_normalizedEquation (a b c : ℂ) :
    ∀ z ∈ gaussChartB,
      HasDerivAt (deriv (gaussChartBSolution a b c))
        (-(gaussFirstCoefficient a b c z * deriv (gaussChartBSolution a b c) z +
          gaussZeroCoefficient a b z * gaussChartBSolution a b c z)) z :=
  (Classical.choose_spec (exists_gaussChartB_solution a b c)).2.2.2.1

private theorem gaussChartSolutions_eqOn_inter (a b c : ℂ) :
    Set.EqOn (gaussChartASolution a b c) (gaussChartBSolution a b c)
      (gaussChartA ∩ gaussChartB) := by
  have htriple : Set.EqOn (gaussChartASolution a b c) (gaussChartBSolution a b c)
      ((gaussChartA ∩ gaussChartB) ∩ gaussSeriesDisk) := by
    intro z hz
    exact (gaussChartASolution_eqOn_seriesDisk a b c ⟨hz.1.1, hz.2⟩).trans
      (gaussChartBSolution_eqOn_seriesDisk a b c ⟨hz.1.2, hz.2⟩).symm
  have hopenTriple : IsOpen ((gaussChartA ∩ gaussChartB) ∩ gaussSeriesDisk) :=
    (isOpen_gaussChartA.inter isOpen_gaussChartB).inter isOpen_gaussSeriesDisk
  have hUpperSubset : gaussUpperHalfPlane ⊆ gaussChartA ∩ gaussChartB := by
    rw [gaussChart_inter_eq_halfPlanes]
    exact subset_union_left
  have hLowerSubset : gaussLowerHalfPlane ⊆ gaussChartA ∩ gaussChartB := by
    rw [gaussChart_inter_eq_halfPlanes]
    exact subset_union_right
  have hUpper : Set.EqOn (gaussChartASolution a b c) (gaussChartBSolution a b c)
      gaussUpperHalfPlane := by
    have hq : (Complex.I / 2 : ℂ) ∈ gaussUpperHalfPlane := by
      norm_num [gaussUpperHalfPlane]
    have hqTriple : (Complex.I / 2 : ℂ) ∈
        (gaussChartA ∩ gaussChartB) ∩ gaussSeriesDisk := by
      norm_num [gaussChartA, gaussChartB, gaussSeriesDisk, gaussHypergeometricDomain,
        Complex.le_def, div_eq_mul_inv]
    have hevent : gaussChartASolution a b c =ᶠ[𝓝 (Complex.I / 2)]
        gaussChartBSolution a b c :=
      htriple.eventuallyEq_of_mem (hopenTriple.mem_nhds hqTriple)
    exact (gaussChartASolution_analyticOnNhd a b c).mono
      (hUpperSubset.trans inter_subset_left)
      |>.eqOn_of_preconnected_of_eventuallyEq
        ((gaussChartBSolution_analyticOnNhd a b c).mono
          (hUpperSubset.trans inter_subset_right))
        (convex_halfSpace_im_gt 0).isPreconnected hq hevent
  have hLower : Set.EqOn (gaussChartASolution a b c) (gaussChartBSolution a b c)
      gaussLowerHalfPlane := by
    have hq : (-Complex.I / 2 : ℂ) ∈ gaussLowerHalfPlane := by
      norm_num [gaussLowerHalfPlane]
    have hqTriple : (-Complex.I / 2 : ℂ) ∈
        (gaussChartA ∩ gaussChartB) ∩ gaussSeriesDisk := by
      norm_num [gaussChartA, gaussChartB, gaussSeriesDisk, gaussHypergeometricDomain,
        Complex.le_def, div_eq_mul_inv]
    have hevent : gaussChartASolution a b c =ᶠ[𝓝 (-Complex.I / 2)]
        gaussChartBSolution a b c :=
      htriple.eventuallyEq_of_mem (hopenTriple.mem_nhds hqTriple)
    exact (gaussChartASolution_analyticOnNhd a b c).mono
      (hLowerSubset.trans inter_subset_left)
      |>.eqOn_of_preconnected_of_eventuallyEq
        ((gaussChartBSolution_analyticOnNhd a b c).mono
          (hLowerSubset.trans inter_subset_right))
        (convex_halfSpace_im_lt 0).isPreconnected hq hevent
  rw [gaussChart_inter_eq_halfPlanes]
  intro z hz
  rcases hz with hz | hz
  · exact hUpper hz
  · exact hLower hz

/-- The ambient regularized principal Gauss function. On the principal domain it glues the local
series to the two slit-chart continuations; off the domain it retains the ambient series value.-/
noncomputable def regularizedGaussHypergeometric (a b c : ℂ) : ℂ → ℂ := by
  classical
  exact fun z ↦
    if z ∈ gaussHypergeometricDomain then
      if z ∈ gaussSeriesDisk then
        regularizedGaussHypergeometricSeriesSum a b c z
      else if z ∈ gaussChartA then
        gaussChartASolution a b c z
      else
        gaussChartBSolution a b c z
    else
      regularizedGaussHypergeometricSeriesSum a b c z

/-- The ordinary principal Gauss function is Gamma scaling of the regularized function.-/
noncomputable def gaussHypergeometric (a b c : ℂ) : ℂ → ℂ := fun z ↦
  Complex.Gamma c * regularizedGaussHypergeometric a b c z

/-- On the open unit disk, the regularized principal function is the original series sum.-/
theorem regularizedGaussHypergeometric_eqOn_seriesSum (a b c : ℂ) :
    Set.EqOn (regularizedGaussHypergeometric a b c)
      (regularizedGaussHypergeometricSeriesSum a b c) (Metric.ball 0 1) := by
  intro z hz
  have hzDisk : z ∈ gaussSeriesDisk := by simpa [gaussSeriesDisk] using hz
  have hzD := gaussSeriesDisk_subset_domain hzDisk
  rw [regularizedGaussHypergeometric, ite_eq_left hzD, ite_eq_left hzDisk]

/-- Off the principal domain, the ambient regularized function retains the original series sum.-/
theorem regularizedGaussHypergeometric_eqOn_seriesSum_compl (a b c : ℂ) :
    Set.EqOn (regularizedGaussHypergeometric a b c)
      (regularizedGaussHypergeometricSeriesSum a b c) gaussHypergeometricDomainᶜ := by
  intro z hz
  have hnD : z ∉ gaussHypergeometricDomain := hz
  rw [regularizedGaussHypergeometric, ite_eq_right hnD]

private theorem regularizedGaussHypergeometric_eqOn_chartA (a b c : ℂ) :
    Set.EqOn (regularizedGaussHypergeometric a b c) (gaussChartASolution a b c)
      gaussChartA := by
  intro z hz
  by_cases hzBall : z ∈ gaussSeriesDisk
  · rw [regularizedGaussHypergeometric, ite_eq_left hz.2, ite_eq_left hzBall]
    exact (gaussChartASolution_eqOn_seriesDisk a b c ⟨hz, hzBall⟩).symm
  · rw [regularizedGaussHypergeometric, ite_eq_left hz.2, ite_eq_right hzBall, ite_eq_left hz]

private theorem regularizedGaussHypergeometric_eqOn_chartB (a b c : ℂ) :
    Set.EqOn (regularizedGaussHypergeometric a b c) (gaussChartBSolution a b c)
      gaussChartB := by
  intro z hz
  have hzD := gaussChartB_subset_domain hz
  by_cases hzBall : z ∈ gaussSeriesDisk
  · rw [regularizedGaussHypergeometric, ite_eq_left hzD, ite_eq_left hzBall]
    exact (gaussChartBSolution_eqOn_seriesDisk a b c ⟨hz, hzBall⟩).symm
  · by_cases hzA : z ∈ gaussChartA
    · rw [regularizedGaussHypergeometric, ite_eq_left hzD, ite_eq_right hzBall, ite_eq_left hzA]
      exact gaussChartSolutions_eqOn_inter a b c ⟨hzA, hz⟩
    · rw [regularizedGaussHypergeometric, ite_eq_left hzD, ite_eq_right hzBall, ite_eq_right hzA]

/-- The regularized principal function is analytic throughout the cut plane.-/
theorem regularizedGaussHypergeometric_analyticOnNhd (a b c : ℂ) :
    AnalyticOnNhd ℂ (regularizedGaussHypergeometric a b c) gaussHypergeometricDomain := by
  have hDisk : AnalyticOnNhd ℂ (regularizedGaussHypergeometric a b c) gaussSeriesDisk :=
    (regularizedGaussHypergeometricSeriesSum_analyticOnNhd a b c).congr
      isOpen_gaussSeriesDisk
      (fun z hz ↦ (regularizedGaussHypergeometric_eqOn_seriesSum a b c
        (by simpa [gaussSeriesDisk] using hz)).symm)
  have hA : AnalyticOnNhd ℂ (regularizedGaussHypergeometric a b c) gaussChartA :=
    (gaussChartASolution_analyticOnNhd a b c).congr isOpen_gaussChartA
      (regularizedGaussHypergeometric_eqOn_chartA a b c).symm
  have hB : AnalyticOnNhd ℂ (regularizedGaussHypergeometric a b c) gaussChartB :=
    (gaussChartBSolution_analyticOnNhd a b c).congr isOpen_gaussChartB
      (regularizedGaussHypergeometric_eqOn_chartB a b c).symm
  intro z hz
  have hzCover : z ∈ gaussSeriesDisk ∪ gaussChartA ∪ gaussChartB := by
    rw [gaussThreeSets_cover]
    exact hz
  rcases hzCover with (hzDisk | hzA) | hzB
  · exact hDisk z hzDisk
  · exact hA z hzA
  · exact hB z hzB

/-- An analytic function on the principal domain is determined by the whole local-series germ.-/
theorem regularizedGaussHypergeometric_eqOn_of_eqOn_seriesSum
    (a b c : ℂ) {v : ℂ → ℂ}
    (hv : AnalyticOnNhd ℂ v gaussHypergeometricDomain)
    (hvgerm : Set.EqOn v (regularizedGaussHypergeometricSeriesSum a b c)
      (Metric.ball 0 1)) :
    Set.EqOn (regularizedGaussHypergeometric a b c) v gaussHypergeometricDomain := by
  have hEqDisk : Set.EqOn (regularizedGaussHypergeometric a b c) v (Metric.ball 0 1) :=
    fun z hz ↦ (regularizedGaussHypergeometric_eqOn_seriesSum a b c hz).trans
      (hvgerm hz).symm
  have hevent : regularizedGaussHypergeometric a b c =ᶠ[𝓝 (0 : ℂ)] v :=
    hEqDisk.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (by simp))
  exact (regularizedGaussHypergeometric_analyticOnNhd a b c)
    |>.eqOn_of_preconnected_of_eventuallyEq hv
      (starConvex_gaussHypergeometricDomain.isPathConnected
        zero_mem_gaussHypergeometricDomain).isConnected.isPreconnected
      zero_mem_gaussHypergeometricDomain hevent

/-- On the source disk, the ordinary principal function is the ordinary Gauss series.-/
theorem gaussHypergeometric_eqOn_seriesSum
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    Set.EqOn (gaussHypergeometric a b c) (gaussHypergeometricSeriesSum a b c)
      (Metric.ball 0 1) := by
  intro z hz
  have hG : Complex.Gamma c ≠ 0 := Complex.Gamma_ne_zero hc
  have hbridge := gaussHypergeometricSeriesSum_div_Gamma
    (a := a) (b := b) (c := c) (z := z) hc (by simpa using hz)
  have hseries : gaussHypergeometricSeriesSum a b c z =
      regularizedGaussHypergeometricSeriesSum a b c z * Complex.Gamma c :=
    (div_eq_iff hG).mp hbridge
  rw [gaussHypergeometric,
    regularizedGaussHypergeometric_eqOn_seriesSum a b c hz, hseries]
  ring

/-- The ordinary principal function is analytic on the principal domain.-/
theorem gaussHypergeometric_analyticOnNhd
    (a b c : ℂ) (_hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    AnalyticOnNhd ℂ (gaussHypergeometric a b c) gaussHypergeometricDomain := by
  exact analyticOnNhd_const.mul (regularizedGaussHypergeometric_analyticOnNhd a b c)

/-- An analytic ordinary function on the principal domain is determined by its whole series
germ.-/
theorem gaussHypergeometric_eqOn_of_eqOn_seriesSum
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) {v : ℂ → ℂ}
    (hv : AnalyticOnNhd ℂ v gaussHypergeometricDomain)
    (hvgerm : Set.EqOn v (gaussHypergeometricSeriesSum a b c) (Metric.ball 0 1)) :
    Set.EqOn (gaussHypergeometric a b c) v gaussHypergeometricDomain := by
  have hEqDisk : Set.EqOn (gaussHypergeometric a b c) v (Metric.ball 0 1) :=
    fun z hz ↦ (gaussHypergeometric_eqOn_seriesSum a b c hc hz).trans (hvgerm hz).symm
  have hevent : gaussHypergeometric a b c =ᶠ[𝓝 (0 : ℂ)] v :=
    hEqDisk.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (by simp))
  exact (gaussHypergeometric_analyticOnNhd a b c hc)
    |>.eqOn_of_preconnected_of_eventuallyEq hv
      (starConvex_gaussHypergeometricDomain.isPathConnected
        zero_mem_gaussHypergeometricDomain).isConnected.isPreconnected
      zero_mem_gaussHypergeometricDomain hevent

/-- Dividing the ordinary principal function by its nonzero Gamma factor recovers the
regularized principal function at every ambient point.-/
theorem gaussHypergeometric_div_Gamma
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (z : ℂ) :
    gaussHypergeometric a b c z / Complex.Gamma c =
      regularizedGaussHypergeometric a b c z := by
  exact (mul_div_cancel_left₀ _ (Complex.Gamma_ne_zero hc))

private theorem regularizedGaussHypergeometric_gaussEquation_chartA
    (a b c : ℂ) {z : ℂ} (hz : z ∈ gaussChartA) :
    z * (1 - z) * deriv (deriv (regularizedGaussHypergeometric a b c)) z +
        (c - (a + b + 1) * z) * deriv (regularizedGaussHypergeometric a b c) z -
      a * b * regularizedGaussHypergeometric a b c z = 0 := by
  let P := regularizedGaussHypergeometric a b c
  let W := gaussChartASolution a b c
  have hPW : Set.EqOn P W gaussChartA := regularizedGaussHypergeometric_eqOn_chartA a b c
  have hPW' : Set.EqOn (deriv P) (deriv W) gaussChartA := hPW.deriv isOpen_gaussChartA
  have hPW'' : Set.EqOn (deriv (deriv P)) (deriv (deriv W)) gaussChartA :=
    hPW'.deriv isOpen_gaussChartA
  have hnorm := (gaussChartASolution_normalizedEquation a b c z hz).deriv
  have hd := gaussDenominator_ne_zero_of_mem_chartA hz
  change z * (1 - z) * deriv (deriv P) z +
      (c - (a + b + 1) * z) * deriv P z - a * b * P z = 0
  rw [hPW hz, hPW' hz, hPW'' hz]
  simp only [gaussFirstCoefficient, gaussZeroCoefficient] at hnorm
  field_simp [gaussDenominator, hd] at hnorm
  unfold gaussDenominator at hnorm
  linear_combination hnorm

private theorem regularizedGaussHypergeometric_gaussEquation_chartB
    (a b c : ℂ) {z : ℂ} (hz : z ∈ gaussChartB) :
    z * (1 - z) * deriv (deriv (regularizedGaussHypergeometric a b c)) z +
        (c - (a + b + 1) * z) * deriv (regularizedGaussHypergeometric a b c) z -
      a * b * regularizedGaussHypergeometric a b c z = 0 := by
  let P := regularizedGaussHypergeometric a b c
  let W := gaussChartBSolution a b c
  have hPW : Set.EqOn P W gaussChartB := regularizedGaussHypergeometric_eqOn_chartB a b c
  have hPW' : Set.EqOn (deriv P) (deriv W) gaussChartB := hPW.deriv isOpen_gaussChartB
  have hPW'' : Set.EqOn (deriv (deriv P)) (deriv (deriv W)) gaussChartB :=
    hPW'.deriv isOpen_gaussChartB
  have hnorm := (gaussChartBSolution_normalizedEquation a b c z hz).deriv
  have hd := gaussDenominator_ne_zero_of_mem_chartB hz
  change z * (1 - z) * deriv (deriv P) z +
      (c - (a + b + 1) * z) * deriv P z - a * b * P z = 0
  rw [hPW hz, hPW' hz, hPW'' hz]
  simp only [gaussFirstCoefficient, gaussZeroCoefficient] at hnorm
  field_simp [gaussDenominator, hd] at hnorm
  unfold gaussDenominator at hnorm
  linear_combination hnorm

end LMLF.Definitions

namespace LMLF.ODE

open LMLF.Definitions

/-- The regularized principal Gauss function satisfies the unnormalized Gauss equation on the
entire principal domain, including the singular origin and every denominator parameter.-/
theorem regularizedGaussHypergeometric_gaussEquation
    (a b c : ℂ) {z : ℂ} (hz : z ∈ gaussHypergeometricDomain) :
    z * (1 - z) * deriv (deriv (regularizedGaussHypergeometric a b c)) z +
        (c - (a + b + 1) * z) * deriv (regularizedGaussHypergeometric a b c) z -
      a * b * regularizedGaussHypergeometric a b c z = 0 := by
  by_cases hz0 : z = 0
  · subst z
    let P := regularizedGaussHypergeometric a b c
    let R := regularizedGaussHypergeometricSeriesSum a b c
    have hPR : Set.EqOn P R (Metric.ball 0 1) :=
      regularizedGaussHypergeometric_eqOn_seriesSum a b c
    have hPR' : Set.EqOn (deriv P) (deriv R) (Metric.ball 0 1) :=
      hPR.deriv Metric.isOpen_ball
    have hPR'' : Set.EqOn (deriv (deriv P)) (deriv (deriv R)) (Metric.ball 0 1) :=
      hPR'.deriv Metric.isOpen_ball
    have hzero : (0 : ℂ) ∈ Metric.ball 0 1 := by simp
    change (0 : ℂ) * (1 - 0) * deriv (deriv P) 0 +
        (c - (a + b + 1) * 0) * deriv P 0 - a * b * P 0 = 0
    rw [hPR hzero, hPR' hzero, hPR'' hzero]
    exact regularizedGaussHypergeometricSeriesSum_gaussEquation (by norm_num)
  · have hp : z ∈ gaussHypergeometricDomain \ {0} := ⟨hz, by simpa⟩
    rw [← gaussCharts_cover_punctured] at hp
    rcases hp with hzA | hzB
    · exact regularizedGaussHypergeometric_gaussEquation_chartA a b c hzA
    · exact regularizedGaussHypergeometric_gaussEquation_chartB a b c hzB

/-- The ordinary principal Gauss function satisfies the same homogeneous equation on the
principal domain.-/
theorem gaussHypergeometric_gaussEquation
    (a b c : ℂ) (_hc : ∀ n : ℕ, c ≠ -(n : ℂ)) {z : ℂ}
    (hz : z ∈ gaussHypergeometricDomain) :
    z * (1 - z) * deriv (deriv (gaussHypergeometric a b c)) z +
        (c - (a + b + 1) * z) * deriv (gaussHypergeometric a b c) z -
      a * b * gaussHypergeometric a b c z = 0 := by
  let O := gaussHypergeometric a b c
  let P := regularizedGaussHypergeometric a b c
  let G := Complex.Gamma c
  have hP := regularizedGaussHypergeometric_gaussEquation a b c hz
  have hOP : Set.EqOn O (fun w ↦ G * P w) Set.univ := fun _ _ ↦ rfl
  have hOP' : Set.EqOn (deriv O) (fun w ↦ G * deriv P w) Set.univ := by
    intro w hw
    simpa only [deriv_const_mul_field G] using (hOP.deriv isOpen_univ) hw
  have hOP'' : Set.EqOn (deriv (deriv O)) (fun w ↦ G * deriv (deriv P) w) Set.univ := by
    intro w hw
    simpa only [deriv_const_mul_field G] using (hOP'.deriv isOpen_univ) hw
  change z * (1 - z) * deriv (deriv O) z +
      (c - (a + b + 1) * z) * deriv O z - a * b * O z = 0
  rw [hOP (mem_univ z), hOP' (mem_univ z), hOP'' (mem_univ z)]
  calc
    _ = G * (z * (1 - z) * deriv (deriv P) z +
          (c - (a + b + 1) * z) * deriv P z - a * b * P z) := by ring
    _ = 0 := by rw [hP, mul_zero]

end LMLF.ODE
