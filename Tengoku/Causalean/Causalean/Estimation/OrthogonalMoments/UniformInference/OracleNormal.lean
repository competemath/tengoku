module
public import Tengoku.Causalean.Causalean.Estimation.OrthogonalMoments.UniformInference.Basic
public import Tengoku.Causalean.Causalean.Stat.CLT.BerryEsseen.BerryEsseenCore
public import Tengoku.Causalean.Causalean.Stat.Sample.PiTransport

/-! # Uniform Gaussian approximation for bounded oracle scores

The oracle score has mean zero, a uniform positive variance floor, and a
uniform third absolute moment bound. A quantitative scalar Berry–Esseen
bound gives a normal approximation uniformly over a changing class of laws.
The bounded score assumption also supplies the fourth moment needed for
variance estimation downstream.
-/

@[expose] public section

namespace Causalean.Estimation.OrthogonalMoments.UniformInference

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat Causalean.Stat.CLT.BerryEsseen

variable {ι Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  {K : ℕ} (F : Family ι Ω Z K)

/-- Oracle regularity means that the mean-zero score is measurable and
uniformly bounded, its variance stays above `vmin > 0`, and its third
absolute moment stays below `M3` over every current law class. -/
structure OracleConditions (B vmin M3 : ℝ) : Prop where
  B_nonneg : 0 ≤ B
  vmin_pos : 0 < vmin
  M3_nonneg : 0 ≤ M3
  measurable : ∀ p, Measurable (F.oracle p)
  mean_zero : ∀ n p, p ∈ F.lawClass n →
    ∫ z, F.oracle p z ∂F.laws p = 0
  bounded : ∀ n p, p ∈ F.lawClass n → ∀ z,
    |F.oracle p z| ≤ B
  variance_lower : ∀ n p, p ∈ F.lawClass n →
    vmin ≤ F.oracleVar p
  third_moment : ∀ n p, p ∈ F.lawClass n →
    ∫ z, |F.oracle p z| ^ 3 ∂F.laws p ≤ M3

namespace Family

/-- The standardized oracle sum divides the normalized empirical influence
score by its law-specific population standard deviation. -/
noncomputable def standardizedOracle (n : ℕ) (p : ι) (ω : Ω) : ℝ :=
  F.oracleSum n p ω / Real.sqrt (F.oracleVar p)

end Family
end Causalean.Estimation.OrthogonalMoments.UniformInference
