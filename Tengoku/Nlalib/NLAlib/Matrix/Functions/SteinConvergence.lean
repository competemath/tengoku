import Tengoku.Nlalib.NLAlib.Matrix.Functions.SteinGeometricBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Convergence of the actual Smith doubling process -/

noncomputable section
open Filter
open scoped Matrix MatrixOrder ComplexOrder Topology
namespace NLAlib
variable {K n : Type*} [RCLike K] [Fintype n] [DecidableEq n]

/-- Every summable actual Stein series is the limit of the actual Smith
iterates, whose prefix lengths are exactly `2^j`.
Source: user derivations, Stein Gramians and Smith doubling.
atlas: stein-gramian-smith-doubling (partial)
@isnad1 id=tendsto.1h4v.s8.ffa1d865c1ef from=translated src=- shape=584ae6c8 vocab=3df517da
-/
theorem tendsto_smithDoubling_snd (A Q : Matrix n n K)
    (hs : Summable (fun j : ℕ => A ^ j * Q * (Aᴴ) ^ j)) :
    Tendsto (fun j => (smithDoubling A Q j).2) atTop (𝓝 (steinGramian A Q)) := by
  have ht : Tendsto (fun j : ℕ => 2 ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))
  simpa only [Function.comp_def, smithDoubling_eq, steinPartialSum, steinGramian] using hs.hasSum.tendsto_sum_nat.comp ht

/-- Smith doubling converges monotonically to the actual complex Stein
Gramian under the spectral-radius hypothesis itself.
@isnad1 id=and.2h3v.s7.1df01a5f01fc from=translated src=- shape=e672ba1e vocab=8f3d3956
-/
theorem monotone_tendsto_smithDoubling_of_spectralRadius_lt_one (A Q : Matrix n n ℂ)
    (hA : spectralRadius ℂ A < 1) (hQ : Q.PosSemidef) :
    Monotone (fun j => (smithDoubling A Q j).2) ∧
    Tendsto (fun j => (smithDoubling A Q j).2) atTop (𝓝 (steinGramian A Q)) := by
  refine ⟨?_, tendsto_smithDoubling_snd A Q (summable_stein_of_spectralRadius_lt_one A Q hA)⟩
  intro i j hij
  simp only [smithDoubling_eq]
  exact monotone_steinPartialSum A Q hQ (Nat.pow_le_pow_right (by norm_num) hij)

/-- The same actual Smith process converges for real matrices with stable
complexified spectrum.
@isnad1 id=tendsto.1h3v.s6.f7ad22a394b1 from=translated src=- shape=99874e0e vocab=4de3f4dc
-/
theorem tendsto_real_smithDoubling_snd (A Q : Matrix n n ℝ)
    (hA : spectralRadius ℂ (A.map Complex.ofReal) < 1) :
    Tendsto (fun j => (smithDoubling A Q j).2) atTop (𝓝 (steinGramian A Q)) :=
  tendsto_smithDoubling_snd A Q (summable_real_stein_of_complex_spectralRadius_lt_one A Q hA)

end NLAlib
