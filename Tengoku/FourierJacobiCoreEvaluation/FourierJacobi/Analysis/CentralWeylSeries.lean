import Tengoku.FourierJacobiCoreEvaluation.FourierJacobi.Analysis.LatticeLimits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Finite Weyl grouping of the already norm-summable independent family.
These interfaces are used by the actual Haar integration proof. -/

noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra

def centralWeightedTerm (q : ℝ) (a b d : ℂ) (T : ℝ) (r : Fin 3)
    (p : LatticeIndex) : ℂ := ∑ i : Fin 8, weightedLatticeTerm q a b d T (i,r,p)

def centralLatticeCore (q : ℝ) (a b d : ℂ) (T : ℝ) (r : Fin 3) : ℂ :=
  ∑ i : Fin 8, (weylWeights (inverseSqrt q : ℂ) a b i / paperC q) *
    ∑' p : LatticeIndex, masterTerm (q : ℂ) (inverseSqrt q : ℂ) d
      (weylU a b i) (weylV a b i) (T : ℂ) (r.val : ℤ) p

/--
@isnad1 id=eq.0h5v.s5.381446541f9a from=translated src=- shape=f8e55d3d vocab=4ef93096
-/
theorem centralLatticeCore_sum (q : ℝ) (a b d : ℂ) (T : ℝ) :
    (∑ r : Fin 3, centralLatticeCore q a b d T r) = latticeCore q a b d T := by
  unfold centralLatticeCore latticeCore
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  ring

/--
@isnad1 id=summable.8h6v.s7.e029bdbbdbf1 from=translated src=- shape=b70c1d7a vocab=87b6995b
-/
theorem summable_central_norm_majorant (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt q < ‖d‖) (r : Fin 3) :
    Summable (fun p : LatticeIndex =>
      ∑ i : Fin 8, ‖weightedLatticeTerm q a b d T (i,r,p)‖) := by
  have hs := summable_norm_weightedLatticeTerm q T a b d hq ha hb hT₀ hT₁ hd₀ hd₁ hstrict
  exact summable_sum (s := Finset.univ) (fun i _ => (hs.prod_factor i).prod_factor r)

/--
@isnad1 id=hassum.8h6v.s7.c9ec52cc442e from=translated src=- shape=79f75a2d vocab=8d0c6af8
-/
theorem hasSum_centralWeightedTerm (q T : ℝ) (a b d : ℂ) (hq : 2 < q)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 ≤ T) (hT₁ : T ≤ 1)
    (hd₀ : inverseSqrt q ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt q < ‖d‖) (r : Fin 3) :
    HasSum (centralWeightedTerm q a b d T r) (centralLatticeCore q a b d T r) := by
  unfold centralWeightedTerm centralLatticeCore
  have hs := summable_norm_weightedLatticeTerm q T a b d hq ha hb hT₀ hT₁ hd₀ hd₁ hstrict
  have hi (i : Fin 8) := ((hs.prod_factor i).prod_factor r).of_norm.hasSum
  have he := hasSum_sum (s := Finset.univ) (fun i _ => hi i)
  simpa only [weightedLatticeTerm, tsum_mul_left] using he

end FourierJacobi.Analysis
