import Tengoku.AbelFormalization.AbelFormalization.SmoothGeometricFamily

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

/--
@isnad1 id=eq.1h3v.s8.50cd5f104b6f from=translated src=- shape=2116a205 vocab=bfb77e21
-/
theorem smoothRegularFiber_eq_regularZeroSet_univ_sub
    {n : ℕ} (g : RealEuclidean n → RealEuclidean n)
    (hg : ContDiff ℝ 1 g) (t : RealEuclidean n) :
    smoothRegularFiber g t =
      regularZeroSet Set.univ (fun x ↦ g x - t) := by
  ext x
  rw [mem_smoothRegularFiber_iff_of_contDiff_square g hg t x]
  simp only [regularZeroSet, Set.mem_ofPred_eq, Set.mem_univ, true_and,
    sub_eq_zero, fderiv_sub_const]

/--
@isnad1 id=iszerore.2h1v.s7.22c5998d396d from=translated src=- shape=f5095026 vocab=90996c13
-/
theorem IsZeroRegularFunctionFamily.of_regularZeroSet_finite
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hfinite : ∀ n (g : RealEuclidean n → RealEuclidean n),
      FunctionTupleInFamily G g → ∀ t,
        (regularZeroSet Set.univ (fun x ↦ g x - t)).Finite) :
    IsZeroRegularFunctionFamily G := by
  intro n g hg t
  rw [smoothRegularFiber_eq_regularZeroSet_univ_sub g
    (by
      rw [contDiff_pi]
      intro i
      exact (hsmooth n (fun x ↦ g x i) (hg i)).of_le (by simp)) t]
  exact hfinite n g hg t

end AbelFormalization
