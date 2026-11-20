import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.GeneralLowerBound
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.ParitySquare
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.PathMetricAdjacency
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.PathMetricBall

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The path-token graph distance dominates the ordered-coordinate distance

This is the half of the path-token metric theorem needed for every volume lower bound.
-/

namespace BurningPath

/-- The ordered-coordinate distance between the endpoints of a walk is at most its length.-/
theorem pathConfigurationDist_le_walk_length {n k : ℕ}
    {A B : Configuration (Fin n) k} (p : (pathTokenGraph n k).Walk A B) :
    pathConfigurationDist A B ≤ p.length := by
  induction p with
  | nil => simp
  | @cons A B C hAB p ih =>
      calc
        pathConfigurationDist A C ≤
            pathConfigurationDist A B + pathConfigurationDist B C :=
          pathConfigurationDist_triangle A B C
        _ = 1 + pathConfigurationDist B C := by
          rw [pathConfigurationDist_eq_one_of_adj A B hAB]
        _ ≤ 1 + p.length := Nat.add_le_add_left ih 1
        _ = (SimpleGraph.Walk.cons hAB p).length := by simp [add_comm]

/-- Every graph ball is contained in the corresponding ordered-coordinate ball.-/
theorem pathToken_closedBall_subset_pathConfigurationBall {n k : ℕ}
    (C : Configuration (Fin n) k) (r : ℕ) :
    (pathTokenGraph n k).closedBall C r ⊆ pathConfigurationBall C r := by
  intro A hA
  have hfinite : (pathTokenGraph n k).edist A C ≠ ⊤ := by
    intro htop
    simp [SimpleGraph.mem_closedBall, htop] at hA
  obtain ⟨p, hp⟩ := (pathTokenGraph n k).exists_walk_of_edist_ne_top hfinite
  have hlength : p.length ≤ r := by
    have hlength' : (p.length : ℕ∞) ≤ (r : ℕ∞) := by
      simpa [SimpleGraph.mem_closedBall, hp] using hA
    exact_mod_cast hlength'
  exact (pathConfigurationDist_le_walk_length p).trans hlength

/-- Path-token graph balls satisfy the exact ambient lattice-ball cardinality bound.-/
theorem pathToken_closedBall_ncard_le {n k : ℕ}
    (C : Configuration (Fin n) k) (r : ℕ) :
    ((pathTokenGraph n k).closedBall C r).ncard ≤ latticeBallPolynomial k r := by
  calc
    ((pathTokenGraph n k).closedBall C r).ncard ≤ (pathConfigurationBall C r).ncard :=
      Set.ncard_mono (pathToken_closedBall_subset_pathConfigurationBall C r)
    _ ≤ latticeBallPolynomial k r := pathConfigurationBall_ncard_le C r

/-- In the square model, a two-token graph ball has at most `2r² + 2r + 1` vertices.-/
theorem twoToken_closedBall_ncard_le {n : ℕ}
    (C : Configuration (Fin n) 2) (r : ℕ) :
    ((pathTokenGraph n 2).closedBall C r).ncard ≤ 2 * r ^ 2 + 2 * r + 1 := by
  simpa [latticeBallPolynomial_two] using pathToken_closedBall_ncard_le C r

/-- The burning number of `F_k(P_n)`, with nonemptiness supplied by `k ≤ n`.-/
noncomputable def pathTokenBurningNumber (n k : ℕ) (hk : k ≤ n) : ℕ := by
  letI := nonempty_configuration_of_le (Fin n) (by simpa using hk)
  exact (pathTokenGraph n k).burningNumber

theorem pathTokenBurningNumber_proof_irrel (n k : ℕ) (h₁ h₂ : k ≤ n) :
    pathTokenBurningNumber n k h₁ = pathTokenBurningNumber n k h₂ := by
  congr

/-- A totalized version used for asymptotic sequences; invalid small parameters are sent to zero.-/
noncomputable def pathTokenBurningNumberTotal (k n : ℕ) : ℕ :=
  if h : k ≤ n then pathTokenBurningNumber n k h else 0

@[simp]
theorem pathTokenBurningNumberTotal_eq {k n : ℕ} (hk : k ≤ n) :
    pathTokenBurningNumberTotal k n = pathTokenBurningNumber n k hk := by
  simp only [pathTokenBurningNumberTotal, dite_eq_left hk]

/--
Part (A), exact finite form: the path-token burning number is at least the least positive `t`
whose ranked ambient volume polynomial reaches `choose n k`.-/
theorem pathToken_volumeThreshold_lower {n k : ℕ} (hnk : k + 1 ≤ n) :
    volumeThreshold k (n.choose k) ≤ pathTokenBurningNumber n k
      ((Nat.le_add_right k 1).trans hnk) := by
  let hk : k ≤ n := (Nat.le_add_right k 1).trans hnk
  letI := nonempty_configuration_of_le (Fin n) (by simpa using hk)
  change volumeThreshold k (n.choose k) ≤ (pathTokenGraph n k).burningNumber
  simpa using
    volumeThreshold_le_burningNumber_of_ball_bound (pathTokenGraph n k) k
      pathToken_closedBall_ncard_le

/-- The same exact lower bound under the minimal nonemptiness assumption `k ≤ n`.-/
theorem pathToken_volumeThreshold_lower_of_le {n k : ℕ} (hk : k ≤ n) :
    volumeThreshold k (n.choose k) ≤ pathTokenBurningNumber n k hk := by
  letI := nonempty_configuration_of_le (Fin n) (by simpa using hk)
  change volumeThreshold k (n.choose k) ≤ (pathTokenGraph n k).burningNumber
  simpa using
    volumeThreshold_le_burningNumber_of_ball_bound (pathTokenGraph n k) k
      pathToken_closedBall_ncard_le

/-- Exact two-token lower bound, including the endpoint case `n = 2`.-/
theorem twoTokenCubicThreshold_lower {n : ℕ} (hn : 2 ≤ n) :
    twoTokenCubicThreshold (n.choose 2) ≤ pathTokenBurningNumber n 2 hn := by
  exact pathToken_volumeThreshold_lower_of_le hn

end BurningPath
