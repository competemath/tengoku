import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Scalar.TestCertificate.Certificate
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Scalar.FibreObstruction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lemma F.5 (finite test certificate)

Over a normed field `K` with `k! = 0`, there are finite sets of admissible tests for the family
`F` of (F.2) such that every `k`-linear `τ` satisfying condition (1) of Lemma F.4 has a test value
of norm at least `1`. The proof applies `exists_finite_test_certificate_of_fibre` with Lemma F.4
over the prime field `ZMod p` (`AlternatingAnalytic.FibreObstruction.not_exists_fibre_map`).
The paper leaves the hypothesis `k! = 0` implicit in Lemma F.5.
-/

namespace AlternatingAnalytic.TestCertificate

/-- Lemma F.5: finite test sets certify threshold `1` for every `τ` satisfying condition (1).-/
theorem exists_finite_test_certificate (K : Type*) [NormedField K] (k : ℕ)
    (hk : (k.factorial : K) = 0) :
    ∃ T : Submodule K (Fin (k + 1) → K) × Submodule K (Fin k → K) →
        Finset ((Fin k → ((Fin (k + 1) → K) →ₗ[K] (Fin k → K))) × (Fin k → (Fin (k + 1) → K))),
      (∀ j ∈ pairFamily K k, ∀ t ∈ T j,
        (∀ r, j.1.map (t.1 r) ≤ j.2) ∧ ∀ r, t.2 r ∈ j.1) ∧
      ∀ τ : MultilinearMap K (fun _ : Fin k => (Fin (k + 1) → K) →ₗ[K] (Fin k → K))
          ((Fin (k + 1) → K) [⋀^Fin k]→ₗ[K] K),
        FibreCondition1 K k τ →
          ∃ j ∈ pairFamily K k, ∃ t ∈ T j, 1 ≤ ‖τ t.1 t.2‖ :=
  exists_finite_test_certificate_of_fibre K k hk fun _ _ hp =>
    AlternatingAnalytic.FibreObstruction.not_exists_fibre_map hp

end AlternatingAnalytic.TestCertificate
