import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Scalar.TestCertificate.Descent
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.FiniteFieldNorm
import Tengoku.Seed.Analysis.Normed.Group.Ultra
import Tengoku.Seed.Algebra.Algebra.ZMod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The finite test certificate (Lemma F.5), conditional on Lemma F.4

Let `K` be an ultrametric normed field containing a finite field `F`, and assume Lemma F.4 over
`F`: no `F`-multilinear `τ` satisfies conditions (1) and (2). The tests for a pair `j` of (F.2) over
`K` are the base changes of all `F`-rational tuples `(g; ξ)` admissible for `j`; there are
finitely many. If every test value of a `K`-multilinear `τ` satisfying (1) had norm `< 1`, the
`F`-span of the test values would miss `1` (the span consists of elements of norm `< 1`, as
nonzero elements of `F` have norm `1`). An `F`-linear functional `φ : K → F` with `φ 1 = 1`
vanishing on the test values then descends `τ` to an `F`-multilinear map satisfying (1) and (2),
contradicting Lemma F.4 over `F`. This replaces the paper's row reduction by duality over `F`.
For a normed field with `k! = 0` we take `F = ZMod p`, `p` the characteristic.
-/
namespace Tengoku.AlternatingAnalyticCharacteristicP end Tengoku.AlternatingAnalyticCharacteristicP open Tengoku.AlternatingAnalyticCharacteristicP
namespace AlternatingAnalytic.TestCertificate

section Subfield

variable (F K : Type*) [Field F] [Finite F] [NormedField K] [Algebra F K] (k : ℕ)

instance finite_linearMap_coord : Finite ((Fin (k + 1) → F) →ₗ[F] (Fin k → F)) :=
  Module.finite_of_finite F

/-- The finite set of base changes to `K` of all `F`-rational test tuples `(g; ξ)`.-/
noncomputable def rationalTests :
    Finset ((Fin k → ((Fin (k + 1) → K) →ₗ[K] (Fin k → K))) × (Fin k → (Fin (k + 1) → K))) :=
  (Set.finite_range fun q : (Fin k → ((Fin (k + 1) → F) →ₗ[F] (Fin k → F))) ×
      (Fin k → (Fin (k + 1) → F)) =>
    ((fun r => bcMap (q.1 r)), (fun r => (incl (q.2 r) : Fin (k + 1) → K)))).toFinset

/-- The tests for a pair `j = (Σ, Σ')`: the rational test tuples admissible for `j`.-/
noncomputable def testSets (j : Submodule K (Fin (k + 1) → K) × Submodule K (Fin k → K)) :
    Finset ((Fin k → ((Fin (k + 1) → K) →ₗ[K] (Fin k → K))) × (Fin k → (Fin (k + 1) → K))) := by
  classical
  exact (rationalTests F K k).filter fun t => (∀ r, j.1.map (t.1 r) ≤ j.2) ∧ ∀ r, t.2 r ∈ j.1

variable [IsUltrametricDist K]

/-- If Lemma F.4 holds over a finite field `F ⊆ K`, the `F`-rational tests certify threshold `1`
for every `τ` satisfying condition (1).-/
theorem exists_test_certificate_of_subfield
    (hF4 : ¬ ∃ τ : MultilinearMap F (fun _ : Fin k => (Fin (k + 1) → F) →ₗ[F] (Fin k → F))
        ((Fin (k + 1) → F) [⋀^Fin k]→ₗ[F] F),
      FibreCondition1 F k τ ∧ FibreCondition2 F k τ) :
    ∃ T : Submodule K (Fin (k + 1) → K) × Submodule K (Fin k → K) →
        Finset ((Fin k → ((Fin (k + 1) → K) →ₗ[K] (Fin k → K))) × (Fin k → (Fin (k + 1) → K))),
      (∀ j ∈ pairFamily K k, ∀ t ∈ T j,
        (∀ r, j.1.map (t.1 r) ≤ j.2) ∧ ∀ r, t.2 r ∈ j.1) ∧
      ∀ τ : MultilinearMap K (fun _ : Fin k => (Fin (k + 1) → K) →ₗ[K] (Fin k → K))
          ((Fin (k + 1) → K) [⋀^Fin k]→ₗ[K] K),
        FibreCondition1 K k τ →
          ∃ j ∈ pairFamily K k, ∃ t ∈ T j, 1 ≤ ‖τ t.1 t.2‖ := by
  classical
  refine ⟨testSets F K k, fun j _ t ht => (Finset.mem_filter.mp ht).2, fun τ hτ => ?_⟩
  by_contra hlt
  push Not at hlt
  let X : Set K := {x | ∃ j ∈ pairFamily K k, ∃ t ∈ testSets F K k j, x = τ t.1 t.2}
  have hone : (1 : K) ∈ Submodule.span F X := by
    by_contra hnot
    obtain ⟨f, hf1, hfX⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    let φ : K →ₗ[F] F := (f 1)⁻¹ • f
    have hφ : φ 1 = 1 := by simp [φ, hf1]
    have hφX : ∀ x ∈ X, φ x = 0 := by
      intro x hx
      have hmem : f x ∈ (Submodule.span F X).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span hx)
      rw [hfX, Submodule.mem_bot] at hmem
      simp [φ, hmem]
    apply hF4
    refine ⟨descendFibreMap φ τ, fibreCondition1_descendFibreMap hφ hτ, ?_⟩
    intro P hP g hg ξ hξ
    obtain ⟨j, hj, hgj, hξj⟩ := exists_pairFamily_transfer (K := K) hP hg hξ
    rw [descendFibreMap_apply]
    refine hφX _ ⟨j, hj, ((fun r => bcMap (g r)), fun r => incl (ξ r)), ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨?_, hgj, hξj⟩
    exact (Set.Finite.mem_toFinset _).mpr ⟨(g, ξ), rfl⟩
  have hsmall : ∀ x ∈ Submodule.span F X, ‖x‖ < 1 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, t, ht, rfl⟩ := hx
      exact hlt j hj t ht
    | zero => simp
    | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)
    | smul c x _ hx =>
      rw [Algebra.smul_def, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (norm_finiteField_map_le_one (algebraMap F K) c)).trans_lt hx
  simpa using hsmall 1 hone

end Subfield

/-- Lemma F.5, assuming Lemma F.4 over the prime fields: if `k! = 0` in `K`, finite test sets
certify threshold `1` for every `K`-multilinear `τ` satisfying condition (1) of Lemma F.4.-/
theorem exists_finite_test_certificate_of_fibre (K : Type*) [NormedField K] (k : ℕ)
    (hk : (k.factorial : K) = 0)
    (hF4 : ∀ (p : ℕ) [Fact p.Prime], (k.factorial : ZMod p) = 0 →
      ¬ ∃ τ : MultilinearMap (ZMod p)
          (fun _ : Fin k => (Fin (k + 1) → ZMod p) →ₗ[ZMod p] (Fin k → ZMod p))
          ((Fin (k + 1) → ZMod p) [⋀^Fin k]→ₗ[ZMod p] ZMod p),
        FibreCondition1 (ZMod p) k τ ∧ FibreCondition2 (ZMod p) k τ) :
    ∃ T : Submodule K (Fin (k + 1) → K) × Submodule K (Fin k → K) →
        Finset ((Fin k → ((Fin (k + 1) → K) →ₗ[K] (Fin k → K))) × (Fin k → (Fin (k + 1) → K))),
      (∀ j ∈ pairFamily K k, ∀ t ∈ T j,
        (∀ r, j.1.map (t.1 r) ≤ j.2) ∧ ∀ r, t.2 r ∈ j.1) ∧
      ∀ τ : MultilinearMap K (fun _ : Fin k => (Fin (k + 1) → K) →ₗ[K] (Fin k → K))
          ((Fin (k + 1) → K) [⋀^Fin k]→ₗ[K] K),
        FibreCondition1 K k τ →
          ∃ j ∈ pairFamily K k, ∃ t ∈ T j, 1 ≤ ‖τ t.1 t.2‖ := by
  have hdvd : ringChar K ∣ k.factorial := (ringChar.spec K _).mp hk
  have hp0 : ringChar K ≠ 0 := fun h => by
    rw [h, zero_dvd_iff] at hdvd
    exact Nat.factorial_ne_zero k hdvd
  have : Fact (ringChar K).Prime := ⟨(CharP.char_is_prime_or_zero K _).resolve_right hp0⟩
  let : Algebra (ZMod (ringChar K)) K := ZMod.algebra K _
  have : IsUltrametricDist K := charP_isUltrametricDist (ringChar K)
  exact exists_test_certificate_of_subfield (ZMod (ringChar K)) K k
    (hF4 _ ((ZMod.natCast_eq_zero_iff _ _).mpr hdvd))

end AlternatingAnalytic.TestCertificate
-- Tengoku: root names of this library moved to Tengoku.AlternatingAnalyticCharacteristicP so they do not collide with other libraries (generated)
