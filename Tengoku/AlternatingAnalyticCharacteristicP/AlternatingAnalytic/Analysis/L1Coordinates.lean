import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.L1ProductSummation
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.L1FiniteSupport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounded coefficient arrays on ℓ¹

A bounded array `c : (Fin d → J) → W` with `‖c a‖ ≤ M` defines a continuous `d`-linear
map on `ℓ¹(J, K)`, `x ↦ ∑_a (∏_r x_r(a_r)) • c a`, of norm at most `M`. This is the
summation used in the proof of Theorem 4.5(2). The output `W` must be complete;
`K` need not be.
-/

open scoped lp BigOperators

namespace L1Coordinates

variable {K J W : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup W] [NormedSpace K W]

noncomputable local instance : DecidableEq J := Classical.decEq J

/-- The coordinate monomial `x ↦ (∏_r x_r(a_r)) • c a`.-/
noncomputable def coordinateTerm {d : ℕ} (c : (Fin d → J) → W) (a : Fin d → J) :
    MultilinearMap K (fun _ : Fin d => lp (fun _ : J => K) 1) W :=
  (MultilinearMap.mkPiRing K (Fin d) (c a)).compLinearMap
    (fun r => lp.evalₗ (fun _ : J => K) 1 (a r))

/--
@isnad1 id=eq.0h7v.s11.e0c158193cb5 from=translated src=- shape=7edd2e97 vocab=5daf1ab1
-/
@[simp]
theorem coordinateTerm_apply {d : ℕ} (c : (Fin d → J) → W) (a : Fin d → J)
    (x : Fin d → lp (fun _ : J => K) 1) :
    coordinateTerm (K := K) c a x = (∏ r, x r (a r)) • c a := rfl

/--
@isnad1 id=le.1h8v.s11.3a3f132dc549 from=translated src=- shape=41fb1018 vocab=e3c64383
-/
theorem norm_coordinateTerm_le {d : ℕ} (c : (Fin d → J) → W) (M : ℝ)
    (hc : ∀ a, ‖c a‖ ≤ M) (x : Fin d → lp (fun _ : J => K) 1) (a : Fin d → J) :
    ‖coordinateTerm (K := K) c a x‖ ≤ M * ∏ r, ‖x r (a r)‖ := by
  rw [coordinateTerm_apply, norm_smul, norm_prod, mul_comm]
  exact mul_le_mul_of_nonneg_right (hc a) (Finset.prod_nonneg fun r _ => norm_nonneg _)

/-- The terms of the array, evaluated at `x`, are absolutely summable.
@isnad1 id=summable.1h7v.s11.c4b6ec3c1f8d from=translated src=- shape=b40b7689 vocab=7ab75875
-/
theorem summable_norm_coordinateTerm {d : ℕ} (c : (Fin d → J) → W) (M : ℝ)
    (hc : ∀ a, ‖c a‖ ≤ M) (x : Fin d → lp (fun _ : J => K) 1) :
    Summable (fun a => ‖coordinateTerm (K := K) c a x‖) :=
  ((hasSum_prod_norm d x).summable.mul_left M).of_nonneg_of_le
    (fun _ => norm_nonneg _) (norm_coordinateTerm_le c M hc x)

variable [CompleteSpace W]

/--
@isnad1 id=summable.1h7v.s11.d6b5c6a3f5ce from=translated src=- shape=db482161 vocab=ee1d02ce
-/
theorem summable_coordinateTerm {d : ℕ} (c : (Fin d → J) → W) (M : ℝ)
    (hc : ∀ a, ‖c a‖ ≤ M) (x : Fin d → lp (fun _ : J => K) 1) :
    Summable (fun a => coordinateTerm (K := K) c a x) :=
  (summable_norm_coordinateTerm (K := K) c M hc x).of_norm

/-- The unconditional sum of the coordinate monomials, as a multilinear map.-/
noncomputable def multilinearOfBounded {d : ℕ} (c : (Fin d → J) → W) (M : ℝ)
    (hc : ∀ a, ‖c a‖ ≤ M) :
    MultilinearMap K (fun _ : Fin d => lp (fun _ : J => K) 1) W where
  toFun x := ∑' a, coordinateTerm (K := K) c a x
  map_update_add' x r y z := by
    simp only [MultilinearMap.map_update_add]
    exact (summable_coordinateTerm (K := K) c M hc _).tsum_add
      (summable_coordinateTerm (K := K) c M hc _)
  map_update_smul' x r t y := by
    simp only [MultilinearMap.map_update_smul]
    exact (summable_coordinateTerm (K := K) c M hc _).tsum_const_smul t

/--
@isnad1 id=le.1h7v.s11.e27cc473e6d7 from=translated src=- shape=7f5ee2fc vocab=debe1451
-/
theorem norm_multilinearOfBounded_le {d : ℕ} (c : (Fin d → J) → W) (M : ℝ)
    (hc : ∀ a, ‖c a‖ ≤ M) (x : Fin d → lp (fun _ : J => K) 1) :
    ‖multilinearOfBounded (K := K) c M hc x‖ ≤ M * ∏ r, ‖x r‖ :=
  (summable_coordinateTerm (K := K) c M hc x).hasSum.norm_le_of_bounded
    ((hasSum_prod_norm d x).mul_left M) (norm_coordinateTerm_le c M hc x)

/-- The continuous multilinear map associated to a bounded coefficient array.-/
noncomputable def continuousMultilinearOfBounded {d : ℕ} (c : (Fin d → J) → W)
    (M : ℝ) (hc : ∀ a, ‖c a‖ ≤ M) :
    ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : J => K) 1) W :=
  (multilinearOfBounded (K := K) c M hc).mkContinuous M (norm_multilinearOfBounded_le c M hc)

/--
@isnad1 id=hassum.1h7v.s12.fd14aadee0f3 from=translated src=- shape=11b5d1dd vocab=50fc1af9
-/
theorem continuousMultilinearOfBounded_hasSum {d : ℕ} (c : (Fin d → J) → W)
    (M : ℝ) (hc : ∀ a, ‖c a‖ ≤ M) (x : Fin d → lp (fun _ : J => K) 1) :
    HasSum (fun a : Fin d → J => (∏ r, x r (a r)) • c a)
      (continuousMultilinearOfBounded (K := K) c M hc x) :=
  (summable_coordinateTerm (K := K) c M hc x).hasSum

/-- On a tuple of basis vectors `e_{a_r}` the map takes the value `c a`.
@isnad1 id=eq.1h7v.s12.c938da0e3b9b from=translated src=- shape=68ba3e0c vocab=350fc5d5
-/
@[simp]
theorem continuousMultilinearOfBounded_single {d : ℕ} (c : (Fin d → J) → W)
    (M : ℝ) (hc : ∀ a, ‖c a‖ ≤ M) (a : Fin d → J) :
    continuousMultilinearOfBounded (K := K) c M hc (fun r => lp.single 1 (a r) (1 : K)) = c a := by
  classical
  change (∑' b, coordinateTerm (K := K) c b (fun r => lp.single 1 (a r) (1 : K))) = c a
  rw [tsum_eq_single a]
  · simp [coordinateTerm_apply]
  · intro b hba
    obtain ⟨r, hr⟩ := Function.ne_iff.mp hba
    rw [coordinateTerm_apply,
      Finset.prod_eq_zero (Finset.mem_univ r) (lp.single_apply_ne 1 (a r) 1 hr), zero_smul]

end L1Coordinates
