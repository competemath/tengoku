import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.FiniteCoordinateCoefficients
import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coefficient lifts in finite coordinates

On `Fin d → K` with the maximum norm, a bounded `n`-linear map whose diagonal lies in a
subspace `W` has a `W`-valued representative with the same diagonal and norm at most
`d ^ n` times the original. This is the coefficient bound of Theorem 4.4.
-/

noncomputable section

namespace FiniteCoordinateReflection

open scoped BigOperators

variable {K Z : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup Z] [NormedSpace K Z] {d n : ℕ}

/-- A coordinate monomial, with a coefficient in a normed vector space.-/
def coordinateMonomial (r : Fin n → Fin d) (z : Z) :
    ContinuousMultilinearMap K (fun _ : Fin n => Fin d → K) Z :=
  (ContinuousMultilinearMap.mkPiRing K (Fin n) z).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (r i))

@[simp]
theorem coordinateMonomial_apply (r : Fin n → Fin d) (z : Z)
    (m : Fin n → Fin d → K) :
    coordinateMonomial r z m = (∏ i, m i (r i)) • z := rfl

theorem norm_coordinateMonomial_le (r : Fin n → Fin d) (z : Z) :
    ‖coordinateMonomial (K := K) r z‖ ≤ ‖z‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro m
  rw [coordinateMonomial_apply, norm_smul, mul_comm]
  gcongr
  rw [norm_prod]
  gcongr with i
  exact norm_le_pi_norm (m i) (r i)

/-- The lift with bound `d ^ n`, assuming the grouped coefficients lie in `W`.-/
theorem exists_lift_of_sumOfType_mem (W : Submodule K Z)
    (p : ContinuousMultilinearMap K (fun _ : Fin n => Fin d → K) Z)
    (hc : ∀ α : Fin d → ℕ,
      p.toMultilinearMap.sumOfType (fun j => Pi.single j 1) α ∈ W) :
    ∃ q : ContinuousMultilinearMap K (fun _ : Fin n => Fin d → K) W,
      (∀ x, (q (fun _ => x) : Z) = p (fun _ => x)) ∧
      ‖q‖ ≤ (d : ℝ) ^ n * ‖p‖ := by
  classical
  let T := Set.range (Polarization.selectionType (J := Fin d) (k := n))
  let : Fintype T := (Set.finite_range _).fintype
  let g : (Fin n → Fin d) → T := fun f => ⟨Polarization.selectionType f, f, rfl⟩
  let r : T → Fin n → Fin d := fun t => Classical.choose t.property
  have hr (t : T) : Polarization.selectionType (r t) = t.val :=
    Classical.choose_spec t.property
  let c : T → W := fun t =>
    ⟨p.toMultilinearMap.sumOfType (fun j => Pi.single j 1) t.val, hc t.val⟩
  let q : ContinuousMultilinearMap K (fun _ : Fin n => Fin d → K) W :=
    ∑ t : T, coordinateMonomial (r t) (c t)
  have hfilter (t : T) :
      (Finset.univ.filter (fun f : Fin n → Fin d => g f = t)) =
        Finset.univ.filter (fun f : Fin n → Fin d =>
          Polarization.selectionType f = t.val) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Subtype.ext_iff
  have hprod (t : T) (f : Fin n → Fin d)
      (hf : Polarization.selectionType f = t.val) (x : Fin d → K) :
      (∏ i, x (r t i)) = ∏ i, x (f i) := by
    rw [← Polarization.monomial_selectionMultiIndex,
      ← Polarization.monomial_selectionMultiIndex]
    congr 1
    exact Finsupp.equivFunOnFinite.symm.injective.eq_iff.mpr ((hr t).trans hf.symm)
  refine ⟨q, ?_, ?_⟩
  · intro x
    have hx : (∑ j, x j • Pi.single j (1 : K)) = x := by
      ext j
      simp [← Pi.single_smul]
    calc
      (q (fun _ => x) : Z) = ∑ t : T,
          (∏ i, x (r t i)) • p.toMultilinearMap.sumOfType
            (fun j => Pi.single j 1) t.val := by
        simp [q, c, coordinateMonomial_apply]
      _ = ∑ t : T, ∑ f ∈ Finset.univ.filter (fun f => g f = t),
          (∏ i, x (f i)) • p (fun i => Pi.single (f i) 1) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [hfilter, MultilinearMap.sumOfType, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro f hf
        rw [hprod t f (Finset.mem_filter.mp hf).2 x]
        rfl
      _ = ∑ f : Fin n → Fin d,
          (∏ i, x (f i)) • p (fun i => Pi.single (f i) 1) :=
        Finset.sum_fiberwise Finset.univ g _
      _ = p (fun _ => x) := by
        conv_rhs => rw [← hx]
        rw [p.map_sum]
        apply Finset.sum_congr rfl
        intro f _
        exact (p.map_smul_univ (fun i => x (f i)) (fun i => Pi.single (f i) 1)).symm
  · have hc_norm (t : T) : ‖c t‖ ≤
        ∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin d => g f = t), ‖p‖ := by
      rw [hfilter]
      change ‖p.toMultilinearMap.sumOfType (fun j => Pi.single j 1) t.val‖ ≤ _
      unfold MultilinearMap.sumOfType
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun f _ => ?_)
      simpa only [ContinuousMultilinearMap.coe_coe, Pi.norm_single, norm_one,
        Finset.prod_const_one, mul_one] using p.le_opNorm (fun i => Pi.single (f i) 1)
    calc
      ‖q‖ ≤ ∑ t : T, ‖coordinateMonomial (r t) (c t)‖ := norm_sum_le _ _
      _ ≤ ∑ t : T, ‖c t‖ := Finset.sum_le_sum fun t _ => norm_coordinateMonomial_le _ _
      _ ≤ ∑ t : T, ∑ f ∈ Finset.univ.filter (fun f => g f = t), ‖p‖ :=
        Finset.sum_le_sum fun t _ => hc_norm t
      _ = ∑ _f : Fin n → Fin d, ‖p‖ := Finset.sum_fiberwise Finset.univ g _
      _ = (d : ℝ) ^ n * ‖p‖ := by simp

end FiniteCoordinateReflection
