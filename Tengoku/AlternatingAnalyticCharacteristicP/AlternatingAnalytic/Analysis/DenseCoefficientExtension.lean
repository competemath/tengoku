import Tengoku.Seed.Analysis.Normed.Operator.LinearIsometry
import Tengoku.Seed.Topology.MetricSpace.Pseudo.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extending coefficient maps across a dense isometry

A linear coefficient map on a dense subspace, determined by a map `L` that is
constant on balls of radius one, extends to the whole space, keeping its
defining identity and its linear norm bound. This is used in Proposition C.3.
-/

noncomputable section

namespace AlternatingAnalytic

variable {κ E B V W : Type*} [Field κ]
  [NormedAddCommGroup E] [Module κ E]
  [NormedAddCommGroup B] [Module κ B]
  [AddCommGroup V] [Module κ V] [AddCommGroup W] [Module κ W]

/-- If `L` is constant on balls of radius one and `Ω ∘ η = L ∘ i` on the dense
subspace, then `η` extends to `ηB` with `Ω ∘ ηB = L` and the same bound on `cost`.-/
theorem exists_denseCoefficientExtension
    (i : E →ₗ[κ] B) (hi : Isometry i) (hd : DenseRange i)
    (Ω : V →ₗ[κ] W) (hΩ : Function.Injective Ω)
    (L : B →ₗ[κ] W)
    (hloc : ∀ b b', ‖b - b'‖ < 1 → L b = L b')
    (η : E →ₗ[κ] V) (hη : ∀ x, Ω (η x) = L (i x))
    (cost : V → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, cost (η x) ≤ C * ‖x‖) :
    ∃ ηB : B →ₗ[κ] V,
      (∀ b, Ω (ηB b) = L b) ∧
      (∀ x, ηB (i x) = η x) ∧
      (∀ b, cost (ηB b) ≤ C * ‖b‖) := by
  classical
  have hex (b : B) : ∃ v, Ω v = L b := by
    obtain ⟨x, hx⟩ := hd.exists_dist_lt b zero_lt_one
    exact ⟨η x, (hη x).trans (hloc b (i x) (by simpa [dist_eq_norm] using hx)).symm⟩
  let ηB : B →ₗ[κ] V :=
    { toFun := fun b => (hex b).choose
      map_add' := fun b b' => hΩ (by
        rw [(hex (b + b')).choose_spec, Ω.map_add, (hex b).choose_spec,
          (hex b').choose_spec, L.map_add])
      map_smul' := fun c b => hΩ (by
        rw [(hex (c • b)).choose_spec, Ω.map_smul, (hex b).choose_spec, L.map_smul]
        rfl) }
  have hηB (b : B) : Ω (ηB b) = L b := (hex b).choose_spec
  have hfix (x : E) : ηB (i x) = η x := hΩ ((hηB (i x)).trans (hη x).symm)
  refine ⟨ηB, hηB, hfix, ?_⟩
  intro b
  apply le_of_forall_pos_le_add
  intro ε hε
  have hδ : 0 < min 1 (ε / (C + 1)) := lt_min zero_lt_one (div_pos hε (by linarith))
  obtain ⟨x, hx⟩ := hd.exists_dist_lt b hδ
  rw [dist_comm, dist_eq_norm] at hx
  have hx1 : ‖i x - b‖ < 1 := (show ‖i x - b‖ < min 1 (ε / (C + 1)) by
    simpa [dist_eq_norm] using hx).trans_le (min_le_left _ _)
  have hxe : ‖i x - b‖ < ε / (C + 1) := (show ‖i x - b‖ < min 1 (ε / (C + 1)) by
    simpa [dist_eq_norm] using hx).trans_le (min_le_right _ _)
  have hv : ηB b = η x := hΩ ((hηB b).trans ((hloc (i x) b hx1).symm.trans (hη x).symm))
  have hnorm : ‖x‖ ≤ ‖b‖ + ‖i x - b‖ := by
    rw [← hi.norm_map_of_map_zero i.map_zero]
    have h := norm_add_le b (i x - b)
    simpa [add_sub_cancel_left] using h
  rw [hv]
  have hmul : (C + 1) * ‖i x - b‖ < ε := by
    have := (lt_div_iff₀ (show 0 < C + 1 by linarith)).mp hxe
    nlinarith
  calc
    cost (η x) ≤ C * ‖x‖ := hbound x
    _ ≤ C * (‖b‖ + ‖i x - b‖) := mul_le_mul_of_nonneg_left hnorm hC
    _ ≤ C * ‖b‖ + ε := by nlinarith [norm_nonneg (i x - b)]

end AlternatingAnalytic
