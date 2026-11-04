import Tengoku.Seed.Analysis.InnerProductSpace.PiL2
import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension
import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The manuscript's proper affine embedding, with the Euclidean (L2) norm.
The ambient coordinates contain both each torus coordinate and its inverse. -/

namespace DuistermaatVanDerKallen

abbrev TorusAmbient (d : ℕ) := EuclideanSpace ℂ (Fin d ⊕ Fin d)

/-- The closed affine torus, including the rank-zero case.-/
def affineTorus (d : ℕ) : Set (TorusAmbient d) :=
  {x | ∀ i, x (.inl i) * x (.inr i) = 1}

/-- The coordinate embedding. Its torus domain is imposed in `embed_mem`.-/
noncomputable def torusEmbed {d : ℕ} (z : Fin d → ℂ) : TorusAmbient d :=
  WithLp.toLp 2 (Sum.elim z fun i => (z i)⁻¹)

/--
@isnad1 id=mem.1h2v.s5.413f72c47f78 from=translated src=- shape=40ac954f vocab=af70165c
-/
theorem embed_mem {d : ℕ} {z : Fin d → ℂ} (hz : ∀ i, z i ≠ 0) :
    torusEmbed z ∈ affineTorus d := by
  intro i
  exact mul_inv_cancel₀ (hz i)

/--
@isnad1 id=isclosed.0h1v.s5.0270151694b0 from=translated src=- shape=fc2c1e2b vocab=793f15b5
-/
theorem affineTorus_isClosed (d : ℕ) : IsClosed (affineTorus d) := by
  simp only [affineTorus, Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_eq ((PiLp.continuous_apply 2 (fun _ : Fin d ⊕ Fin d => ℂ) (.inl i)).mul (PiLp.continuous_apply 2 (fun _ : Fin d ⊕ Fin d => ℂ) (.inr i)))
    continuous_const

/--
@isnad1 id=ne.1h3v.s6.f95e82648cad from=translated src=- shape=bb17a970 vocab=e9be8316
-/
theorem affineTorus_coordinate_ne_zero {d : ℕ} {x : TorusAmbient d}
    (hx : x ∈ affineTorus d) (i : Fin d) : x (.inl i) ≠ 0 := by
  exact left_ne_zero_of_mul_eq_one (hx i)

/--
@isnad1 id=eq.1h3v.s6.1d945464731a from=translated src=- shape=60f54031 vocab=57732d13
-/
theorem affineTorus_inverse_coordinate {d : ℕ} {x : TorusAmbient d}
    (hx : x ∈ affineTorus d) (i : Fin d) : x (.inr i) = (x (.inl i))⁻¹ := by
  exact eq_inv_of_mul_eq_one_right (hx i)

/--
@isnad1 id=eq.1h2v.s5.a48fdcd23cd4 from=translated src=- shape=f3135678 vocab=587faf1b
-/
theorem embed_coordinates {d : ℕ} {x : TorusAmbient d} (hx : x ∈ affineTorus d) :
    torusEmbed (fun i => x (.inl i)) = x := by
  apply PiLp.ext
  intro i
  cases i with
  | inl i => rfl
  | inr i => exact (affineTorus_inverse_coordinate hx i).symm

/-- Proper-radius sublevel sets are compact in the closed affine model.
@isnad1 id=iscompac.0h2v.s7.8ffb234941b6 from=translated src=- shape=1f054a83 vocab=62ca8ff5
-/
theorem affineTorus_radius_isCompact (d : ℕ) (R : ℝ) :
    IsCompact (affineTorus d ∩ Metric.closedBall 0 R) :=
  (isCompact_closedBall (0 : TorusAmbient d) R).inter_left (affineTorus_isClosed d)

/-- Both directions of coordinate escape are controlled by the same proper radius.
@isnad1 id=and.1h3v.s7.64c9e932f96e from=translated src=- shape=7f1a352e vocab=07f85f6d
-/
theorem affineTorus_coordinate_bounds {d : ℕ} {x : TorusAmbient d}
    (hx : x ∈ affineTorus d) (i : Fin d) :
    ‖x (.inl i)‖ ≤ ‖x‖ ∧ ‖(x (.inl i))⁻¹‖ ≤ ‖x‖ := by
  constructor
  · exact PiLp.norm_apply_le x (.inl i)
  · rw [← affineTorus_inverse_coordinate hx i]
    exact PiLp.norm_apply_le x (.inr i)

/-- The norm really is the induced Hermitian radius, not a sup/product norm.
@isnad1 id=eq.0h2v.s7.4d2fb2a11816 from=translated src=- shape=9df8b1a1 vocab=51f0d45a
-/
theorem torusEmbed_norm_sq {d : ℕ} (z : Fin d → ℂ) :
    ‖torusEmbed z‖ ^ 2 = ∑ i, (‖z i‖ ^ 2 + ‖z i‖⁻¹ ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [torusEmbed, Fintype.sum_sum_type, Finset.sum_add_distrib]

end DuistermaatVanDerKallen
