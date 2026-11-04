import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.TorusDifferential
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SphereFamily

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The exact scalar lift identities and minimality in the induced Hermitian
metric. The norm is the operator norm on the tangent subspace identified in
`TorusDifferential`, rather than the norm of an ambient extension. -/

namespace DuistermaatVanDerKallen

noncomputable section

/-- The explicit coordinate lift, embedded in the actual tangent subspace.-/
def normalizedTangentLift {d : ℕ} (z g : Fin d → ℂ) (a : ℂ) : torusTangentSpace z :=
  ⟨torusTangentMap z (scalarLift g (torusWeight z) a), ⟨_, rfl⟩⟩

/-- First identity in manuscript `eq:gradient-identities`.-/
theorem normalizedTangentLift_right_inverse {d : ℕ} (z g : Fin d → ℂ) (a : ℂ)
    (h : differentialNormSq g (torusWeight z) ≠ 0) :
    restrictedDifferential z g (normalizedTangentLift z g a) = a := by
  simpa [restrictedDifferential_apply, normalizedTangentLift] using
    scalarLift_right_inverse g (torusWeight z) a h

theorem normalizedTangentLift_norm_sq {d : ℕ} (z g : Fin d → ℂ) (a : ℂ)
    (h : differentialNormSq g (torusWeight z) ≠ 0) :
    ‖normalizedTangentLift z g a‖ ^ 2 =
      ‖a‖ ^ 2 / ‖restrictedDifferential z g‖ ^ 2 := by
  change ‖torusTangentMap z (scalarLift g (torusWeight z) a)‖ ^ 2 = _
  rw [torusTangentMap_norm_sq, restrictedDifferential_norm_sq]
  simpa only [Complex.normSq_eq_norm_sq] using
    scalarLift_weighted_normSq g (torusWeight z) a (torusWeight_pos z) h

/-- Second identity in manuscript `eq:gradient-identities`, in unsquared norms.-/
theorem normalizedTangentLift_norm {d : ℕ} (z g : Fin d → ℂ) (a : ℂ)
    (h : differentialNormSq g (torusWeight z) ≠ 0) :
    ‖normalizedTangentLift z g a‖ = ‖a‖ / ‖restrictedDifferential z g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg (normalizedTangentLift z g a))
    (div_nonneg (norm_nonneg a) (norm_nonneg (restrictedDifferential z g)))).mp
  rw [div_pow]
  exact normalizedTangentLift_norm_sq z g a h

/-- Positivity of the operator norm at a regular point.-/
theorem restrictedDifferential_norm_pos {d : ℕ} (z g : Fin d → ℂ)
    (h : differentialNormSq g (torusWeight z) ≠ 0) :
    0 < ‖restrictedDifferential z g‖ := by
  apply lt_of_le_of_ne (norm_nonneg (restrictedDifferential z g))
  intro heq
  apply h
  rw [← restrictedDifferential_norm_sq, ← heq]
  norm_num

/-- Every competing tangent lift has at least the norm of the explicit lift.-/
theorem normalizedTangentLift_minimal {d : ℕ} (z g : Fin d → ℂ) (a : ℂ)
    (h : differentialNormSq g (torusWeight z) ≠ 0)
    (v : torusTangentSpace z) (hv : restrictedDifferential z g v = a) :
    ‖normalizedTangentLift z g a‖ ≤ ‖v‖ := by
  rw [normalizedTangentLift_norm z g a h]
  apply (div_le_iff₀ (restrictedDifferential_norm_pos z g h)).2
  simpa [hv, mul_comm] using (restrictedDifferential z g).le_opNorm v

/-- At a regular point the restricted scalar differential is surjective.-/
theorem restrictedDifferential_surjective {d : ℕ} (z g : Fin d → ℂ)
    (h : differentialNormSq g (torusWeight z) ≠ 0) :
    Function.Surjective (restrictedDifferential z g) :=
  fun a => ⟨normalizedTangentLift z g a, normalizedTangentLift_right_inverse z g a h⟩

/-- The complex and real operator norms coincide, as required by real ODE theory.-/
theorem restrictedDifferential_real_norm {d : ℕ} (z g : Fin d → ℂ) :
    ‖(restrictedDifferential z g).restrictScalars ℝ‖ =
      Real.sqrt (differentialNormSq g (torusWeight z)) := by
  rw [ContinuousLinearMap.norm_restrictScalars, restrictedDifferential_norm]

/-- The polynomial coordinate expression used by the semialgebraic sphere family
is exactly this restricted operator norm at the embedded torus point.-/
theorem ambientDifferentialNorm_eq_restricted {d : ℕ}
    (G : Fin d → AmbientPolynomial d) (z : Fin d → ℂ) :
    ambientDifferentialNorm G (torusEmbed z) =
      ‖restrictedDifferential z (fun i => ambientEval (G i) (torusEmbed z))‖ := by
  rw [restrictedDifferential_norm]
  unfold ambientDifferentialNorm
  congr 2
  funext i
  simp [torusWeight, torusEmbed]

end
end DuistermaatVanDerKallen
