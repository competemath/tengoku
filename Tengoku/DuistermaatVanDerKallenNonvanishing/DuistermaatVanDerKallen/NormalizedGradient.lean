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

/-- First identity in manuscript `eq:gradient-identities`.
@isnad1 id=eq.1h4v.s11.a1ce001e9180 from=translated src=- shape=095487a4 vocab=81e430f0
-/
theorem normalizedTangentLift_right_inverse {d : ℕ} (z g : Fin d → ℂ) (a : ℂ)
    (h : differentialNormSq g (torusWeight z) ≠ 0) :
    restrictedDifferential z g (normalizedTangentLift z g a) = a := by
  simpa [restrictedDifferential_apply, normalizedTangentLift] using
    scalarLift_right_inverse g (torusWeight z) a h

/--
@isnad1 id=eq.1h4v.s11.02c45ce86ed9 from=translated src=- shape=f1421b7a vocab=06ce5dd2
-/
theorem normalizedTangentLift_norm_sq {d : ℕ} (z g : Fin d → ℂ) (a : ℂ)
    (h : differentialNormSq g (torusWeight z) ≠ 0) :
    ‖normalizedTangentLift z g a‖ ^ 2 =
      ‖a‖ ^ 2 / ‖restrictedDifferential z g‖ ^ 2 := by
  change ‖torusTangentMap z (scalarLift g (torusWeight z) a)‖ ^ 2 = _
  rw [torusTangentMap_norm_sq, restrictedDifferential_norm_sq]
  simpa only [Complex.normSq_eq_norm_sq] using
    scalarLift_weighted_normSq g (torusWeight z) a (torusWeight_pos z) h

/-- Second identity in manuscript `eq:gradient-identities`, in unsquared norms.
@isnad1 id=eq.1h4v.s11.b0a261df9ecb from=translated src=- shape=096b82f1 vocab=f0e884bb
-/
theorem normalizedTangentLift_norm {d : ℕ} (z g : Fin d → ℂ) (a : ℂ)
    (h : differentialNormSq g (torusWeight z) ≠ 0) :
    ‖normalizedTangentLift z g a‖ = ‖a‖ / ‖restrictedDifferential z g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg (normalizedTangentLift z g a))
    (div_nonneg (norm_nonneg a) (norm_nonneg (restrictedDifferential z g)))).mp
  rw [div_pow]
  exact normalizedTangentLift_norm_sq z g a h

/-- Positivity of the operator norm at a regular point.
@isnad1 id=lt.1h3v.s10.a4da14033693 from=translated src=- shape=2317bdfd vocab=3c64a66a
-/
theorem restrictedDifferential_norm_pos {d : ℕ} (z g : Fin d → ℂ)
    (h : differentialNormSq g (torusWeight z) ≠ 0) :
    0 < ‖restrictedDifferential z g‖ := by
  apply lt_of_le_of_ne (norm_nonneg (restrictedDifferential z g))
  intro heq
  apply h
  rw [← restrictedDifferential_norm_sq, ← heq]
  norm_num

/-- Every competing tangent lift has at least the norm of the explicit lift.
@isnad1 id=le.2h5v.s12.12f2827f6ffe from=translated src=- shape=10397431 vocab=5a45afb7
-/
theorem normalizedTangentLift_minimal {d : ℕ} (z g : Fin d → ℂ) (a : ℂ)
    (h : differentialNormSq g (torusWeight z) ≠ 0)
    (v : torusTangentSpace z) (hv : restrictedDifferential z g v = a) :
    ‖normalizedTangentLift z g a‖ ≤ ‖v‖ := by
  rw [normalizedTangentLift_norm z g a h]
  apply (div_le_iff₀ (restrictedDifferential_norm_pos z g h)).2
  simpa [hv, mul_comm] using (restrictedDifferential z g).le_opNorm v

/-- At a regular point the restricted scalar differential is surjective.
@isnad1 id=surjecti.1h3v.s11.4402c0aa13a5 from=translated src=- shape=3c75e729 vocab=082b1422
-/
theorem restrictedDifferential_surjective {d : ℕ} (z g : Fin d → ℂ)
    (h : differentialNormSq g (torusWeight z) ≠ 0) :
    Function.Surjective (restrictedDifferential z g) :=
  fun a => ⟨normalizedTangentLift z g a, normalizedTangentLift_right_inverse z g a h⟩

/-- The complex and real operator norms coincide, as required by real ODE theory.
@isnad1 id=eq.0h3v.s11.0130d8522d27 from=translated src=- shape=9f93256d vocab=0494c6dd
-/
theorem restrictedDifferential_real_norm {d : ℕ} (z g : Fin d → ℂ) :
    ‖(restrictedDifferential z g).restrictScalars ℝ‖ =
      Real.sqrt (differentialNormSq g (torusWeight z)) := by
  rw [ContinuousLinearMap.norm_restrictScalars, restrictedDifferential_norm]

/-- The polynomial coordinate expression used by the semialgebraic sphere family
is exactly this restricted operator norm at the embedded torus point.
@isnad1 id=eq.0h3v.s10.e8e95f217206 from=translated src=- shape=46d85a33 vocab=89e6bef8
-/
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
