import Tengoku.WasowAsymptoticsLean.NormalFormGoal
import Tengoku.Seed.Analysis.Calculus.Deriv.Add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms WasowPhaseNormalization.normalizePhase_coeff_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseNormalization.phaseOnRay_normalize` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseNormalization.deriv_phaseOnRay_normalize` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseNormalization.normalizedWitness` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseNormalization.exists_normalized_rayGauge` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseNormalization.normalize_phase_family` (it only prints; the queue checks the axioms of every declaration). -/

/-! Remove constant phase coefficients without changing the actual gauge.
The family is normalized once, before the choice of ray and root branch.
This is an implication for supplied phase families, not an existence theorem
for arbitrary rational systems. -/
set_option autoImplicit false
noncomputable section
namespace WasowPhaseNormalization
open CRGNormalFormGoal

/-- The phase polynomial with its constant coefficient removed.-/
def normalizePhase (F : Polynomial ℂ) : Polynomial ℂ :=
  F - Polynomial.C (F.coeff 0)

/--
@isnad1 id=eq.0h1v.s4.b543faf508f2 from=translated src=- shape=2c6ce007 vocab=afe81e06
-/
@[simp] theorem normalizePhase_coeff_zero (F : Polynomial ℂ) :
    (normalizePhase F).coeff 0 = 0 := by simp [normalizePhase]

/-- Normalization changes the actual phase by precisely one constant.
@isnad1 id=eq.0h5v.s5.4ddf98f97e7b from=translated src=- shape=435632cf vocab=88269124
-/
theorem phaseOnRay_normalize (p : ℕ) (F : Polynomial ℂ) (θ : ℝ) (ℓ : Fin p) (r : ℝ) :
    phaseOnRay p (normalizePhase F) θ ℓ r = phaseOnRay p F θ ℓ r - F.coeff 0 := by
  simp [phaseOnRay, normalizePhase]

/-- The actual real derivatives coincide everywhere, without an added
regularity premise or a restriction on the root branch.
@isnad1 id=eq.0h5v.s7.9e8acd40f057 from=translated src=- shape=1866c049 vocab=3dfd0f7d
-/
theorem deriv_phaseOnRay_normalize (p : ℕ) (F : Polynomial ℂ) (θ : ℝ) (ℓ : Fin p) (r : ℝ) :
    deriv (phaseOnRay p (normalizePhase F) θ ℓ) r = deriv (phaseOnRay p F θ ℓ) r := by
  have he : phaseOnRay p (normalizePhase F) θ ℓ =
      (fun r => phaseOnRay p F θ ℓ r - F.coeff 0) := funext (phaseOnRay_normalize p F θ ℓ)
  rw [he, deriv_sub_const]

/-- Reuse exactly the same matrices, derivatives, starting radius, and growth
constants for the normalized phases.-/
def normalizedWitness {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (p : ℕ) (F : Fin m → Polynomial ℂ) (θ : ℝ) (ℓ : Fin p)
    (W : RayGaugeWitness A θ (fun i => phaseOnRay p (F i) θ ℓ)) :
    RayGaugeWitness A θ (fun i => phaseOnRay p (normalizePhase (F i)) θ ℓ) where
  T := W.T
  S := W.S
  T' := W.T'
  R := W.R
  C := W.C
  K := W.K
  R_pos := W.R_pos
  C_pos := W.C_pos
  K_nonneg := W.K_nonneg
  pole_free := W.pole_free
  T_derivative := W.T_derivative
  inverse_left := W.inverse_left
  inverse_right := W.inverse_right
  T_bound := W.T_bound
  S_bound := W.S_bound
  gauge_identity := by
    intro r hr
    simpa only [deriv_phaseOnRay_normalize] using W.gauge_identity r hr

/-- Constant normalization preserves the already constructed actual ray gauge.
@isnad1 id=nonempty.0h7v.s5.40c291ce147d from=translated src=- shape=db6d904a vocab=f57ad9d9
-/
theorem exists_normalized_rayGauge {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (p : ℕ) (F : Fin m → Polynomial ℂ) (θ : ℝ) (ℓ : Fin p)
    (W : RayGaugeWitness A θ (fun i => phaseOnRay p (F i) θ ℓ)) :
    Nonempty (RayGaugeWitness A θ (fun i => phaseOnRay p (normalizePhase (F i)) θ ℓ)) :=
  ⟨normalizedWitness A p F θ ℓ W⟩

/-- A fixed phase family for every ray can be normalized before the ray and
branch quantifiers, yielding precisely the fixed-system conclusion of the
original normal-form goal. Existence of the initial family is explicit.
@isnad1 id=ex.1h2v.s7.cf2381566b24 from=translated src=- shape=8997b8e5 vocab=8a308e16
-/
theorem normalize_phase_family {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (h : ∃ p : ℕ, 0 < p ∧ ∃ F : Fin m → Polynomial ℂ,
      ∀ θ : ℝ, ∃ ℓ : Fin p, Nonempty (RayGaugeWitness A θ (fun i => phaseOnRay p (F i) θ ℓ))) :
    ∃ p : ℕ, 0 < p ∧ ∃ F : Fin m → Polynomial ℂ,
      (∀ i, (F i).coeff 0 = 0) ∧
      ∀ θ : ℝ, ∃ ℓ : Fin p, Nonempty (RayGaugeWitness A θ (fun i => phaseOnRay p (F i) θ ℓ)) := by
  obtain ⟨p, hp, F, hF⟩ := h
  refine ⟨p, hp, fun i => normalizePhase (F i), fun i => normalizePhase_coeff_zero (F i), ?_⟩
  intro θ
  obtain ⟨ℓ, ⟨W⟩⟩ := hF θ
  exact ⟨ℓ, exists_normalized_rayGauge A p F θ ℓ W⟩

end WasowPhaseNormalization
