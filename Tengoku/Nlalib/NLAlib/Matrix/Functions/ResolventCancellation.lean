import Tengoku.Nlalib.NLAlib.Matrix.Functions.AggregateResolvent
import Tengoku.Seed.Tactic.Abel
import Tengoku.Seed.Tactic.NoncommRing
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Exact cubic remainder for resolvent derivatives

Three-slot telescoping restores the same reference resolvent in both
first-difference words. The resulting six ordered cubic words are actual
matrices and require no Taylor-remainder or norm-bound hypothesis.

Source: Tatiana Brailovskaya and Ramon van Handel, *Universality and sharp
matrix concentration inequalities*, arXiv:2201.05142v3 (2024), §6.4, proof
of Lemma 6.11. This supports `matrix-resolvent-gaussian-universality`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib

private theorem three_slot_telescope {𝔸 : Type*} [Ring 𝔸]
    (A B C H U V : 𝔸) :
    A * U * B * V * C - H * U * H * V * H =
      (A - H) * U * B * V * C + H * U * (B - H) * V * C +
        H * U * H * V * (C - H) := by
  noncomm_ring

private theorem mul_sub_mul_eq_smul_add_smul_sq
    {𝔸 : Type*} [Ring 𝔸] [Algebra ℝ 𝔸]
    (R₀ R₁ R₂ D E F : 𝔸) (a : ℝ)
    (h₀₁ : R₀ - R₁ = a • (R₀ * D * R₁))
    (h₀₂ : R₀ - R₂ = a • (R₀ * F * R₂))
    (h₁₂ : R₁ - R₂ = a • (R₁ * E * R₂)) :
    R₀ * D * R₀ - R₁ * D * R₁ =
      a • ((2 : ℝ) • (R₂ * D * R₂ * D * R₂)) +
        a ^ 2 •
          (R₀ * F * R₂ * D * R₁ * D * R₀ +
            R₂ * D * R₁ * E * R₂ * D * R₀ +
            R₂ * D * R₂ * D * R₀ * F * R₂ +
            R₁ * E * R₂ * D * R₀ * D * R₁ +
            R₂ * D * R₀ * F * R₂ * D * R₁ +
            R₂ * D * R₂ * D * R₁ * E * R₂) := by
  let T := R₂ * D * R₂ * D * R₂
  let X := R₀ * F * R₂ * D * R₁ * D * R₀ +
    R₂ * D * R₁ * E * R₂ * D * R₀ +
    R₂ * D * R₂ * D * R₀ * F * R₂
  let Y := R₁ * E * R₂ * D * R₀ * D * R₁ +
    R₂ * D * R₀ * F * R₂ * D * R₁ +
    R₂ * D * R₂ * D * R₁ * E * R₂
  have hfirst : R₀ * D * R₀ - R₁ * D * R₁ =
      a • (R₀ * D * R₁ * D * R₀ + R₁ * D * R₀ * D * R₁) := by
    calc
      _ = (R₀ - R₁) * D * R₀ + R₁ * D * (R₀ - R₁) := by noncomm_ring
      _ = _ := by
        rw [h₀₁]
        simp only [smul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]
  have hleft : R₀ * D * R₁ * D * R₀ - T = a • X := by
    dsimp only [T, X]
    calc
      _ = (R₀ - R₂) * D * R₁ * D * R₀ + R₂ * D * (R₁ - R₂) * D * R₀ +
          R₂ * D * R₂ * D * (R₀ - R₂) := three_slot_telescope R₀ R₁ R₀ R₂ D D
      _ = _ := by
        rw [h₀₂, h₁₂]
        simp only [smul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]
  have hright : R₁ * D * R₀ * D * R₁ - T = a • Y := by
    dsimp only [T, Y]
    calc
      _ = (R₁ - R₂) * D * R₀ * D * R₁ + R₂ * D * (R₀ - R₂) * D * R₁ +
          R₂ * D * R₂ * D * (R₁ - R₂) := three_slot_telescope R₁ R₀ R₁ R₂ D D
      _ = _ := by
        rw [h₁₂, h₀₂]
        simp only [smul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]
  have ht : R₀ * D * R₁ * D * R₀ + R₁ * D * R₀ * D * R₁ =
      (2 : ℝ) • T + a • (X + Y) := by
    rw [sub_eq_iff_eq_add'.mp hleft, sub_eq_iff_eq_add'.mp hright]
    simp only [two_smul, smul_add]
    abel
  have hsum : X + Y =
      R₀ * F * R₂ * D * R₁ * D * R₀ +
        R₂ * D * R₁ * E * R₂ * D * R₀ +
        R₂ * D * R₂ * D * R₀ * F * R₂ +
        R₁ * E * R₂ * D * R₀ * D * R₁ +
        R₂ * D * R₀ * F * R₂ * D * R₁ +
        R₂ * D * R₂ * D * R₁ * E * R₂ := by dsimp [X, Y]; abel
  calc
    _ = a • (R₀ * D * R₁ * D * R₀ + R₁ * D * R₀ * D * R₁) := hfirst
    _ = a • ((2 : ℝ) • T + a • (X + Y)) := congrArg (fun q : 𝔸 => a • q) ht
    _ = a • ((2 : ℝ) • T) + a • (a • (X + Y)) := smul_add a _ _
    _ = a • ((2 : ℝ) • T) + a ^ 2 • (X + Y) := by
      rw [smul_smul a a (X + Y), pow_two]
    _ = _ := by
      simpa only [T] using
        congrArg (fun q : 𝔸 => a • ((2 : ℝ) • T) + a ^ 2 • q) hsum

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ

/-- The six ordered cubic resolvent words obtained by comparing two directional
resolvent derivatives at the common third base. The three bases are `A₀`,
`A₀ - a • D` and `A₀ - a • F`, with the third direction `F - D`.
The definition is total; Hermiticity and a nonreal shift are hypotheses of
its cancellation and norm theorems.
Source: Brailovskaya--van Handel, arXiv:2201.05142v3 (2024), §6.4,
proof of Lemma 6.11.-/
def resolventCubicRemainder (A₀ D F : M) (a : ℝ) (ζ : ℂ) : M :=
  let R₀ := resolvent A₀ ζ
  let R₁ := resolvent (A₀ - a • D) ζ
  let R₂ := resolvent (A₀ - a • F) ζ
  let E := F - D
  R₀ * F * R₂ * D * R₁ * D * R₀ +
    R₂ * D * R₁ * E * R₂ * D * R₀ +
    R₂ * D * R₂ * D * R₀ * F * R₂ +
    R₁ * E * R₂ * D * R₀ * D * R₁ +
    R₂ * D * R₀ * F * R₂ * D * R₁ +
    R₂ * D * R₂ * D * R₁ * E * R₂

/-- Two directional resolvent derivatives differ by the common quadratic
term and six explicit cubic words. Every factor is the actual resolvent of a
Hermitian matrix, and the real interpolation coefficient is arbitrary.

Source: Tatiana Brailovskaya and Ramon van Handel, *Universality and sharp
matrix concentration inequalities*, arXiv:2201.05142v3 (2024), §6.4, proof
of Lemma 6.11, with the exact ordered remainder made explicit.
atlas: matrix-resolvent-gaussian-universality (partial)
@isnad1 id=other.4h6v.s9.9a0790303cc5 from=translated src=- shape=b4076657 vocab=55c5a0d0
-/
theorem resolvent_mul_resolvent_sub_eq_smul_add_smul_sq
    (A₀ D F : M) (a : ℝ) (ζ : ℂ) (hA₀ : A₀.IsHermitian)
    (hD : D.IsHermitian) (hF : F.IsHermitian) (hζ : ζ.im ≠ 0) :
    let R₀ := resolvent A₀ ζ
    let R₁ := resolvent (A₀ - a • D) ζ
    let R₂ := resolvent (A₀ - a • F) ζ
    R₀ * D * R₀ - R₁ * D * R₁ =
      a • ((2 : ℝ) • (R₂ * D * R₂ * D * R₂)) +
        a ^ 2 • resolventCubicRemainder A₀ D F a ζ := by
  dsimp only
  have h₀₁ : resolvent A₀ ζ - resolvent (A₀ - a • D) ζ =
      a • (resolvent A₀ ζ * D * resolvent (A₀ - a • D) ζ) := by
    have h := resolvent_sub_smul_eq_sub_mul_resolvent A₀ D a ζ hA₀ hD hζ
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using (eq_sub_iff_add_eq.mp h).symm
  have h₀₂ : resolvent A₀ ζ - resolvent (A₀ - a • F) ζ =
      a • (resolvent A₀ ζ * F * resolvent (A₀ - a • F) ζ) := by
    have h := resolvent_sub_smul_eq_sub_mul_resolvent A₀ F a ζ hA₀ hF hζ
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using (eq_sub_iff_add_eq.mp h).symm
  have hbase : (A₀ - a • D) - a • (F - D) = A₀ - a • F := by
    simp only [smul_sub]
    abel
  have h₁₂ : resolvent (A₀ - a • D) ζ - resolvent (A₀ - a • F) ζ =
      a • (resolvent (A₀ - a • D) ζ * (F - D) * resolvent (A₀ - a • F) ζ) := by
    have h := resolvent_sub_smul_eq_sub_mul_resolvent (A₀ - a • D) (F - D) a ζ
      (hA₀.sub (hD.smul (isSelfAdjoint_iff.mpr (star_trivial a)))) (hF.sub hD) hζ
    rw [hbase] at h
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using (eq_sub_iff_add_eq.mp h).symm
  exact mul_sub_mul_eq_smul_add_smul_sq _ _ _ D (F - D) F a h₀₁ h₀₂ h₁₂

variable {ι : Type*} [Fintype ι]

end NLAlib
