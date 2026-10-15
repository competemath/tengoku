/-
Copyright (c) 2026 Wondermonger-daydreaming. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wondermonger-daydreaming
-/
module

public import Tengoku

/-!
  Group-theoretic helpers used with rotation normalization.

  The `finRotate` arithmetic lemmas live in `SemicircleCheck.FinRotateLemmas`.
-/

@[expose] public section

open Equiv Equiv.Perm

variable {n : ℕ}

/-! ## The group-theoretic layer -/

section GroupTheory

-- Parameterize on explicit Fin values to avoid (0 : Fin m) instance issues.
-- The group theory doesn't care what the target values are.
variable {m : ℕ} {π ρ : Perm (Fin m)}
variable {i γi a b : Fin m}

/-- If ρ sends a to b, then ρ⁻¹ sends b back to a. Pure injectivity.
@isnad1 id=eq.1h4v.s6.9d609244a7ee from=translated src=- shape=7aa161bc vocab=1b153eac
-/
lemma inv_apply_of_apply (h : ρ a = b) : ρ⁻¹ b = a := by
  subst h; exact ρ.symm_apply_apply a

/-- The involution gives us the reverse map.
    If π² = 1 and π(i) = γi, then π(γi) = i.
@isnad1 id=eq.2h4v.s7.3b6bca748099 from=translated src=- shape=f5a126ea vocab=1525f464
-/
lemma involution_reverse (hsq : π ^ 2 = 1) (hadj : π i = γi) :
    π γi = i := by
  have h2 : π * π = 1 := by rwa [← sq]
  have h3 : π (π i) = i := by
    change (π * π) i = i; simp [h2]
  rwa [hadj] at h3

/-- Conjugation sends a to b when ρ, π, and the adjacency align.

    calc: (ρ * π * ρ⁻¹)(a) = ρ(π(ρ⁻¹(a))) = ρ(π(i)) = ρ(γi) = b
@isnad1 id=eq.3h7v.s7.0ddac6ada99c from=translated src=- shape=17c58f21 vocab=35ccf058
-/
lemma conjugate_sends
    (hρi : ρ i = a) (hργi : ρ γi = b) (hadj : π i = γi) :
    (ρ * π * ρ⁻¹) a = b := by
  simp only [mul_apply]
  rw [inv_apply_of_apply hρi, hadj, hργi]

/-- Conjugation sends b to a (the reverse direction via involution).

    calc: (ρ * π * ρ⁻¹)(b) = ρ(π(ρ⁻¹(b))) = ρ(π(γi)) = ρ(i) = a
@isnad1 id=eq.4h7v.s7.0a06f53a13b9 from=translated src=- shape=f19d9c62 vocab=37a751b9
-/
lemma conjugate_sends_back
    (hρi : ρ i = a) (hργi : ρ γi = b)
    (hsq : π ^ 2 = 1) (hadj : π i = γi) :
    (ρ * π * ρ⁻¹) b = a := by
  simp only [mul_apply]
  rw [inv_apply_of_apply hργi, involution_reverse hsq hadj, hρi]

end GroupTheory
