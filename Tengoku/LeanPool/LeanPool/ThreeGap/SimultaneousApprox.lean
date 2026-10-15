/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/
module

public import Tengoku

/-!
# Simultaneous Diophantine approximation: the remainder-vector difference inequality

The separation lemma behind the higher-dimensional growth inequality (Lagarias 1980, Ermakov
arXiv:1002.2713) splits into an **elementary algebraic core** and a **convex-geometry completion**.
This file formalizes the algebraic core, faithfully.

For `α : Fin n → ℝ` and an integer `q`, the *approximation defect* is

  `δ_q = inf over p ∈ ℤⁿ of ‖q • α − p‖`,

with `r(q) = q • α − p(q)` the *remainder vector* (`‖r(q)‖ = δ_q`). The crucial elementary fact,
used throughout Ermakov's Lemma 2 (*"`r(qᵢ) − r(qⱼ)` is the remainder vector for `qᵢ − qⱼ`"*): the
difference of two remainder vectors is itself an approximation remainder for the difference of the
denominators, hence its norm is `≥ δ_{qᵢ − qⱼ}`:

  `‖r(qᵢ) − r(qⱼ)‖ ≥ δ_{qᵢ − qⱼ}`.

This is `delta_diff_le`. It is the algebraic input that makes the remainder vectors *spread out*;
the
remaining geometric step (their direction angles exceed `π/3`, so at most `K` = contact-number many
fit) is Ermakov's Lemmas 1–2, the cited geometric completion. Norm-agnostic: holds for every norm
(here the sup norm on `Fin n → ℝ`).

Axiom-clean; elementary.
-/

@[expose] public section

namespace ThreeGap.SimApprox

variable {n : ℕ}

/-- The integer-vector translate of `q • α` by `p`, as an element of `Fin n → ℝ`. Its norm over all
`p ∈ ℤⁿ` is minimised at the best approximation; here we only need the value and its lower bound. -/
noncomputable def rem (α : Fin n → ℝ) (q : ℤ) (p : Fin n → ℤ) : Fin n → ℝ :=
  (q : ℝ) • α - (fun k => (p k : ℝ))

/-- The **approximation defect** `δ_q = inf_{p ∈ ℤⁿ} ‖q • α − p‖`. -/
noncomputable def delta (α : Fin n → ℝ) (q : ℤ) : ℝ :=
  ⨅ p : Fin n → ℤ, ‖rem α q p‖

/-- The **approximation defect for an arbitrary norm `N`**: `δ^N_q = inf_{p ∈ ℤⁿ} N (q • α − p)`.
(`delta` is the `N = ‖·‖` sup-norm case.) -/
noncomputable def deltaN (N : (Fin n → ℝ) → ℝ) (α : Fin n → ℝ) (q : ℤ) : ℝ :=
  ⨅ p : Fin n → ℤ, N (rem α q p)

/-- For a nonnegative `N`, the defect `δ^N_q` is a lower bound on every concrete approximation.
@isnad1 id=le.1h5v.s5.2a222b2f0b20 from=translated src=- shape=6bdbd7c7 vocab=a8a2f78a
-/
theorem deltaN_le (N : (Fin n → ℝ) → ℝ) (hN : ∀ x, 0 ≤ N x) (α : Fin n → ℝ) (q : ℤ)
    (p : Fin n → ℤ) : deltaN N α q ≤ N (rem α q p) :=
  ciInf_le ⟨0, by rintro _ ⟨p, rfl⟩; exact hN _⟩ p

/-- The range of `p ↦ ‖rem α q p‖` is bounded below (by `0`), so the infimum is genuine.
@isnad1 id=bddbelow.0h3v.s5.3a479ef91fa5 from=translated src=- shape=9ddb13cf vocab=2dba3b97
-/
theorem bddBelow_rem (α : Fin n → ℝ) (q : ℤ) :
    BddBelow (Set.range fun p : Fin n → ℤ => ‖rem α q p‖) :=
  ⟨0, by rintro _ ⟨p, rfl⟩; exact norm_nonneg _⟩

/-- `δ_q` is a lower bound for every concrete approximation: `δ_q ≤ ‖q • α − p‖` for all `p ∈ ℤⁿ`.
@isnad1 id=le.0h4v.s5.a1bf706b80c8 from=translated src=- shape=dcf7c075 vocab=cf384b56
-/
theorem delta_le (α : Fin n → ℝ) (q : ℤ) (p : Fin n → ℤ) : delta α q ≤ ‖rem α q p‖ :=
  ciInf_le (bddBelow_rem α q) p

/-- `δ_q ≥ 0`.
@isnad1 id=le.0h3v.s4.8ac92030f8f3 from=translated src=- shape=1b3c4496 vocab=ff342287
-/
theorem delta_nonneg (α : Fin n → ℝ) (q : ℤ) : 0 ≤ delta α q :=
  le_ciInf fun _p => norm_nonneg _

/-- **The remainder-vector difference is an approximation remainder for the difference of
denominators.** Algebraically, `(qᵢ • α − pᵢ) − (qⱼ • α − pⱼ) = (qᵢ − qⱼ) • α − (pᵢ − pⱼ)`.
@isnad1 id=eq.0h6v.s6.5673ea28dc98 from=translated src=- shape=89877124 vocab=6308b797
-/
theorem rem_sub (α : Fin n → ℝ) (qi qj : ℤ) (pi pj : Fin n → ℤ) :
    rem α qi pi - rem α qj pj = rem α (qi - qj) (pi - pj) := by
  funext k
  simp only [rem, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **Halving homogeneity.** `r(2q, 2p) = 2 · r(q, p)` — doubling both the denominator and the
integer translate doubles the remainder vector. Used in the mod-2 pigeonhole growth argument, where
two best approximations agreeing mod 2 produce a half-integer combination.
@isnad1 id=eq.0h4v.s6.2d9e366a6d3a from=translated src=- shape=53db46ef vocab=1fb9a177
-/
theorem rem_two_smul (α : Fin n → ℝ) (q : ℤ) (p : Fin n → ℤ) :
    rem α (2 * q) (fun k => 2 * p k) = (2 : ℝ) • rem α q p := by
  funext k
  simp only [rem, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- **The separation core (Ermakov Lemma 2, algebraic part).** The distance between two remainder
vectors is at least the approximation defect of the difference of their denominators:

  `δ_{qᵢ − qⱼ} ≤ ‖r(qᵢ) − r(qⱼ)‖`.

Combined with the best-approximation property (every nonzero denominator below `qₖ₊₁` has defect
`≥ δ_{qₖ}`), this makes the remainder vectors `r(qₖ), …, r(qₖ₊ₖ)` pairwise `≥ δ_{qₖ}` apart — the
input to the convex-geometry/contact-number count that yields the growth inequality.
@isnad1 id=le.0h6v.s6.d7f0bb327c12 from=translated src=- shape=c9a3ebb7 vocab=2e852b45
-/
theorem delta_diff_le (α : Fin n → ℝ) (qi qj : ℤ) (pi pj : Fin n → ℤ) :
    delta α (qi - qj) ≤ ‖rem α qi pi - rem α qj pj‖ := by
  rw [rem_sub]
  exact delta_le α (qi - qj) (pi - pj)

end ThreeGap.SimApprox
