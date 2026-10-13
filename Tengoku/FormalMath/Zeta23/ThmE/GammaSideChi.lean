/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/GammaSideChi.lean — the Γ/conductor side of the folded contour
for L(s,χ) is EXACTLY ∫ μ_χ:
  (1/π)·Im ∫_L logDeriv(arch) = ∫_{T₁}^{T₂} μ_χ(t) dt,   arch(s) := q^{s/2} · Γℝ(s + κ),
where κ ∈ {0,1} is the parity (gammaFactor χ s = Γℝ(s + κ) by Even/Odd.gammaFactor_def), because
logDeriv arch = (log q)/2 + logDeriv Γℝ(·+κ) is holomorphic on Re s > 0 and on the critical line
  Re[(log q)/2 − (log π)/2 + ψ(¼ + κ/2 + it/2)/2] = π·μ_χ(t)   (μ_χ = Zeta23.ThmE.muq κ q).
This is the analogue of Zeta23/RvM/GammaSide.lean for L(s,χ).
-/
import Tengoku.FormalMath.Zeta23.ThmE.Hypotheses
import Tengoku.FormalMath.Zeta23.RvM.GammaSide
import Tengoku

open Complex MeasureTheory Set Zeta23.RvM
open scoped Interval

noncomputable section

namespace Zeta23
namespace ThmE

variable (q κ : ℕ) [NeZero q]

/-- the archimedean factor carrying the conductor: arch(s) := q^{s/2}·Γℝ(s+κ). -/
def archChi (s : ℂ) : ℂ := (q : ℂ) ^ (s / 2) * Complex.Gammaℝ (s + κ)

/--
@isnad1 id=ne.0h2v.s5.b37f18e1e8c7 from=translated src=- shape=cd5759d0 vocab=2611ec58
-/
lemma q_cpow_ne_zero (s : ℂ) : (q : ℂ) ^ (s / 2) ≠ 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q)).ne'
  simp [Complex.cpow_eq_zero_iff, hq0]

/--
@isnad1 id=differen.0h2v.s6.8a4954cd471d from=translated src=- shape=f00db728 vocab=2356b353
-/
lemma archChi_differentiableOn :
    DifferentiableOn ℂ (archChi q κ) rightHalfPlane := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (q : ℂ) ^ (s / 2)) s := by
    apply DifferentiableAt.const_cpow (by fun_prop)
    exact Or.inl (by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q)).ne')
  have h2 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gammaℝ (s + κ)) s := by
    have hre : 0 < (s + (κ:ℂ)).re := by
      have : (0:ℝ) ≤ κ := Nat.cast_nonneg κ
      have hs' : 0 < s.re := hs
      simp only [Complex.add_re, Complex.natCast_re]
      linarith
    have hG : DifferentiableAt ℂ Complex.Gammaℝ (s + κ) :=
      (Gammaℝ_differentiableOn (s + κ) hre).differentiableAt
        (isOpen_rightHalfPlane.mem_nhds hre)
    have haff : DifferentiableAt ℂ (fun z : ℂ => z + (κ:ℂ)) s := by fun_prop
    have hcomp : DifferentiableAt ℂ (Complex.Gammaℝ ∘ fun z : ℂ => z + (κ:ℂ)) s :=
      DifferentiableAt.comp s hG haff
    exact hcomp
  exact h1.mul h2

/--
@isnad1 id=ne.1h3v.s5.d07dfefe1542 from=translated src=- shape=5a695d19 vocab=04399d5c
-/
lemma archChi_ne_zero {s : ℂ} (hs : 0 < s.re) : archChi q κ s ≠ 0 := by
  unfold archChi
  apply mul_ne_zero (q_cpow_ne_zero q s)
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  simp only [Complex.add_re, Complex.natCast_re]
  have : (0:ℝ) ≤ κ := Nat.cast_nonneg κ
  linarith

/--
@isnad1 id=differen.0h2v.s6.87775bbae01d from=translated src=- shape=79e0e297 vocab=9ba6d98a
-/
lemma logDeriv_archChi_differentiableOn :
    DifferentiableOn ℂ (logDeriv (archChi q κ)) rightHalfPlane := by
  have hA : AnalyticOnNhd ℂ (archChi q κ) rightHalfPlane :=
    (archChi_differentiableOn q κ).analyticOnNhd isOpen_rightHalfPlane
  have : logDeriv (archChi q κ) = fun s => deriv (archChi q κ) s / archChi q κ s := by
    funext s; rfl
  rw [this]
  exact hA.deriv.differentiableOn.div hA.differentiableOn fun s hs => archChi_ne_zero q κ hs

end ThmE
end Zeta23
