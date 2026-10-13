/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Params.lean.  Consumer-facing layer, part 1:
the `P : Params`, `T : ℝ` versions of everything that depends only on Taper/Basic, Taper/Norms
and Taper/Strip (φ facts [eq:phidef], [eq:abdef], C₁ and [eq:hfbound] for φ), plus the rfl
bridges to Defs.  Split out of Zeta23/Taper.lean so that Zeta23/Main.lean can import it without
pulling Taper/Decay, Taper/Fourier.  Hypotheses: `hP : P.Valid`,
`hwL : 8 * P.w ≤ P.L T` ([eq:wrange]).  The remaining Params-layer facts (φ̂/Φ, ψ, g, A_φ,
Plancherel) are in the umbrella Zeta23/Taper.lean.
-/
import Tengoku.FormalMath.Zeta23.Taper.Basic
import Tengoku.FormalMath.Zeta23.Taper.Norms
import Tengoku.FormalMath.Zeta23.Taper.Strip

open Complex MeasureTheory Real Set Filter Topology

namespace Zeta23

namespace Params

variable (P : Params) (T : ℝ)

/--
@isnad1 id=eq.0h2v.s4.48b068562a14 from=translated src=- shape=721a527c vocab=fee989d1
-/
theorem phi_eq : P.phi T = Taper.phi P.ϱ (P.L T) P.w := rfl
/--
@isnad1 id=eq.0h2v.s4.b7d88f583bb7 from=translated src=- shape=f164d91d vocab=93988474
-/
theorem a_eq : P.a T = Taper.aConst P.ϱ (P.L T) P.w := rfl
/--
@isnad1 id=eq.0h2v.s4.5c90cf506988 from=translated src=- shape=f164d91d vocab=dbb90ca7
-/
theorem b_eq : P.b T = Taper.bConst P.ϱ (P.L T) P.w := rfl
/--
@isnad1 id=eq.0h2v.s4.2b7e6f7976a0 from=translated src=- shape=9c2de5d4 vocab=2c3381db
-/
theorem phiHat_eq : P.phiHat T = Taper.phiHat P.ϱ (P.L T) P.w := rfl
/--
@isnad1 id=eq.0h2v.s4.5c1f28ee5fac from=translated src=- shape=721a527c vocab=757c792b
-/
theorem phiHatR_eq : P.phiHatR T = Taper.phiHatR P.ϱ (P.L T) P.w := rfl
/--
@isnad1 id=eq.0h2v.s4.26a7f2d4adfe from=translated src=- shape=9c2de5d4 vocab=00e7b53a
-/
theorem Phi_eq : P.Phi T = Taper.Phi P.ϱ (P.L T) P.w := rfl
/--
@isnad1 id=eq.0h2v.s4.a19a1d0e68bf from=translated src=- shape=721a527c vocab=fa7e7a4b
-/
theorem PhiR_eq : P.PhiR T = Taper.PhiR P.ϱ (P.L T) P.w := rfl
/--
@isnad1 id=eq.0h2v.s4.4f222aaf3773 from=translated src=- shape=721a527c vocab=506f1308
-/
theorem g_eq : P.g T = Taper.g P.ϱ (P.L T) P.w := rfl
/--
@isnad1 id=eq.0h2v.s4.468d43c63ed1 from=translated src=- shape=721a527c vocab=81df0add
-/
theorem Aphi_eq : P.Aphi T = Taper.Aphi P.ϱ (P.L T) P.w := rfl
/--
@isnad1 id=eq.0h1v.s3.b9a283c4d9f6 from=translated src=- shape=69b989be vocab=d01b61a1
-/
theorem crho_eq : P.crho = Taper.cRho P.ϱ := rfl

/-- ψ (value `L` at `r = 0`); see `Taper.psi`.  Since Defs uses the same body,
`P.psi T = P.psi' T` is `rfl` (`psi_eq_psi'`); both names are available. -/
noncomputable def psi' (r : ℝ) : ℝ := Taper.psi P.ϱ (P.L T) P.w r

/--
@isnad1 id=eq.0h2v.s3.5b8a1933e010 from=translated src=- shape=417294a9 vocab=b41ece22
-/
theorem psi_eq_psi' : P.psi T = P.psi' T := rfl
/--
@isnad1 id=eq.0h2v.s4.0a11cada9041 from=translated src=- shape=721a527c vocab=fa06d7fe
-/
theorem psi_eq : P.psi T = Taper.psi P.ϱ (P.L T) P.w := rfl

/-- `C₁ := ‖φ''‖₁` [prop:tail]. -/
noncomputable def C1 : ℝ := Taper.C1 P.ϱ (P.L T) P.w

variable {P T}

/--
@isnad1 id=lt.1h1v.s4.c1d9dec08468 from=translated src=- shape=a124ee4e vocab=e23ac41f
-/
theorem w_pos (hP : P.Valid) : 0 < P.w := lt_of_lt_of_le one_pos hP.one_le_w
/--
@isnad1 id=le.2h2v.s5.39a67c9a919b from=translated src=- shape=9390fbad vocab=7a2a87c4
-/
theorem two_w_le (hwL : 8 * P.w ≤ P.L T) (hP : P.Valid) : 2 * P.w ≤ P.L T := by
  linarith [hP.one_le_w]

/-! #### hypothesis-free facts -/
/--
@isnad1 id=eq.0h3v.s4.1ace30bab442 from=translated src=- shape=0153c957 vocab=ee4e3348
-/
theorem phi_even' (u : ℝ) : P.phi T (-u) = P.phi T u := Taper.phi_even u

section
variable (hP : P.Valid)
include hP
/--
@isnad1 id=le.1h3v.s4.b7cdb7625f99 from=translated src=- shape=f00bcebb vocab=52ce4af0
-/
theorem phi_nonneg (u : ℝ) : 0 ≤ P.phi T u := Taper.phi_nonneg hP.taper u
/--
@isnad1 id=le.1h3v.s4.bfa119ea5424 from=translated src=- shape=a9010b54 vocab=52ce4af0
-/
theorem phi_le_one (u : ℝ) : P.phi T u ≤ 1 := Taper.phi_le_one hP.taper u
/--
@isnad1 id=eq.2h3v.s5.32d7f2feb4f1 from=translated src=- shape=e2c55864 vocab=3d613eaf
-/
theorem phi_eq_zero {u : ℝ} (hu : P.L T / 2 ≤ |u|) : P.phi T u = 0 :=
  Taper.phi_eq_zero hP.taper (w_pos hP) hu
/--
@isnad1 id=eq.2h3v.s5.de74d581478b from=translated src=- shape=41876264 vocab=5039b7c8
-/
theorem phi_eq_one {u : ℝ} (hu : |u| ≤ P.L T / 2 - P.w) : P.phi T u = 1 :=
  Taper.phi_eq_one hP.taper (w_pos hP) hu
/--
@isnad1 id=hascompa.1h2v.s4.b43a1e5ef637 from=translated src=- shape=e5efb1b8 vocab=df8f4463
-/
theorem phi_hasCompactSupport : HasCompactSupport (P.phi T) :=
  Taper.phi_hasCompactSupport hP.taper (w_pos hP)
/--
@isnad1 id=le.1h2v.s6.e99249f02d93 from=translated src=- shape=dbb8ae92 vocab=355ece36
-/
theorem phi_support_subset : Function.support (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2) :=
  Taper.phi_support_subset hP.taper (w_pos hP)
end

section
variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL

/-! #### φ -/
/--
@isnad1 id=contdiff.2h2v.s6.0406d0425b3c from=translated src=- shape=c4cb0580 vocab=255ae08a
-/
theorem phi_contDiff : ContDiff ℝ 3 (P.phi T) :=
  Taper.phi_contDiff hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=continuo.2h2v.s5.78216674fab2 from=translated src=- shape=ba2c2dea vocab=1218dfae
-/
theorem phi_continuous : Continuous (P.phi T) :=
  Taper.phi_continuous hP.taper (w_pos hP) (two_w_le hwL hP)

/-! #### [eq:abdef] -/
/--
@isnad1 id=le.2h2v.s5.a72552dac74a from=translated src=- shape=bf7af56e vocab=8161d7c3
-/
theorem b_le_a : P.b T ≤ P.a T := Taper.bConst_le_aConst hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=le.2h2v.s5.2c03954e6f17 from=translated src=- shape=940c5a95 vocab=d80a3bf4
-/
theorem a_le_one : P.a T ≤ 1 := Taper.aConst_le_one hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=le.2h2v.s6.a9d85ed474b9 from=translated src=- shape=02e6e516 vocab=3844aebc
-/
theorem one_sub_le_b : 1 - 2 * P.w / P.L T ≤ P.b T :=
  Taper.one_sub_le_bConst hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=le.2h2v.s5.606b198405d5 from=translated src=- shape=ba90efea vocab=0dac06bc
-/
theorem b_nonneg : 0 ≤ P.b T := Taper.bConst_nonneg hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=le.2h2v.s5.d572d71d66a0 from=translated src=- shape=94377564 vocab=572008ab
-/
theorem three_quarters_le_b : 3 / 4 ≤ P.b T := by
  have h1 := one_sub_le_b hP hwL
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have : 2 * P.w / P.L T ≤ 1 / 4 := by
    rw [div_le_iff₀ hL]; linarith
  linarith
/-- "and `a ≥ 1/2`" [prop:tail, last line].
@isnad1 id=le.2h2v.s5.f87d229ba87d from=translated src=- shape=94377564 vocab=068e5593
-/
theorem half_le_a : 1 / 2 ≤ P.a T := by
  linarith [three_quarters_le_b hP hwL, b_le_a hP hwL]

/-! #### [eq:hfbound] for φ ([prop:tail]) -/
/--
@isnad1 id=le.2h2v.s5.4f5000e4b944 from=translated src=- shape=554b51b0 vocab=56e07ff7
-/
theorem C1_le : P.C1 T ≤ 2 * Taper.l1Deriv2 P.ϱ :=
  Taper.C1_le hP.taper hP.one_le_w (two_w_le hwL hP)
/--
@isnad1 id=le.2h3v.s6.5ffe5b00ab9e from=translated src=- shape=fc27e5ef vocab=fc00c456
-/
theorem norm_phiHat_mul_sq_le (z : ℂ) :
    ‖P.phiHat T z‖ * ‖z‖ ^ 2 ≤ Real.exp (|z.im| * (P.L T / 2)) * P.C1 T :=
  Taper.norm_phiHat_mul_sq_le hP.taper (w_pos hP) (two_w_le hwL hP) z
/--
@isnad1 id=le.2h3v.s6.7d3ea0a57ef5 from=translated src=- shape=bff9a087 vocab=16a01e81
-/
theorem norm_phiHat_le (z : ℂ) : ‖P.phiHat T z‖ ≤ Real.exp (|z.im| * (P.L T / 2)) * P.L T :=
  Taper.norm_phiHat_le hP.taper (w_pos hP) (two_w_le hwL hP) z
/--
@isnad1 id=le.4h4v.s7.73c81a89c0db from=translated src=- shape=0153cc4a vocab=d3440bf6
-/
theorem norm_phiHat_sub_I_mul_le (r y : ℝ) (hy : |y| ≤ 1 / 2) (hz : (r : ℂ) - I * y ≠ 0) :
    ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * P.C1 T / ‖(r : ℂ) - I * y‖ ^ 2 :=
  Taper.norm_phiHat_sub_I_mul_le hP.taper (w_pos hP) (two_w_le hwL hP) r y hy hz

end

end Params

end Zeta23
