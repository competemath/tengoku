/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Taper.lean — the test family [subsec:family] of the paper §2.2 and its
elementary facts: text after [eq:phidef], [eq:phinorms], [eq:abdef], the facts after [eq:PhigA]
(incl. [eq:Phi2FT]), [eq:gbounds], [eq:psidef], [eq:psiints], and [eq:hfbound] specialized to φ.
([eq:hfbound] for general f is in `Zeta23.Poisson.PaperFT`.)

SUB-FILES: Zeta23/Taper/Basic.lean (defs + [eq:phidef] facts),
Norms.lean ([eq:phinorms], [eq:abdef]), Strip.lean ([eq:hfbound] for φ),
Decay.lean ([eq:gbounds], [eq:psidef], [eq:psiints]),
Fourier.lean ([eq:PhigA]-line facts, Plancherel, [eq:Phi2FT]).  This umbrella file
holds the consumer-facing `Params` layer, part 2 (φ̂/Φ/ψ/g/A_φ facts); part 1 (φ, a, b, C₁,
hfbound — depends only on Basic/Norms/Strip) is Zeta23/Taper/Params.lean, importable on its own.

ORGANIZATION.  Namespace `Zeta23.Taper`: generic parameters `(ϱ : ℝ → ℝ) (L w : ℝ)` — pure
one-variable calculus, no `T`.  Namespace `Zeta23.Params` (last section): the same facts for
`P : Params`, `T : ℝ` of Zeta23/Defs.lean (`L = P.L T`, `w = P.w`, `ϱ = P.ϱ`); the bridges
`P.phi T = Taper.phi P.ϱ (P.L T) P.w` etc. are `rfl`.  Consumers use the `Params` versions.

Side conditions: the paper fixes `1 ≤ w ≤ L/8` [eq:wrange].  Generic lemmas carry the minimal
hypothesis they need (`0 < w`, `2w ≤ L`, …); the `Params` versions uniformly assume
`hP : P.Valid` (gives `1 ≤ w`, `TaperProfile ϱ`) and `hwL : 8 * P.w ≤ P.L T` ([eq:wrange]).
-/
import Tengoku.FormalMath.Zeta23.Taper.Params
import Tengoku.FormalMath.Zeta23.Taper.Decay
import Tengoku.FormalMath.Zeta23.Taper.Fourier

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

/-! ## Instantiation for `P : Params`, `T : ℝ` (Zeta23/Defs.lean).
Consumer-facing names.  Hypotheses: `hP : P.Valid`, `hwL : 8 * P.w ≤ P.L T` ([eq:wrange]). -/

namespace Params

variable {P : Params} {T : ℝ}

/-! #### hypothesis-free facts -/
/--
@isnad1 id=eq.0h3v.s4.2c3f8dfb19b5 from=translated src=- shape=638b1db3 vocab=1f889851
-/
theorem phiHat_ofReal (r : ℝ) : P.phiHat T r = (P.phiHatR T r : ℂ) := Taper.phiHat_ofReal r
/--
@isnad1 id=eq.0h3v.s4.1bc0cbfc16bd from=translated src=- shape=638b1db3 vocab=f3e2f2b5
-/
theorem Phi_ofReal (r : ℝ) : P.Phi T r = (P.PhiR T r : ℂ) := Taper.Phi_ofReal r
/--
@isnad1 id=eq.0h3v.s6.7e29da44f99c from=translated src=- shape=ed9e1aa9 vocab=6af283da
-/
theorem phiHat_conj (z : ℂ) : P.phiHat T (starRingEnd ℂ z) = starRingEnd ℂ (P.phiHat T z) :=
  Taper.phiHat_conj z
/--
@isnad1 id=eq.0h3v.s4.5bb682bf9493 from=translated src=- shape=0153c957 vocab=5475fb41
-/
theorem phiHatR_even (r : ℝ) : P.phiHatR T (-r) = P.phiHatR T r := Taper.phiHatR_even r
/--
@isnad1 id=eq.0h3v.s4.78301fd1ff5b from=translated src=- shape=0153c957 vocab=241b4ff8
-/
theorem PhiR_even (r : ℝ) : P.PhiR T (-r) = P.PhiR T r := Taper.PhiR_even r
/--
@isnad1 id=eq.0h3v.s4.776c05386fb7 from=translated src=- shape=0153c957 vocab=e4ff2b0f
-/
theorem Aphi_even (y : ℝ) : P.Aphi T (-y) = P.Aphi T y := Taper.Aphi_even y
/--
@isnad1 id=eq.0h3v.s4.ac4183c32197 from=translated src=- shape=0153c957 vocab=e2ba8035
-/
theorem g_even (y : ℝ) : P.g T (-y) = P.g T y := Taper.g_even y
/--
@isnad1 id=eq.0h3v.s4.b381b7d0287f from=translated src=- shape=0153c957 vocab=1fb254eb
-/
theorem psi'_even (r : ℝ) : P.psi' T (-r) = P.psi' T r := Taper.psi_even r

section
variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL

/-! #### φ̂, Φ real/even/continuous; conj symmetry -/
/--
@isnad1 id=continuo.2h2v.s5.fee53bfb0004 from=translated src=- shape=ba2c2dea vocab=acf5f34f
-/
theorem phiHatR_continuous : Continuous (P.phiHatR T) :=
  Taper.phiHatR_continuous hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=continuo.2h2v.s5.3e5c467eea10 from=translated src=- shape=ba2c2dea vocab=cb9e6f88
-/
theorem PhiR_continuous : Continuous (P.PhiR T) :=
  Taper.PhiR_continuous hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=contdiff.2h2v.s6.cde908685ca9 from=translated src=- shape=c4cb0580 vocab=7db0e2e8
-/
theorem PhiR_contDiff_one : ContDiff ℝ 1 (P.PhiR T) :=
  Taper.PhiR_contDiff_one hP.taper (w_pos hP) (two_w_le hwL hP)

/-! #### [eq:PhigA]-line facts -/
/--
@isnad1 id=le.2h2v.s5.ca3da14b0afd from=translated src=- shape=d97769ed vocab=5dde2ac1
-/
theorem phiHatR_zero_le : P.phiHatR T 0 ≤ P.L T :=
  Taper.phiHatR_zero_le hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=eq.2h2v.s5.52382e94c60e from=translated src=- shape=8c338aa5 vocab=6e623af6
-/
theorem PhiR_zero : P.PhiR T 0 = P.a T * P.L T :=
  Taper.PhiR_zero hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=eq.2h2v.s5.1a8ff0f635be from=translated src=- shape=8c338aa5 vocab=be97371a
-/
theorem g_zero : P.g T 0 = P.b T * P.L T := Taper.g_zero hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=eq.2h2v.s5.847c0b4b7713 from=translated src=- shape=8c338aa5 vocab=da81497a
-/
theorem Aphi_zero : P.Aphi T 0 = P.a T * P.L T :=
  Taper.Aphi_zero hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=eq.2h3v.s6.20c000258872 from=translated src=- shape=994bef08 vocab=5fd27737
-/
theorem phiHatR_sq_eq (r : ℝ) :
    ((P.phiHatR T r) ^ 2 : ℂ) = paperFT (fun u => (P.Aphi T u : ℂ)) r :=
  Taper.phiHatR_sq_eq hP.taper (w_pos hP) (two_w_le hwL hP) r
/--
@isnad1 id=eq.2h3v.s6.851a19a34627 from=translated src=- shape=994bef08 vocab=ca565b9f
-/
theorem PhiR_sq_eq (r : ℝ) : ((P.PhiR T r) ^ 2 : ℂ) = paperFT (fun u => (P.g T u : ℂ)) r :=
  Taper.PhiR_sq_eq hP.taper (w_pos hP) (two_w_le hwL hP) r
/--
@isnad1 id=eq.2h2v.s6.3d6af67e8643 from=translated src=- shape=8fbf36da vocab=876a4dcf
-/
theorem integral_phiHatR_sq : ∫ r, P.phiHatR T r ^ 2 = 2 * π * P.a T * P.L T :=
  Taper.integral_phiHatR_sq hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=eq.2h2v.s6.962dbcd7fdab from=translated src=- shape=8fbf36da vocab=24773130
-/
theorem integral_PhiR_sq : ∫ r, P.PhiR T r ^ 2 = 2 * π * P.b T * P.L T :=
  Taper.integral_PhiR_sq hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=eq.2h3v.s6.b56554bb0fde from=translated src=- shape=9700c353 vocab=57d02dd8
-/
theorem integral_phiHatR_sq_mul_cos (y : ℝ) :
    ∫ r, P.phiHatR T r ^ 2 * Real.cos (r * y) = 2 * π * P.Aphi T y :=
  Taper.integral_phiHatR_sq_mul_cos hP.taper (w_pos hP) (two_w_le hwL hP) y
/--
@isnad1 id=eq.2h3v.s6.e5f002f6f1d8 from=translated src=- shape=9700c353 vocab=a1c7bb57
-/
theorem integral_PhiR_sq_mul_cos (y : ℝ) :
    ∫ x, P.PhiR T x ^ 2 * Real.cos (x * y) = 2 * π * P.g T y :=
  Taper.integral_PhiR_sq_mul_cos hP.taper (w_pos hP) (two_w_le hwL hP) y
/--
@isnad1 id=integrab.2h2v.s6.5e876b640c2e from=translated src=- shape=1cb521be vocab=5ad33bbe
-/
theorem integrable_phiHatR_sq : Integrable (fun r => P.phiHatR T r ^ 2) :=
  Taper.integrable_phiHatR_sq hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=integrab.2h2v.s6.38c679b234ab from=translated src=- shape=21e9733f vocab=8248af73
-/
theorem integrable_phiHatR_sq_mul_abs : Integrable (fun r => P.phiHatR T r ^ 2 * |r|) :=
  Taper.integrable_phiHatR_sq_mul_abs hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=integrab.2h2v.s6.2a52a1c7ddea from=translated src=- shape=1cb521be vocab=a6dbfd99
-/
theorem integrable_PhiR_sq : Integrable (fun x => P.PhiR T x ^ 2) :=
  Taper.integrable_PhiR_sq hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=integrab.2h2v.s6.80d1933e2a6a from=translated src=- shape=21e9733f vocab=2abbca24
-/
theorem integrable_PhiR_sq_mul_abs : Integrable (fun x => P.PhiR T x ^ 2 * |x|) :=
  Taper.integrable_PhiR_sq_mul_abs hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=le.2h2v.s7.545724172ebe from=translated src=- shape=cb83a217 vocab=4d1180df
-/
theorem integral_phiHatR_sq_mul_abs_le :
    ∫ r, P.phiHatR T r ^ 2 * |r| ≤ 8 + 8 * Real.log (P.crho * P.L T / (4 * P.w)) :=
  Taper.integral_phiHatR_sq_mul_abs_le hP.taper hP.one_le_w hwL
/--
@isnad1 id=le.2h2v.s7.b9cf95e479f7 from=translated src=- shape=cb83a217 vocab=dff171b0
-/
theorem integral_PhiR_sq_mul_abs_le :
    ∫ x, P.PhiR T x ^ 2 * |x| ≤ 8 + 8 * Real.log (P.crho * P.L T / (4 * P.w)) :=
  Taper.integral_PhiR_sq_mul_abs_le hP.taper hP.one_le_w hwL
/--
@isnad1 id=integrab.2h2v.s6.765c79cc3225 from=translated src=- shape=4be744af vocab=5ad33bbe
-/
theorem integrable_phiHatR_sq_mul_sq : Integrable (fun r => P.phiHatR T r ^ 2 * r ^ 2) :=
  Taper.integrable_phiHatR_sq_mul_sq hP.taper hP.one_le_w hwL
/--
@isnad1 id=le.2h2v.s7.a3543770b6f7 from=translated src=- shape=bdecf6bf vocab=5b0fe2ab
-/
theorem integral_phiHatR_sq_mul_sq_le : ∫ r, P.phiHatR T r ^ 2 * r ^ 2 ≤ 8 + 2 * (P.crho / P.w) ^ 2 :=
  Taper.integral_phiHatR_sq_mul_sq_le hP.taper hP.one_le_w hwL
/--
@isnad1 id=integrab.2h2v.s6.12be22af11a4 from=translated src=- shape=4be744af vocab=a6dbfd99
-/
theorem integrable_PhiR_sq_mul_sq : Integrable (fun x => P.PhiR T x ^ 2 * x ^ 2) :=
  Taper.integrable_PhiR_sq_mul_sq hP.taper hP.one_le_w hwL
/--
@isnad1 id=le.2h2v.s7.904ca380e4c9 from=translated src=- shape=bdecf6bf vocab=3f1d473c
-/
theorem integral_PhiR_sq_mul_sq_le : ∫ x, P.PhiR T x ^ 2 * x ^ 2 ≤ 8 + 2 * (P.crho / P.w) ^ 2 :=
  Taper.integral_PhiR_sq_mul_sq_le hP.taper hP.one_le_w hwL

/-! #### [eq:gbounds] -/
/--
@isnad1 id=le.2h3v.s6.9c804a87a540 from=translated src=- shape=969ff5ce vocab=bc6367a2
-/
theorem g_ge (y : ℝ) : max (P.L T - 2 * P.w - |y|) 0 ≤ P.g T y :=
  Taper.g_ge hP.taper (w_pos hP) (two_w_le hwL hP) y
/--
@isnad1 id=le.2h3v.s5.2c26f82d5ea5 from=translated src=- shape=ac677565 vocab=f6fc034e
-/
theorem g_le_Aphi (y : ℝ) : P.g T y ≤ P.Aphi T y :=
  Taper.g_le_Aphi hP.taper (w_pos hP) (two_w_le hwL hP) y
/--
@isnad1 id=le.2h3v.s6.6c3127fec4d8 from=translated src=- shape=bd6af409 vocab=751024e8
-/
theorem Aphi_le (y : ℝ) : P.Aphi T y ≤ max (P.L T - |y|) 0 :=
  Taper.Aphi_le hP.taper (w_pos hP) (two_w_le hwL hP) y
/--
@isnad1 id=le.2h3v.s5.73dfdf86743a from=translated src=- shape=14ce4e72 vocab=032c63d9
-/
theorem g_nonneg (y : ℝ) : 0 ≤ P.g T y := Taper.g_nonneg hP.taper (w_pos hP) (two_w_le hwL hP) y
/--
@isnad1 id=le.2h3v.s5.7295a3b4e9ca from=translated src=- shape=14ce4e72 vocab=26d3bf86
-/
theorem Aphi_nonneg (y : ℝ) : 0 ≤ P.Aphi T y :=
  Taper.Aphi_nonneg hP.taper (w_pos hP) (two_w_le hwL hP) y
/--
@isnad1 id=eq.3h3v.s5.b36c4bdf8960 from=translated src=- shape=3ccd49dd vocab=b4e607b4
-/
theorem g_eq_zero {y : ℝ} (hy : P.L T ≤ |y|) : P.g T y = 0 :=
  Taper.g_eq_zero hP.taper (w_pos hP) (two_w_le hwL hP) hy
/--
@isnad1 id=eq.3h3v.s5.f2b52ecc2076 from=translated src=- shape=3ccd49dd vocab=289251f5
-/
theorem Aphi_eq_zero {y : ℝ} (hy : P.L T ≤ |y|) : P.Aphi T y = 0 :=
  Taper.Aphi_eq_zero hP.taper (w_pos hP) (two_w_le hwL hP) hy
/--
@isnad1 id=continuo.2h2v.s5.ae9861686830 from=translated src=- shape=ba2c2dea vocab=ca22f612
-/
theorem g_continuous : Continuous (P.g T) :=
  Taper.g_continuous hP.taper (w_pos hP) (two_w_le hwL hP)
/--
@isnad1 id=continuo.2h2v.s5.4ff3daba04f0 from=translated src=- shape=ba2c2dea vocab=381ad81f
-/
theorem Aphi_continuous : Continuous (P.Aphi T) :=
  Taper.Aphi_continuous hP.taper (w_pos hP) (two_w_le hwL hP)

/-! #### [eq:psidef] division-free, and ψ form -/
/--
@isnad1 id=le.2h3v.s5.839f6293d1ef from=translated src=- shape=08752bf8 vocab=f59bf621
-/
theorem abs_phiHatR_le_L (r : ℝ) : |P.phiHatR T r| ≤ P.L T :=
  Taper.abs_phiHatR_le_L hP.taper (w_pos hP) (two_w_le hwL hP) r
/--
@isnad1 id=le.2h3v.s6.7c50de94d6ce from=translated src=- shape=7ca40a74 vocab=f59bf621
-/
theorem abs_phiHatR_mul_abs_le (r : ℝ) : |P.phiHatR T r| * |r| ≤ 2 :=
  Taper.abs_phiHatR_mul_abs_le hP.taper (w_pos hP) (two_w_le hwL hP) r
/--
@isnad1 id=le.2h3v.s6.156dbd0cf777 from=translated src=- shape=c3b412a1 vocab=f043a177
-/
theorem abs_phiHatR_mul_sq_le (r : ℝ) : |P.phiHatR T r| * r ^ 2 ≤ P.crho / P.w :=
  Taper.abs_phiHatR_mul_sq_le hP.taper hP.one_le_w (two_w_le hwL hP) r
/--
@isnad1 id=le.2h3v.s5.257c29c6c75d from=translated src=- shape=08752bf8 vocab=0e9cfd21
-/
theorem abs_PhiR_le_L (r : ℝ) : |P.PhiR T r| ≤ P.L T :=
  Taper.abs_PhiR_le_L hP.taper (w_pos hP) (two_w_le hwL hP) r
/--
@isnad1 id=le.2h3v.s6.9997fbac1fee from=translated src=- shape=7ca40a74 vocab=0e9cfd21
-/
theorem abs_PhiR_mul_abs_le (r : ℝ) : |P.PhiR T r| * |r| ≤ 2 :=
  Taper.abs_PhiR_mul_abs_le hP.taper (w_pos hP) (two_w_le hwL hP) r
/--
@isnad1 id=le.2h3v.s6.b0932b3ca771 from=translated src=- shape=c3b412a1 vocab=377b186a
-/
theorem abs_PhiR_mul_sq_le (r : ℝ) : |P.PhiR T r| * r ^ 2 ≤ P.crho / P.w :=
  Taper.abs_PhiR_mul_sq_le hP.taper hP.one_le_w (two_w_le hwL hP) r
/--
@isnad1 id=le.2h3v.s5.a2bba8af5c5e from=translated src=- shape=406bb80f vocab=e7b5bf5b
-/
theorem abs_phiHatR_le_psi' (r : ℝ) : |P.phiHatR T r| ≤ P.psi' T r :=
  Taper.abs_phiHatR_le_psi hP.taper hP.one_le_w (two_w_le hwL hP) r
/--
@isnad1 id=le.2h3v.s5.59c8cc3af201 from=translated src=- shape=406bb80f vocab=0cc6b5a4
-/
theorem abs_PhiR_le_psi' (r : ℝ) : |P.PhiR T r| ≤ P.psi' T r :=
  Taper.abs_PhiR_le_psi hP.taper hP.one_le_w (two_w_le hwL hP) r
/--
@isnad1 id=le.2h3v.s5.9a3ef83f1bb4 from=translated src=- shape=14ce4e72 vocab=afc36c75
-/
theorem psi'_nonneg (r : ℝ) : 0 ≤ P.psi' T r :=
  Taper.psi_nonneg hP.taper hP.one_le_w (two_w_le hwL hP) r

/-! #### [eq:psiints] -/
/--
@isnad1 id=le.2h2v.s7.e52c2eb00175 from=translated src=- shape=90035d6f vocab=68eca36f
-/
theorem integral_psi'_Ioi_le :
    ∫ r in Ioi 0, P.psi' T r ≤ 4 + 2 * Real.log (P.crho * P.L T / (4 * P.w)) :=
  Taper.integral_psi_Ioi_le hP.taper hP.one_le_w hwL
/--
@isnad1 id=le.2h2v.s7.b7c9ec5ed51e from=translated src=- shape=cb83a217 vocab=45b918e3
-/
theorem integral_psi'_sq_mul_abs_le :
    ∫ r, P.psi' T r ^ 2 * |r| ≤ 8 + 8 * Real.log (P.crho * P.L T / (4 * P.w)) :=
  Taper.integral_psi_sq_mul_abs_le hP.taper hP.one_le_w hwL
/--
@isnad1 id=le.2h2v.s6.2d5df7aa7edd from=translated src=- shape=541c2108 vocab=24018a3c
-/
theorem integral_psi'_sq_le : ∫ r, P.psi' T r ^ 2 ≤ 8 * P.L T :=
  Taper.integral_psi_sq_le hP.taper hP.one_le_w hwL
/--
@isnad1 id=integrab.2h2v.s5.8cddf725d4be from=translated src=- shape=fa26e63d vocab=96a34987
-/
theorem psi'_integrable : Integrable (P.psi' T) := Taper.psi_integrable hP.taper hP.one_le_w hwL
/--
@isnad1 id=integrab.2h2v.s6.7aea6c58d960 from=translated src=- shape=1cb521be vocab=7e4e94a9
-/
theorem psi'_sq_integrable : Integrable (fun r => P.psi' T r ^ 2) :=
  Taper.psi_sq_integrable hP.taper hP.one_le_w hwL
/--
@isnad1 id=integrab.2h2v.s6.1cd8f154a910 from=translated src=- shape=21e9733f vocab=04d324a1
-/
theorem psi'_sq_mul_abs_integrable : Integrable (fun r => P.psi' T r ^ 2 * |r|) :=
  Taper.psi_sq_mul_abs_integrable hP.taper hP.one_le_w hwL

end

end Params

end Zeta23
