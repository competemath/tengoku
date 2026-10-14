/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Statement/SeamClosed.lean — the ζ-seam is closed.
All four fields of Zeta23.ZetaSeam are theorems of Mathlib:
  one_le_mult, finite_window  — Zeta23/Statement/Seam.lean ;
  reflect_zero, mult_reflect  — Zeta23/ZetaReflect.lean (Schwarz reflection
                                 riemannZeta_conj + functional equation at the analyticOrderAt level).
Hence the abstract ZeroConfig of ζ's nontrivial zeros and [eq:trivialchain] are hypothesis-free.
-/
import Tengoku.FormalMath.Zeta23.Statement.Seam
import Tengoku.FormalMath.Zeta23.ZetaReflect

noncomputable section

namespace Zeta23

/-- The ζ-seam, fully discharged: no hypotheses.
@isnad1 id=zetaseam.0h0v.s0.90c8f16bde98 from=translated src=- shape=45709ebd vocab=90c8f16b
-/
theorem zetaSeam : ZetaSeam := ZetaSeam.of_reflect zeta_reflect_zero zeta_mult_reflect

/-- The nontrivial zeros of ζ with multiplicities, as an abstract Zeta23.ZeroConfig — hypothesis-free.
carrier = {ρ | IsNontrivialZero ρ}, mult = zeroMult (both rfl). -/
def zetaZeroConfig : ZeroConfig := zetaZeros zetaSeam

/--
@isnad1 id=eq.0h0v.s3.7425f3036657 from=translated src=- shape=dcf582a4 vocab=c4ccf351
-/
@[simp] lemma zetaZeroConfig_carrier : zetaZeroConfig.carrier = {ρ | IsNontrivialZero ρ} := rfl
/--
@isnad1 id=eq.0h0v.s2.5ccbf875fa22 from=translated src=- shape=fbd2708e vocab=6a1dd5da
-/
@[simp] lemma zetaZeroConfig_mult : zetaZeroConfig.mult = zeroMult := rfl

/--
@isnad1 id=eq.0h2v.s3.8121d1dc0a6f from=translated src=- shape=88abb201 vocab=a3123829
-/
@[simp] lemma zetaZeroConfig_N (T₁ T₂ : ℝ) : zetaZeroConfig.N T₁ T₂ = Ncount T₁ T₂ :=
  zetaZeros_N _ _ _
/--
@isnad1 id=eq.0h2v.s3.04dfcb376a3f from=translated src=- shape=88abb201 vocab=46bf4689
-/
@[simp] lemma zetaZeroConfig_N0star (T₁ T₂ : ℝ) : zetaZeroConfig.N0star T₁ T₂ = N0star T₁ T₂ :=
  zetaZeros_N0star _ _ _
/--
@isnad1 id=eq.0h2v.s3.5fc64afa52d0 from=translated src=- shape=88abb201 vocab=e4689ae0
-/
@[simp] lemma zetaZeroConfig_N0s (T₁ T₂ : ℝ) : zetaZeroConfig.N0s T₁ T₂ = N0simple T₁ T₂ :=
  zetaZeros_N0s _ _ _
/--
@isnad1 id=eq.0h2v.s3.2ea2e546c926 from=translated src=- shape=88abb201 vocab=8f4ce542
-/
@[simp] lemma zetaZeroConfig_Nd (T₁ T₂ : ℝ) : zetaZeroConfig.Nd T₁ T₂ = Ndist T₁ T₂ :=
  zetaZeros_Nd _ _ _

/-- [eq:trivialchain] for ζ, hypothesis-free: N₀ˢ ≤ N₀* ≤ N₀ ≤ N and N₀ˢ ≤ Nˢ ≤ N_d ≤ N.
@isnad1 id=and.0h2v.s5.0f8dbe8ea9dc from=translated src=- shape=6169bac2 vocab=25de0e4c
-/
theorem trivial_chain₀ (T₁ T₂ : ℝ) :
    N0simple T₁ T₂ ≤ N0star T₁ T₂ ∧ N0star T₁ T₂ ≤ N0 T₁ T₂ ∧ N0 T₁ T₂ ≤ Ncount T₁ T₂ ∧
    N0simple T₁ T₂ ≤ Nsimple T₁ T₂ ∧ Nsimple T₁ T₂ ≤ Ndist T₁ T₂ ∧ Ndist T₁ T₂ ≤ Ncount T₁ T₂ :=
  trivial_chain zetaSeam T₁ T₂

/-- Finiteness of every ordinate window of nontrivial zeros, hypothesis-free.
@isnad1 id=finite.0h2v.s3.731066c07ec5 from=translated src=- shape=215a98a0 vocab=8168efcf
-/
theorem zerosIn_finite (T₁ T₂ : ℝ) : (zerosIn T₁ T₂).Finite := by
  simpa [zetaZeros_window] using (zetaZeros zetaSeam).window_finite T₁ T₂

end Zeta23
