/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PairCeiling/Defs.lean — shared definitions for the bandwidth-1 pair-correlation CEILING theorem
(analytic half: Stability.lean; numeric-certificate half: NumericCert.lean, RowCert.lean).

Weights s : ℕ → ℝ are the atom masses at the grid points j/N, j = 1..N (for a configuration: s j = S(j)/N).
  Csum s m        := Σ_{j=1}^{m} s j                                   (C_m)
  Cstep s N x     := Σ_{1 ≤ j ≤ N, j/N ≤ x} s j                         (right-continuous step function; = C_m on [m/N,(m+1)/N))
  Dfun s N x      := Cstep s N x − x²/2                                 (discrepancy against the GUE datum k dk)
  Efun s N x      := ∫₀ˣ Dfun                                           (integrated discrepancy)
-/
import Tengoku

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace Zeta23
namespace PairCeiling

/-- partial sums C_m := Σ_{j=1}^{m} s j. -/
def Csum (s : ℕ → ℝ) (m : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 m, s j

/-- the right-continuous step function C(x) = Σ_{1 ≤ j ≤ N, j/N ≤ x} s_j. -/
def Cstep (s : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ := ∑ j ∈ (Finset.Icc 1 N).filter (fun j : ℕ => ((j : ℕ) : ℝ) / N ≤ x), s j

/-- D := C − x²/2. -/
def Dfun (s : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ := Cstep s N x - x ^ 2 / 2

/-- E := ∫₀ˣ D. -/
def Efun (s : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, Dfun s N t

variable {s : ℕ → ℝ} {N : ℕ}

/--
@isnad1 id=eq.0h1v.s4.5034a8d0936a from=translated src=- shape=777ad2f6 vocab=07166699
-/
@[simp] lemma Csum_zero : Csum s 0 = 0 := by simp [Csum]

/--
@isnad1 id=eq.0h2v.s5.dfacfecd9faa from=translated src=- shape=c1f4b50c vocab=e8c05b4f
-/
lemma Csum_succ (m : ℕ) : Csum s (m + 1) = Csum s m + s (m + 1) := by
  unfold Csum
  rw [Finset.sum_Icc_succ_top (by omega)]

/-- on the cell [m/N, (m+1)/N) the step function equals C_m (m + 1 ≤ N).
@isnad1 id=eq.3h4v.s6.76311e4de20b from=translated src=- shape=b9ee7262 vocab=fb803fcf
-/
lemma Cstep_eq_Csum_of_mem (hN : 0 < N) {m : ℕ} (hm : m + 1 ≤ N) {x : ℝ}
    (hx : x ∈ Ico ((m : ℝ) / N) ((m + 1 : ℝ) / N)) : Cstep s N x = Csum s m := by
  unfold Cstep Csum
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, hjx⟩
    refine ⟨h1, ?_⟩
    have h' : (j : ℝ) / N < (m + 1 : ℝ) / N := lt_of_le_of_lt hjx hx.2
    rw [div_lt_div_iff_of_pos_right hNr] at h'
    have : (j : ℕ) < m + 1 := by exact_mod_cast h'
    omega
  · rintro ⟨h1, hjm⟩
    refine ⟨⟨h1, by omega⟩, le_trans ?_ hx.1⟩
    gcongr

/-- past the last atom the step function is C_N: for x ≥ 1.
@isnad1 id=eq.2h3v.s5.ea00381acb48 from=translated src=- shape=3cd11aa6 vocab=c5b2f1b8
-/
lemma Cstep_eq_Csum_of_one_le (hN : 0 < N) {x : ℝ} (hx : 1 ≤ x) : Cstep s N x = Csum s N := by
  unfold Cstep Csum
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc, and_iff_left_iff_imp, and_imp]
  intro _ hj
  refine le_trans ?_ hx
  rw [div_le_one hNr]; exact_mod_cast hj

/--
@isnad1 id=eq.1h2v.s4.06a291029178 from=translated src=- shape=99773298 vocab=169f69d5
-/
lemma Cstep_one (hN : 0 < N) : Cstep s N 1 = Csum s N := Cstep_eq_Csum_of_one_le hN le_rfl

/-- before the first atom: C = 0 for x < 1/N (in particular for x < 0).
@isnad1 id=eq.2h3v.s5.0df8013ccb92 from=translated src=- shape=fe4875a4 vocab=1a4cc525
-/
lemma Cstep_eq_zero_of_lt (hN : 0 < N) {x : ℝ} (hx : x < 1 / N) : Cstep s N x = 0 := by
  unfold Cstep
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine Finset.sum_eq_zero fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_Icc] at hj
  exfalso
  have : (1 : ℝ) / N ≤ (j : ℝ) / N := by gcongr; exact_mod_cast hj.1.1
  linarith [hj.2]

/--
@isnad1 id=eq.1h2v.s5.79f3bd8d41b9 from=translated src=- shape=431663f1 vocab=e0df6fc3
-/
lemma Dfun_one (hN : 0 < N) : Dfun s N 1 = Csum s N - 1 / 2 := by
  simp [Dfun, Cstep_one hN]

/--
@isnad1 id=eq.0h2v.s4.04ca92ae133d from=translated src=- shape=515686d5 vocab=f7797561
-/
@[simp] lemma Efun_zero : Efun s N 0 = 0 := by simp [Efun]

end PairCeiling
end Zeta23

end
