/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Core.Components.Gates
public import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Util.Polynomial
import Tengoku.LeanPool.LeanPool.LeanQuantumAlg.Util.Complex

/-!
# Quantum signal processing (single qubit) — Chebyshev basis

The Chebyshev-basis single-qubit QSP characterizations: the reflection-derived
**O-convention** of [Lin22, hermfunc.tex:1103] and the **Wx-convention (XZX
form)** of [GSLW19, BlockHam.tex:295]. Both interleave a fixed one-parameter
signal rotation with tunable `e^{iφZ}` processing rotations (in
`Core.Components.Gates`) and characterize exactly which `SU(2)`-valued
polynomial transforms of the signal `x ∈ [-1,1]` are achievable.

O-convention: the signal operator is `O(x) = [[x, -√(1-x²)], [√(1-x²), x]]`
and the QSP sequence with phase factors `(φ₀, …, φ_d)` is
`U_Φ(x) = e^{iφ₀Z} · ∏_{j=1}^d (O(x) e^{iφ_j Z})`.

`LeanPool.LeanQuantumAlg.ReflectionBasedQuantumSignalProcessing.main` [Lin22,
hermfunc.tex:1118]: `U_Φ(x)` takes the form
`[[P(x), -Q(x)√(1-x²)], [Q*(x)√(1-x²), P*(x)]]` for all `x ∈ [-1,1]` for some
phase factors **iff** `(P, Q)` is an `IsQSPPair d`, i.e.

1. `deg P ≤ d` and `Q.degree < d`,
2. `P` has parity `d mod 2` and `Q` has parity `(d-1) mod 2`,
3. `P·P* + (1-X²)·Q·Q* = 1` (`*` conjugates the coefficients; `conjP`).

Condition 3 is equivalent to the pointwise `|P(x)|² + (1-x²)|Q(x)|² = 1` on the
infinite set `[-1,1]` (`LeanPool.LeanQuantumAlg.qsp_normalization_iff`).

The **Wx-convention** replaces `O(x)` by `W(x) = e^{i·arccos(x)·X}`; the fixed
conjugation `W(x) = e^{-i(π/4)Z}·O(x)·e^{i(π/4)Z}` [Lin22, hermfunc.tex:1279]
transports the characterization
(`LeanPool.LeanQuantumAlg.ReflectionBasedQuantumSignalProcessing.main_wx`) with
the same pair conditions `IsQSPPair`.

This module is one half of the single-qubit QSP development; the Fourier-basis
(trigonometric YZY/YZZYZ) forms live in `LeanPool.LeanQuantumAlg.Primitives.QSP.Fourier`,
and `LeanPool.LeanQuantumAlg.Primitives.QSP` re-exports both.

## Main results

- `LeanPool.LeanQuantumAlg.qspO_mem_unitaryGroup` — `U_Φ(x)` is unitary for
  `x ∈ [-1,1]`.
- `LeanPool.LeanQuantumAlg.qspO_forward` /
  `LeanPool.LeanQuantumAlg.qspO_converse` — soundness and completeness of the
  O-convention.
- `LeanPool.LeanQuantumAlg.ReflectionBasedQuantumSignalProcessing.main` — the
  O-convention characterization (registered target entry point).
- `LeanPool.LeanQuantumAlg.ReflectionBasedQuantumSignalProcessing.main_wx` —
  the Wx-convention (XZX) characterization.

Pinned Mathlib API: `Polynomial.coeff_X_mul`, `Polynomial.coeff_mul`,
`Polynomial.degree_le_iff_coeff_zero`, `Polynomial.degree_lt_iff_coeff_zero`,
`Polynomial.eq_of_infinite_eval_eq`, `Complex.exp_mul_I`, `Complex.mul_conj`,
`Set.Icc.infinite`, `List.reverseRecOn`.
-/

@[expose] public section

namespace QuantumAlg

open Polynomial Complex

noncomputable section

/-! ### Signal operator (the processing rotation `rotZ` is in
`Core.Components.Gates`) -/

/-- The signal rotation `O(x) = [[x, -√(1-x²)], [√(1-x²), x]]`
[Lin22, hermfunc.tex:1103]; equals `U_A(x)·Z` for the reflection `U_A(x)` of
[GSLW19, BlockHam.tex:488]. -/
def signalO (x : ℝ) : HilbertOperator 1 :=
  !![(x : ℂ), -(Real.sqrt (1 - x ^ 2) : ℂ);
     (Real.sqrt (1 - x ^ 2) : ℂ), (x : ℂ)]

/-- The QSP sequence `U_Φ(x) = e^{iφ₀Z} ∏_j (O(x) e^{iφ_jZ})` with phase
factors `Φ = (φ₀, φs)` [Lin22, hermfunc.tex:1121]. -/
def qspO (φ₀ : ℝ) (φs : List ℝ) (x : ℝ) : HilbertOperator 1 :=
  φs.foldl (fun U φ => U * (signalO x * rotZ φ)) (rotZ φ₀ : HilbertOperator 1)

/--
@isnad1 id=eq.0h2v.s4.79d5124c59cd from=translated src=- shape=7e366221 vocab=91d9902a
-/
@[simp]
theorem qspO_nil (φ₀ : ℝ) (x : ℝ) : qspO φ₀ [] x = rotZ φ₀ := rfl

/--
@isnad1 id=eq.0h4v.s8.eb8de70b23d6 from=translated src=- shape=df682ab8 vocab=6042e039
-/
theorem qspO_concat (φ₀ : ℝ) (φs : List ℝ) (φ : ℝ) (x : ℝ) :
    qspO φ₀ (φs ++ [φ]) x = qspO φ₀ φs x * (signalO x * rotZ φ) := by
  simp [qspO, List.foldl_append]

/--
@isnad1 id=mem.1h1v.s9.970ceb2ee1e6 from=translated src=- shape=498473ad vocab=3c1ec962
-/
theorem signalO_mem_unitaryGroup {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    signalO x ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  have hs := sq_sqrt_one_sub_sq hx
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [signalO, Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
    linear_combination hs
  · simp [signalO, Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
    ring
  · simp [signalO, Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
    ring
  · simp [signalO, Matrix.mul_apply, Matrix.star_apply, Complex.conj_ofReal]
    linear_combination hs

/--
@isnad1 id=mem.1h3v.s9.554d18e77c52 from=translated src=- shape=46739481 vocab=7cf370d3
-/
theorem qspO_mem_unitaryGroup (φ₀ : ℝ) (φs : List ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    qspO φ₀ φs x ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  induction φs using List.reverseRecOn with
  | nil => exact rotZ_mem_unitaryGroup φ₀
  | append_singleton φs φ ih =>
      rw [qspO_concat]
      exact mul_mem ih (mul_mem (signalO_mem_unitaryGroup hx)
        (rotZ_mem_unitaryGroup φ))

/-! ### The QSP form and its one-step recurrence -/

/-- The target matrix form `[[P(x), -Q(x)s], [Q*(x)s, P*(x)]]`, `s = √(1-x²)`
[Lin22, hermfunc.tex:1121]. -/
def qspMat (P Q : ℂ[X]) (x : ℝ) : HilbertOperator 1 :=
  !![P.eval (x : ℂ), -Q.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ);
     starRingEnd ℂ (Q.eval (x : ℂ)) * (Real.sqrt (1 - x ^ 2) : ℂ),
     starRingEnd ℂ (P.eval (x : ℂ))]

/-- `rotZ φ₀` is the `d = 0` instance of the QSP form. -/
private theorem rotZ_eq_qspMat (c : ℂ) (φ₀ : ℝ) (x : ℝ)
    (hc : Complex.exp (φ₀ * Complex.I) = c) :
    (rotZ φ₀ : HilbertOperator 1) = qspMat (C c) 0 x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, rotZOp, qspMat, ← hc, conj_exp_I]

/-- One-step recurrence [Lin22, hermfunc.tex:1148]: appending a signal-phase
pair `O(x)·e^{iφZ}` maps the form `(P, Q)` to the form
`(e^{iφ}(X·P - (1-X²)·Q), e^{-iφ}(P + X·Q))`. -/
private theorem qspMat_step (P Q : ℂ[X]) (φ : ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    qspMat P Q x * (signalO x * rotZ φ) =
      qspMat (C (Complex.exp (φ * Complex.I)) * (X * P - (1 - X ^ 2) * Q))
        (C (Complex.exp (-(φ * Complex.I))) * (P + X * Q)) x := by
  have hs := sq_sqrt_one_sub_sq hx
  ext i j
  fin_cases i <;> fin_cases j
  · simp [qspMat, signalO, rotZ, rotZOp, Matrix.mul_apply, conj_exp_I, conj_exp_neg_I,
      Complex.conj_ofReal]
    linear_combination (-(Complex.exp ((φ : ℂ) * Complex.I) *
      Q.eval (x : ℂ))) * hs
  · simp [qspMat, signalO, rotZ, rotZOp, Matrix.mul_apply, conj_exp_I, conj_exp_neg_I,
      Complex.conj_ofReal]
    ring
  · simp [qspMat, signalO, rotZ, rotZOp, Matrix.mul_apply, conj_exp_I, conj_exp_neg_I,
      Complex.conj_ofReal]
    ring
  · simp [qspMat, signalO, rotZ, rotZOp, Matrix.mul_apply, conj_exp_I, conj_exp_neg_I,
      Complex.conj_ofReal]
    linear_combination (-(Complex.exp (-((φ : ℂ) * Complex.I)) *
      starRingEnd ℂ (Q.eval (x : ℂ)))) * hs

/-! ### The QSP pair conditions -/

/-- Conditions (1)–(3) of the QSP theorem [Lin22, hermfunc.tex:1127] for
degree budget `d`: degree bounds (`Q.degree < d` encodes `deg Q ≤ d-1`,
with `Q = 0` forced when `d = 0`), parities, and the polynomial normalization
identity (`*` = coefficient conjugation `conjP`). -/
structure IsQSPPair (d : ℕ) (P Q : ℂ[X]) : Prop where
  degP : P.degree ≤ d
  degQ : Q.degree < d
  parP : HasParity P d
  parQ : HasParity Q (d + 1)
  norm : P * conjP P + (1 - X ^ 2) * (Q * conjP Q) = 1

/--
@isnad1 id=eq.2h4v.s5.2e80831a30f2 from=translated src=- shape=3735c68f vocab=66a7634c
-/
theorem IsQSPPair.coeff_P_eq_zero {d : ℕ} {P Q : ℂ[X]} (h : IsQSPPair d P Q)
    {m : ℕ} (hm : d < m) : P.coeff m = 0 := by
  refine (Polynomial.degree_le_iff_coeff_zero P d).mp h.degP m ?_
  exact_mod_cast hm

/--
@isnad1 id=eq.2h4v.s5.31446c74d28a from=translated src=- shape=f7fdd3fd vocab=6dd860dd
-/
theorem IsQSPPair.coeff_Q_eq_zero {d : ℕ} {P Q : ℂ[X]} (h : IsQSPPair d P Q)
    {m : ℕ} (hm : d ≤ m) : Q.coeff m = 0 :=
  (Polynomial.degree_lt_iff_coeff_zero Q d).mp h.degQ m (by exact_mod_cast hm)

/-- Build the degree conditions from coefficient bounds.
@isnad1 id=isqsppai.5h3v.s7.78056dec7fe9 from=translated src=- shape=6bf081d7 vocab=2eb467a9
-/
theorem isQSPPair_of_coeff {d : ℕ} {P Q : ℂ[X]}
    (hP : ∀ m, d < m → P.coeff m = 0) (hQ : ∀ m, d ≤ m → Q.coeff m = 0)
    (parP : HasParity P d) (parQ : HasParity Q (d + 1))
    (norm : P * conjP P + (1 - X ^ 2) * (Q * conjP Q) = 1) :
    IsQSPPair d P Q := by
  refine ⟨?_, ?_, parP, parQ, norm⟩
  · refine (Polynomial.degree_le_iff_coeff_zero P d).mpr fun m hm => hP m ?_
    exact_mod_cast hm
  · exact (Polynomial.degree_lt_iff_coeff_zero Q d).mpr fun m hm =>
      hQ m (by exact_mod_cast hm)

/-- The normalization identity is preserved by the one-step recurrence: a pure
ring identity once the unit-modulus factor `v·w = v·v* = 1` cancels. -/
private theorem qsp_norm_step (P Q : ℂ[X]) (v w : ℂ) (hv : starRingEnd ℂ v = w)
    (hvw : v * w = 1)
    (hnorm : P * conjP P + (1 - X ^ 2) * (Q * conjP Q) = 1) :
    (C v * (X * P - (1 - X ^ 2) * Q)) *
        conjP (C v * (X * P - (1 - X ^ 2) * Q))
      + (1 - X ^ 2) *
        ((C w * (P + X * Q)) * conjP (C w * (P + X * Q))) = 1 := by
  have hw : starRingEnd ℂ w = v := by rw [← hv, Complex.conj_conj]
  have hCvw : (C v * C w : ℂ[X]) = 1 := by rw [← C_mul, hvw, map_one]
  simp only [conjP_mul, conjP_sub, conjP_add, conjP_C, conjP_X, conjP_one,
    conjP_pow, hv, hw]
  linear_combination (C v * C w : ℂ[X]) * hnorm + hCvw

/-- One-step closure of the QSP pair conditions, matching `qspMat_step`. -/
private theorem IsQSPPair.step {d : ℕ} {P Q : ℂ[X]} (h : IsQSPPair d P Q) (φ : ℝ) :
    IsQSPPair (d + 1)
      (C (Complex.exp (φ * Complex.I)) * (X * P - (1 - X ^ 2) * Q))
      (C (Complex.exp (-(φ * Complex.I))) * (P + X * Q)) := by
  refine isQSPPair_of_coeff (fun m hm => ?_) (fun m hm => ?_) ?_ ?_ ?_
  · have h1 : P.coeff (m - 1) = 0 := h.coeff_P_eq_zero (by omega)
    have h2 : Q.coeff m = 0 := h.coeff_Q_eq_zero (by omega)
    have h3 : Q.coeff (m - 2) = 0 := h.coeff_Q_eq_zero (by omega)
    have hm0 : ¬ m = 0 := by omega
    have hm2 : ¬ m < 2 := by omega
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_sub, sub_mul, one_mul,
      coeff_X_mul', coeff_X_sq_mul, h1, h2, h3, hm0, hm2]
  · have h1 : P.coeff m = 0 := h.coeff_P_eq_zero (by omega)
    have h2 : Q.coeff (m - 1) = 0 := h.coeff_Q_eq_zero (by omega)
    have hm0 : ¬ m = 0 := by omega
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_add, coeff_X_mul', h1, h2,
      hm0]
  · exact ((h.parP.X_mul).sub (h.parQ.one_sub_X_sq_mul.congr (by omega))).C_mul _
  · exact ((h.parP.congr (by omega)).add (h.parQ.X_mul)).C_mul _
  · exact qsp_norm_step P Q _ _ (conj_exp_I φ) (exp_I_mul_exp_neg_I φ) h.norm

/-! ### Soundness (forward direction) -/

/-- Soundness of QSP [Lin22, hermfunc.tex:1139]: every QSP product
`U_Φ(x)` takes the form `qspMat P Q x` on `[-1,1]` for a pair `(P, Q)`
satisfying the degree, parity, and normalization conditions.
@isnad1 id=ex.0h2v.s6.55c0b1dc68f2 from=translated src=- shape=72a915d2 vocab=0369e366
-/
theorem qspO_forward (φ₀ : ℝ) (φs : List ℝ) :
    ∃ P Q : ℂ[X], IsQSPPair φs.length P Q ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1, qspO φ₀ φs x = qspMat P Q x := by
  induction φs using List.reverseRecOn with
  | nil =>
      refine ⟨C (Complex.exp (φ₀ * Complex.I)), 0, ⟨?_, ?_, ?_, ?_, ?_⟩,
        fun x _ => rotZ_eq_qspMat _ φ₀ x rfl⟩
      · simp
      · simp
      · exact hasParity_C _ rfl
      · exact hasParity_zero _
      · have hC : (C (Complex.exp (φ₀ * Complex.I)) *
            C (Complex.exp (-(φ₀ * Complex.I))) : ℂ[X]) = 1 := by
          rw [← C_mul, exp_I_mul_exp_neg_I, map_one]
        simpa [conj_exp_I] using hC
  | append_singleton φs φ ih =>
      obtain ⟨P, Q, hpair, hmat⟩ := ih
      refine ⟨_, _, by simpa using hpair.step φ, fun x hx => ?_⟩
      rw [qspO_concat, hmat x hx, qspMat_step P Q φ hx]

/-! ### Completeness (converse direction)

Degree-reduction induction [Lin22, hermfunc.tex:1212]: given an `IsQSPPair`
pair with `deg P = d ≥ 1`, a phase `φ` with `e^{2iφ} q_{d-1} = p_d` makes the
*inverse* recurrence drop the degree by one; if instead both leading
coefficients vanish, the pair already satisfies the conditions two levels
down and the sequence is padded with the no-op pair
`O(x)e^{i(π/2)Z} · O(x)e^{-i(π/2)Z} = 1`. -/

/-- First inverse-recurrence polynomial `e^{-iφ}·X·P + e^{iφ}·(1-X²)·Q`
(with `v = e^{iφ}`, `w = e^{-iφ}`). -/
private def unstepP (v w : ℂ) (P Q : ℂ[X]) : ℂ[X] :=
  C w * (X * P) + C v * ((1 - X ^ 2) * Q)

/-- Second inverse-recurrence polynomial `e^{iφ}·X·Q - e^{-iφ}·P`. -/
private def unstepQ (v w : ℂ) (P Q : ℂ[X]) : ℂ[X] :=
  C v * (X * Q) - C w * P

/-! ### Padding with a no-op pair -/

/-! ### Completeness and the characterization -/

/-- The polynomial normalization identity is equivalent to the pointwise
normalization `|P(x)|² + (1-x²)|Q(x)|² = 1` on `[-1,1]`
[Lin22, hermfunc.tex:1134].
@isnad1 id=iff.0h2v.s8.3abfe85770a3 from=translated src=- shape=9c985b11 vocab=1b3479e0
-/
theorem qsp_normalization_iff (P Q : ℂ[X]) :
    P * conjP P + (1 - X ^ 2) * (Q * conjP Q) = 1 ↔
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        P.eval (x : ℂ) * starRingEnd ℂ (P.eval (x : ℂ))
          + (1 - (x : ℂ) ^ 2) *
            (Q.eval (x : ℂ) * starRingEnd ℂ (Q.eval (x : ℂ))) = 1 := by
  constructor
  · intro hid x hx
    have h := congrArg (Polynomial.eval (x : ℂ)) hid
    simpa [conjP_eval_ofReal] using h
  · intro hpt
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine (((Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).image
      Complex.ofReal_injective.injOn).mono ?_)
    rintro z ⟨x, hx, rfl⟩
    have h := hpt x hx
    simp only [Set.mem_ofPred_eq]
    simpa [conjP_eval_ofReal] using h

/-! ### The Wx-convention (XZX form)

The `Wx`-convention of [GSLW19, BlockHam.tex:295] uses the signal rotation
`W(x) = e^{i·arccos(x)·X}` in place of `O(x)`. The two are related by the
fixed conjugation `W(x) = e^{-i(π/4)Z} · O(x) · e^{i(π/4)Z}`
[Lin22, hermfunc.tex:1279], so the characterization
[GSLW19, BlockHam.tex:313] (`thm:basicCharacterisation`) transports verbatim
from `qsp_reflection_iff` with the *same* pair conditions `IsQSPPair`. -/

/-- The `Wx` signal rotation
`W(x) = [[x, i√(1-x²)], [i√(1-x²), x]] = e^{i·arccos(x)·X}`
[GSLW19, BlockHam.tex:295]. -/
def signalW (x : ℝ) : HilbertOperator 1 :=
  !![(x : ℂ), Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ);
     Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ), (x : ℂ)]

/-- The Wx-convention QSP sequence `e^{iφ₀Z} ∏_j (W(x) e^{iφ_jZ})`
[GSLW19, BlockHam.tex:317]. -/
def qspW (φ₀ : ℝ) (φs : List ℝ) (x : ℝ) : HilbertOperator 1 :=
  φs.foldl (fun U φ => U * (signalW x * rotZ φ)) (rotZ φ₀ : HilbertOperator 1)

/--
@isnad1 id=eq.0h2v.s4.89463e99a2a8 from=translated src=- shape=7e366221 vocab=c59a3768
-/
@[simp]
theorem qspW_nil (φ₀ : ℝ) (x : ℝ) : qspW φ₀ [] x = rotZ φ₀ := rfl

/--
@isnad1 id=eq.0h4v.s8.a718dfb41722 from=translated src=- shape=df682ab8 vocab=dc304e5d
-/
theorem qspW_concat (φ₀ : ℝ) (φs : List ℝ) (φ : ℝ) (x : ℝ) :
    qspW φ₀ (φs ++ [φ]) x = qspW φ₀ φs x * (signalW x * rotZ φ) := by
  simp [qspW, List.foldl_append]

private theorem rotZ_comm_op (a b : ℝ) :
    (rotZ a : HilbertOperator 1) * (rotZ b : HilbertOperator 1) =
      (rotZ b : HilbertOperator 1) * (rotZ a : HilbertOperator 1) := by
  simpa using congrArg (fun G : Gate 1 => (G : HilbertOperator 1)) (rotZ_comm a b)

private theorem rotZ_neg_mul_rotZ_op (φ : ℝ) :
    (rotZ (-φ) : HilbertOperator 1) * (rotZ φ : HilbertOperator 1) = 1 := by
  simpa using congrArg (fun G : Gate 1 => (G : HilbertOperator 1)) (rotZ_neg_mul_rotZ φ)

private theorem rotZ_mul_rotZ_neg_op (φ : ℝ) :
    (rotZ φ : HilbertOperator 1) * (rotZ (-φ) : HilbertOperator 1) = 1 := by
  simpa using congrArg (fun G : Gate 1 => (G : HilbertOperator 1)) (rotZ_mul_rotZ_neg φ)

/-- The Wx target form `[[P(x), iQ(x)s], [iQ*(x)s, P*(x)]]`, `s = √(1-x²)`
[GSLW19, BlockHam.tex:313]. -/
def qspMatW (P Q : ℂ[X]) (x : ℝ) : HilbertOperator 1 :=
  !![P.eval (x : ℂ),
     Complex.I * Q.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ);
     Complex.I * starRingEnd ℂ (Q.eval (x : ℂ)) * (Real.sqrt (1 - x ^ 2) : ℂ),
     starRingEnd ℂ (P.eval (x : ℂ))]

/-- The fixed conjugation relating the two signal operators,
`e^{i(π/4)Z} · W(x) = O(x) · e^{i(π/4)Z}` [Lin22, hermfunc.tex:1279]. -/
private theorem rotZ_mul_signalW (x : ℝ) :
    (rotZ (Real.pi / 4) : HilbertOperator 1) * signalW x =
      signalO x * rotZ (Real.pi / 4) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [rotZ, rotZOp, signalW, signalO, Matrix.mul_apply]
    ring
  · simp [rotZ, rotZOp, signalW, signalO, Matrix.mul_apply]
    linear_combination ((Real.sqrt (1 - x ^ 2) : ℂ)) * exp_pi_div_four_mul_I
  · simp [rotZ, rotZOp, signalW, signalO, Matrix.mul_apply]
    linear_combination ((Real.sqrt (1 - x ^ 2) : ℂ)) *
      exp_neg_pi_div_four_mul_I
  · simp [rotZ, rotZOp, signalW, signalO, Matrix.mul_apply]
    ring

/-- The conjugation transports the Wx target form to the reflection form. -/
private theorem rotZ_mul_qspMatW (P Q : ℂ[X]) (x : ℝ) :
    (rotZ (Real.pi / 4) : HilbertOperator 1) * qspMatW P Q x =
      qspMat P Q x * rotZ (Real.pi / 4) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [rotZ, rotZOp, qspMatW, qspMat, Matrix.mul_apply]
    ring
  · simp [rotZ, rotZOp, qspMatW, qspMat, Matrix.mul_apply]
    linear_combination (Q.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ)) *
      exp_pi_div_four_mul_I
  · simp [rotZ, rotZOp, qspMatW, qspMat, Matrix.mul_apply]
    linear_combination (starRingEnd ℂ (Q.eval (x : ℂ)) *
      (Real.sqrt (1 - x ^ 2) : ℂ)) * exp_neg_pi_div_four_mul_I
  · simp [rotZ, rotZOp, qspMatW, qspMat, Matrix.mul_apply]
    ring

/-- The conjugation intertwines the full QSP sequences:
`e^{i(π/4)Z} · U^W_Φ(x) = U^O_Φ(x) · e^{i(π/4)Z}`. -/
private theorem rotZ_mul_qspW (φ₀ : ℝ) (φs : List ℝ) (x : ℝ) :
    (rotZ (Real.pi / 4) : HilbertOperator 1) * qspW φ₀ φs x =
      qspO φ₀ φs x * rotZ (Real.pi / 4) := by
  induction φs using List.reverseRecOn with
  | nil => simpa using rotZ_comm_op (Real.pi / 4) φ₀
  | append_singleton φs φ ih =>
      rw [qspW_concat, qspO_concat, ← mul_assoc, ih, mul_assoc,
        ← mul_assoc (rotZ (Real.pi / 4) : HilbertOperator 1) (signalW x)
          (rotZ φ : HilbertOperator 1),
        rotZ_mul_signalW, mul_assoc (signalO x)
          (rotZ (Real.pi / 4) : HilbertOperator 1) (rotZ φ : HilbertOperator 1),
        rotZ_comm_op (Real.pi / 4) φ,
        ← mul_assoc (signalO x) (rotZ φ : HilbertOperator 1)
          (rotZ (Real.pi / 4) : HilbertOperator 1),
        ← mul_assoc]

/--
@isnad1 id=mem.1h1v.s9.7fe32b014afd from=translated src=- shape=498473ad vocab=acafeebd
-/
theorem signalW_mem_unitaryGroup {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    signalW x ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  have h : signalW x = (rotZ (-(Real.pi / 4)) : HilbertOperator 1) *
      (signalO x * rotZ (Real.pi / 4)) := by
    rw [← rotZ_mul_signalW, ← mul_assoc, rotZ_neg_mul_rotZ_op, one_mul]
  rw [h]
  exact mul_mem (rotZ_mem_unitaryGroup _)
    (mul_mem (signalO_mem_unitaryGroup hx) (rotZ_mem_unitaryGroup _))

/--
@isnad1 id=mem.1h3v.s9.b1cf740647d0 from=translated src=- shape=46739481 vocab=93dcff68
-/
theorem qspW_mem_unitaryGroup (φ₀ : ℝ) (φs : List ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    qspW φ₀ φs x ∈ Matrix.unitaryGroup (Fin (2 ^ 1)) ℂ := by
  induction φs using List.reverseRecOn with
  | nil => exact rotZ_mem_unitaryGroup φ₀
  | append_singleton φs φ ih =>
      rw [qspW_concat]
      exact mul_mem ih (mul_mem (signalW_mem_unitaryGroup hx)
        (rotZ_mem_unitaryGroup φ))

/-- Pointwise, the Wx form holds iff the reflection form holds (conjugation
by the unit `e^{i(π/4)Z}`).
@isnad1 id=iff.0h5v.s5.8cd2a98d72b6 from=translated src=- shape=d3e72c32 vocab=09db6094
-/
theorem qspW_form_iff (φ₀ : ℝ) (φs : List ℝ) (P Q : ℂ[X]) (x : ℝ) :
    qspW φ₀ φs x = qspMatW P Q x ↔ qspO φ₀ φs x = qspMat P Q x := by
  constructor
  · intro h
    calc qspO φ₀ φs x
        = (rotZ (Real.pi / 4) * qspW φ₀ φs x) * rotZ (-(Real.pi / 4)) := by
          rw [rotZ_mul_qspW, mul_assoc, rotZ_mul_rotZ_neg_op, mul_one]
      _ = (rotZ (Real.pi / 4) * qspMatW P Q x) * rotZ (-(Real.pi / 4)) := by
          rw [h]
      _ = qspMat P Q x := by
          rw [rotZ_mul_qspMatW, mul_assoc, rotZ_mul_rotZ_neg_op, mul_one]
  · intro h
    calc qspW φ₀ φs x
        = rotZ (-(Real.pi / 4)) * (rotZ (Real.pi / 4) * qspW φ₀ φs x) := by
          rw [← mul_assoc, rotZ_neg_mul_rotZ_op, one_mul]
      _ = rotZ (-(Real.pi / 4)) * (qspMat P Q x * rotZ (Real.pi / 4)) := by
          rw [rotZ_mul_qspW, h]
      _ = rotZ (-(Real.pi / 4)) * (rotZ (Real.pi / 4) * qspMatW P Q x) := by
          rw [rotZ_mul_qspMatW]
      _ = qspMatW P Q x := by
          rw [← mul_assoc, rotZ_neg_mul_rotZ_op, one_mul]

end

end QuantumAlg
