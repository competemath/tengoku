import Tengoku
import Tengoku.Xilab.XiLab.Kernel
import Tengoku.Xilab.XiLab.Wintner
import Tengoku.Xilab.XiLab.Evenness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms XiLab.J_nine_neg` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.iteratedDeriv_eight_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.iteratedDeriv_nine_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.iteratedDeriv_ten_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.G_c8_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.G_c10_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.G_c9_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.Phi_eq_G` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.hasDerivAt_G` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.iter10` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.G_at_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.poly_c8` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.poly_c10` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.tail_small` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# XiLab.Csordas — refutation of the Coffey–Csordás log-concavity conjecture

Consumes `XiLab/Kernel.lean` (`Phi`, `phiTerm`) and `XiLab/Evenness.lean`
(`T`, `thTerm`, `hasDerivAt_T`, `summable_thTerm_succ`, `Phi_eq_T`, `Phi_even`,
`hasDerivAt_neg_self`).  There is no `sorry`, no `native_decide`, no custom `axiom` and no
FRONTIER lemma in this file.

## The result

M. W. Coffey and G. Csordás, *On the log-concavity of a Jacobi theta function*,
Math. Comp. **82** (2013), 2265–2272, Conjecture 2.5 — restated as Open Problem 4.13 of
G. Csordás, Comput. Methods Funct. Theory **15** (2015), 373–391 — asserts that

  `J_n(t) = (Φ⁽ⁿ⁾(t))² − Φ⁽ⁿ⁻¹⁾(t) Φ⁽ⁿ⁺¹⁾(t) > 0`

for every real `t` and every `n`.  `XiLab.J_nine_neg` proves `J₉(0) < 0`.

(The kernel of `XiLab/Kernel.lean` is twice the classical one — `4π²n⁴ − 6πn²` rather than
`2π²n⁴ − 3πn²`.  `J` is homogeneous of degree two in `Φ`, so the sign is unaffected.)

## The argument

1. `Φ` is even (`XiLab.Phi_even`, proved in `Evenness.lean` from Poisson summation), so every
   odd-order derivative vanishes at the origin: `Φ⁽⁹⁾(0) = 0` (`iteratedDeriv_nine_zero`).
   Hence `J₉(0) = −Φ⁽⁸⁾(0) · Φ⁽¹⁰⁾(0)`.
2. `Φ⁽⁸⁾(0) ≈ 1823335.79 > 0` and `Φ⁽¹⁰⁾(0) ≈ 655898825.86 > 0`, so `J₉(0) ≈ −1.196·10¹⁵ < 0`.

The sign anomaly is at step 2: the signs of `Φ⁽²ʲ⁾(0)` for `j = 0..6` run `+,−,+,−,+,+,−`,
so the expected alternation fails at `j = 5`, which is precisely what makes `n = 9` a
counterexample.

## How the derivatives are taken

`Evenness.lean` already supplies the family `T k u = ∑_{n≥1} (πn²)^k e^{−πn²e^{2u}}` together
with `T k' = −2e^{2u} T (k+1)` (`hasDerivAt_T`), valid for *every* `k`.  Setting
`Eterm i u = e^{(1/2+2i)u} T i u` gives a family closed under `d/du`:

  `Eterm i' = (1/2 + 2i) Eterm i − 2 Eterm (i+1)`,

so no new term-by-term differentiation is needed at any order.  Writing
`G a u = ∑_{i<14} a i · Eterm i u`, differentiation is the linear coefficient recursion
`(stp a) i = (1/2+2i) a i − 2 a (i−1)` (`hasDerivAt_G`), and `Φ = G c₀` with
`c₀ = (0,−6,4,0,…)` (`Phi_eq_G`).  Iterating gives `iteratedDeriv m Φ = G cₘ` for `m ≤ 10`.

In polynomial language `Eterm i ↔ Xⁱ` and `G a ↔ P(X)`, `stp` is
`P ↦ ½P + 2XP′ − 2XP`, and at `u = 0`

  `Φ⁽ᵐ⁾(0) = ∑_{n≥1} e^{−πn²} Pₘ(πn²)`     (`G_at_zero`, `V_split`).

## The sign certification

`P₈` has degree 10 and `P₁₀` degree 12 (`poly_c8`, `poly_c10`).  With
`3.14159265358979 < π < 3.1415926535898` and the induced two-sided bounds on `π²,…,π¹²`,
each `Pₘ(kπ)` is a *linear* problem, closed by `linarith`.  The values are

| | `n=1` | `n=2` | `n=3` | `n=4` |
|---|---|---|---|---|
| `P₈`  | `+6.7153·10⁷`  | `−3.1450·10¹¹` | `+3.4569·10¹⁶` | `+3.5542·10¹⁹` |
| `P₁₀` | `−1.5150·10⁹`  | `+2.0309·10¹⁴` | `+2.4959·10¹⁹` | `+2.0604·10²³` |

so after multiplying by `e^{−πn²}` the first two terms of `Φ⁽⁸⁾(0)` are `+2901927` and
`−1096759`, and those of `Φ⁽¹⁰⁾(0)` are `−65469162` and `+708250608`.  **Two terms are
needed, not one**: at `j = 5` the `n = 1` term has the wrong sign and is overwhelmed by
`n = 2`.  Terms `n = 3, 4` are certified nonnegative and simply dropped; `n = 5` and the
tail `n ≥ 6` are bounded crudely (`|Pₘ(X)| ≤ (∑|aᵢ|) X¹²` for `X ≥ 1`, then `n²⁴ ≤ 4²⁴(e⁶)ⁿ`
against `e^{−πn²} ≤ (e^{−6π})ⁿ`) and contribute at most `1` each against margins of
`1.7·10⁶` and `6.1·10⁸`.

All numeric constants come from `Real.pi_gt_d20`, `Real.pi_lt_d20`, `Real.exp_one_gt_d9`,
`Real.exp_one_lt_d9` and `Real.add_one_le_exp`.
-/

open scoped Real
open Set Filter Topology

namespace XiLab

/-! ### The family `Eterm i u = e^{(1/2 + 2i)u} T i u` -/

/-- `Eterm i u = e^{(1/2+2i)u} · T i u = ∑_{n≥1} e^{u/2} (π n² e^{2u})^i e^{−π n² e^{2u}}`.-/
noncomputable def Eterm (i : ℕ) (u : ℝ) : ℝ := Real.exp ((1 / 2 + 2 * (i : ℝ)) * u) * T i u

/--
@isnad1 id=eq.0h1v.s4.198f5f9eacc1 from=translated src=- shape=ea5dac26 vocab=1683c02b
-/
lemma Eterm_zero (i : ℕ) : Eterm i 0 = T i 0 := by
  simp [Eterm]

/-- Differentiating `Eterm i` stays inside the family: `Eterm i' = (1/2+2i) Eterm i − 2 Eterm (i+1)`.
@isnad1 id=hasderiv.0h2v.s7.0970fd813494 from=translated src=- shape=01ca11aa vocab=54000ea8
-/
lemma hasDerivAt_Eterm (i : ℕ) (u : ℝ) :
    HasDerivAt (Eterm i) ((1 / 2 + 2 * (i : ℝ)) * Eterm i u - 2 * Eterm (i + 1) u) u := by
  have hexp : HasDerivAt (fun v : ℝ => Real.exp ((1 / 2 + 2 * (i : ℝ)) * v))
      (Real.exp ((1 / 2 + 2 * (i : ℝ)) * u) * (1 / 2 + 2 * (i : ℝ))) u := by
    simpa using ((hasDerivAt_id u).const_mul (1 / 2 + 2 * (i : ℝ))).exp
  have h := hexp.mul (hasDerivAt_T i u)
  have hE : Real.exp ((1 / 2 + 2 * ((i + 1 : ℕ) : ℝ)) * u)
      = Real.exp ((1 / 2 + 2 * (i : ℝ)) * u) * Real.exp (2 * u) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  have heq : (1 / 2 + 2 * (i : ℝ)) * Eterm i u - 2 * Eterm (i + 1) u
      = Real.exp ((1 / 2 + 2 * (i : ℝ)) * u) * (1 / 2 + 2 * (i : ℝ)) * T i u
        + Real.exp ((1 / 2 + 2 * (i : ℝ)) * u) * (-2 * Real.exp (2 * u) * T (i + 1) u) := by
    simp only [Eterm]
    rw [hE]; ring
  rw [heq]
  exact h

/-! ### Coefficient vectors and the finite combinations `G a` -/

/-- Shift a coefficient vector up by one index.-/
noncomputable def shf (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | (i + 1) => a i

/-- The coefficient recursion induced by `d/du`: `(stp a) i = (1/2+2i) a i − 2 a (i−1)`.-/
noncomputable def stp (a : ℕ → ℝ) : ℕ → ℝ := fun i => (1 / 2 + 2 * (i : ℝ)) * a i - 2 * shf a i

/-- `G a u = ∑_{i<14} a i · Eterm i u`.-/
noncomputable def G (a : ℕ → ℝ) (u : ℝ) : ℝ := ∑ i ∈ Finset.range 14, a i * Eterm i u

/-- Differentiating `G a` applies `stp` to the coefficients.  The hypothesis `a 13 = 0`
keeps the result inside the fixed window `i < 14`.
@isnad1 id=hasderiv.1h2v.s5.9810a3eaf4ff from=translated src=- shape=3436e64f vocab=f256e2f8
-/
lemma hasDerivAt_G (a : ℕ → ℝ) (h13 : a 13 = 0) (u : ℝ) :
    HasDerivAt (G a) (G (stp a) u) u := by
  have hfun : (fun v : ℝ => ∑ i ∈ Finset.range 14, a i * Eterm i v)
      = ∑ i ∈ Finset.range 14, (fun v : ℝ => a i * Eterm i v) := by
    funext v; simp
  have h : HasDerivAt (fun v : ℝ => ∑ i ∈ Finset.range 14, a i * Eterm i v)
      (∑ i ∈ Finset.range 14,
        a i * ((1 / 2 + 2 * (i : ℝ)) * Eterm i u - 2 * Eterm (i + 1) u)) u := by
    rw [hfun]
    exact HasDerivAt.sum (fun i _ => (hasDerivAt_Eterm i u).const_mul (a i))
  have e2 : ∑ i ∈ Finset.range 14, a i * Eterm (i + 1) u
      = ∑ i ∈ Finset.range 14, shf a i * Eterm i u := by
    rw [Finset.sum_range_succ (fun i => a i * Eterm (i + 1) u) 13,
      Finset.sum_range_succ' (fun i => shf a i * Eterm i u) 13]
    simp [shf, h13]
  have key : ∑ i ∈ Finset.range 14,
        a i * ((1 / 2 + 2 * (i : ℝ)) * Eterm i u - 2 * Eterm (i + 1) u)
      = ∑ i ∈ Finset.range 14, stp a i * Eterm i u := by
    have e1 : ∑ i ∈ Finset.range 14,
          a i * ((1 / 2 + 2 * (i : ℝ)) * Eterm i u - 2 * Eterm (i + 1) u)
        = (∑ i ∈ Finset.range 14, (1 / 2 + 2 * (i : ℝ)) * a i * Eterm i u)
          - 2 * ∑ i ∈ Finset.range 14, a i * Eterm (i + 1) u := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e1, e2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp only [stp]; ring)
  rw [G, ← key]
  exact h

/-! ### The eleven coefficient vectors -/

/-- `Φ = −6 Eterm₁ + 4 Eterm₂`, i.e. the polynomial `4X² − 6X`.-/
noncomputable def c0 : ℕ → ℝ := fun i => if i = 1 then -6 else if i = 2 then 4 else 0

noncomputable def c1 : ℕ → ℝ := stp c0
noncomputable def c2 : ℕ → ℝ := stp c1
noncomputable def c3 : ℕ → ℝ := stp c2
noncomputable def c4 : ℕ → ℝ := stp c3
noncomputable def c5 : ℕ → ℝ := stp c4
noncomputable def c6 : ℕ → ℝ := stp c5
noncomputable def c7 : ℕ → ℝ := stp c6
noncomputable def c8 : ℕ → ℝ := stp c7
noncomputable def c9 : ℕ → ℝ := stp c8
noncomputable def c10 : ℕ → ℝ := stp c9

/--
@isnad1 id=eq.0h1v.s5.80fb93e32c90 from=translated src=- shape=7e8f3a3e vocab=6b08ae25
-/
lemma Eterm_one (u : ℝ) : Eterm 1 u = Real.exp (5 * u / 2) * T 1 u := by
  simp only [Eterm]
  rw [show (1 / 2 + 2 * ((1 : ℕ) : ℝ)) * u = 5 * u / 2 by push_cast; ring]

/--
@isnad1 id=eq.0h1v.s5.21cd2d95509f from=translated src=- shape=7e8f3a3e vocab=6b08ae25
-/
lemma Eterm_two (u : ℝ) : Eterm 2 u = Real.exp (9 * u / 2) * T 2 u := by
  simp only [Eterm]
  rw [show (1 / 2 + 2 * ((2 : ℕ) : ℝ)) * u = 9 * u / 2 by push_cast; ring]

/--
@isnad1 id=eq.0h0v.s2.cadf7aa1e1ef from=translated src=- shape=b514ad24 vocab=3f98d719
-/
lemma Phi_eq_G : Phi = G c0 := by
  funext u
  rw [Phi_eq_T, G]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0]
  norm_num [Eterm_one, Eterm_two]
  ring

/-! ### The derivative chain -/

/--
@isnad1 id=hasderiv.0h1v.s5.4d3841617d87 from=translated src=- shape=8196f6d0 vocab=00c552cb
-/
lemma hasDerivAt_G0 (u : ℝ) : HasDerivAt (G c0) (G c1 u) u :=
  hasDerivAt_G c0 (by norm_num [c0]) u
/--
@isnad1 id=hasderiv.0h1v.s5.522a583839f1 from=translated src=- shape=8196f6d0 vocab=e8176d7c
-/
lemma hasDerivAt_G1 (u : ℝ) : HasDerivAt (G c1) (G c2 u) u :=
  hasDerivAt_G c1 (by norm_num [c1, c0, stp, shf]) u
/--
@isnad1 id=hasderiv.0h1v.s5.6195b3381cb7 from=translated src=- shape=8196f6d0 vocab=1486e6e8
-/
lemma hasDerivAt_G2 (u : ℝ) : HasDerivAt (G c2) (G c3 u) u :=
  hasDerivAt_G c2 (by norm_num [c2, c1, c0, stp, shf]) u
/--
@isnad1 id=hasderiv.0h1v.s5.d178d9cef3cb from=translated src=- shape=8196f6d0 vocab=6556358a
-/
lemma hasDerivAt_G3 (u : ℝ) : HasDerivAt (G c3) (G c4 u) u :=
  hasDerivAt_G c3 (by norm_num [c3, c2, c1, c0, stp, shf]) u
/--
@isnad1 id=hasderiv.0h1v.s5.a7cc1d65a715 from=translated src=- shape=8196f6d0 vocab=ed2c91cb
-/
lemma hasDerivAt_G4 (u : ℝ) : HasDerivAt (G c4) (G c5 u) u :=
  hasDerivAt_G c4 (by norm_num [c4, c3, c2, c1, c0, stp, shf]) u
/--
@isnad1 id=hasderiv.0h1v.s5.189924ea8d33 from=translated src=- shape=8196f6d0 vocab=70b0f73a
-/
lemma hasDerivAt_G5 (u : ℝ) : HasDerivAt (G c5) (G c6 u) u :=
  hasDerivAt_G c5 (by norm_num [c5, c4, c3, c2, c1, c0, stp, shf]) u
/--
@isnad1 id=hasderiv.0h1v.s5.da6c56397385 from=translated src=- shape=8196f6d0 vocab=966e368d
-/
lemma hasDerivAt_G6 (u : ℝ) : HasDerivAt (G c6) (G c7 u) u :=
  hasDerivAt_G c6 (by norm_num [c6, c5, c4, c3, c2, c1, c0, stp, shf]) u
/--
@isnad1 id=hasderiv.0h1v.s5.de62657f4720 from=translated src=- shape=8196f6d0 vocab=c42637c8
-/
lemma hasDerivAt_G7 (u : ℝ) : HasDerivAt (G c7) (G c8 u) u :=
  hasDerivAt_G c7 (by norm_num [c7, c6, c5, c4, c3, c2, c1, c0, stp, shf]) u
/--
@isnad1 id=hasderiv.0h1v.s5.410618d5372e from=translated src=- shape=8196f6d0 vocab=84579ac1
-/
lemma hasDerivAt_G8 (u : ℝ) : HasDerivAt (G c8) (G c9 u) u :=
  hasDerivAt_G c8 (by norm_num [c8, c7, c6, c5, c4, c3, c2, c1, c0, stp, shf]) u
/--
@isnad1 id=hasderiv.0h1v.s5.2c9476ef03fa from=translated src=- shape=8196f6d0 vocab=7be99e64
-/
lemma hasDerivAt_G9 (u : ℝ) : HasDerivAt (G c9) (G c10 u) u :=
  hasDerivAt_G c9 (by norm_num [c9, c8, c7, c6, c5, c4, c3, c2, c1, c0, stp, shf]) u

/-! ### `iteratedDeriv` -/

/--
@isnad1 id=eq.2h3v.s6.0cd39c8e1237 from=translated src=- shape=c0df8dd2 vocab=9e209479
-/
lemma iter_step {f g : ℝ → ℝ} {m : ℕ} (h : iteratedDeriv m Phi = f)
    (hd : ∀ u, HasDerivAt f (g u) u) : iteratedDeriv (m + 1) Phi = g := by
  rw [iteratedDeriv_succ, h]
  funext u
  exact (hd u).deriv

/--
@isnad1 id=eq.0h0v.s4.c189224005bf from=translated src=- shape=3fb171c6 vocab=d52c96ec
-/
lemma iter0 : iteratedDeriv 0 Phi = G c0 := by rw [iteratedDeriv_zero]; exact Phi_eq_G
/--
@isnad1 id=eq.0h0v.s4.c2d5146ae36c from=translated src=- shape=3fb171c6 vocab=38e449dd
-/
lemma iter1 : iteratedDeriv 1 Phi = G c1 := iter_step iter0 hasDerivAt_G0
/--
@isnad1 id=eq.0h0v.s4.12ec3fbb5bb1 from=translated src=- shape=3fb171c6 vocab=990f6d63
-/
lemma iter2 : iteratedDeriv 2 Phi = G c2 := iter_step iter1 hasDerivAt_G1
/--
@isnad1 id=eq.0h0v.s4.76f6e55360e2 from=translated src=- shape=3fb171c6 vocab=7bba22e6
-/
lemma iter3 : iteratedDeriv 3 Phi = G c3 := iter_step iter2 hasDerivAt_G2
/--
@isnad1 id=eq.0h0v.s4.f57a4407498f from=translated src=- shape=3fb171c6 vocab=292067a7
-/
lemma iter4 : iteratedDeriv 4 Phi = G c4 := iter_step iter3 hasDerivAt_G3
/--
@isnad1 id=eq.0h0v.s4.0e93349ba205 from=translated src=- shape=3fb171c6 vocab=dff42637
-/
lemma iter5 : iteratedDeriv 5 Phi = G c5 := iter_step iter4 hasDerivAt_G4
/--
@isnad1 id=eq.0h0v.s4.2e35da0f32fa from=translated src=- shape=3fb171c6 vocab=08727774
-/
lemma iter6 : iteratedDeriv 6 Phi = G c6 := iter_step iter5 hasDerivAt_G5
/--
@isnad1 id=eq.0h0v.s4.76e61afb13a4 from=translated src=- shape=3fb171c6 vocab=d49f67f7
-/
lemma iter7 : iteratedDeriv 7 Phi = G c7 := iter_step iter6 hasDerivAt_G6
/--
@isnad1 id=eq.0h0v.s4.82cf37985599 from=translated src=- shape=3fb171c6 vocab=957d7d3a
-/
lemma iter8 : iteratedDeriv 8 Phi = G c8 := iter_step iter7 hasDerivAt_G7
/--
@isnad1 id=eq.0h0v.s4.42cd95940e47 from=translated src=- shape=3fb171c6 vocab=315176a3
-/
lemma iter9 : iteratedDeriv 9 Phi = G c9 := iter_step iter8 hasDerivAt_G8
/--
@isnad1 id=eq.0h0v.s4.c0355bc3e196 from=translated src=- shape=3fb171c6 vocab=9e0ba459
-/
lemma iter10 : iteratedDeriv 10 Phi = G c10 := iter_step iter9 hasDerivAt_G9

/-! ### Parity:  `Φ` is even, hence `Φ⁽⁹⁾` is odd -/

/--
@isnad1 id=eq.2h4v.s6.96d5465a3386 from=translated src=- shape=b75e4ff6 vocab=499dc39c
-/
lemma parity_step {f g : ℝ → ℝ} {s : ℝ} (hf : ∀ u, f (-u) = s * f u)
    (hd : ∀ u, HasDerivAt f (g u) u) : ∀ u, g (-u) = (-s) * g u := by
  intro u
  have h1 : HasDerivAt (fun v : ℝ => f (-v)) (-(g (-u))) u := by
    have h := (hd (-u)).comp u (hasDerivAt_neg_self u)
    have heq : -(g (-u)) = g (-u) * (-1) := by ring
    rw [heq]
    exact h
  have hfun : (fun v : ℝ => f (-v)) = fun v : ℝ => s * f v := funext hf
  rw [hfun] at h1
  have h2 : HasDerivAt (fun v : ℝ => s * f v) (s * g u) u := (hd u).const_mul s
  have h3 := h1.unique h2
  linarith

/--
@isnad1 id=eq.0h1v.s4.533fa0283006 from=translated src=- shape=a4099341 vocab=125dcf32
-/
lemma par0 : ∀ u, G c0 (-u) = (1 : ℝ) * G c0 u := by
  intro u; rw [← Phi_eq_G]; simpa using Phi_even u
/--
@isnad1 id=eq.0h1v.s4.4c87571f84af from=translated src=- shape=58414838 vocab=31bda11d
-/
lemma par1 : ∀ u, G c1 (-u) = (-1 : ℝ) * G c1 u := by
  intro u; have := parity_step par0 hasDerivAt_G0 u; linarith
/--
@isnad1 id=eq.0h1v.s4.806071b48df7 from=translated src=- shape=a4099341 vocab=72c78f41
-/
lemma par2 : ∀ u, G c2 (-u) = (1 : ℝ) * G c2 u := by
  intro u; have := parity_step par1 hasDerivAt_G1 u; linarith
/--
@isnad1 id=eq.0h1v.s4.022ca015786c from=translated src=- shape=58414838 vocab=0f20e7eb
-/
lemma par3 : ∀ u, G c3 (-u) = (-1 : ℝ) * G c3 u := by
  intro u; have := parity_step par2 hasDerivAt_G2 u; linarith
/--
@isnad1 id=eq.0h1v.s4.ea53b8977f56 from=translated src=- shape=a4099341 vocab=8aefcd6e
-/
lemma par4 : ∀ u, G c4 (-u) = (1 : ℝ) * G c4 u := by
  intro u; have := parity_step par3 hasDerivAt_G3 u; linarith
/--
@isnad1 id=eq.0h1v.s4.f8270b75ab02 from=translated src=- shape=58414838 vocab=1f57f9b3
-/
lemma par5 : ∀ u, G c5 (-u) = (-1 : ℝ) * G c5 u := by
  intro u; have := parity_step par4 hasDerivAt_G4 u; linarith
/--
@isnad1 id=eq.0h1v.s4.d52fc0b83a84 from=translated src=- shape=a4099341 vocab=962fa680
-/
lemma par6 : ∀ u, G c6 (-u) = (1 : ℝ) * G c6 u := by
  intro u; have := parity_step par5 hasDerivAt_G5 u; linarith
/--
@isnad1 id=eq.0h1v.s4.d125bbd7970e from=translated src=- shape=58414838 vocab=541bd657
-/
lemma par7 : ∀ u, G c7 (-u) = (-1 : ℝ) * G c7 u := by
  intro u; have := parity_step par6 hasDerivAt_G6 u; linarith
/--
@isnad1 id=eq.0h1v.s4.fe8871e5c24f from=translated src=- shape=a4099341 vocab=717b198e
-/
lemma par8 : ∀ u, G c8 (-u) = (1 : ℝ) * G c8 u := by
  intro u; have := parity_step par7 hasDerivAt_G7 u; linarith
/--
@isnad1 id=eq.0h1v.s4.5a247ba3da2d from=translated src=- shape=58414838 vocab=6ccb64d4
-/
lemma par9 : ∀ u, G c9 (-u) = (-1 : ℝ) * G c9 u := by
  intro u; have := parity_step par8 hasDerivAt_G8 u; linarith

/-- **`Φ⁽⁹⁾(0) = 0`** — the odd-order derivatives of an even function vanish at the origin.
@isnad1 id=eq.0h0v.s4.aa3f61209d20 from=translated src=- shape=904d2e91 vocab=a5b58093
-/
theorem G_c9_zero : G c9 0 = 0 := by
  have h := par9 0
  rw [neg_zero] at h
  linarith

/-! ### Rewriting `G a 0` as a single series over `n` -/

/-- `poly a X = ∑_{i<14} a i X^i`.-/
noncomputable def poly (a : ℕ → ℝ) (X : ℝ) : ℝ := ∑ i ∈ Finset.range 14, a i * X ^ i

/-- The `n`-th term of `Φ⁽ᵐ⁾(0)`: `e^{−πn²} · P_m(πn²)`.-/
noncomputable def V (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  poly a (π * (n : ℝ) ^ 2) * Real.exp (-(π * (n : ℝ) ^ 2))

/--
@isnad1 id=eq.0h2v.s6.b9280d1b7100 from=translated src=- shape=af966f2e vocab=f4b869f8
-/
lemma thTerm_at_zero (i n : ℕ) :
    thTerm i n 0 = (π * (n : ℝ) ^ 2) ^ i * Real.exp (-(π * (n : ℝ) ^ 2)) := by
  simp [thTerm]

/--
@isnad1 id=eq.0h2v.s5.c0e563c687e4 from=translated src=- shape=1068a147 vocab=eb48b723
-/
lemma V_eq_sum (a : ℕ → ℝ) (n : ℕ) :
    V a n = ∑ i ∈ Finset.range 14, a i * thTerm i n 0 := by
  simp only [V, poly, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => by rw [thTerm_at_zero]; ring)

/--
@isnad1 id=summable.0h1v.s5.6d50ca66d99e from=translated src=- shape=995d1c99 vocab=e040fbd8
-/
lemma summable_V (a : ℕ → ℝ) : Summable (fun n : ℕ => V a (n + 1)) := by
  have : (fun n : ℕ => V a (n + 1))
      = fun n : ℕ => ∑ i ∈ Finset.range 14, a i * thTerm i (n + 1) 0 :=
    funext fun n => V_eq_sum a (n + 1)
  rw [this]
  exact summable_sum (fun i _ => (summable_thTerm_succ i 0).mul_left _)

/--
@isnad1 id=eq.0h1v.s5.2c702ad84a26 from=translated src=- shape=048af1e0 vocab=ad6458ac
-/
lemma G_at_zero (a : ℕ → ℝ) : G a 0 = ∑' n : ℕ, V a (n + 1) := by
  have hsum : ∀ i ∈ Finset.range 14, Summable (fun n : ℕ => a i * thTerm i (n + 1) 0) :=
    fun i _ => (summable_thTerm_succ i 0).mul_left _
  have step1 : ∀ i ∈ Finset.range 14,
      a i * Eterm i 0 = ∑' n : ℕ, a i * thTerm i (n + 1) 0 := by
    intro i _
    rw [Eterm_zero, T, tsum_mul_left]
  rw [G, Finset.sum_congr rfl step1, ← Summable.tsum_finsetSum hsum]
  exact tsum_congr (fun n => (V_eq_sum a (n + 1)).symm)

/--
@isnad1 id=eq.0h1v.s7.852cd34b80f0 from=translated src=- shape=c5c292ca vocab=820a2c93
-/
lemma V_split (a : ℕ → ℝ) :
    ∑' n : ℕ, V a (n + 1)
      = (V a 1 + V a 2 + V a 3 + V a 4 + V a 5) + ∑' n : ℕ, V a (n + 6) := by
  have h := (summable_V a).sum_add_tsum_nat_add 5
  rw [← h]
  congr 1
  simp [Finset.sum_range_succ]

/-! ### The two polynomials we need, written out -/

/-- `P₈(X) = 1024X¹⁰ − 48640X⁹ + 862976X⁸ − 7284480X⁷ + 30936024X⁶ − 64558956X⁵
    + 60281251X⁴ − 20628202X³ + (107030865/64)X² − (1171875/128)X`.
@isnad1 id=eq.0h1v.s8.3f03a7d2a4b4 from=translated src=- shape=12190b39 vocab=2d9b3ca0
-/
lemma poly_c8 (X : ℝ) : poly c8 X =
    -(1171875 / 128) * X + (107030865 / 64) * X ^ 2 - 20628202 * X ^ 3 + 60281251 * X ^ 4
      - 64558956 * X ^ 5 + 30936024 * X ^ 6 - 7284480 * X ^ 7 + 862976 * X ^ 8
      - 48640 * X ^ 9 + 1024 * X ^ 10 := by
  simp only [poly, Finset.sum_range_succ, Finset.sum_range_zero,
    c8, c7, c6, c5, c4, c3, c2, c1, c0, stp, shf]
  norm_num
  ring

/-- `P₁₀(X)`, degree 12.
@isnad1 id=eq.0h1v.s9.7132339370af from=translated src=- shape=dae61371 vocab=7ba37cb2
-/
lemma poly_c10 (X : ℝ) : poly c10 X =
    -(29296875 / 512) * X + (8702312565 / 256) * X ^ 2 - (14533920247 / 16) * X ^ 3
      + (79693693981 / 16) * X ^ 4 - 9490825245 * X ^ 5 + 8044590730 * X ^ 6
      - 3460343040 * X ^ 7 + 810327072 * X ^ 8 - 106193280 * X ^ 9 + 7676160 * X ^ 10
      - 282624 * X ^ 11 + 4096 * X ^ 12 := by
  simp only [poly, Finset.sum_range_succ, Finset.sum_range_zero,
    c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, c0, stp, shf]
  norm_num
  ring

/--
@isnad1 id=eq.0h0v.s3.fd7fc0a8853b from=translated src=- shape=1ac31801 vocab=eb3ccefe
-/
lemma c8_13 : c8 13 = 0 := by
  norm_num [c8, c7, c6, c5, c4, c3, c2, c1, c0, stp, shf]

/--
@isnad1 id=eq.0h0v.s3.19077ccb4e08 from=translated src=- shape=1ac31801 vocab=0331cc84
-/
lemma c10_13 : c10 13 = 0 := by
  norm_num [c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, c0, stp, shf]

/--
@isnad1 id=le.0h0v.s4.9f5efdd2ad36 from=translated src=- shape=503b97e4 vocab=90e704e1
-/
lemma sumabs_c8 : ∑ i ∈ Finset.range 14, |c8 i| ≤ 27843518766 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    c8, c7, c6, c5, c4, c3, c2, c1, c0, stp, shf]
  norm_num

/--
@isnad1 id=le.0h0v.s4.ee98105c7ea9 from=translated src=- shape=503b97e4 vocab=b943bb13
-/
lemma sumabs_c10 : ∑ i ∈ Finset.range 14, |c10 i| ≤ 27843518766 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    c10, c9, c8, c7, c6, c5, c4, c3, c2, c1, c0, stp, shf]
  norm_num

/-! ### Numerical bounds on `π` and its powers -/

/--
@isnad1 id=lt.0h0v.s3.6f4e6b54a0f0 from=translated src=- shape=a948b8aa vocab=489aaca7
-/
lemma pi_lo : (3.14159265358979 : ℝ) < π := lt_trans (by norm_num) Real.pi_gt_d20
/--
@isnad1 id=lt.0h0v.s3.fbfc97656e92 from=translated src=- shape=425298da vocab=489aaca7
-/
lemma pi_hi : π < 3.1415926535898 := lt_trans Real.pi_lt_d20 (by norm_num)

/--
@isnad1 id=le.0h1v.s5.8088d9a1c2fb from=translated src=- shape=b5620330 vocab=ffd43dcf
-/
lemma piLow (i : ℕ) : (3.14159265358979 : ℝ) ^ i ≤ π ^ i :=
  pow_le_pow_left₀ (by norm_num) pi_lo.le i
/--
@isnad1 id=le.0h1v.s5.91b5a419587f from=translated src=- shape=c42b012c vocab=ffd43dcf
-/
lemma piHigh (i : ℕ) : π ^ i ≤ (3.1415926535898 : ℝ) ^ i :=
  pow_le_pow_left₀ Real.pi_pos.le pi_hi.le i

/--
@isnad1 id=lt.0h0v.s4.71bb9f1a6cfc from=translated src=- shape=b5132205 vocab=60ab1fb8
-/
lemma piL2 : (9.869604401089338 : ℝ) < π ^ 2 := lt_of_lt_of_le (by norm_num) (piLow 2)
/--
@isnad1 id=lt.0h0v.s4.11533211a54a from=translated src=- shape=67906b3e vocab=60ab1fb8
-/
lemma piH2 : π ^ 2 < 9.869604401089402 := lt_of_le_of_lt (piHigh 2) (by norm_num)
/--
@isnad1 id=lt.0h0v.s4.15c330c4be4a from=translated src=- shape=b5132205 vocab=60ab1fb8
-/
lemma piL3 : (31.00627668029972 : ℝ) < π ^ 3 := lt_of_lt_of_le (by norm_num) (piLow 3)
/--
@isnad1 id=lt.0h0v.s4.bc900069e3b1 from=translated src=- shape=67906b3e vocab=60ab1fb8
-/
lemma piH3 : π ^ 3 < 31.00627668030003 := lt_of_le_of_lt (piHigh 3) (by norm_num)
/--
@isnad1 id=lt.0h0v.s4.3ba25714df74 from=translated src=- shape=b5132205 vocab=60ab1fb8
-/
lemma piL4 : (97.40909103400203 : ℝ) < π ^ 4 := lt_of_lt_of_le (by norm_num) (piLow 4)
/--
@isnad1 id=lt.0h0v.s4.b86b91fe019a from=translated src=- shape=67906b3e vocab=60ab1fb8
-/
lemma piH4 : π ^ 4 < 97.40909103400328 := lt_of_le_of_lt (piHigh 4) (by norm_num)
/--
@isnad1 id=lt.0h0v.s4.cf6a2911ed66 from=translated src=- shape=b5132205 vocab=60ab1fb8
-/
lemma piL5 : (306.0196847852798 : ℝ) < π ^ 5 := lt_of_lt_of_le (by norm_num) (piLow 5)
/--
@isnad1 id=lt.0h0v.s4.7aae65a486c5 from=translated src=- shape=67906b3e vocab=60ab1fb8
-/
lemma piH5 : π ^ 5 < 306.0196847852848 := lt_of_le_of_lt (piHigh 5) (by norm_num)
/--
@isnad1 id=lt.0h0v.s4.bddd25a4c670 from=translated src=- shape=b5132205 vocab=60ab1fb8
-/
lemma piL6 : (961.3891935752984 : ℝ) < π ^ 6 := lt_of_lt_of_le (by norm_num) (piLow 6)
/--
@isnad1 id=lt.0h0v.s4.bca4b00f4c4d from=translated src=- shape=67906b3e vocab=60ab1fb8
-/
lemma piH6 : π ^ 6 < 961.3891935753169 := lt_of_le_of_lt (piHigh 6) (by norm_num)
/--
@isnad1 id=lt.0h0v.s4.12ead4eaf326 from=translated src=- shape=b5132205 vocab=60ab1fb8
-/
lemma piL7 : (3020.29322777677 : ℝ) < π ^ 7 := lt_of_lt_of_le (by norm_num) (piLow 7)
/--
@isnad1 id=lt.0h0v.s4.5fc641e2a8b6 from=translated src=- shape=67906b3e vocab=60ab1fb8
-/
lemma piH7 : π ^ 7 < 3020.293227776838 := lt_of_le_of_lt (piHigh 7) (by norm_num)
/--
@isnad1 id=lt.0h0v.s4.5849579d5965 from=translated src=- shape=b5132205 vocab=60ab1fb8
-/
lemma piL8 : (9488.531016070495 : ℝ) < π ^ 8 := lt_of_lt_of_le (by norm_num) (piLow 8)
/--
@isnad1 id=lt.0h0v.s4.e857b3becb82 from=translated src=- shape=67906b3e vocab=60ab1fb8
-/
lemma piH8 : π ^ 8 < 9488.531016070738 := lt_of_le_of_lt (piHigh 8) (by norm_num)
/--
@isnad1 id=lt.0h0v.s4.5a58f27f8e5e from=translated src=- shape=b5132205 vocab=60ab1fb8
-/
lemma piL9 : (29809.09933344593 : ℝ) < π ^ 9 := lt_of_lt_of_le (by norm_num) (piLow 9)
/--
@isnad1 id=lt.0h0v.s4.c1653373fbfe from=translated src=- shape=67906b3e vocab=60ab1fb8
-/
lemma piH9 : π ^ 9 < 29809.09933344679 := lt_of_le_of_lt (piHigh 9) (by norm_num)
/--
@isnad1 id=lt.0h0v.s4.146ad7899a0a from=translated src=- shape=b5132205 vocab=60ab1fb8
-/
lemma piL10 : (93648.04747608205 : ℝ) < π ^ 10 := lt_of_lt_of_le (by norm_num) (piLow 10)
/--
@isnad1 id=lt.0h0v.s4.e9d7cea155f8 from=translated src=- shape=67906b3e vocab=60ab1fb8
-/
lemma piH10 : π ^ 10 < 93648.04747608504 := lt_of_le_of_lt (piHigh 10) (by norm_num)
/--
@isnad1 id=lt.0h0v.s4.116599867729 from=translated src=- shape=b5132205 vocab=60ab1fb8
-/
lemma piL11 : (294204.0179738872 : ℝ) < π ^ 11 := lt_of_lt_of_le (by norm_num) (piLow 11)
/--
@isnad1 id=lt.0h0v.s4.fc1644300098 from=translated src=- shape=67906b3e vocab=60ab1fb8
-/
lemma piH11 : π ^ 11 < 294204.0179738976 := lt_of_le_of_lt (piHigh 11) (by norm_num)
/--
@isnad1 id=lt.0h0v.s4.5f1a2500aa85 from=translated src=- shape=b5132205 vocab=60ab1fb8
-/
lemma piL12 : (924269.1815233627 : ℝ) < π ^ 12 := lt_of_lt_of_le (by norm_num) (piLow 12)
/--
@isnad1 id=lt.0h0v.s4.09711e71db90 from=translated src=- shape=67906b3e vocab=60ab1fb8
-/
lemma piH12 : π ^ 12 < 924269.1815233981 := lt_of_le_of_lt (piHigh 12) (by norm_num)

/-! ### Numerical bounds on `e^{−π}` -/

/--
@isnad1 id=eq.0h0v.s5.40910f90ca40 from=translated src=- shape=8911115d vocab=3e41f8b2
-/
lemma exp_three_eq : Real.exp 3 = Real.exp 1 ^ 3 := by
  rw [← Real.exp_nat_mul]; norm_num

/--
@isnad1 id=lt.0h0v.s4.ee2faaadf8f9 from=translated src=- shape=8905eb1d vocab=ced2a307
-/
lemma exp_three_lb : (20.0855367 : ℝ) < Real.exp 3 := by
  rw [exp_three_eq]
  calc (20.0855367 : ℝ) < (2.7182818283 : ℝ) ^ 3 := by norm_num
    _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 3

/--
@isnad1 id=lt.0h0v.s4.9eef4d943b4b from=translated src=- shape=339e478a vocab=ced2a307
-/
lemma exp_three_ub : Real.exp 3 < 20.085537 := by
  rw [exp_three_eq]
  calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    _ < 20.085537 := by norm_num

/--
@isnad1 id=lt.0h0v.s4.00167c47f785 from=translated src=- shape=635c684c vocab=59eaf7ff
-/
lemma exp_pimm_lb : (1.14159265358979 : ℝ) < Real.exp (π - 3) := by
  have h := Real.add_one_le_exp (π - 3)
  have := pi_lo
  linarith

/--
@isnad1 id=lt.0h0v.s4.a502a8203e04 from=translated src=- shape=7dbff845 vocab=59eaf7ff
-/
lemma exp_pimm_ub : Real.exp (π - 3) < 1.16495 := by
  have h := Real.add_one_le_exp (-(π - 3))
  rw [Real.exp_neg] at h
  have hpos : 0 < Real.exp (π - 3) := Real.exp_pos _
  have hmul : (1 - (π - 3)) * Real.exp (π - 3) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h hpos.le
    rw [inv_mul_cancel₀ hpos.ne'] at this
    linarith
  have hlow : (0.8584073464102 : ℝ) ≤ 1 - (π - 3) := by have := pi_hi; linarith
  nlinarith [hpos, hmul, hlow]

/--
@isnad1 id=eq.0h0v.s5.d2bfa2ccc73e from=translated src=- shape=f45ea84b vocab=2f7042e7
-/
lemma exp_pi_eq : Real.exp π = Real.exp 3 * Real.exp (π - 3) := by
  rw [← Real.exp_add]; ring_nf

/--
@isnad1 id=lt.0h0v.s3.cc04dfc48484 from=translated src=- shape=1df70b40 vocab=ad21434e
-/
lemma exp_pi_lb : (22.9294 : ℝ) < Real.exp π := by
  rw [exp_pi_eq]
  nlinarith [exp_three_lb, exp_pimm_lb, Real.exp_pos 3, Real.exp_pos (π - 3)]

/--
@isnad1 id=lt.0h0v.s3.5bbdfb2dbecd from=translated src=- shape=f856419b vocab=ad21434e
-/
lemma exp_pi_ub : Real.exp π < 23.3987 := by
  rw [exp_pi_eq]
  nlinarith [exp_three_ub, exp_pimm_ub, Real.exp_pos 3, Real.exp_pos (π - 3)]

/-- `e^{−π} ≥ 0.0427374`.
@isnad1 id=le.0h0v.s4.6a915c5ab7ad from=translated src=- shape=9e6a1a0f vocab=2078ed18
-/
lemma Emin : (0.0427374 : ℝ) ≤ Real.exp (-π) := by
  have hpos : 0 < Real.exp π := Real.exp_pos _
  have h := exp_pi_ub
  rw [Real.exp_neg, le_inv_comm₀ (by norm_num) hpos]
  norm_num
  linarith

/-- `e^{−π} ≤ 0.0436122`.
@isnad1 id=le.0h0v.s4.f0f2eb4a2b2e from=translated src=- shape=888253f9 vocab=2078ed18
-/
lemma Emax : Real.exp (-π) ≤ 0.0436122 := by
  rw [Real.exp_neg]
  have h := exp_pi_lb
  have hpos : 0 < Real.exp π := Real.exp_pos _
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

/--
@isnad1 id=lt.0h0v.s3.981328e90b62 from=translated src=- shape=1e353136 vocab=cb681a3b
-/
lemma Epos : (0 : ℝ) < Real.exp (-π) := Real.exp_pos _

/-! ### Values of `P₈` and `P₁₀` at `π, 4π, 9π, 16π`

Each of these is a purely linear consequence of the two-sided bounds on `π, π², …, π¹²`;
the cancellation is at most three decimal digits while the bounds carry fifteen. -/

/-- `P₈(π) ≈ 6.7152610·10⁷ > 0`.
@isnad1 id=le.0h0v.s3.530e0c62f722 from=translated src=- shape=7164367e vocab=908794a1
-/
lemma poly_c8_1 : (67152610 : ℝ) ≤ poly c8 π := by
  rw [poly_c8]
  linarith [pi_lo, pi_hi, piL2, piH2, piL3, piH3, piL4, piH4, piL5, piH5, piL6, piH6,
    piL7, piH7, piL8, piH8, piL9, piH9, piL10, piH10]

/-- `P₈(4π) ≈ −3.1449722·10¹¹ < 0` — this is the term that spoils naive `n = 1` dominance.
@isnad1 id=le.0h0v.s5.375aed94d13a from=translated src=- shape=6b150803 vocab=c261230e
-/
lemma poly_c8_2 : (-314497220000 : ℝ) ≤ poly c8 (π * 4) := by
  rw [poly_c8]
  linarith [pi_lo, pi_hi, piL2, piH2, piL3, piH3, piL4, piH4, piL5, piH5, piL6, piH6,
    piL7, piH7, piL8, piH8, piL9, piH9, piL10, piH10]

/--
@isnad1 id=le.0h0v.s4.55099e3f3907 from=translated src=- shape=4592c955 vocab=ce4ec24c
-/
lemma poly_c8_3 : (0 : ℝ) ≤ poly c8 (π * 9) := by
  rw [poly_c8]
  linarith [pi_lo, pi_hi, piL2, piH2, piL3, piH3, piL4, piH4, piL5, piH5, piL6, piH6,
    piL7, piH7, piL8, piH8, piL9, piH9, piL10, piH10]

/--
@isnad1 id=le.0h0v.s4.34a5499e8b29 from=translated src=- shape=4592c955 vocab=ce4ec24c
-/
lemma poly_c8_4 : (0 : ℝ) ≤ poly c8 (π * 16) := by
  rw [poly_c8]
  linarith [pi_lo, pi_hi, piL2, piH2, piL3, piH3, piL4, piH4, piL5, piH5, piL6, piH6,
    piL7, piH7, piL8, piH8, piL9, piH9, piL10, piH10]

/-- `P₁₀(π) ≈ −1.5150017·10⁹ < 0` — at `j = 5` the `n = 1` term is *negative*.
@isnad1 id=le.0h0v.s4.7cbf44788ebc from=translated src=- shape=1f444d87 vocab=b7cf14e7
-/
lemma poly_c10_1 : (-1515001800 : ℝ) ≤ poly c10 π := by
  rw [poly_c10]
  linarith [pi_lo, pi_hi, piL2, piH2, piL3, piH3, piL4, piH4, piL5, piH5, piL6, piH6,
    piL7, piH7, piL8, piH8, piL9, piH9, piL10, piH10, piL11, piH11, piL12, piH12]

/-- `P₁₀(4π) ≈ 2.0309179·10¹⁴ > 0` — the `n = 2` term is what makes `Φ⁽¹⁰⁾(0)` positive.
@isnad1 id=le.0h0v.s4.4daea21119dd from=translated src=- shape=4592c955 vocab=166dee72
-/
lemma poly_c10_2 : (203091791000000 : ℝ) ≤ poly c10 (π * 4) := by
  rw [poly_c10]
  linarith [pi_lo, pi_hi, piL2, piH2, piL3, piH3, piL4, piH4, piL5, piH5, piL6, piH6,
    piL7, piH7, piL8, piH8, piL9, piH9, piL10, piH10, piL11, piH11, piL12, piH12]

/--
@isnad1 id=le.0h0v.s4.570993151027 from=translated src=- shape=4592c955 vocab=166dee72
-/
lemma poly_c10_3 : (0 : ℝ) ≤ poly c10 (π * 9) := by
  rw [poly_c10]
  linarith [pi_lo, pi_hi, piL2, piH2, piL3, piH3, piL4, piH4, piL5, piH5, piL6, piH6,
    piL7, piH7, piL8, piH8, piL9, piH9, piL10, piH10, piL11, piH11, piL12, piH12]

/--
@isnad1 id=le.0h0v.s4.69849b922647 from=translated src=- shape=4592c955 vocab=166dee72
-/
lemma poly_c10_4 : (0 : ℝ) ≤ poly c10 (π * 16) := by
  rw [poly_c10]
  linarith [pi_lo, pi_hi, piL2, piH2, piL3, piH3, piL4, piH4, piL5, piH5, piL6, piH6,
    piL7, piH7, piL8, piH8, piL9, piH9, piL10, piH10, piL11, piH11, piL12, piH12]

/-! ### The crude envelope, used only for `n ≥ 5`

For `X ≥ 1` every `P_m` is dominated by `(∑ᵢ |aᵢ|) X¹²`.  That is far too lossy at
`n ≤ 4` — which is exactly the phenomenon Coffey and Csordás record — but from `n = 5`
on there are eighteen orders of magnitude of slack. -/

/--
@isnad1 id=le.3h3v.s6.334256f11be5 from=translated src=- shape=a7e736f7 vocab=c92d8b5c
-/
lemma poly_abs_le (a : ℕ → ℝ) (h13 : a 13 = 0) {A : ℝ}
    (hA : ∑ i ∈ Finset.range 14, |a i| ≤ A) {X : ℝ} (hX : 1 ≤ X) :
    |poly a X| ≤ A * X ^ 12 := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have h1 : |poly a X| ≤ ∑ i ∈ Finset.range 14, |a i| * X ^ 12 := by
    simp only [poly]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun i hi => ?_))
    rw [abs_mul, abs_pow, abs_of_nonneg hX0]
    by_cases h : i = 13
    · subst h; simp [h13]
    · have hi12 : i ≤ 12 := by have := Finset.mem_range.mp hi; omega
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX hi12) (abs_nonneg _)
  calc |poly a X| ≤ ∑ i ∈ Finset.range 14, |a i| * X ^ 12 := h1
    _ = (∑ i ∈ Finset.range 14, |a i|) * X ^ 12 := by rw [Finset.sum_mul]
    _ ≤ A * X ^ 12 := mul_le_mul_of_nonneg_right hA (by positivity)

/--
@isnad1 id=eq.0h1v.s6.e7e3ad7a61c9 from=translated src=- shape=4c738b7e vocab=f9bb8d9b
-/
lemma exp_neg_pi_sq (n : ℕ) :
    Real.exp (-(π * (n : ℝ) ^ 2)) = (Real.exp (-π)) ^ (n ^ 2) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/--
@isnad1 id=le.3h2v.s7.a39724184ba7 from=translated src=- shape=16adbd02 vocab=3eed8a5e
-/
lemma V_abs_le (a : ℕ → ℝ) (h13 : a 13 = 0)
    (hA : ∑ i ∈ Finset.range 14, |a i| ≤ 27843518766) {n : ℕ} (hn : 1 ≤ n) :
    |V a n| ≤ 27843518766 * (π * (n : ℝ) ^ 2) ^ 12 * (Real.exp (-π)) ^ (n ^ 2) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hX : (1 : ℝ) ≤ π * (n : ℝ) ^ 2 := by nlinarith [pi_lo]
  have hp := poly_abs_le a h13 hA hX
  rw [V, abs_mul, abs_of_nonneg (Real.exp_pos _).le, exp_neg_pi_sq]
  exact mul_le_mul_of_nonneg_right hp (by positivity)

/--
@isnad1 id=le.0h0v.s4.813dc9fe784e from=translated src=- shape=339e478a vocab=8b6aaff6
-/
lemma exp_six_ub : Real.exp 6 ≤ 403.4287937 := by
  have h : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h]
  calc Real.exp 1 ^ 6 ≤ (2.7182818286 : ℝ) ^ 6 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 6
    _ ≤ 403.4287937 := by norm_num

/-- `n²⁴ ≤ 4²⁴ (e⁶)ⁿ`, from `x ≤ eˣ` at `x = n/4` raised to the 24th power.
@isnad1 id=le.0h1v.s5.2069b9b087ef from=translated src=- shape=aba922b5 vocab=f8f3d287
-/
lemma pow24_le (n : ℕ) : ((n : ℝ)) ^ 24 ≤ 281474976710656 * (Real.exp 6) ^ n := by
  have h1 : ((n : ℝ) / 4) ≤ Real.exp ((n : ℝ) / 4) := by
    have := Real.add_one_le_exp ((n : ℝ) / 4); linarith
  have h2 : ((n : ℝ) / 4) ^ 24 ≤ (Real.exp ((n : ℝ) / 4)) ^ 24 :=
    pow_le_pow_left₀ (by positivity) h1 24
  have h3 : (Real.exp ((n : ℝ) / 4)) ^ 24 = (Real.exp 6) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h3] at h2
  have h4 : ((n : ℝ) / 4) ^ 24 = (n : ℝ) ^ 24 / 281474976710656 := by
    rw [div_pow]; norm_num
  rw [h4] at h2
  linarith

/--
@isnad1 id=le.0h0v.s3.f33e86b2a890 from=translated src=- shape=dab69e96 vocab=5adf480a
-/
lemma Emax_le_one : Real.exp (-π) ≤ 1 := by have := Emax; linarith

/--
@isnad1 id=le.0h0v.s5.9926afeec9c6 from=translated src=- shape=b3dea1f7 vocab=689e3bfb
-/
lemma E6_le : (Real.exp (-π)) ^ 6 ≤ 0.00000000688095 := by
  calc (Real.exp (-π)) ^ 6 ≤ (0.0436122 : ℝ) ^ 6 := pow_le_pow_left₀ Epos.le Emax 6
    _ ≤ 0.00000000688095 := by norm_num

/--
@isnad1 id=le.3h2v.s6.8c1969da5c88 from=translated src=- shape=78f24859 vocab=f4d01590
-/
lemma tail_term_le (a : ℕ → ℝ) (h13 : a 13 = 0)
    (hA : ∑ i ∈ Finset.range 14, |a i| ≤ 27843518766) {n : ℕ} (hn : 6 ≤ n) :
    |V a n| ≤ 7243740000000000000000000000000 * (0.00000277598 : ℝ) ^ n := by
  have h0 := V_abs_le a h13 hA (le_trans (by norm_num) hn)
  have hEn : (Real.exp (-π)) ^ (n ^ 2) ≤ (0.00000000688095 : ℝ) ^ n := by
    calc (Real.exp (-π)) ^ (n ^ 2) ≤ (Real.exp (-π)) ^ (6 * n) :=
          pow_le_pow_of_le_one Epos.le Emax_le_one (by nlinarith)
      _ = ((Real.exp (-π)) ^ 6) ^ n := by rw [pow_mul]
      _ ≤ (0.00000000688095 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) E6_le n
  have hinner : π ^ 12 * ((n : ℝ)) ^ 24
      ≤ 924269.1815233981 * (281474976710656 * (Real.exp 6) ^ n) :=
    mul_le_mul piH12.le (pow24_le n) (by positivity) (by norm_num)
  have hstep : (π * (n : ℝ) ^ 2) ^ 12 * (Real.exp (-π)) ^ (n ^ 2)
      ≤ 924269.1815233981 * (281474976710656 * (Real.exp 6) ^ n)
        * (0.00000000688095 : ℝ) ^ n := by
    have e1 : (π * (n : ℝ) ^ 2) ^ 12 = π ^ 12 * ((n : ℝ)) ^ 24 := by ring
    rw [e1]
    exact mul_le_mul hinner hEn (by positivity) (by positivity)
  have hrho : (Real.exp 6 * 0.00000000688095 : ℝ) ^ n ≤ (0.00000277598 : ℝ) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith [exp_six_ub]) n
  have hcollect : 924269.1815233981 * (281474976710656 * (Real.exp 6) ^ n)
        * (0.00000000688095 : ℝ) ^ n
      = (924269.1815233981 * 281474976710656) * (Real.exp 6 * 0.00000000688095) ^ n := by
    rw [mul_pow]; ring
  rw [hcollect] at hstep
  have hfinal : (π * (n : ℝ) ^ 2) ^ 12 * (Real.exp (-π)) ^ (n ^ 2)
      ≤ (924269.1815233981 * 281474976710656) * (0.00000277598 : ℝ) ^ n := by
    refine le_trans hstep ?_
    exact mul_le_mul_of_nonneg_left hrho (by norm_num)
  calc |V a n| ≤ 27843518766 * ((π * (n : ℝ) ^ 2) ^ 12 * (Real.exp (-π)) ^ (n ^ 2)) := by
        rw [← mul_assoc]; exact h0
    _ ≤ 27843518766 * ((924269.1815233981 * 281474976710656) * (0.00000277598 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hfinal (by norm_num)
    _ ≤ 7243740000000000000000000000000 * (0.00000277598 : ℝ) ^ n := by
        have hp : (0 : ℝ) ≤ (0.00000277598 : ℝ) ^ n := by positivity
        nlinarith [hp]

/--
@isnad1 id=le.2h1v.s6.1730673b91d0 from=translated src=- shape=0af7503b vocab=cf4386fd
-/
lemma tail_small (a : ℕ → ℝ) (h13 : a 13 = 0)
    (hA : ∑ i ∈ Finset.range 14, |a i| ≤ 27843518766) :
    |∑' n : ℕ, V a (n + 6)| ≤ 1 := by
  have hmaj : ∀ n : ℕ, |V a (n + 6)|
      ≤ 7243740000000000000000000000000 * (0.00000277598 : ℝ) ^ (n + 6) :=
    fun n => tail_term_le a h13 hA (by omega)
  have hgeo : Summable (fun n : ℕ => (0.00000277598 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hrw : (fun n : ℕ => 7243740000000000000000000000000 * (0.00000277598 : ℝ) ^ (n + 6))
      = fun n : ℕ => (7243740000000000000000000000000 * (0.00000277598 : ℝ) ^ 6)
          * (0.00000277598 : ℝ) ^ n := by
    funext n; rw [pow_add]; ring
  have hsumMaj : Summable
      (fun n : ℕ => 7243740000000000000000000000000 * (0.00000277598 : ℝ) ^ (n + 6)) := by
    rw [hrw]; exact hgeo.mul_left _
  have hsumAbs : Summable (fun n : ℕ => |V a (n + 6)|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hmaj hsumMaj
  have hnorm : |∑' n : ℕ, V a (n + 6)| ≤ ∑' n : ℕ, |V a (n + 6)| := by
    simpa [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun n : ℕ => V a (n + 6)) (by simpa [Real.norm_eq_abs] using hsumAbs)
  have hle : ∑' n : ℕ, |V a (n + 6)|
      ≤ ∑' n : ℕ, 7243740000000000000000000000000 * (0.00000277598 : ℝ) ^ (n + 6) :=
    Summable.tsum_le_tsum hmaj hsumAbs hsumMaj
  have hval : ∑' n : ℕ, 7243740000000000000000000000000 * (0.00000277598 : ℝ) ^ (n + 6)
      = (7243740000000000000000000000000 * (0.00000277598 : ℝ) ^ 6)
        * (1 - (0.00000277598 : ℝ))⁻¹ := by
    rw [hrw, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  have hnum : (7243740000000000000000000000000 * (0.00000277598 : ℝ) ^ 6)
      * (1 - (0.00000277598 : ℝ))⁻¹ ≤ 1 := by norm_num
  linarith [hnorm, hle, hval ▸ hle]

/--
@isnad1 id=le.2h1v.s6.f981dafce54f from=translated src=- shape=742b5c53 vocab=4165518b
-/
lemma V5_small (a : ℕ → ℝ) (h13 : a 13 = 0)
    (hA : ∑ i ∈ Finset.range 14, |a i| ≤ 27843518766) : |V a 5| ≤ 1 := by
  have h := V_abs_le a h13 hA (n := 5) (by norm_num)
  have h1 : (π * ((5 : ℕ) : ℝ) ^ 2) ^ 12 ≤ 55100000000000000000000 := by
    have e : (π * ((5 : ℕ) : ℝ) ^ 2) ^ 12 = π ^ 12 * 59604644775390625 := by
      push_cast; ring
    rw [e]
    nlinarith [piH12]
  have h2 : (Real.exp (-π)) ^ (5 ^ 2) ≤ (1 / 10 ^ 34 : ℝ) := by
    calc (Real.exp (-π)) ^ (5 ^ 2) ≤ (0.0436122 : ℝ) ^ (5 ^ 2) :=
          pow_le_pow_left₀ Epos.le Emax _
      _ ≤ (1 / 10 ^ 34 : ℝ) := by norm_num
  have s1 : (27843518766 : ℝ) * (π * ((5 : ℕ) : ℝ) ^ 2) ^ 12
      ≤ 27843518766 * 55100000000000000000000 :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  have s2 : (27843518766 : ℝ) * (π * ((5 : ℕ) : ℝ) ^ 2) ^ 12 * (Real.exp (-π)) ^ (5 ^ 2)
      ≤ (27843518766 * 55100000000000000000000 : ℝ) * (Real.exp (-π)) ^ (5 ^ 2) :=
    mul_le_mul_of_nonneg_right s1 (by positivity)
  have s3 : (27843518766 * 55100000000000000000000 : ℝ) * (Real.exp (-π)) ^ (5 ^ 2)
      ≤ (27843518766 * 55100000000000000000000 : ℝ) * (1 / 10 ^ 34 : ℝ) :=
    mul_le_mul_of_nonneg_left h2 (by norm_num)
  have s4 : (27843518766 * 55100000000000000000000 : ℝ) * (1 / 10 ^ 34 : ℝ) ≤ 1 := by
    norm_num
  calc |V a 5| ≤ 27843518766 * (π * ((5 : ℕ) : ℝ) ^ 2) ^ 12 * (Real.exp (-π)) ^ (5 ^ 2) := h
    _ ≤ (27843518766 * 55100000000000000000000 : ℝ) * (Real.exp (-π)) ^ (5 ^ 2) := s2
    _ ≤ (27843518766 * 55100000000000000000000 : ℝ) * (1 / 10 ^ 34 : ℝ) := s3
    _ ≤ 1 := s4

/-! ### The first four terms -/

/--
@isnad1 id=eq.0h2v.s6.018d6f99e8ff from=translated src=- shape=4a2c0a3d vocab=b3aba981
-/
lemma V_eq_pow (a : ℕ → ℝ) (n : ℕ) :
    V a n = poly a (π * (n : ℝ) ^ 2) * (Real.exp (-π)) ^ (n ^ 2) := by
  rw [V, exp_neg_pi_sq]

/--
@isnad1 id=eq.0h1v.s4.9c11ddb4a1bb from=translated src=- shape=46a4f078 vocab=d41f58d4
-/
lemma V1 (a : ℕ → ℝ) : V a 1 = poly a π * Real.exp (-π) := by
  rw [V_eq_pow]; norm_num
/--
@isnad1 id=eq.0h1v.s5.22d8169d5c8d from=translated src=- shape=8fc07db4 vocab=329d0b65
-/
lemma V2 (a : ℕ → ℝ) : V a 2 = poly a (π * 4) * (Real.exp (-π)) ^ 4 := by
  rw [V_eq_pow]; norm_num
/--
@isnad1 id=eq.0h1v.s5.80f26edff829 from=translated src=- shape=8fc07db4 vocab=329d0b65
-/
lemma V3 (a : ℕ → ℝ) : V a 3 = poly a (π * 9) * (Real.exp (-π)) ^ 9 := by
  rw [V_eq_pow]; norm_num
/--
@isnad1 id=eq.0h1v.s5.44fea5f7d49f from=translated src=- shape=8fc07db4 vocab=329d0b65
-/
lemma V4 (a : ℕ → ℝ) : V a 4 = poly a (π * 16) * (Real.exp (-π)) ^ 16 := by
  rw [V_eq_pow]; norm_num

/--
@isnad1 id=le.0h0v.s5.bf07bceb26e4 from=translated src=- shape=f7556fb5 vocab=689e3bfb
-/
lemma E4_lb : (0.0000033359 : ℝ) ≤ (Real.exp (-π)) ^ 4 := by
  calc (0.0000033359 : ℝ) ≤ (0.0427374 : ℝ) ^ 4 := by norm_num
    _ ≤ (Real.exp (-π)) ^ 4 := pow_le_pow_left₀ (by norm_num) Emin 4

/--
@isnad1 id=le.0h0v.s5.efbefeec4f1e from=translated src=- shape=b3dea1f7 vocab=689e3bfb
-/
lemma E4_ub : (Real.exp (-π)) ^ 4 ≤ 0.0000036178 := by
  calc (Real.exp (-π)) ^ 4 ≤ (0.0436122 : ℝ) ^ 4 := pow_le_pow_left₀ Epos.le Emax 4
    _ ≤ 0.0000036178 := by norm_num

/-! ### `Φ⁽⁸⁾(0) > 0` and `Φ⁽¹⁰⁾(0) > 0` -/

/-- **`Φ⁽⁸⁾(0) ≈ 1823335.79 > 0`** (`j = 4`).
@isnad1 id=lt.0h0v.s4.128e50db3818 from=translated src=- shape=942ea929 vocab=024596f1
-/
theorem G_c8_pos : 0 < G c8 0 := by
  rw [G_at_zero, V_split]
  have h1 : (2869900 : ℝ) ≤ V c8 1 := by
    rw [V1]
    refine le_trans (by norm_num) (mul_le_mul poly_c8_1 Emin (by norm_num) ?_)
    linarith [poly_c8_1]
  have h2 : (-1137800 : ℝ) ≤ V c8 2 := by
    rw [V2]
    have hA : (-314497220000 : ℝ) * (Real.exp (-π)) ^ 4 ≤ poly c8 (π * 4) * (Real.exp (-π)) ^ 4 :=
      mul_le_mul_of_nonneg_right poly_c8_2 (by positivity)
    have hB : (-314497220000 : ℝ) * (0.0000036178 : ℝ)
        ≤ (-314497220000 : ℝ) * (Real.exp (-π)) ^ 4 := by nlinarith [E4_ub]
    linarith [hA, hB]
  have h3 : (0 : ℝ) ≤ V c8 3 := by rw [V3]; exact mul_nonneg poly_c8_3 (by positivity)
  have h4 : (0 : ℝ) ≤ V c8 4 := by rw [V4]; exact mul_nonneg poly_c8_4 (by positivity)
  have h5 : (-1 : ℝ) ≤ V c8 5 := by
    have := abs_le.mp (V5_small c8 c8_13 sumabs_c8); linarith [this.1]
  have h6 : (-1 : ℝ) ≤ ∑' n : ℕ, V c8 (n + 6) := by
    have := abs_le.mp (tail_small c8 c8_13 sumabs_c8); linarith [this.1]
  linarith

/-- **`Φ⁽¹⁰⁾(0) ≈ 655898825.86 > 0`** (`j = 5`).  Here the `n = 1` term is negative and the
`n = 2` term carries the sign — the "sign anomaly" that breaks the expected alternation.
@isnad1 id=lt.0h0v.s4.30ba5fc85525 from=translated src=- shape=942ea929 vocab=69faa27b
-/
theorem G_c10_pos : 0 < G c10 0 := by
  rw [G_at_zero, V_split]
  have h1 : (-66072700 : ℝ) ≤ V c10 1 := by
    rw [V1]
    have hA : (-1515001800 : ℝ) * Real.exp (-π) ≤ poly c10 π * Real.exp (-π) :=
      mul_le_mul_of_nonneg_right poly_c10_1 Epos.le
    have hB : (-1515001800 : ℝ) * (0.0436122 : ℝ) ≤ (-1515001800 : ℝ) * Real.exp (-π) := by
      nlinarith [Emax]
    linarith [hA, hB]
  have h2 : (677490000 : ℝ) ≤ V c10 2 := by
    rw [V2]
    refine le_trans (by norm_num) (mul_le_mul poly_c10_2 E4_lb (by norm_num) ?_)
    linarith [poly_c10_2]
  have h3 : (0 : ℝ) ≤ V c10 3 := by rw [V3]; exact mul_nonneg poly_c10_3 (by positivity)
  have h4 : (0 : ℝ) ≤ V c10 4 := by rw [V4]; exact mul_nonneg poly_c10_4 (by positivity)
  have h5 : (-1 : ℝ) ≤ V c10 5 := by
    have := abs_le.mp (V5_small c10 c10_13 sumabs_c10); linarith [this.1]
  have h6 : (-1 : ℝ) ≤ ∑' n : ℕ, V c10 (n + 6) := by
    have := abs_le.mp (tail_small c10 c10_13 sumabs_c10); linarith [this.1]
  linarith

/-! ### The Coffey–Csordás conjecture is false at `n = 9` -/

/-- `Φ⁽⁸⁾(0) > 0`.
@isnad1 id=lt.0h0v.s5.8fc224f051b2 from=translated src=- shape=382ef02b vocab=e25c9dd6
-/
theorem iteratedDeriv_eight_pos : 0 < iteratedDeriv 8 Phi 0 := by
  rw [iter8]; exact G_c8_pos

/-- `Φ⁽⁹⁾(0) = 0`, because `Φ` is even.
@isnad1 id=eq.0h0v.s5.af66cfcd7439 from=translated src=- shape=6a036764 vocab=8164b758
-/
theorem iteratedDeriv_nine_zero : iteratedDeriv 9 Phi 0 = 0 := by
  rw [iter9]; exact G_c9_zero

/-- `Φ⁽¹⁰⁾(0) > 0`.
@isnad1 id=lt.0h0v.s5.24087eeada8a from=translated src=- shape=382ef02b vocab=e25c9dd6
-/
theorem iteratedDeriv_ten_pos : 0 < iteratedDeriv 10 Phi 0 := by
  rw [iter10]; exact G_c10_pos

/-- The Coffey–Csordás functional
`J_n(t) = (Φ⁽ⁿ⁾(t))² − Φ⁽ⁿ⁻¹⁾(t) Φ⁽ⁿ⁺¹⁾(t)`.-/
noncomputable def J (n : ℕ) (t : ℝ) : ℝ :=
  (iteratedDeriv n Phi t) ^ 2 - iteratedDeriv (n - 1) Phi t * iteratedDeriv (n + 1) Phi t

/-- **Coffey–Csordás Conjecture 2.5 (= Csordás, Open Problem 4.13) is false.**
`J₉(0) = −Φ⁽⁸⁾(0)·Φ⁽¹⁰⁾(0) ≈ −1.1959·10¹⁵ < 0`.
@isnad1 id=lt.0h0v.s4.eeee05fda066 from=translated src=- shape=11536466 vocab=0dfa5679
-/
theorem J_nine_neg : J 9 0 < 0 := by
  have hJ : J 9 0 = -(iteratedDeriv 8 Phi 0 * iteratedDeriv 10 Phi 0) := by
    rw [J]
    norm_num [iteratedDeriv_nine_zero]
  rw [hJ]
  have h8 := iteratedDeriv_eight_pos
  have h10 := iteratedDeriv_ten_pos
  nlinarith

end XiLab

section AxiomAudit

end AxiomAudit
