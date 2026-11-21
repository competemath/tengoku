/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license.
-/
import Tengoku.Grlab.GRLab.Pderiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Chart-level pseudo-Riemannian curvature

A metric on a chart is a matrix-valued function `g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ`.
No positivity is assumed anywhere, so Lorentzian signature `(-,+,+,+)` is admissible; this
is why `Mathlib.Topology.VectorBundle.Riemannian.RiemannianMetric` cannot be reused (its
`pos` field is literal positive-definiteness).

## Fidelity to the textbook formulas

With `∂_b = GRLab.pderiv b` and `g^{ab} = (g x)⁻¹ a b` (Mathlib's `Matrix.inv`, i.e.
`det⁻¹ʳ • adjugate`, which is the true inverse exactly when `det ≠ 0`):

* `christoffel`  `Γ^a_{bc} = ½ gᵃᵈ (∂_b g_{dc} + ∂_c g_{db} − ∂_d g_{bc})`
  — Wald (3.1.30), MTW (8.24), Carroll (3.27).
* `riemann`      `R^a_{bcd} = ∂_c Γ^a_{db} − ∂_d Γ^a_{cb} + Γ^a_{ce} Γ^e_{db} − Γ^a_{de} Γ^e_{cb}`
  — Wald (3.2.3) / Carroll (3.66) convention.  `GRLab.Flat` pins the conventions in Lean
  from below (a constant metric gives `R^a_{bcd} = 0`, and `gᵇᵈg_{bd} = 4` fixes the index
  placement); `GRLab.Schwarzschild.ricci_deSitter_thetaTheta` pins the *sign* in Lean from
  above, by exhibiting a metric whose Ricci tensor is provably nonzero and positive.  The
  independent symbolic computation described in `README.md` reproduces `R = +12/L²` for static
  de Sitter and `K = 48M²/r⁶` for Schwarzschild in this convention.
* `ricci`        `R_{bd} = R^a_{bad}` (contraction on the *first* and *third* slots).
* `scalarCurvature` `R = gᵇᵈ R_{bd}`.
* `einstein`     `G_{bd} = R_{bd} − ½ R g_{bd}`.

Every definition is a finite `Finset.sum` over `Fin n` and each is self-contained: the
whole file inlines into ≤ 60 lines of Mathlib-only Lean, which is what a Palomar Challenge
statement requires.
-/

namespace GRLab

open Matrix Filter Topology

variable {n : ℕ}

/-- A chart-level metric: a matrix-valued function on (an open subset of) `ℝⁿ`.-/
abbrev MetricFn (n : ℕ) := (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ

/-- Pointwise symmetry of a chart-level metric.-/
def IsSymmetricMetric (g : MetricFn n) : Prop := ∀ y i j, g y i j = g y j i

/-- **Christoffel symbols of the second kind.**
`Γ^a_{bc} = ½ gᵃᵈ (∂_b g_{dc} + ∂_c g_{db} − ∂_d g_{bc})`.-/
noncomputable def christoffel (g : MetricFn n) (x : Fin n → ℝ) (a b c : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ d : Fin n, (g x)⁻¹ a d *
    (pderiv b (fun y => g y d c) x + pderiv c (fun y => g y d b) x
      - pderiv d (fun y => g y b c) x)

/-- **Riemann curvature tensor**, `(1,3)` form.
`R^a_{bcd} = ∂_c Γ^a_{db} − ∂_d Γ^a_{cb} + Γ^a_{ce} Γ^e_{db} − Γ^a_{de} Γ^e_{cb}`.-/
noncomputable def riemann (g : MetricFn n) (x : Fin n → ℝ) (a b c d : Fin n) : ℝ :=
  pderiv c (fun y => christoffel g y a d b) x - pderiv d (fun y => christoffel g y a c b) x
    + ∑ e : Fin n, (christoffel g x a c e * christoffel g x e d b
        - christoffel g x a d e * christoffel g x e c b)

/-- **Ricci tensor**, `R_{bd} = R^a_{bad}`.-/
noncomputable def ricci (g : MetricFn n) (x : Fin n → ℝ) (b d : Fin n) : ℝ :=
  ∑ a : Fin n, riemann g x a b a d

/-- **Scalar curvature**, `R = gᵇᵈ R_{bd}`.-/
noncomputable def scalarCurvature (g : MetricFn n) (x : Fin n → ℝ) : ℝ :=
  ∑ b : Fin n, ∑ d : Fin n, (g x)⁻¹ b d * ricci g x b d

/-- **Einstein tensor**, `G_{bd} = R_{bd} − ½ R g_{bd}`.-/
noncomputable def einstein (g : MetricFn n) (x : Fin n → ℝ) (b d : Fin n) : ℝ :=
  ricci g x b d - (1 / 2 : ℝ) * scalarCurvature g x * g x b d

/-- A chart-level metric is **Ricci-flat** (solves the vacuum Einstein equation) at `x`
when every component of its Ricci tensor vanishes there.-/
def RicciFlatAt (g : MetricFn n) (x : Fin n → ℝ) : Prop := ∀ b d, ricci g x b d = 0

/-! ## Structural lemmas

These are the identities that follow from the *shape* of the definitions by pure algebra,
with no analytic input beyond what is stated.  Everything genuinely requiring the symmetry
of second partial derivatives (notably `R_{bd} = R_{db}`) is deliberately **not** here; the
scope note in `README.md` says exactly what is and is not proved.
-/

/-- The Christoffel symbols are symmetric in their two lower indices — the connection is
torsion-free.  This is exactly where symmetry of the metric is used.
@isnad1 id=eq.1h6v.s5.53742dc083d6 from=translated src=- shape=da7b6ac0 vocab=aeeb01ea
-/
theorem christoffel_symm {g : MetricFn n} (hg : IsSymmetricMetric g) (x : Fin n → ℝ)
    (a b c : Fin n) : christoffel g x a b c = christoffel g x a c b := by
  unfold christoffel
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  have hbc : (fun y => g y b c) = fun y => g y c b := by funext y; exact hg y b c
  rw [hbc]
  ring

/-- The Riemann tensor is antisymmetric in its last two indices.
@isnad1 id=eq.0h7v.s5.83d5cf196dfa from=translated src=- shape=eaf0cd62 vocab=c62ec523
-/
theorem riemann_antisymm (g : MetricFn n) (x : Fin n → ℝ) (a b c d : Fin n) :
    riemann g x a b c d = -riemann g x a b d c := by
  have hs : ∑ e : Fin n, (christoffel g x a d e * christoffel g x e c b
        - christoffel g x a c e * christoffel g x e d b)
      = -∑ e : Fin n, (christoffel g x a c e * christoffel g x e d b
        - christoffel g x a d e * christoffel g x e c b) := by
    rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun e _ => by ring
  unfold riemann
  rw [hs]; ring

/-- `R^a_{bcc} = 0`.
@isnad1 id=eq.0h6v.s5.57c196cf986a from=translated src=- shape=5d38e909 vocab=c18bc5b8
-/
@[simp] theorem riemann_self (g : MetricFn n) (x : Fin n → ℝ) (a b c : Fin n) :
    riemann g x a b c c = 0 := by
  have := riemann_antisymm g x a b c c
  linarith

/-- A metric that is *locally constant* around `x` has vanishing Christoffel symbols
at every point of that neighbourhood, hence vanishing curvature at `x`.
@isnad1 id=eq.1h7v.s5.5dc2f4bb669d from=translated src=- shape=195c3830 vocab=2820ac5c
-/
theorem christoffel_eq_zero_of_const {g : MetricFn n} {G : Matrix (Fin n) (Fin n) ℝ}
    (hg : ∀ y, g y = G) (x : Fin n → ℝ) (a b c : Fin n) : christoffel g x a b c = 0 := by
  have hz : ∀ (b d c : Fin n), pderiv b (fun y => g y d c) x = 0 := by
    intro b d c
    have : (fun y => g y d c) = fun _ : Fin n → ℝ => G d c := by funext y; rw [hg y]
    rw [this]; exact pderiv_const _ _ _
  simp [christoffel, hz]

/-- If the Christoffel symbols vanish identically then so does the Riemann tensor.
@isnad1 id=eq.1h7v.s6.f41a3b5805e2 from=translated src=- shape=2d91a0b6 vocab=a9cc24f6
-/
theorem riemann_eq_zero_of_christoffel_eq_zero {g : MetricFn n}
    (h : ∀ y a b c, christoffel g y a b c = 0) (x : Fin n → ℝ) (a b c d : Fin n) :
    riemann g x a b c d = 0 := by
  have hfun : ∀ (a d b : Fin n),
      (fun y => christoffel g y a d b) = fun _ : Fin n → ℝ => (0 : ℝ) := by
    intro a d b; funext y; exact h y a d b
  simp [riemann, h]

/-! ### The metric trace, and the vacuum equations -/

/-- `gᵇᵈ g_{bd} = n` for a symmetric invertible metric.
@isnad1 id=eq.2h3v.s6.45fb4aa430db from=translated src=- shape=58019a7d vocab=aba576b9
-/
theorem sum_inv_mul_metric {g : MetricFn n} (hg : IsSymmetricMetric g) {x : Fin n → ℝ}
    (hx : IsUnit (g x).det) :
    ∑ b : Fin n, ∑ d : Fin n, (g x)⁻¹ b d * g x b d = (n : ℝ) := by
  have hsymm : ∀ b d, g x b d = g x d b := fun b d => hg x b d
  have h1 : ∑ b : Fin n, ∑ d : Fin n, (g x)⁻¹ b d * g x b d
      = ∑ b : Fin n, ((g x)⁻¹ * g x) b b := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun d _ => by rw [hsymm b d]
  rw [h1, Matrix.nonsing_inv_mul _ hx]
  simp

/-- Contracting the Einstein tensor: `gᵇᵈ G_{bd} = (1 − n/2) R`.
@isnad1 id=eq.2h3v.s7.65f3771b42dc from=translated src=- shape=d1e84d93 vocab=a689b709
-/
theorem trace_einstein {g : MetricFn n} (hg : IsSymmetricMetric g) {x : Fin n → ℝ}
    (hx : IsUnit (g x).det) :
    ∑ b : Fin n, ∑ d : Fin n, (g x)⁻¹ b d * einstein g x b d
      = (1 - (n : ℝ) / 2) * scalarCurvature g x := by
  have hsplit : ∀ b d : Fin n, (g x)⁻¹ b d * einstein g x b d
      = (g x)⁻¹ b d * ricci g x b d
        - (1 / 2 : ℝ) * scalarCurvature g x * ((g x)⁻¹ b d * g x b d) := by
    intro b d; unfold einstein; ring
  calc ∑ b : Fin n, ∑ d : Fin n, (g x)⁻¹ b d * einstein g x b d
      = (∑ b : Fin n, ∑ d : Fin n, (g x)⁻¹ b d * ricci g x b d)
        - (1 / 2 : ℝ) * scalarCurvature g x
          * ∑ b : Fin n, ∑ d : Fin n, (g x)⁻¹ b d * g x b d := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun d _ => hsplit b d
    _ = (1 - (n : ℝ) / 2) * scalarCurvature g x := by
        rw [sum_inv_mul_metric hg hx, ← scalarCurvature]; ring

/-- **Vacuum Einstein equations.**  Away from `n = 2`, `G_{bd} = 0` and `R_{bd} = 0` are
equivalent.  This is why "Ricci-flat" and "solves the vacuum field equations" are used
interchangeably in general relativity.
@isnad1 id=iff.3h3v.s6.429a7cc19588 from=translated src=- shape=5763bd31 vocab=14ca01e2
-/
theorem einstein_eq_zero_iff_ricciFlat {g : MetricFn n} (hg : IsSymmetricMetric g)
    {x : Fin n → ℝ} (hx : IsUnit (g x).det) (hn : (n : ℝ) ≠ 2) :
    (∀ b d, einstein g x b d = 0) ↔ RicciFlatAt g x := by
  constructor
  · intro h
    have htr : (1 - (n : ℝ) / 2) * scalarCurvature g x = 0 := by
      rw [← trace_einstein hg hx]; simp [h]
    have hR : scalarCurvature g x = 0 := by
      rcases mul_eq_zero.mp htr with h' | h'
      · exact absurd (by linarith : (n : ℝ) = 2) hn
      · exact h'
    intro b d
    have := h b d
    unfold einstein at this
    rw [hR] at this
    linarith
  · intro h b d
    have hR : scalarCurvature g x = 0 := by
      unfold scalarCurvature
      exact Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun d _ => by rw [h b d]; ring
    unfold einstein
    rw [h b d, hR]; ring

end GRLab
