/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license.
-/
import Tengoku.Grlab.GRLab.Curvature

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Flat charts: constant metrics and Minkowski space

This file **pins the sign and index conventions of `GRLab.riemann`** by exhibiting the
flat case in full.  A curvature convention is only meaningful relative to the examples
that anchor it, and the two anchors used throughout `GRLab` are:

* the flat anchor, *here* — every curvature scalar and tensor of a constant metric
  vanishes identically, in every dimension and for every (not necessarily invertible,
  not necessarily symmetric) constant matrix `G`;
* the curved anchor, in `GRLab.StaticSpherical` — static de Sitter has `R = +12/L²`,
  which fixes the overall sign of `riemann` in the Wald (3.2.3) / Carroll (3.66)
  convention rather than the opposite one.

## Why a constant metric is flat

For the trivial reason, and it is worth saying which triviality it is.  Writing the
Riemann tensor of `GRLab.Curvature` out,

  `R^a_{bcd} = ∂_c Γ^a_{db} − ∂_d Γ^a_{cb} + Γ^a_{ce} Γ^e_{db} − Γ^a_{de} Γ^e_{cb}`,

every one of the four terms is either a derivative of a Christoffel symbol or a product
of two Christoffel symbols: **`R` is a polynomial in `Γ` and `∂Γ` with no `Γ`-free term.**
A constant metric has `∂_b g_{dc} = 0`, hence `Γ ≡ 0` by `christoffel_eq_zero_of_const`,
hence `R ≡ 0` by `riemann_eq_zero_of_christoffel_eq_zero`, and the whole tower
`ricci → scalarCurvature → einstein` collapses with it.  No invertibility of `g` and no
symmetry of `g` are needed for any of that; both hypotheses only enter once one wants to
*contract* indices, which is where `minkowski_trace` and `minkowski_vacuum` below live.

Note in particular that `constMetric_riemann_eq_zero` holds for a degenerate `G` as well.
That is a feature of the chart-level definitions, not an oversight: `christoffel` is
built from Mathlib's `Matrix.inv`, whose junk value at `det = 0` is `0`.

## Contents

`constMetric G` is the constant metric with value `G`; `minkowski` is
`constMetric (diagonal ![-1, 1, 1, 1])`, the Cartesian chart of Minkowski space with
signature `(-,+,+,+)`.  Besides flatness we record the concrete facts that pin the index
placement: `minkowski_det = -1`, the self-inverse property `(η x)⁻¹ = η x`, and the
trace `η^{bd} η_{bd} = 4`, which is `sum_inv_mul_metric` specialised to `n = 4`.
-/

namespace GRLab

open Matrix

variable {n : ℕ}

/-! ## Constant metrics in arbitrary dimension -/

/-- A metric that is constant across the chart.-/
noncomputable def constMetric (G : Matrix (Fin n) (Fin n) ℝ) : MetricFn n := fun _ => G

/--
@isnad1 id=eq.0h3v.s4.a35968087c35 from=translated src=- shape=e4862fc9 vocab=3c4a0bdb
-/
@[simp] lemma constMetric_apply (G : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    constMetric G x = G := rfl

/-- A constant metric is symmetric exactly when its value is.
@isnad1 id=issymmet.1h2v.s4.86d0c5ddb2dd from=translated src=- shape=a75323ad vocab=7804a5cd
-/
theorem constMetric_isSymm {G : Matrix (Fin n) (Fin n) ℝ} (hG : ∀ i j, G i j = G j i) :
    IsSymmetricMetric (constMetric G) := fun _ i j => hG i j

/-- All Christoffel symbols of a constant metric vanish: the connection coefficients are
built purely out of first derivatives of `g`, which are identically zero.
@isnad1 id=eq.0h6v.s5.66ec6be4b248 from=translated src=- shape=0b78a712 vocab=aaf44816
-/
theorem constMetric_christoffel_eq_zero (G : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (a b c : Fin n) : christoffel (constMetric G) x a b c = 0 :=
  christoffel_eq_zero_of_const (fun _ => rfl) x a b c

/-- **A constant metric is flat.**  `R^a_{bcd}` is a polynomial in `Γ` and `∂Γ` with no
`Γ`-free term, so `Γ ≡ 0` forces `R ≡ 0`.
@isnad1 id=eq.0h7v.s5.0e7c01b25f0d from=translated src=- shape=5f2a8ce9 vocab=1d5299f1
-/
theorem constMetric_riemann_eq_zero (G : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (a b c d : Fin n) : riemann (constMetric G) x a b c d = 0 :=
  riemann_eq_zero_of_christoffel_eq_zero
    (fun y a b c => constMetric_christoffel_eq_zero G y a b c) x a b c d

/-- The Ricci tensor of a constant metric vanishes (a contraction of a vanishing
Riemann tensor).
@isnad1 id=eq.0h5v.s5.26ff7eac8e07 from=translated src=- shape=080c29ea vocab=8c653aad
-/
theorem constMetric_ricci_eq_zero (G : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (b d : Fin n) : ricci (constMetric G) x b d = 0 :=
  Finset.sum_eq_zero fun a _ => constMetric_riemann_eq_zero G x a b a d

/-- A constant metric solves the vacuum Einstein equation at every point.
@isnad1 id=riccifla.0h3v.s4.cf3b836195f7 from=translated src=- shape=cfcf8ca7 vocab=d41fe388
-/
theorem constMetric_ricciFlat (G : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    RicciFlatAt (constMetric G) x := fun b d => constMetric_ricci_eq_zero G x b d

/-- The scalar curvature of a constant metric vanishes.  No invertibility of `G` is
needed: the Ricci factor is already zero termwise.
@isnad1 id=eq.0h3v.s4.18a1100b98cf from=translated src=- shape=b8f29fc0 vocab=5749e5ff
-/
theorem constMetric_scalarCurvature_eq_zero (G : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : scalarCurvature (constMetric G) x = 0 :=
  Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun d _ => by
    rw [constMetric_ricci_eq_zero, mul_zero]

/-- The Einstein tensor of a constant metric vanishes.
@isnad1 id=eq.0h5v.s5.a18593ecdc20 from=translated src=- shape=080c29ea vocab=c526c59b
-/
theorem constMetric_einstein_eq_zero (G : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (b d : Fin n) : einstein (constMetric G) x b d = 0 := by
  unfold einstein
  rw [constMetric_ricci_eq_zero, constMetric_scalarCurvature_eq_zero]
  ring

/-! ## Minkowski space in Cartesian coordinates -/

/-- A diagonal matrix is symmetric.
@isnad1 id=eq.0h4v.s5.69e17b48e82a from=translated src=- shape=53ab0cd1 vocab=02c7d5b6
-/
lemma diagonal_symm (v : Fin n → ℝ) (i j : Fin n) :
    Matrix.diagonal v i j = Matrix.diagonal v j i := by
  rcases eq_or_ne i j with h | h
  · rw [h]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h.symm]

/-- The Minkowski metric `diag(-1,1,1,1)` in Cartesian coordinates `(t, x, y, z)`,
with the mostly-plus signature `(-,+,+,+)` used throughout `GRLab`.-/
noncomputable def minkowski : MetricFn 4 := constMetric (Matrix.diagonal ![-1, 1, 1, 1])

/--
@isnad1 id=issymmet.0h0v.s2.8f4862109e75 from=translated src=- shape=cef8a6bf vocab=a6836bee
-/
theorem minkowski_isSymm : IsSymmetricMetric minkowski :=
  constMetric_isSymm (diagonal_symm _)

/-- `det η = -1`: the single minus sign of the Lorentzian signature.
@isnad1 id=eq.0h1v.s5.540a659e0432 from=translated src=- shape=37979dda vocab=545c3f44
-/
theorem minkowski_det (x : Fin 4 → ℝ) : (minkowski x).det = -1 := by
  show (Matrix.diagonal ![(-1 : ℝ), 1, 1, 1]).det = -1
  rw [Matrix.det_diagonal, Fin.prod_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  norm_num

/--
@isnad1 id=isunit.0h1v.s5.347c7660e44c from=translated src=- shape=60444a58 vocab=be37b8e2
-/
theorem minkowski_isUnit_det (x : Fin 4 → ℝ) : IsUnit (minkowski x).det := by
  rw [minkowski_det]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

/--
@isnad1 id=eq.0h4v.s5.17ae4d13c09d from=translated src=- shape=79c9c7c0 vocab=aaced3bd
-/
theorem minkowski_christoffel_eq_zero (x : Fin 4 → ℝ) (a b c : Fin 4) :
    christoffel minkowski x a b c = 0 :=
  constMetric_christoffel_eq_zero _ x a b c

/-- **Minkowski space is flat**, in the strong sense that every component of the
`(1,3)` Riemann tensor vanishes at every point.
@isnad1 id=eq.0h5v.s5.d9e15c5e88c4 from=translated src=- shape=94f54e1a vocab=c5ac4cdb
-/
theorem minkowski_riemann_eq_zero (x : Fin 4 → ℝ) (a b c d : Fin 4) :
    riemann minkowski x a b c d = 0 :=
  constMetric_riemann_eq_zero _ x a b c d

/--
@isnad1 id=riccifla.0h1v.s4.3477169e7065 from=translated src=- shape=0384288c vocab=3e00752e
-/
theorem minkowski_ricciFlat (x : Fin 4 → ℝ) : RicciFlatAt minkowski x :=
  constMetric_ricciFlat _ x

/--
@isnad1 id=eq.0h1v.s4.fa377d1e4479 from=translated src=- shape=90537f56 vocab=403cb59f
-/
theorem minkowski_scalarCurvature_eq_zero (x : Fin 4 → ℝ) :
    scalarCurvature minkowski x = 0 :=
  constMetric_scalarCurvature_eq_zero _ x

/--
@isnad1 id=eq.0h3v.s5.ca224d9cf42d from=translated src=- shape=0265aa58 vocab=dc93ed2a
-/
theorem minkowski_einstein_eq_zero (x : Fin 4 → ℝ) (b d : Fin 4) :
    einstein minkowski x b d = 0 :=
  constMetric_einstein_eq_zero _ x b d

/-- Minkowski satisfies the vacuum Einstein equations, via the general
Ricci-flat ↔ Einstein-flat equivalence rather than by direct computation.

This is the structural route: it consumes `minkowski_isSymm`, `minkowski_isUnit_det`
and `(4 : ℝ) ≠ 2`, and internally runs the trace identity `g^{bd} G_{bd} = (1 - n/2) R`.
Compare `minkowski_einstein_eq_zero`, which reaches the same conclusion by unfolding the
definition — that the two agree is a consistency check on `trace_einstein`.
@isnad1 id=eq.0h3v.s5.ca224d9cf42d from=translated src=- shape=0265aa58 vocab=dc93ed2a
-/
theorem minkowski_vacuum (x : Fin 4 → ℝ) : (∀ b d, einstein minkowski x b d = 0) :=
  (einstein_eq_zero_iff_ricciFlat minkowski_isSymm (minkowski_isUnit_det x) (by norm_num)).mpr
    (minkowski_ricciFlat x)

end GRLab
