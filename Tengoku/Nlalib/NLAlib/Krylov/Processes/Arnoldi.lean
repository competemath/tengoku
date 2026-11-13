import Tengoku.Nlalib.NLAlib.Matrix.Subspaces.Projections
import Tengoku.Nlalib.NLAlib.Krylov.Spaces.Grade
import Tengoku.Nlalib.NLAlib.ForMathlib.LinearAlgebra.Matrix.Mul
import Tengoku.Nlalib.NLAlib.Matrix.Subspaces.OrthogonalProducts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Graded Krylov bases, the Arnoldi decomposition and the Arnoldi process

The structure layer of Krylov theory (`docs/KRYLOV_DEFINITIONS.md` §3.5, §3.11, §3.12).

* `IsGradedKrylovBasis A b Q`: `Q : n × q` has orthonormal columns and its first `i + 1`
  columns span `K_{i+1}(A, b)`; API `span_col_castLE`, `col_mem`, `range_mulVecLin`,
  `col_dotProduct_eq_zero` (`qᵢ ⟂ K_i`), `eq_sum_of_mem`, `of_mem` / `isGradedKrylovBasis_iff`
  (membership suffices), `le_krylovGrade`, and the Hessenberg facts
  `transpose_mul_mul_apply_eq_zero`, `transpose_mul_mul_apply_succ_ne_zero` (unreduced).
* `ArnoldiDecomp A b q` (a graded basis bundled with `Q`), `ArnoldiDecomp.H = Qᵀ A Q`,
  `restrict` / `H_restrict` (nesting: `H_{q'}` is the leading block of `H_q`), `exists_sign`
  (uniqueness up to column signs, via `col_eq_smul_col`), `Q_eq_of_pos` (positive
  normalisation fixes it), `H_apply_eq_zero_of_add_one_lt` (upper Hessenberg),
  `H_succ_apply_ne_zero` (unreduced).
* `LanczosDecomp := ArnoldiDecomp` for symmetric `A`, `LanczosDecomp.T`,
  `T_apply_eq_zero_of_one_lt_dist` (tridiagonal).
The process (`arnoldiBasis`, the canonical witness `arnoldiDecomp`) is in
`NLAlib.Krylov.Processes.ArnoldiProcess`; the Arnoldi relation and the Lanczos recurrence in
`NLAlib.Krylov.Processes.Lanczos`; Jacobi-matrix identities in `NLAlib.Krylov.Quadrature.Jacobi`.

## Three spellings of the Krylov process, and what each is

| object | ℕ-indexed process (Gram–Schmidt, no hypothesis) | bundled predicate (`D : ArnoldiDecomp A b q`) | three-term recursion (algorithm) |
|---|---|---|---|
| basis vectors | `arnoldiBasis A b j` (zero after the grade) | `D.Q.col j`, `D.vec j` (Lanczos name) | `lanczosRecurrence A b j` |
| basis matrix | `arnoldiMatrix A b q` | `D.Q` | `Matrix.of fun r j => lanczosRecurrence A b j r` |
| Hessenberg / Jacobi matrix | `arnoldiHessenberg A b q = Q_qᵀ A Q_q` | `D.H`, `D.T` (Lanczos name) | — |
| coefficients | entries of `arnoldiHessenberg` | `D.alpha j = t_jj`, `D.beta j = t_{j,j−1}` | `lanczosAlpha A b j`, `lanczosBeta A b j` |
| existence / bridge | `arnoldiDecomp A b q h` (`q ≤ krylovGrade A b`) | `ArnoldiDecomp.Q_eq_arnoldiMatrix` (unique with positive subdiagonal) | `lanczosRecurrence_eq_arnoldiBasis` (realisation theorem) |

`LanczosDecomp A b q` is an abbreviation of `ArnoldiDecomp A b q` (one object; the symmetric
layer is the hypothesis `hA : A.IsHermitian` on the theorems), with the Lanczos names `T`,
`vec`, `alpha`, `beta`. The off-diagonal coefficient is one quantity in all spellings:
`β_j = t_{j,j−1} = q_jᵀ A q_{j−1} = ‖w_{j−1}‖` where `w_{j−1} = A q_{j−1} − α_{j−1} q_{j−1} −
β_{j−1} q_{j−2}` is the recursion's unnormalised vector (`β_0 = 0`; the recursion's definition is
the norm, `lanczosBeta_succ_eq_dotProduct` is the identity with the entry). Beyond the range of
a decomposition (`j ≥ q`) `D.beta j` is `0` by convention, never by theorem: the coefficient
`β_q` multiplying `q_q e_qᵀ` in `A Q_q = Q_q T_q + β_q q_q e_qᵀ` is read off from a decomposition
of size `q + 1` (`LanczosDecomp.mul_restrict_Q_eq_add_beta_smul`); at the grade the relation is
`ArnoldiDecomp.mul_Q_eq_mul_H_iff`.

Source: Saad (2003) [`saad03`], §6.3 (Alg. 6.1, Props 6.4–6.6); Saad (2011) [`saad11`],
§6.3, §6.6; Trefethen–Bau (1997) [`tb97`], Lect. 33, 36; Golub–Meurant (2010) [`gm10`], Ch. 4.
Atlas: `graded-krylov-basis-def`, `arnoldi-def`; `lanczos-recurrence` (tridiagonality).
-/

noncomputable section

open scoped Matrix
open Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Real forms of the orthonormal-column helpers -/

/-- `(Qᵀ Q)_ij = q_i ⬝ q_j` for a real matrix (real form of `conjTranspose_mul_self_apply`).
Helper for `arnoldi-def`.
@isnad1 id=eq.0h5v.s6.6fc95b6d50fc from=translated src=- shape=5bf7c0c1 vocab=d5848740
-/
theorem transpose_mul_self_apply {k : Type*} (Q : Matrix n k ℝ) (i j : k) :
    (Qᵀ * Q) i j = Q.col i ⬝ᵥ Q.col j := by
  simp [Matrix.mul_apply, dotProduct, Matrix.col]

/-- Columns of a real matrix with orthonormal columns: `q_i ⬝ q_j = δ_ij` (real form of
`HasOrthonormalCols.star_col_dotProduct_col`). Helper for `arnoldi-def`.
@isnad1 id=eq.1h5v.s6.400403e8c65b from=translated src=- shape=42c42647 vocab=4e78000d
-/
theorem HasOrthonormalCols.col_dotProduct_col {k : Type*} [Fintype k] [DecidableEq k]
    {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q) (i j : k) :
    Q.col i ⬝ᵥ Q.col j = if i = j then 1 else 0 := by
  simpa using hQ.star_col_dotProduct_col i j

/-! ### Graded Krylov bases -/

/-- `Q` is a **graded orthonormal Krylov basis** of `(A, b)`: its columns are orthonormal and for
every `i < q` the first `i + 1` columns span `K_{i+1}(A, b)`. Equivalently (`of_mem`), the
columns are orthonormal and `q_i ∈ K_{i+1}(A, b)`. Such a basis exists iff `q ≤ krylovGrade A b`
and is unique up to the signs of its columns (`ArnoldiDecomp.exists_sign`).
Source: Saad (2011) [`saad11`], §6.3 and §6.6; Greenbaum (1997) [`greenbaum97`], §2.5.
atlas: graded-krylov-basis-def-/
structure IsGradedKrylovBasis (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ} (Q : Matrix n (Fin q) ℝ) :
    Prop where
  /-- The columns are orthonormal.-/
  orth : HasOrthonormalCols Q
  /-- The first `i + 1` columns span `K_{i+1}(A, b)`.-/
  nested : ∀ i : Fin q,
    Submodule.span ℝ (Set.range fun j : Fin (i + 1) => Q.col (Fin.castLE i.isLt j)) =
      krylovSpace A b (i + 1)

namespace IsGradedKrylovBasis

variable {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ} {Q : Matrix n (Fin q) ℝ}

/-- The first `m ≤ q` columns of a graded basis span `K_m(A, b)` (also for `m = 0`).
Atlas: `graded-krylov-basis-def`.
@isnad1 id=eq.2h6v.s6.90c43607e74f from=translated src=- shape=aa5ef9cb vocab=7f60fa8d
-/
theorem span_col_castLE (hQ : IsGradedKrylovBasis A b Q) {m : ℕ} (hm : m ≤ q) :
    Submodule.span ℝ (Set.range fun j : Fin m => Q.col (Fin.castLE hm j)) =
      krylovSpace A b m := by
  rcases m with _ | m
  · simp [krylovSpace]
  · exact hQ.nested ⟨m, hm⟩

/-- Column `j` of a graded basis lies in `K_{j+1}(A, b)`. Atlas: `graded-krylov-basis-def`.
@isnad1 id=mem.1h6v.s7.6ffc887741ae from=translated src=- shape=e01b8148 vocab=fce7f259
-/
theorem col_mem (hQ : IsGradedKrylovBasis A b Q) (j : Fin q) :
    Q.col j ∈ krylovSpace A b (j + 1) := by
  rw [← hQ.nested j]
  exact Submodule.subset_span ⟨⟨j, Nat.lt_succ_self _⟩, rfl⟩

/-- The columns of a graded basis span `K_q(A, b)`: `range Q = K_q(A, b)`.
Atlas: `graded-krylov-basis-def`.
@isnad1 id=eq.1h5v.s7.a06c844a827a from=translated src=- shape=a53ffc5a vocab=5a269116
-/
theorem range_mulVecLin (hQ : IsGradedKrylovBasis A b Q) :
    LinearMap.range Q.mulVecLin = krylovSpace A b q := by
  rw [Matrix.range_mulVecLin, ← hQ.span_col_castLE le_rfl]
  rfl

/-- Column `i` of a graded basis is orthogonal to `K_i(A, b)`. Atlas: `graded-krylov-basis-def`.
@isnad1 id=eq.2h7v.s7.674bd42679b0 from=translated src=- shape=d2281971 vocab=cb28ff4b
-/
theorem col_dotProduct_eq_zero (hQ : IsGradedKrylovBasis A b Q) (i : Fin q) {x : n → ℝ}
    (hx : x ∈ krylovSpace A b i) : Q.col i ⬝ᵥ x = 0 := by
  rw [← hQ.span_col_castLE i.isLt.le] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [hQ.orth.col_dotProduct_col, ite_eq_right]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castLE] at this
    omega
  | zero => simp
  | add y z _ _ hy hz => rw [dotProduct_add, hy, hz, add_zero]
  | smul c y _ hy => rw [dotProduct_smul, hy, smul_zero]

/-- Expansion in a graded basis: every `x ∈ K_q(A, b)` is `∑ᵢ (qᵢ ⬝ x) qᵢ`.
Atlas: `graded-krylov-basis-def`.-/
theorem eq_sum_of_mem (hQ : IsGradedKrylovBasis A b Q) {x : n → ℝ}
    (hx : x ∈ krylovSpace A b q) : x = ∑ i, (Q.col i ⬝ᵥ x) • Q.col i := by
  rw [← hQ.range_mulVecLin] at hx
  conv_lhs => rw [← mulVec_conjTranspose_mulVec_of_mem_range hQ.orth hx]
  rw [mulVec_eq_sum_smul_col]
  rfl

/-- If `x ∈ K_q(A, b)` is orthogonal to the columns `qᵢ`, `i ≥ m`, then `x ∈ K_m(A, b)`.
Atlas: `graded-krylov-basis-def`.
@isnad1 id=mem.4h7v.s8.5e7fc28fbf14 from=translated src=- shape=38762c45 vocab=5501f096
-/
theorem mem_of_forall_le_dotProduct_eq_zero (hQ : IsGradedKrylovBasis A b Q) {x : n → ℝ}
    (hx : x ∈ krylovSpace A b q) {m : ℕ} (hm : m ≤ q)
    (h0 : ∀ i : Fin q, m ≤ i → Q.col i ⬝ᵥ x = 0) : x ∈ krylovSpace A b m := by
  rw [hQ.eq_sum_of_mem hx, ← hQ.span_col_castLE hm]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : (i : ℕ) < m
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
  · rw [h0 i (not_lt.1 hi), zero_smul]
    exact Submodule.zero_mem _

/-- A matrix with orthonormal columns `qᵢ ∈ K_{i+1}(A, b)` is a graded Krylov basis (the span
equalities follow by counting dimensions). Atlas: `graded-krylov-basis-def`.
@isnad1 id=isgraded.2h5v.s8.08d675cd9096 from=translated src=- shape=66e0f2b4 vocab=44143ddf
-/
theorem of_mem (hQ : HasOrthonormalCols Q) (hmem : ∀ j : Fin q, Q.col j ∈ krylovSpace A b (j + 1)) :
    IsGradedKrylovBasis A b Q := by
  refine ⟨hQ, fun i => ?_⟩
  set v : Fin (i + 1) → n → ℝ := fun j => Q.col (Fin.castLE i.isLt j)
  have hle : Submodule.span ℝ (Set.range v) ≤ krylovSpace A b (i + 1) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact krylovSpace_mono A b (by simp; omega) (hmem _)
  have hli : LinearIndependent ℝ v :=
    hQ.linearIndependent_col.comp _ (Fin.castLE_injective _)
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  rw [finrank_span_eq_card hli, Fintype.card_fin]
  exact finrank_krylovSpace_le A b _

/-- Characterisation of graded bases by membership. Atlas: `graded-krylov-basis-def`.
@isnad1 id=iff.0h5v.s8.24b046f713d3 from=translated src=- shape=15b83d5e vocab=44143ddf
-/
theorem _root_.NLAlib.isGradedKrylovBasis_iff :
    IsGradedKrylovBasis A b Q ↔
      HasOrthonormalCols Q ∧ ∀ j : Fin q, Q.col j ∈ krylovSpace A b (j + 1) :=
  ⟨fun h => ⟨h.orth, h.col_mem⟩, fun h => of_mem h.1 h.2⟩

/-- A graded basis of size `q` forces `q ≤ krylovGrade A b` (its columns are `q` independent
vectors of `K_q(A, b)`). Atlas: `graded-krylov-basis-def`.
@isnad1 id=le.1h5v.s5.8ca5304e8e1c from=translated src=- shape=10b12bff vocab=78989b24
-/
theorem le_krylovGrade (hQ : IsGradedKrylovBasis A b Q) : q ≤ krylovGrade A b := by
  have h1 : Module.finrank ℝ (krylovSpace A b q) = q := by
    rw [← hQ.span_col_castLE le_rfl]
    exact (finrank_span_eq_card
      (hQ.orth.linearIndependent_col.comp _ (Fin.castLE_injective _))).trans (Fintype.card_fin _)
  have h2 := finrank_krylovSpace A b q
  omega

/-- `A q_j ∈ K_{j+2}(A, b)`.
@isnad1 id=mem.1h6v.s8.d9f7dcc06c9d from=translated src=- shape=26c166fd vocab=16fbae0a
-/
theorem mulVec_col_mem (hQ : IsGradedKrylovBasis A b Q) (j : Fin q) :
    A *ᵥ Q.col j ∈ krylovSpace A b (j + 2) :=
  mulVec_mem_krylovSpace_succ A b (hQ.col_mem j)

/-- **Hessenberg structure**: for a graded basis, `(Qᵀ A Q)_ij = 0` whenever `i > j + 1`, for
every `A`. Source: Saad (2003) [`saad03`], Prop. 6.5; Trefethen–Bau (1997) [`tb97`], Lect. 33.
Atlas: `graded-krylov-basis-def`.
@isnad1 id=eq.2h7v.s7.70a28e96be99 from=translated src=- shape=9ec9180d vocab=e804a497
-/
theorem transpose_mul_mul_apply_eq_zero (hQ : IsGradedKrylovBasis A b Q) {i j : Fin q}
    (hij : (j : ℕ) + 1 < i) : (Qᵀ * A * Q) i j = 0 := by
  rw [transpose_mul_mul_apply_eq_dotProduct]
  exact hQ.col_dotProduct_eq_zero i (krylovSpace_mono A b (by omega) (hQ.mulVec_col_mem j))

/-- If `K_m` (`1 ≤ m`) is mapped into itself by `A`, every Krylov space is contained in it.-/
private lemma krylovSpace_le_of_mulVec_mem {m : ℕ} (hm : 0 < m)
    (hinv : ∀ x ∈ krylovSpace A b m, A *ᵥ x ∈ krylovSpace A b m) (p : ℕ) :
    krylovSpace A b p ≤ krylovSpace A b m := by
  have hpow : ∀ i : ℕ, (A ^ i) *ᵥ b ∈ krylovSpace A b m := by
    intro i
    induction i with
    | zero => simpa using pow_mulVec_mem_krylovSpace A b hm
    | succ i ih => rw [pow_succ', ← Matrix.mulVec_mulVec]; exact hinv _ ih
  exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hpow i)

/-- **Unreduced Hessenberg**: the subdiagonal of `Qᵀ A Q` has no zero,
`(Qᵀ A Q)_{j+1, j} ≠ 0`. Source: Saad (2003) [`saad03`], Prop. 6.6 (breakdown at step `j`
iff `K_{j+1}` is invariant). Atlas: `graded-krylov-basis-def`.
@isnad1 id=ne.2h6v.s7.566e2ec7cbb8 from=translated src=- shape=b2dde257 vocab=58e7bfe6
-/
theorem transpose_mul_mul_apply_succ_ne_zero (hQ : IsGradedKrylovBasis A b Q) {j : ℕ}
    (hj : j + 1 < q) : (Qᵀ * A * Q) ⟨j + 1, hj⟩ ⟨j, by omega⟩ ≠ 0 := by
  intro h0
  rw [transpose_mul_mul_apply_eq_dotProduct] at h0
  -- `A q_j ∈ K_{j+1}`
  have hAq : A *ᵥ Q.col ⟨j, by omega⟩ ∈ krylovSpace A b q :=
    krylovSpace_mono A b (show j + 2 ≤ q by omega) (hQ.mulVec_col_mem ⟨j, by omega⟩)
  have hAj : A *ᵥ Q.col ⟨j, by omega⟩ ∈ krylovSpace A b (j + 1) := by
    refine hQ.mem_of_forall_le_dotProduct_eq_zero hAq (by omega) fun i hi => ?_
    rcases Nat.lt_or_ge (j + 1) i with hlt | hge
    · rw [← transpose_mul_mul_apply_eq_dotProduct]; exact hQ.transpose_mul_mul_apply_eq_zero hlt
    · obtain rfl : i = ⟨j + 1, hj⟩ := Fin.ext (by simp only; omega)
      exact h0
  -- hence `K_{j+1}` is invariant
  have hinv : ∀ x ∈ krylovSpace A b (j + 1), A *ᵥ x ∈ krylovSpace A b (j + 1) := by
    intro x hx
    rw [← hQ.span_col_castLE (show j + 1 ≤ q by omega)] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      by_cases hk : (k : ℕ) = j
      · convert hAj using 3; exact Fin.ext (by simp [hk])
      · have hk' : (k : ℕ) < j := by have := k.isLt; omega
        exact krylovSpace_mono A b (by simp; omega) (hQ.mulVec_col_mem _)
    | zero => simp
    | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hy
  have hmem := krylovSpace_le_of_mulVec_mem (Nat.succ_pos j) hinv _ (hQ.col_mem ⟨j + 1, hj⟩)
  have h1 := hQ.col_dotProduct_eq_zero ⟨j + 1, hj⟩ hmem
  rw [hQ.orth.col_dotProduct_col, ite_eq_left rfl] at h1
  exact one_ne_zero h1

end IsGradedKrylovBasis

/-! ### The bundled decomposition -/

/-- An **Arnoldi decomposition** of `(A, b)` of size `q`: a matrix `Q` whose columns form a graded
orthonormal Krylov basis. The compression `H = Qᵀ A Q` is `ArnoldiDecomp.H`; for symmetric `A`
the same object is a `LanczosDecomp` with `T = H`. Exists iff `q ≤ krylovGrade A b`
(`arnoldiDecomp`, `IsGradedKrylovBasis.le_krylovGrade`); unique up to column signs
(`ArnoldiDecomp.exists_sign`). Source: Saad (2003) [`saad03`], §6.3 (Alg. 6.1, Prop. 6.4);
Trefethen–Bau (1997) [`tb97`], Lect. 33.
atlas: arnoldi-def-/
structure ArnoldiDecomp (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) where
  /-- The basis matrix `Q_q`.-/
  Q : Matrix n (Fin q) ℝ
  /-- Its columns form a graded orthonormal Krylov basis.-/
  graded : IsGradedKrylovBasis A b Q

/-- A **Lanczos decomposition**: an Arnoldi decomposition, used for symmetric `A` (then
`T = Qᵀ A Q` is a Jacobi matrix, `LanczosDecomp.T`). Source: Golub–Meurant (2010) [`gm10`],
Ch. 4.
atlas: lanczos-recurrence-/
abbrev LanczosDecomp (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) := ArnoldiDecomp A b q

namespace ArnoldiDecomp

variable {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- The Hessenberg matrix `H_q = Q_qᵀ A Q_q` of an Arnoldi decomposition.
Source: Saad (2003) [`saad03`], §6.3.
atlas: arnoldi-def-/
def H (D : ArnoldiDecomp A b q) : Matrix (Fin q) (Fin q) ℝ := D.Qᵀ * A * D.Q

/-- Unfolding `H`. Atlas: `arnoldi-def`.
@isnad1 id=eq.0h5v.s6.fd3751ec9926 from=translated src=- shape=aa1917a5 vocab=38344c38
-/
theorem H_def (D : ArnoldiDecomp A b q) : D.H = D.Qᵀ * A * D.Q := rfl

/-- `H_ij = q_iᵀ A q_j`. Atlas: `arnoldi-def`.
@isnad1 id=eq.0h7v.s6.27210e29b773 from=translated src=- shape=66f86399 vocab=8e449060
-/
theorem H_apply (D : ArnoldiDecomp A b q) (i j : Fin q) : D.H i j = D.Q.col i ⬝ᵥ (A *ᵥ D.Q.col j) :=
  transpose_mul_mul_apply_eq_dotProduct _ _ _ _ _

/-- The basis matrix has orthonormal columns. Atlas: `arnoldi-def`.
@isnad1 id=hasortho.0h5v.s5.fd7ba5eaf727 from=translated src=- shape=0732a06c vocab=e7271557
-/
theorem hasOrthonormalCols (D : ArnoldiDecomp A b q) : HasOrthonormalCols D.Q := D.graded.orth

/-- The basis matrix spans the Krylov space: `range Q_q = K_q(A, b)`. Atlas: `arnoldi-def`.
@isnad1 id=eq.0h5v.s7.97b4c0bb9476 from=translated src=- shape=cc97c350 vocab=c711ee39
-/
theorem range_Q (D : ArnoldiDecomp A b q) : LinearMap.range D.Q.mulVecLin = krylovSpace A b q :=
  D.graded.range_mulVecLin

/-- An Arnoldi decomposition of size `q` exists only for `q ≤ krylovGrade A b`.
Atlas: `arnoldi-def`.
@isnad1 id=le.0h5v.s5.fd783a0f9717 from=translated src=- shape=166eee09 vocab=e648c0f4
-/
theorem le_krylovGrade (D : ArnoldiDecomp A b q) : q ≤ krylovGrade A b := D.graded.le_krylovGrade

/-- **`H_q` is upper Hessenberg**: `h_ij = 0` for `i > j + 1`, for every `A`.
Source: Saad (2003) [`saad03`], Prop. 6.5; Trefethen–Bau (1997) [`tb97`], Lect. 33.
atlas: arnoldi-def (partial)
@isnad1 id=eq.1h7v.s6.8431ddf7bb9e from=translated src=- shape=4436aa41 vocab=090bd75a
-/
theorem H_apply_eq_zero_of_add_one_lt (D : ArnoldiDecomp A b q) {i j : Fin q}
    (hij : (j : ℕ) + 1 < i) : D.H i j = 0 :=
  D.graded.transpose_mul_mul_apply_eq_zero hij

/-- **`H_q` is unreduced**: its subdiagonal entries `h_{j+1,j}` are nonzero.
Source: Saad (2003) [`saad03`], Prop. 6.6.
atlas: arnoldi-def (partial)
@isnad1 id=ne.1h6v.s6.e4a6540ab476 from=translated src=- shape=5e8c2539 vocab=7a203c22
-/
theorem H_succ_apply_ne_zero (D : ArnoldiDecomp A b q) {j : ℕ} (hj : j + 1 < q) :
    D.H ⟨j + 1, hj⟩ ⟨j, by omega⟩ ≠ 0 :=
  D.graded.transpose_mul_mul_apply_succ_ne_zero hj

/-- The leading `q' × q'` part of an Arnoldi decomposition: the first `q'` columns of `Q`.
Atlas: `graded-krylov-basis-def` (nesting).-/
def restrict (D : ArnoldiDecomp A b q) {q' : ℕ} (h : q' ≤ q) : ArnoldiDecomp A b q' where
  Q := D.Q.submatrix id (Fin.castLE h)
  graded := by
    refine IsGradedKrylovBasis.of_mem ?_ fun j => ?_
    · rw [hasOrthonormalCols_iff_conjTranspose_mul_self,
        Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j
      rw [transpose_mul_self_apply]
      change D.Q.col (Fin.castLE h i) ⬝ᵥ D.Q.col (Fin.castLE h j) = _
      rw [D.hasOrthonormalCols.col_dotProduct_col, Matrix.one_apply]
      simp [Fin.castLE_inj]
    · exact D.graded.col_mem (Fin.castLE h j)

/-- The basis of `D.restrict h` is the first `q'` columns of `D.Q`.
Atlas: `graded-krylov-basis-def`.
@isnad1 id=eq.1h6v.s6.64f2d3dc76fa from=translated src=- shape=7fb3581f vocab=244cc2d5
-/
theorem restrict_Q (D : ArnoldiDecomp A b q) {q' : ℕ} (h : q' ≤ q) :
    (D.restrict h).Q = D.Q.submatrix id (Fin.castLE h) := rfl

/-- **Nesting**: `H_{q'}` is the leading principal `q' × q'` submatrix of `H_q`.
Source: Saad (2011) [`saad11`], §6.3.
atlas: graded-krylov-basis-def (partial)
@isnad1 id=eq.1h6v.s6.30aaa758d115 from=translated src=- shape=dd645cad vocab=4e8c17e4
-/
theorem H_restrict (D : ArnoldiDecomp A b q) {q' : ℕ} (h : q' ≤ q) :
    (D.restrict h).H = D.H.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  rw [H_apply, Matrix.submatrix_apply, H_apply]
  rfl

/-- Columns of two decompositions agree up to a scalar: `q'_j = (q_j ⬝ q'_j) q_j`.
Atlas: `graded-krylov-basis-def`.
@isnad1 id=eq.0h7v.s6.46a1b930bf99 from=translated src=- shape=5b885bea vocab=48f929f5
-/
theorem col_eq_smul_col (D D' : ArnoldiDecomp A b q) (j : Fin q) :
    D'.Q.col j = (D.Q.col j ⬝ᵥ D'.Q.col j) • D.Q.col j := by
  have hmem : D'.Q.col j ∈ krylovSpace A b q :=
    krylovSpace_mono A b (by omega) (D'.graded.col_mem j)
  conv_lhs => rw [D.graded.eq_sum_of_mem hmem]
  refine Finset.sum_eq_single j (fun i _ hij => ?_) (by simp)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [dotProduct_comm, D'.graded.col_dotProduct_eq_zero j
      (krylovSpace_mono A b (by omega) (D.graded.col_mem i)), zero_smul]
  · rw [D.graded.col_dotProduct_eq_zero i
      (krylovSpace_mono A b (by omega) (D'.graded.col_mem j)), zero_smul]

/-- The scalar relating matching columns is a sign: `(q_j ⬝ q'_j)² = 1`.
Atlas: `graded-krylov-basis-def`.
@isnad1 id=eq.0h7v.s6.2471bbbd8841 from=translated src=- shape=21ba2f4d vocab=24bdf213
-/
theorem sq_col_dotProduct_col (D D' : ArnoldiDecomp A b q) (j : Fin q) :
    (D.Q.col j ⬝ᵥ D'.Q.col j) ^ 2 = 1 := by
  have h1 := D'.hasOrthonormalCols.col_dotProduct_col j j
  rw [ite_eq_left rfl, D.col_eq_smul_col D' j, smul_dotProduct, dotProduct_smul,
    D.hasOrthonormalCols.col_dotProduct_col, ite_eq_left rfl] at h1
  simpa [sq] using h1

/-- **Uniqueness up to signs**: two Arnoldi decompositions of the same size differ by a
diagonal `±1` matrix, `Q' = Q diag(s)`. Source: Saad (2003) [`saad03`], §6.3 (implicit-Q);
Trefethen–Bau (1997) [`tb97`], Lect. 33.
atlas: graded-krylov-basis-def (partial)
@isnad1 id=ex.0h6v.s6.5d1c54e4c2fc from=translated src=- shape=41b13e7a vocab=80859332
-/
theorem exists_sign (D D' : ArnoldiDecomp A b q) :
    ∃ s : Fin q → ℤˣ, D'.Q = D.Q * diagonal fun i => ((s i : ℤ) : ℝ) := by
  refine ⟨fun j => if 0 ≤ D.Q.col j ⬝ᵥ D'.Q.col j then 1 else -1, ?_⟩
  ext r j
  rw [Matrix.mul_diagonal]
  have hc : ((((if 0 ≤ D.Q.col j ⬝ᵥ D'.Q.col j then 1 else -1 : ℤˣ)) : ℤ) : ℝ) =
      D.Q.col j ⬝ᵥ D'.Q.col j := by
    have := D.sq_col_dotProduct_col D' j
    split_ifs with h
    · simp only [Units.val_one, Int.cast_one]
      nlinarith [sq_nonneg (D.Q.col j ⬝ᵥ D'.Q.col j - 1)]
    · simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
      nlinarith [sq_nonneg (D.Q.col j ⬝ᵥ D'.Q.col j + 1)]
  rw [hc, mul_comm]
  exact congrFun (D.col_eq_smul_col D' j) r

/-- **Positive normalisation fixes the decomposition**: two Arnoldi decompositions with
`q_1 ⬝ b > 0` and positive subdiagonal `h_{j+1,j} > 0` are equal. Source: Saad (2003)
[`saad03`], §6.3 (implicit-Q theorem; uniqueness of the Arnoldi basis); Trefethen–Bau (1997)
[`tb97`], Lect. 33. Deviation: the hypothesis is that both are graded bases (not only that
`Q̃ᵀ A Q̃` is Hessenberg with `Q̃ e₁ = b/‖b‖`).
atlas: arnoldi-def (partial)
@isnad1 id=eq.4h6v.s8.72bd0d188f14 from=translated src=- shape=4e872482 vocab=56071f01
-/
theorem Q_eq_of_pos (D D' : ArnoldiDecomp A b q)
    (h0 : ∀ hq : 0 < q, 0 < D.Q.col ⟨0, hq⟩ ⬝ᵥ b) (h0' : ∀ hq : 0 < q, 0 < D'.Q.col ⟨0, hq⟩ ⬝ᵥ b)
    (hH : ∀ j (hj : j + 1 < q), 0 < D.H ⟨j + 1, hj⟩ ⟨j, by omega⟩)
    (hH' : ∀ j (hj : j + 1 < q), 0 < D'.H ⟨j + 1, hj⟩ ⟨j, by omega⟩) : D'.Q = D.Q := by
  set s : Fin q → ℝ := fun j => D.Q.col j ⬝ᵥ D'.Q.col j
  have hs1 : ∀ j, 0 < s j → s j = 1 := fun j hj => by
    have := D.sq_col_dotProduct_col D' j
    nlinarith [sq_nonneg (s j - 1)]
  have hs : ∀ (j : ℕ) (hj : j < q), s ⟨j, hj⟩ = 1 := by
    intro j
    induction j with
    | zero =>
      intro hq
      refine hs1 _ ?_
      have h := h0' hq
      rw [D.col_eq_smul_col D', smul_dotProduct, smul_eq_mul] at h
      exact pos_of_mul_pos_left h (h0 hq).le
    | succ j ih =>
      intro hj
      refine hs1 _ ?_
      have h := hH' j hj
      rw [H_apply, D.col_eq_smul_col D', D.col_eq_smul_col D' ⟨j, by omega⟩,
        Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, ← H_apply,
        show D.Q.col ⟨j, by omega⟩ ⬝ᵥ D'.Q.col ⟨j, by omega⟩ = 1 from ih (by omega),
        one_smul, smul_eq_mul] at h
      exact pos_of_mul_pos_left h (hH j hj).le
  ext r j
  have h := congrFun (D.col_eq_smul_col D' j) r
  rw [show D.Q.col j ⬝ᵥ D'.Q.col j = 1 from hs j j.isLt, one_smul] at h
  exact h

end ArnoldiDecomp

namespace LanczosDecomp

variable {A : Matrix n n ℝ} {b : n → ℝ} {q : ℕ}

/-- The Jacobi matrix `T_q = Q_qᵀ A Q_q` of a Lanczos decomposition (the Hessenberg matrix `H_q`
under its Lanczos name). Source: Golub–Meurant (2010) [`gm10`], Ch. 4.
atlas: lanczos-recurrence-/
abbrev T (D : LanczosDecomp A b q) : Matrix (Fin q) (Fin q) ℝ := ArnoldiDecomp.H D

/-- For symmetric `A`, `T_q` is symmetric. Atlas: `lanczos-recurrence`.
@isnad1 id=issymm.1h5v.s6.59d38c2ace28 from=translated src=- shape=582a6537 vocab=e3163c9a
-/
theorem isSymm_T (D : LanczosDecomp A b q) (hA : A.IsHermitian) : D.T.IsSymm :=
  Matrix.isHermitian_iff_isSymm.mp (Matrix.isHermitian_conjTranspose_mul_mul D.Q hA)

/-- **For symmetric `A`, `T_q` is tridiagonal**: `t_ij = 0` whenever `|i − j| > 1`.
Source: Golub–Meurant (2010) [`gm10`], Thm 4.2; Trefethen–Bau (1997) [`tb97`], Lect. 36.
atlas: lanczos-recurrence, graded-krylov-basis-def (partial)
@isnad1 id=eq.2h7v.s6.95a8a8cd02d7 from=translated src=- shape=8c024173 vocab=2fbaf896
-/
theorem T_apply_eq_zero_of_one_lt_dist (D : LanczosDecomp A b q) (hA : A.IsHermitian) {i j : Fin q}
    (hij : 1 < |(i : ℤ) - j|) : D.T i j = 0 := by
  rcases lt_abs.1 hij with h | h
  · exact D.H_apply_eq_zero_of_add_one_lt (by omega)
  · rw [← (D.isSymm_T hA).apply i j]
    exact D.H_apply_eq_zero_of_add_one_lt (by omega)

end LanczosDecomp

end NLAlib
