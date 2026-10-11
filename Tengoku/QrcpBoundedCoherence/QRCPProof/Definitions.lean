import Tengoku
import Tengoku.QrcpBoundedCoherence.QRCPProof.GammaAux

/-! # QRCP Definitions

This file formalizes the exact residual-projector QRCP definitions from the blueprint.

## Naming Conventions

| Blueprint | Lean Identifier | Description |
|-----------|----------------|-------------|
| A = Qᵀ | `AMatrix Q` | The transpose matrix |
| a_i | `columnA Q i` | Column i of A = Qᵀ (row i of Q) |
| span(S) | `prefixSpan Q S` | Span of selected columns |
| P_S | `orthogonalProjector Q S` | Orthogonal projection onto span(S) |
| R_i(S) | `residualScore Q i S` | Squared residual score |
| I_piv | `pivots` (parameter) | Pivot sequence |
| M(Q) | `selectedMatrix Q pivots` | Selected submatrix |
| γ(Q, I_piv) | `gamma Q pivots h` | Inverse operator norm |
| μ(Q) | `mu Q` | Normalized row coherence |

## Key Design Decisions

1. **Vectors in ℝᵏ**: Matrix columns are `Fin k → ℝ`. For inner product operations,
   we convert to `EuclideanSpace ℝ (Fin k)` via `colToEuclidean`.

2. **Orthogonal projector**: Defined using `Submodule.orthogonalProjection`.
   In finite dimensions (EuclideanSpace), the HasOrthogonalProjection instance
   is automatic via `Submodule.HasOrthogonalProjection.ofCompleteSpace`.

3. **Pivot sequence**: Defined as a *property* (`IsQRCPPivotSequence`) rather than
   a recursive construction. This avoids the complexity of argmax with tie-breaking
   in definitions while still capturing the mathematical content.

4. **Gamma (inverse-norm)**: Computed as the operator norm of the continuous
   linear map corresponding to M(Q)⁻¹, via `Matrix.toEuclideanCLM`.

5. **Mu (coherence)**: Computed directly from matrix entries as
   `(n/k) * sup_i ∑_j (Q i j)²`.
-/

noncomputable section QRCPDefinitions

-- ============================================================
-- Section 1: Matrix Setup
-- ============================================================

variable {n k : ℕ}

/-- `A = Qᵀ`, the transpose of `Q`.

The columns of `A` are denoted `a_i ∈ ℝ^k` for `i = 1, ..., n`.
Equivalently, `a_i` is the transpose of row `i` of `Q`. -/
def AMatrix (Q : Matrix (Fin n) (Fin k) ℝ) : Matrix (Fin k) (Fin n) ℝ :=
  Q.transpose

/-- Column `a_i` of `A = Qᵀ`, which is row `i` of `Q` transposed.

Returns a vector in `ℝ^k` (as `Fin k → ℝ`). -/
def columnA (Q : Matrix (Fin n) (Fin k) ℝ) (i : Fin n) : Fin k → ℝ :=
  (AMatrix Q).col i

/-- Convert a column vector (`Fin k → ℝ`) to `EuclideanSpace ℝ (Fin k)`.

This gives the vector the `l²` inner product structure needed for
orthogonal projection. `EuclideanSpace ℝ (Fin k)` is `WithLp 2 (Fin k → ℝ)`. -/
def colToEuclidean {k : ℕ} (v : Fin k → ℝ) : EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm v

-- ============================================================
-- Section 2: Prefix Span and Orthogonal Projector
-- ============================================================

/-- The prefix span: span of selected columns `{a_s : s ∈ S}`.

`S` is an ordered prefix of selected labels. The span is taken in
`EuclideanSpace ℝ (Fin k)` so that orthogonal projection is well-defined. -/
def prefixSpan (Q : Matrix (Fin n) (Fin k) ℝ) (S : List (Fin n)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin k)) :=
  Submodule.span ℝ {colToEuclidean (columnA Q s) | s ∈ S}

/-- The orthogonal projector `P_S` onto `span(S)`.

If `S` is empty, `P_S = 0` (the zero linear map).
Otherwise, `P_S` is the orthogonal projection onto the span of selected columns,
composed with the subtype inclusion back into the ambient space.

In finite dimensions, every submodule of a complete inner product space has
an orthogonal projection (instance `Submodule.HasOrthogonalProjection.ofCompleteSpace`). -/
def orthogonalProjector (Q : Matrix (Fin n) (Fin k) ℝ) (S : List (Fin n)) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
  if _h : S = [] then
    0
  else
    let V := prefixSpan Q S
    have : V.HasOrthogonalProjection := by
      infer_instance
    V.subtype.comp (V.orthogonalProjectionOnto : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] V)

-- ============================================================
-- Section 3: Residual Score
-- ============================================================

/-- Squared residual score `R_i(S) = ‖(I_k - P_S) a_i‖₂²`.

For an unselected label `i`, this is the squared Euclidean norm of the
residual after orthogonally projecting `a_i` onto the span of selected columns. -/
def residualScore (Q : Matrix (Fin n) (Fin k) ℝ) (i : Fin n) (S : List (Fin n)) : ℝ :=
  let a_i := colToEuclidean (columnA Q i)
  let P_S := orthogonalProjector Q S
  let residual := a_i - P_S a_i
  ‖residual‖ ^ 2

-- ============================================================
-- Section 4: QRCP Pivot Sequence
-- ============================================================

/-- Build the prefix list from pivots up to index `t` (exclusive).

That is, `[pivots[0], pivots[1], ..., pivots[t-1]]`.
For `t > k`, the list is truncated at `k` elements. -/
def pivotPrefix (pivots : Fin k → Fin n) : ℕ → List (Fin n)
  | 0 => []
  | t+1 =>
    if h : t < k then
      pivotPrefix pivots t ++ [pivots ⟨t, h⟩]
    else
      pivotPrefix pivots t

/-- A pivot sequence satisfies the QRCP pivot rule if at each step `t < k`:

1. `pivots[t]` is not in the previous prefix (no repeats);
2. `pivots[t]` has maximal residual score among unselected labels;
3. Tie-breaking: if equal score, then `pivots[t]` has the smallest original label.

The blueprint notes: "The construction below actually proves strict inequalities
at every pivot step, so tie-breaking is not needed for the chosen pivots." -/
def IsQRCPPivotSequence (Q : Matrix (Fin n) (Fin k) ℝ) (pivots : Fin k → Fin n) : Prop :=
  ∀ (t : Fin k),
    let S_t := pivotPrefix pivots t.val
    ¬(pivots t ∈ S_t) ∧
    ∀ (i : Fin n), ¬(i ∈ S_t) →
      residualScore Q i S_t ≤ residualScore Q (pivots t) S_t ∧
      (residualScore Q i S_t = residualScore Q (pivots t) S_t → (pivots t).val ≤ i.val)

-- ============================================================
-- Section 5: Selected Matrix and Inverse-Norm
-- ============================================================

/-- Selected matrix `M(Q) = Q(I_piv, :) ∈ ℝ^{k×k}`.

Extracts rows of `Q` at the pivot indices. If `pivots : Fin k → Fin n`
maps step index to original label, then `M(Q)_{t,j} = Q_{pivots[t], j}`. -/
def selectedMatrix (Q : Matrix (Fin n) (Fin k) ℝ) (pivots : Fin k → Fin n) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.submatrix Q pivots id

/-- Inverse-norm `γ(Q, I_piv) = ‖M(Q)^{-1}‖₂`.

The operator (spectral) norm of the inverse of the selected matrix.
Computed as the operator norm of the corresponding continuous linear map
(via `Matrix.toEuclideanCLM`).

Requires `M(Q)` to be nonsingular (provided by the `Invertible` instance). -/
noncomputable def gamma (Q : Matrix (Fin n) (Fin k) ℝ) (pivots : Fin k → Fin n)
    [DecidableEq (Fin k)] (_hNonsingular : Invertible (selectedMatrix Q pivots)) : ℝ :=
  ‖(Matrix.toEuclideanCLM.toFun (selectedMatrix Q pivots)⁻¹)‖

/-- Alternative formulation of `gamma` via the smallest eigenvalue.

If `G_I = M(Q)ᵀ M(Q)`, then `γ(Q, I_piv) = 1 / √(λ_min(G_I))`.
This is stated as a theorem to be proved later.

Mathematical proof sketch:
  Let `M = selectedMatrix Q pivots`, `G = MᴴM` (PSD Hermitian, invertible since `M` is).
  σ_min(M) = smallest singular value of M, σ_min(M)² = λ_min(G).
  For invertible M, the operator norm identity
    ‖M⁻¹‖ = 1 / σ_min(M)
  gives ‖M⁻¹‖² = 1 / λ_min(G), hence ‖M⁻¹‖ = 1 / √(λ_min(G)).

  Proved via `norm_inv_eq_inv_sqrt_min_eigenvalue` from GammaAux.lean. -/
theorem gamma_eq_inv_sqrt_min_eigenvalue
    (Q : Matrix (Fin n) (Fin k) ℝ) (pivots : Fin k → Fin n)
    [DecidableEq (Fin k)] [Nonempty (Fin k)] (hNonsingular : Invertible (selectedMatrix Q pivots)) :
    gamma Q pivots hNonsingular =
      1 / Real.sqrt (⨅ (i : Fin k), (Matrix.isHermitian_conjTranspose_mul_self
        (selectedMatrix Q pivots)).eigenvalues i) := by
  -- Abbreviation for the selected matrix.
  set M : Matrix (Fin k) (Fin k) ℝ := selectedMatrix Q pivots with hM_def
  -- The Gram matrix `Mᴴ * M` is Hermitian (PSD, in fact PD since M is invertible).
  have hH : (M.conjTranspose * M).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self M
  -- Reduce to the spectral identity in GammaAux.lean.
  simp only [gamma]
  rw [← hM_def]
  exact norm_inv_eq_inv_sqrt_min_eigenvalue M

-- ============================================================
-- Section 6: Normalized Row Coherence
-- ============================================================

/-- Normalized row coherence `μ(Q) = (n/k) * max_i ‖Q(i,:)‖₂²`.

Equivalently `(n/k) * max_i ‖a_i‖₂²` since rows of `Q` are columns of `A`.
Computed directly from matrix entries as `(n/k) * sup_i ∑_j (Q i j)²`. -/
def mu (Q : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  (n / k : ℝ) * ⨆ (i : Fin n), ∑ (j : Fin k), (Q i j) ^ 2

-- ============================================================
-- Section 7: Existence of QRCP Pivot Sequence (to be proved)
-- ============================================================

end QRCPDefinitions
