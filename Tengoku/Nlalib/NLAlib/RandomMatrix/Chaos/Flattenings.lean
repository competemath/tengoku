import Tengoku.Nlalib.NLAlib.Matrix.Norms.Reindex
import Tengoku.Seed.Data.Fintype.Powerset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite coefficient flattenings for matrix chaos

Every flattening is an ordinary matrix with disjoint row and column coordinate
sets. Empty coordinate sets have a singleton function space. No tensor-product
or overlapping-coordinate convention is involved.

Source: Bandeira–Lucca–Nizić-Nikolac–van Handel, §§2.1–2.2;
`matrix-chaos-flattenings-def`.
-/

noncomputable section

namespace NLAlib

variable {τ ι m n 𝕜 : Type*} [Fintype τ] [DecidableEq τ]

/-- Assemble the two disjoint coordinate groups of a finite chaos flattening.
atlas: matrix-chaos-flattenings-def (partial)-/
def chaosAssemble (S : Finset τ) (x : S → ι) (y : (Sᶜ : Finset τ) → ι) : τ → ι :=
  fun t => if ht : t ∈ S then x ⟨t, ht⟩ else y ⟨t, Finset.mem_compl.mpr ht⟩

/-- The assembled tuple restricts to its row coordinates.
@isnad1 id=eq.0h6v.s6.48e84599781e from=translated src=- shape=443a90fa vocab=47e96e6f
-/
@[simp] theorem chaosAssemble_row (S : Finset τ) (x : S → ι)
    (y : (Sᶜ : Finset τ) → ι) (t : S) : chaosAssemble S x y t = x t := by
  simp [chaosAssemble, t.property]

/-- The assembled tuple restricts to its column coordinates.
@isnad1 id=eq.0h6v.s7.d6b405004734 from=translated src=- shape=3620741a vocab=47e96e6f
-/
@[simp] theorem chaosAssemble_col (S : Finset τ) (x : S → ι)
    (y : (Sᶜ : Finset τ) → ι) (t : (Sᶜ : Finset τ)) : chaosAssemble S x y t = y t := by
  simp [chaosAssemble, Finset.mem_compl.mp t.property]

/-- Splitting a tuple and then assembling it recovers that tuple.
@isnad1 id=eq.0h4v.s6.6ac70dfad440 from=translated src=- shape=2037a7c6 vocab=47e96e6f
-/
@[simp] theorem chaosAssemble_restrict (S : Finset τ) (z : τ → ι) :
    chaosAssemble S (fun t => z t) (fun t => z t) = z := by
  funext t
  simp [chaosAssemble]

/-- Splitting a tuple into complementary coordinate groups is a genuine bijection.
atlas: matrix-chaos-flattenings-def (partial)-/
def chaosSplitEquiv (S : Finset τ) : (τ → ι) ≃ (S → ι) × ((Sᶜ : Finset τ) → ι) where
  toFun z := (fun t => z t, fun t => z t)
  invFun z := chaosAssemble S z.1 z.2
  left_inv := chaosAssemble_restrict S
  right_inv z := by ext t <;> simp

/-- The variance flattening places the original matrix row and column on opposite
sides. Source: Bandeira–Lucca–Nizić-Nikolac–van Handel, equations (1)–(4).
atlas: matrix-chaos-flattenings-def-/
def chaosFlattening (A : (τ → ι) → Matrix m n 𝕜) (S : Finset τ) :
    Matrix ((S → ι) × m) ((((Sᶜ : Finset τ) → ι)) × n) 𝕜 :=
  fun x y => A (chaosAssemble S x.1 y.1) x.2 y.2

/-- The covariance flattening places both original matrix coordinates in the
column index. Its parameter uses only nonempty row subsets.
Source: Bandeira–Lucca–Nizić-Nikolac–van Handel, parameter (5).
atlas: matrix-chaos-flattenings-def-/
def chaosCovarianceFlattening (A : (τ → ι) → Matrix m n 𝕜) (S : Finset τ) :
    Matrix (S → ι) ((((Sᶜ : Finset τ) → ι)) × (m × n)) 𝕜 :=
  fun x y => A (chaosAssemble S x y.1) y.2.1 y.2.2

/-- The matrix chaos with independent coordinate groups; equal index values in
different groups are retained. Independence and laws enter its probability theorems.
Source: Bandeira–Lucca–Nizić-Nikolac–van Handel, equation (1).
atlas: matrix-chaos-flattenings-def-/
def decoupledMatrixChaos [Fintype ι] [AddCommMonoid 𝕜]
    [SMul ℝ 𝕜] (A : (τ → ι) → Matrix m n 𝕜) (h : τ → ι → ℝ) :
    Matrix m n 𝕜 := ∑ z, (∏ t, h t (z t)) • A z

/-- The coupled matrix chaos uses the same coordinate vector in every factor.
atlas: matrix-chaos-flattenings-def (partial)-/
def coupledMatrixChaos [Fintype ι] [AddCommMonoid 𝕜]
    [SMul ℝ 𝕜] (A : (τ → ι) → Matrix m n 𝕜) (h : ι → ℝ) :
    Matrix m n 𝕜 := decoupledMatrixChaos A (fun _ => h)

variable [Fintype ι] [Fintype m] [Fintype n] [DecidableEq ι]
  [DecidableEq m] [DecidableEq n] [RCLike 𝕜]

/-- The maximum spectral norm over all variance flattenings, including the two
extreme subsets. Source: Bandeira–Lucca–Nizić-Nikolac–van Handel, equation (4).
atlas: matrix-chaos-flattenings-def-/
def chaosSigma (A : (τ → ι) → Matrix m n 𝕜) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun S => specNorm (chaosFlattening A S))

/-- The maximum covariance-flattening norm over nonempty row subsets. For zero
degree the parameter is zero. Source: Bandeira–Lucca–Nizić-Nikolac–van Handel,
parameter (5).
atlas: matrix-chaos-flattenings-def-/
def chaosCovariance (A : (τ → ι) → Matrix m n 𝕜) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun S => if S = ∅ then 0 else specNorm (chaosCovarianceFlattening A S))

/-- Every variance flattening is bounded by the common variance parameter.
@isnad1 id=le.0h7v.s9.4c2651fc8c54 from=translated src=- shape=d2dfecf9 vocab=71716460
-/
theorem specNorm_chaosFlattening_le (A : (τ → ι) → Matrix m n 𝕜) (S : Finset τ) :
    specNorm (chaosFlattening A S) ≤ chaosSigma A := by
  exact Finset.le_sup' (fun T => specNorm (chaosFlattening A T)) (Finset.mem_univ S)

/-- Every covariance flattening with nonempty row coordinates is bounded by the
common covariance parameter.
@isnad1 id=le.1h7v.s9.f91f37970a9c from=translated src=- shape=1e86f098 vocab=f345d346
-/
theorem specNorm_chaosCovarianceFlattening_le (A : (τ → ι) → Matrix m n 𝕜)
    (S : Finset τ) (hS : S.Nonempty) :
    specNorm (chaosCovarianceFlattening A S) ≤ chaosCovariance A := by
  have h := Finset.le_sup'
    (fun T : Finset τ => if T = ∅ then 0 else specNorm (chaosCovarianceFlattening A T))
    (Finset.mem_univ S)
  change specNorm (chaosCovarianceFlattening A S) ≤
    Finset.univ.sup' Finset.univ_nonempty
      (fun T => if T = ∅ then 0 else specNorm (chaosCovarianceFlattening A T))
  simpa only [ite_eq_right hS.ne_empty] using h

/-- The variance parameter is nonnegative, including empty matrix dimensions.
@isnad1 id=le.0h6v.s6.29f6dd9cd200 from=translated src=- shape=af2e2abe vocab=c848d576
-/
theorem chaosSigma_nonneg (A : (τ → ι) → Matrix m n 𝕜) : 0 ≤ chaosSigma A :=
  (specNorm_nonneg _).trans (specNorm_chaosFlattening_le A ∅)

/-- The covariance parameter is nonnegative, including degree zero.
@isnad1 id=le.0h6v.s6.edb3494ac7e9 from=translated src=- shape=af2e2abe vocab=3f3a4090
-/
theorem chaosCovariance_nonneg (A : (τ → ι) → Matrix m n 𝕜) :
    0 ≤ chaosCovariance A := by
  have h := Finset.le_sup'
    (fun T : Finset τ => if T = ∅ then 0 else specNorm (chaosCovarianceFlattening A T))
    (Finset.mem_univ (∅ : Finset τ))
  change 0 ≤ Finset.univ.sup' Finset.univ_nonempty
    (fun T => if T = ∅ then 0 else specNorm (chaosCovarianceFlattening A T))
  simp only [ite_true] at h
  exact h

/-- A bound for all variance flattenings bounds their maximum.
@isnad1 id=le.1h7v.s9.194e4cdfc64c from=translated src=- shape=0c0d8086 vocab=71716460
-/
theorem chaosSigma_le (A : (τ → ι) → Matrix m n 𝕜) {c : ℝ}
    (h : ∀ S, specNorm (chaosFlattening A S) ≤ c) : chaosSigma A ≤ c :=
  Finset.sup'_le _ _ (fun S _ => h S)

/-- A nonnegative bound for the nonempty covariance flattenings bounds their
maximum. This includes the zero-degree convention.
@isnad1 id=le.2h7v.s9.4fb41febb618 from=translated src=- shape=78d4ea56 vocab=f345d346
-/
theorem chaosCovariance_le (A : (τ → ι) → Matrix m n 𝕜) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ S, S.Nonempty → specNorm (chaosCovarianceFlattening A S) ≤ c) :
    chaosCovariance A ≤ c := by
  apply Finset.sup'_le
  intro S _
  split_ifs with hS
  · exact hc
  · exact h S (Finset.nonempty_iff_ne_empty.mpr hS)

/-- The number of variance-flattening rows is the original number of rows times
one coordinate-cardinality factor for every selected mode.
atlas: matrix-chaos-flattenings-def (partial)
@isnad1 id=eq.0h4v.s7.f71476be6978 from=translated src=- shape=b70c0635 vocab=82160f8a
-/
theorem card_chaosFlattening_rows (S : Finset τ) :
    Fintype.card ((S → ι) × m) = Fintype.card m * Fintype.card ι ^ S.card := by
  simp [Fintype.card_fun, Nat.mul_comm]

/-- The number of columns uses precisely the complementary modes.
atlas: matrix-chaos-flattenings-def (partial)
@isnad1 id=eq.0h4v.s8.abdfcbe48d6a from=translated src=- shape=e8cb1283 vocab=54bd5896
-/
theorem card_chaosFlattening_cols (S : Finset τ) :
    Fintype.card ((((Sᶜ : Finset τ) → ι)) × n) =
      Fintype.card n * Fintype.card ι ^ (Fintype.card τ - S.card) := by
  simp [Fintype.card_fun, Nat.mul_comm, Finset.card_compl]

/-- Changing the ordering of either flattened coordinate set preserves the norm.
Source: finite permutation isometries.
atlas: matrix-chaos-flattenings-def (partial)
@isnad1 id=eq.0h11v.s10.202997fe1a1d from=translated src=- shape=d95e8b3a vocab=8b9a2e1b
-/
theorem specNorm_chaosFlattening_reindex {p r : Type*} [Fintype p] [Fintype r]
    [DecidableEq p] [DecidableEq r] (A : (τ → ι) → Matrix m n 𝕜) (S : Finset τ)
    (e : ((S → ι) × m) ≃ p) (f : ((((Sᶜ : Finset τ) → ι)) × n) ≃ r) :
    specNorm ((chaosFlattening A S).reindex e f) = specNorm (chaosFlattening A S) :=
  specNorm_reindex _ _ _

end NLAlib
