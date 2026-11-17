import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Algebra.PolynomialIdentity
import Tengoku.Seed.LinearAlgebra.Multilinear.Basic
import Tengoku.Seed.Algebra.Module.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Full polarization over an infinite field

The coefficients of the diagonal of a multilinear map are the sums of its values over
coordinate selections with fixed multiplicities. Over an infinite field the identity
principle for vector polynomials (Lemma B.6) recovers every such sum from the diagonal.
No factorial is divided out, and the map need not be symmetric.
-/

noncomputable section

namespace Polarization

variable {J : Type*} [Fintype J] {k : ℕ}

/-- The multiplicity of each label in a coordinate selection map.-/
def selectionType (f : Fin k → J) (j : J) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => f i = j)).card

/-- The multiplicities of a selection map as a multi-index.-/
def selectionMultiIndex (f : Fin k → J) : J →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (selectionType f)

/--
@isnad1 id=eq.0h4v.s5.eb1afa82a5a2 from=translated src=- shape=c1ee2384 vocab=e39cb9f2
-/
@[simp]
theorem selectionMultiIndex_apply (f : Fin k → J) (j : J) :
    selectionMultiIndex f j = selectionType f j := by
  simp [selectionMultiIndex]

/--
@isnad1 id=iff.0h4v.s6.922ee8e7f44b from=translated src=- shape=cc61e1b6 vocab=14db2242
-/
@[simp]
theorem selectionMultiIndex_eq_iff (f : Fin k → J) (α : J → ℕ) :
    selectionMultiIndex f = Finsupp.equivFunOnFinite.symm α ↔ selectionType f = α := by
  exact Finsupp.equivFunOnFinite.symm.injective.eq_iff

/-- The multiplicities of a selection map sum to `k`.
@isnad1 id=eq.0h3v.s4.227468c3174c from=translated src=- shape=df05cbc6 vocab=f71ba327
-/
theorem sum_selectionType (f : Fin k → J) : ∑ j, selectionType f j = k := by
  classical
  simpa [selectionType] using
    (Finset.sum_fiberwise' (Finset.univ : Finset (Fin k)) f (fun _ => (1 : ℕ)))

/-- The monomial indexed by a selection type is the product of its selected scalars.
@isnad1 id=eq.0h5v.s6.b54892394adf from=translated src=- shape=346723e3 vocab=be841d03
-/
theorem monomial_selectionMultiIndex {K : Type*} [CommMonoid K]
    (f : Fin k → J) (t : J → K) :
    (selectionMultiIndex f).prod (fun j n => t j ^ n) = ∏ i, t (f i) := by
  classical
  rw [Finsupp.prod_pow]
  simpa [selectionType] using
    (Finset.prod_fiberwise' (Finset.univ : Finset (Fin k)) f t)

end Polarization

namespace MultilinearMap

variable {K A Y J : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup Y] [Module K Y]
  [Fintype J] {k : ℕ}

open scoped Classical

/-- The sum of `M (b ∘ f)` over selection maps `f` with multiplicities `α`.-/
def sumOfType (M : MultilinearMap K (fun _ : Fin k => A) Y)
    (b : J → A) (α : J → ℕ) : Y := by
  classical
  exact ∑ f ∈ Finset.univ.filter (fun f : Fin k → J => Polarization.selectionType f = α),
    M (fun i => b (f i))

/-- The coefficients of `t ↦ M (fun _ => ∑ j, t j • b j)`, obtained by grouping the
multilinear expansion by multiplicity.-/
def diagonalCoefficients (M : MultilinearMap K (fun _ : Fin k => A) Y)
    (b : J → A) : (J →₀ ℕ) →₀ Y := by
  classical
  exact ∑ f : Fin k → J,
    Finsupp.single (Polarization.selectionMultiIndex f) (M (fun i => b (f i)))

/-- The coefficient at `α` is `sumOfType M b α`.
@isnad1 id=eq.0h8v.s7.c223ba2eb535 from=translated src=- shape=c494e372 vocab=12a827cd
-/
theorem diagonalCoefficients_apply (M : MultilinearMap K (fun _ : Fin k => A) Y)
    (b : J → A) (α : J → ℕ) :
    M.diagonalCoefficients b (Finsupp.equivFunOnFinite.symm α) = M.sumOfType b α := by
  classical
  simp only [diagonalCoefficients, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Polarization.selectionMultiIndex_eq_iff, sumOfType, Finset.sum_filter]

/-- Evaluating the coefficient family at `t` gives the diagonal at `∑ j, t j • b j`.
@isnad1 id=eq.0h8v.s8.3dbc1ccf03ff from=translated src=- shape=9b68dae1 vocab=4beab856
-/
theorem eval_diagonalCoefficients (M : MultilinearMap K (fun _ : Fin k => A) Y)
    (b : J → A) (t : J → K) :
    VectorPolynomial.eval (M.diagonalCoefficients b) t = M (fun _ => ∑ j, t j • b j) := by
  classical
  unfold VectorPolynomial.eval diagonalCoefficients
  rw [← Finsupp.sum_finsetSum_index (fun _ => smul_zero _)
    (fun _ _ _ => smul_add _ _ _)]
  simp only [Finsupp.sum_single_index, smul_zero, Polarization.monomial_selectionMultiIndex]
  rw [M.map_sum]
  exact Finset.sum_congr rfl fun f _ => (M.map_smul_univ _ _).symm

/-- Grouped sums vanish unless the multiplicities sum to `k`.
@isnad1 id=eq.1h8v.s7.919a6e60b338 from=translated src=- shape=b3d4d969 vocab=df8b43c7
-/
theorem sumOfType_eq_zero_of_sum_ne (M : MultilinearMap K (fun _ : Fin k => A) Y)
    (b : J → A) (α : J → ℕ) (hα : ∑ j, α j ≠ k) : M.sumOfType b α = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro f hf
  have h := (Finset.mem_filter.mp hf).2
  exact False.elim (hα (h ▸ Polarization.sum_selectionType f))

/-- A one-label grouped coefficient is the original diagonal value.
@isnad1 id=eq.0h6v.s7.a42919003d89 from=translated src=- shape=a558d39e vocab=4c10827e
-/
@[simp]
theorem sumOfType_unit (M : MultilinearMap K (fun _ : Fin k => A) Y) (a : A) :
    M.sumOfType (fun _ : Unit => a) (fun _ => k) = M (fun _ => a) := by
  classical
  have htype (f : Fin k → Unit) : Polarization.selectionType f = fun _ => k := by
    funext j
    simp [Polarization.selectionType]
  simp [sumOfType, htype]

/-- Over any field, equal one-label grouped sums give equal diagonals.
@isnad1 id=eq.1h7v.s8.067dff581bc5 from=translated src=- shape=35b44c22 vocab=4c10827e
-/
theorem diagonal_eq_of_sumOfType_eq
    (M N : MultilinearMap K (fun _ : Fin k => A) Y)
    (h : ∀ (b : Unit → A) (α : Unit → ℕ), M.sumOfType b α = N.sumOfType b α)
    (a : A) : M (fun _ => a) = N (fun _ => a) := by
  simpa only [sumOfType_unit] using h (fun _ => a) (fun _ => k)

end MultilinearMap
