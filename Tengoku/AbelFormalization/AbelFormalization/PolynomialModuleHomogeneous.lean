import Tengoku.AbelFormalization.AbelFormalization.PolynomialModuleLeadingTerm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Actual shifted weighted homogeneous components of polynomial modules

Components are actual coefficient filters. In particular, extracting the
degree of an actual leading term preserves that
term, irrespective of whether the module term order compares degrees first.
-/

noncomputable section

namespace AbelFormalization

variable {K : Type*} [Field K] {n r : ℕ}

/-- The shifted weighted component, constructed from the actual coefficient array.-/
def weightedPolynomialModuleComponent (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) :
    (Fin r → MvPolynomial (Fin n) K) →ₗ[K] (Fin r → MvPolynomial (Fin n) K) := by
  classical
  exact
    { toFun := fun P => polynomialModuleCoeffEquiv.symm
        ((polynomialModuleCoeffEquiv P).filter
          (fun t => shiftedModuleMonomialDegree weight shift t = degree))
      map_add' := by
        intro P Q
        simp only [map_add, Finsupp.filter_add]
      map_smul' := by
        intro c P
        simp only [map_smul, Finsupp.filter_smul, RingHom.id_apply] }

/--
@isnad1 id=eq.0h9v.s9.068e99ce5a3e from=translated src=- shape=eee41504 vocab=d40d4916
-/
theorem weightedPolynomialModuleComponent_coeff (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (P : Fin r → MvPolynomial (Fin n) K)
    (k : Fin r) (d : Fin n →₀ ℕ) :
    (weightedPolynomialModuleComponent weight shift degree P k).coeff d =
      if shiftedModuleMonomialDegree weight shift (k, d) = degree then (P k).coeff d else 0 := by
  classical
  change polynomialModuleCoeffEquiv (weightedPolynomialModuleComponent weight shift degree P)
    (k, d) = _
  change polynomialModuleCoeffEquiv (polynomialModuleCoeffEquiv.symm
    ((polynomialModuleCoeffEquiv P).filter
      (fun t => shiftedModuleMonomialDegree weight shift t = degree))) (k, d) = _
  rw [LinearEquiv.apply_symm_apply, Finsupp.filter_apply]
  rfl

/--
@isnad1 id=iff.0h7v.s8.7d4ad34c8ba5 from=translated src=- shape=94cd39ea vocab=aa670748
-/
theorem mem_weightedPolynomialModulePiece_iff (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (P : Fin r → MvPolynomial (Fin n) K) :
    P ∈ weightedPolynomialModulePiece weight shift degree ↔
      ∀ k d, (P k).coeff d ≠ 0 →
        shiftedModuleMonomialDegree weight shift (k, d) = degree :=
  mem_polynomialModuleSupported _ P

/--
@isnad1 id=mem.0h7v.s9.84fd1cb7988a from=translated src=- shape=0d8eb122 vocab=6b5c17d7
-/
theorem weightedPolynomialModuleComponent_mem (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (degree : ℤ) (P : Fin r → MvPolynomial (Fin n) K) :
    weightedPolynomialModuleComponent weight shift degree P ∈
      weightedPolynomialModulePiece weight shift degree := by
  classical
  apply (mem_weightedPolynomialModulePiece_iff weight shift degree _).mpr
  intro k d hcoeff
  by_contra hdegree
  exact hcoeff (by rw [weightedPolynomialModuleComponent_coeff, ite_eq_right hdegree])

/--
@isnad1 id=eq.1h7v.s9.590831f810bb from=translated src=- shape=b0cbafe4 vocab=6b5c17d7
-/
theorem weightedPolynomialModuleComponent_eq_self (weight : Fin n → ℕ)
    (shift : Fin r → ℤ) (degree : ℤ)
    {P : Fin r → MvPolynomial (Fin n) K}
    (hP : P ∈ weightedPolynomialModulePiece weight shift degree) :
    weightedPolynomialModuleComponent weight shift degree P = P := by
  classical
  funext k
  apply MvPolynomial.ext
  intro d
  rw [weightedPolynomialModuleComponent_coeff]
  by_cases hd : shiftedModuleMonomialDegree weight shift (k, d) = degree
  · exact ite_eq_left hd
  · rw [ite_eq_right hd]
    by_contra hcoeff
    exact hd ((mem_weightedPolynomialModulePiece_iff weight shift degree P).mp hP k d
      (Ne.symm hcoeff))

/-- Ordinary homogeneity means closure under the actual shifted weighted
component projections. No condition about initial terms is included.-/
def IsWeightedPolynomialModuleHomogeneous (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (N : Submodule (MvPolynomial (Fin n) K) (Fin r → MvPolynomial (Fin n) K)) : Prop :=
  ∀ P ∈ N, ∀ degree : ℤ, weightedPolynomialModuleComponent weight shift degree P ∈ N

/-- Projecting to the degree of a leading term preserves its coefficient
and discards only other terms, so it preserves the actual leading term.
@isnad1 id=ispolyno.1h8v.s9.58dd43268c58 from=translated src=- shape=1428d084 vocab=82e971d1
-/
theorem IsPolynomialModuleLeadingTerm.weightedComponent
    {m : MonomialOrder (Fin n)} {P : Fin r → MvPolynomial (Fin n) K}
    {t : Fin r × (Fin n →₀ ℕ)} (hP : IsPolynomialModuleLeadingTerm m P t)
    (weight : Fin n → ℕ) (shift : Fin r → ℤ) :
    IsPolynomialModuleLeadingTerm m
      (weightedPolynomialModuleComponent weight shift
        (shiftedModuleMonomialDegree weight shift t) P) t := by
  classical
  constructor
  · rw [weightedPolynomialModuleComponent_coeff, ite_eq_left rfl]
    exact hP.1
  · intro u hu
    apply hP.2 u
    intro hzero
    apply hu
    simp [weightedPolynomialModuleComponent_coeff, hzero]

/-- Every leading term of a homogeneous submodule has an actual homogeneous
witness of exactly its own shifted weighted degree.
@isnad1 id=ex.3h9v.s10.4e4a8552c58b from=translated src=- shape=8d0a17cd vocab=5f2e5c52
-/
theorem exists_homogeneous_polynomialModuleLeadingTerm
    (m : MonomialOrder (Fin n)) (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (N : Submodule (MvPolynomial (Fin n) K) (Fin r → MvPolynomial (Fin n) K))
    (hN : IsWeightedPolynomialModuleHomogeneous weight shift N)
    {P : Fin r → MvPolynomial (Fin n) K} (hPN : P ∈ N)
    {t : Fin r × (Fin n →₀ ℕ)} (hP : IsPolynomialModuleLeadingTerm m P t) :
    ∃ Q ∈ N, Q ∈ weightedPolynomialModulePiece weight shift
        (shiftedModuleMonomialDegree weight shift t) ∧
      IsPolynomialModuleLeadingTerm m Q t :=
  ⟨weightedPolynomialModuleComponent weight shift (shiftedModuleMonomialDegree weight shift t) P,
    hN P hPN _, weightedPolynomialModuleComponent_mem weight shift _ P,
    hP.weightedComponent weight shift⟩

end AbelFormalization
