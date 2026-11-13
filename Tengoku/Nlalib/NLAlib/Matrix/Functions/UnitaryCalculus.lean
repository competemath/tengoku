import Tengoku.Nlalib.NLAlib.Matrix.Functions.HermitianCalculus
import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Tengoku.Nlalib.NLAlib.Matrix.Functions.TraceExpConvex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Unitary covariance of matrix functional calculus

Unitary conjugation preserves Hermitian matrices, positivity, spectra, and traces.
The logarithm and every real continuous functional calculus on a finite spectrum
commute with conjugation. The exponential and trace exponential do so for all
complex square matrices. Reflection corollaries use the same general automorphism
API. All statements include empty finite index types.

Source: Tropp 2015, §2.1 and the unitary dilation proof of Theorem 8.5.2;
`Re-derivations/matrix_toolkit_operator_derivations.tex`, §7 and its implementation
map. The reflection specialisations (`cfc_reflection_conj`, `spectrum_reflection_conj`) and the
reindexing transport `cfc_reindex_of_isHermitian` serve the operator Jensen inequality
(`Functions/JensenIsometricCompression`).
Atlas: `golden-thompson`, `operator-monotone-convex` (supporting calculus).
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unitary conjugation preserves Hermitian matrices. Source: unitary functional
calculus, Tropp 2015, §2.1; atlas `golden-thompson` (helper).
@isnad1 id=ishermit.1h3v.s8.42aaa8ff0e38 from=translated src=- shape=0f12c09e vocab=ccaf92e4
-/
theorem isHermitian_unitary_conj (U : unitary (Matrix ι ι ℂ))
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix ι ι ℂ) hA

/-- Unitary conjugation preserves the real spectrum. Source: the conjugation
star-algebra automorphism; Tropp 2015, §2.1; atlas `golden-thompson` (helper).
@isnad1 id=eq.0h3v.s8.314aed167651 from=translated src=- shape=99fd1786 vocab=d12af6a8
-/
theorem spectrum_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    spectrum ℝ ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) = spectrum ℝ A := by
  exact AlgEquiv.spectrum_eq (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℂ) U).toAlgEquiv A

/-- Every real function on a Hermitian matrix's finite spectrum commutes with
unitary conjugation. No global continuity premise is needed. Source: Mathlib's
CFC transport and Tropp 2015, Theorem 8.5.2; atlas `golden-thompson`,
`operator-monotone-convex` (helper).
@isnad1 id=eq.1h4v.s9.eff7b6e5eaef from=translated src=- shape=1f459dca vocab=ef33e3fc
-/
theorem cfc_unitary_conj (U : unitary (Matrix ι ι ℂ)) (f : ℝ → ℝ)
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    cfc f ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) =
      (U : Matrix ι ι ℂ) * cfc f A * (U : Matrix ι ι ℂ)ᴴ := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
      let := h
      exact Subsingleton.elim _ _
  | inr h =>
      let := h
      let E := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℂ) U
      symm
      change E (cfc f A) = cfc f (E A)
      exact StarAlgHomClass.map_cfc E f A (A.finite_real_spectrum.continuousOn f)
        E.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional hA
        (isHermitian_unitary_conj U A hA)

/-- Matrix logarithms commute with unitary conjugation of Hermitian matrices.
Source: real logarithm functional calculus, Tropp 2015, §2.1.12;
atlas `golden-thompson` (helper).
@isnad1 id=eq.1h3v.s9.f4611cc29d25 from=translated src=- shape=f1f9256a vocab=ae617eb0
-/
theorem matrixLog_unitary_conj (U : unitary (Matrix ι ι ℂ))
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    matrixLog ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) =
      (U : Matrix ι ι ℂ) * matrixLog A * (U : Matrix ι ι ℂ)ᴴ :=
  cfc_unitary_conj U Real.log A hA

/-- Matrix exponentials commute with unitary conjugation, even without a
Hermitian premise. Source: continuous ring-homomorphism transport of the
exponential, Tropp 2015, §2.1.11; atlas `golden-thompson` (helper).
@isnad1 id=eq.0h3v.s9.eb391df87385 from=translated src=- shape=52397b94 vocab=c1c95c73
-/
theorem matrixExp_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    matrixExp ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) =
      (U : Matrix ι ι ℂ) * matrixExp A * (U : Matrix ι ι ℂ)ᴴ := by
  let E := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  symm
  change E (NormedSpace.exp A) = NormedSpace.exp (E A)
  exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) E
    E.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional A
    ((NormedSpace.expSeries_radius_eq_top ℂ (Matrix ι ι ℂ)).symm ▸ edist_lt_top _ _)

/-- The complex trace is unchanged by unitary conjugation. Source: cyclicity
of trace, Tropp 2015, §2.1; atlas `golden-thompson` (helper).
@isnad1 id=eq.0h3v.s8.7ee7233cea26 from=translated src=- shape=ad33e0f7 vocab=f2d81e6b
-/
theorem trace_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    Matrix.trace ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) = Matrix.trace A := by
  rw [Matrix.trace_mul_cycle]
  simp only [← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self, Matrix.one_mul]

/-- The real trace exponential is unchanged by unitary conjugation, for every
complex square matrix. Source: exponential covariance and trace cyclicity,
Tropp 2015, §3.1; atlas `golden-thompson` (helper).
@isnad1 id=eq.0h3v.s8.4b5dcb3301c1 from=translated src=- shape=b1588c05 vocab=057e3ab6
-/
theorem traceExp_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    traceExp ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ) = traceExp A := by
  unfold traceExp
  rw [matrixExp_unitary_conj, trace_unitary_conj]

/-- Unitary conjugation preserves and reflects positive semidefiniteness.
Source: invertible congruence of Hermitian quadratic forms, Tropp 2015, §2.1.5;
atlas `golden-thompson` (helper).
@isnad1 id=iff.0h3v.s8.b0ad4092e93e from=translated src=- shape=560327fe vocab=781a5822
-/
theorem posSemidef_unitary_conj_iff (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ).PosSemidef ↔ A.PosSemidef :=
  Matrix.IsUnit.posSemidef_star_right_conjugate_iff (Unitary.isUnit_coe (U := U))

/-- Unitary conjugation preserves and reflects positive definiteness.
Source: invertible congruence of Hermitian quadratic forms, Tropp 2015, §2.1.5;
atlas `golden-thompson` (helper).
@isnad1 id=iff.0h3v.s8.9a970858be0b from=translated src=- shape=560327fe vocab=95671f4c
-/
theorem posDef_unitary_conj_iff (U : unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ).PosDef ↔ A.PosDef :=
  Matrix.IsUnit.posDef_star_right_conjugate_iff (Unitary.isUnit_coe (U := U))

/-- Simultaneous unitary conjugation leaves the Lieb trace function unchanged.
Only the logarithm's input needs to be Hermitian. Source: eigenbasis transport
in the operator derivations §7; atlas `golden-thompson` (helper).
@isnad1 id=eq.1h4v.s9.90de7c6f690d from=translated src=- shape=ecbf443d vocab=4f3968a6
-/
theorem traceExp_add_matrixLog_unitary_conj (U : unitary (Matrix ι ι ℂ))
    (H A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    traceExp ((U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ)ᴴ +
      matrixLog ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ)) =
        traceExp (H + matrixLog A) := by
  let E := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  change traceExp (E H + matrixLog (E A)) = _
  have hlog : matrixLog (E A) = E (matrixLog A) := matrixLog_unitary_conj U A hA
  rw [hlog, ← map_add E]
  exact traceExp_unitary_conj U _

/-- The complex trace pairing of a matrix exponential and another matrix is
unchanged by simultaneous unitary conjugation. No Hermitian premises are needed.
Source: exponential covariance and trace cyclicity, operator derivations §7;
atlas `golden-thompson` (helper).
@isnad1 id=eq.0h4v.s9.7a72c168dd78 from=translated src=- shape=77a80be4 vocab=9888c3a9
-/
theorem trace_matrixExp_mul_unitary_conj (U : unitary (Matrix ι ι ℂ))
    (H A : Matrix ι ι ℂ) :
    Matrix.trace (matrixExp ((U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ)ᴴ) *
      ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ)) =
        Matrix.trace (matrixExp H * A) := by
  let E := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  change Matrix.trace (matrixExp (E H) * E A) = _
  have hexp : matrixExp (E H) = E (matrixExp H) := matrixExp_unitary_conj U H
  rw [hexp, ← map_mul E]
  exact trace_unitary_conj U _

/-- The real part of the trace pairing of a matrix exponential and another
matrix is invariant under simultaneous unitary conjugation. Source: operator
derivations §7; atlas `golden-thompson` (helper).
@isnad1 id=eq.0h4v.s9.bf738b338b48 from=translated src=- shape=c66e49f2 vocab=9eb6626f
-/
theorem re_trace_matrixExp_mul_unitary_conj (U : unitary (Matrix ι ι ℂ))
    (H A : Matrix ι ι ℂ) :
    (Matrix.trace (matrixExp ((U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ)ᴴ) *
      ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ))).re =
        (Matrix.trace (matrixExp H * A)).re :=
  congrArg Complex.re (trace_matrixExp_mul_unitary_conj U H A)

/-- The Lieb trace function is invariant under a unitary conjugation that fixes
its Hermitian parameter. Only the logarithm's input needs a Hermitian premise for
this identity. Source: midpoint pinching, operator derivations §7;
atlas `golden-thompson` (helper).
@isnad1 id=eq.2h4v.s9.3d7c3b2424ad from=translated src=- shape=b9679981 vocab=4f3968a6
-/
theorem traceExp_add_matrixLog_unitary_conj_of_conj_eq
    (U : unitary (Matrix ι ι ℂ)) (H A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hH : (U : Matrix ι ι ℂ) * H * (U : Matrix ι ι ℂ)ᴴ = H) :
    traceExp (H + matrixLog ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ)) =
      traceExp (H + matrixLog A) := by
  calc
    traceExp (H + matrixLog ((U : Matrix ι ι ℂ) * A * (U : Matrix ι ι ℂ)ᴴ)) =
        traceExp ((U : Matrix ι ι ℂ) * (H + matrixLog A) * (U : Matrix ι ι ℂ)ᴴ) := by
      rw [matrixLog_unitary_conj U A hA, Matrix.mul_add, Matrix.add_mul, hH]
    _ = traceExp (H + matrixLog A) := traceExp_unitary_conj U _

private theorem reflection_mem_unitary (R : Matrix ι ι ℂ)
    (hR : Rᴴ = R) (hR2 : R * R = 1) : R ∈ unitary (Matrix ι ι ℂ) := by
  constructor <;> simpa only [Matrix.star_eq_conjTranspose, hR] using hR2

/-- Matrix logarithms commute with conjugation by a self-adjoint involution.
Source: reflection pinching, Tropp 2015, Theorem 8.5.2;
atlas `golden-thompson`, `operator-monotone-convex` (helper).
@isnad1 id=eq.3h3v.s7.73395a0190ab from=translated src=- shape=01518d73 vocab=b32bad3b
-/
theorem matrixLog_reflection_conj (R A : Matrix ι ι ℂ)
    (hR : Rᴴ = R) (hR2 : R * R = 1) (hA : A.IsHermitian) :
    matrixLog (R * A * R) = R * matrixLog A * R := by
  simpa only [hR] using
    matrixLog_unitary_conj ⟨R, reflection_mem_unitary R hR hR2⟩ A hA

/-- Matrix exponentials commute with conjugation by a self-adjoint involution.
Source: reflection pinching, Tropp 2015, Theorem 8.5.2;
atlas `golden-thompson`, `operator-monotone-convex` (helper).
@isnad1 id=eq.2h3v.s7.93e67f9c01f8 from=translated src=- shape=a10075a0 vocab=9ed22045
-/
theorem matrixExp_reflection_conj (R A : Matrix ι ι ℂ)
    (hR : Rᴴ = R) (hR2 : R * R = 1) :
    matrixExp (R * A * R) = R * matrixExp A * R := by
  simpa only [hR] using
    matrixExp_unitary_conj ⟨R, reflection_mem_unitary R hR hR2⟩ A

/-- The trace exponential is invariant under a self-adjoint involution.
Source: trace cyclicity and reflection pinching, operator derivations §7;
atlas `golden-thompson` (helper).
@isnad1 id=eq.2h3v.s7.c21692a1d60c from=translated src=- shape=b10eacaf vocab=356e712a
-/
theorem traceExp_reflection_conj (R A : Matrix ι ι ℂ)
    (hR : Rᴴ = R) (hR2 : R * R = 1) :
    traceExp (R * A * R) = traceExp A := by
  simpa only [hR] using
    traceExp_unitary_conj ⟨R, reflection_mem_unitary R hR hR2⟩ A

omit [DecidableEq ι] in
/-- Conjugation by a self-adjoint matrix `R` preserves Hermitian matrices: `(R * A * R)ᴴ = R * A * R`.
Source: reflection pinching, Tropp 2015, Theorem 8.5.2; atlas `operator-monotone-convex` (helper).
@isnad1 id=ishermit.2h3v.s7.d54c5f2e7546 from=translated src=- shape=febd6456 vocab=12fb8d61
-/
theorem isHermitian_reflection_conj (R A : Matrix ι ι ℂ) (hR : Rᴴ = R) (hA : A.IsHermitian) :
    (R * A * R).IsHermitian := by
  simpa only [hR] using Matrix.isHermitian_mul_mul_conjTranspose R hA

/-- Conjugation by a self-adjoint involution preserves the real spectrum.
Source: reflection pinching, Tropp 2015, Theorem 8.5.2; atlas `operator-monotone-convex` (helper).
@isnad1 id=eq.2h3v.s7.7fa422cd0591 from=translated src=- shape=18efe253 vocab=918e9e87
-/
theorem spectrum_reflection_conj (R A : Matrix ι ι ℂ) (hR : Rᴴ = R) (hR2 : R * R = 1) :
    spectrum ℝ (R * A * R) = spectrum ℝ A := by
  simpa only [hR] using spectrum_unitary_conj ⟨R, reflection_mem_unitary R hR hR2⟩ A

/-- Every real function on a Hermitian matrix's finite spectrum commutes with conjugation by a
self-adjoint involution: `cfc f (R * A * R) = R * cfc f A * R`.
Source: reflection pinching, Tropp 2015, Theorem 8.5.2; atlas `operator-monotone-convex` (helper).
@isnad1 id=eq.3h4v.s8.60f82012b22b from=translated src=- shape=fc7c8067 vocab=c58df465
-/
theorem cfc_reflection_conj (R A : Matrix ι ι ℂ) (hR : Rᴴ = R) (hR2 : R * R = 1)
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f (R * A * R) = R * cfc f A * R := by
  simpa only [hR] using cfc_unitary_conj ⟨R, reflection_mem_unitary R hR hR2⟩ f A hA

/-- Positive definiteness is preserved and reflected by a self-adjoint involution.
Source: invertible quadratic-form congruence, Tropp 2015, §2.1.5;
atlas `golden-thompson` (helper).
@isnad1 id=iff.2h3v.s7.d7bbe42c7087 from=translated src=- shape=fd73d76b vocab=565a1288
-/
theorem posDef_reflection_conj_iff (R A : Matrix ι ι ℂ)
    (hR : Rᴴ = R) (hR2 : R * R = 1) :
    (R * A * R).PosDef ↔ A.PosDef := by
  simpa only [hR] using
    posDef_unitary_conj_iff ⟨R, reflection_mem_unitary R hR hR2⟩ A

/-- A reflection fixing the Lieb parameter preserves its trace function.
Source: the midpoint pinching argument in operator derivations §7;
atlas `golden-thompson` (helper).
@isnad1 id=eq.4h4v.s8.7c7e79982687 from=translated src=- shape=0c806b3e vocab=15ab5a63
-/
theorem traceExp_add_matrixLog_reflection_conj_of_conj_eq (R H A : Matrix ι ι ℂ)
    (hR : Rᴴ = R) (hR2 : R * R = 1) (hA : A.IsHermitian)
    (hH : R * H * R = H) :
    traceExp (H + matrixLog (R * A * R)) = traceExp (H + matrixLog A) := by
  simpa only [hR] using
    traceExp_add_matrixLog_unitary_conj_of_conj_eq
      ⟨R, reflection_mem_unitary R hR hR2⟩ H A hA (by simpa only [hR] using hH)

/-- The diagonal embedding of a finite complex coordinate algebra as a star algebra homomorphism.-/
def diagonalStarAlgHom : (ι → ℂ) →⋆ₐ[ℂ] Matrix ι ι ℂ :=
  { (Matrix.diagonalAlgHom ℂ : (ι → ℂ) →ₐ[ℂ] Matrix ι ι ℂ) with
    map_star' := by intro x; simp [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose] }

set_option backward.isDefEq.respectTransparency false in
/-- Real functional calculus acts entrywise on a real diagonal matrix.
Arbitrary real functions are allowed because the diagonal spectrum is finite.
Source: the private `cfc_diag` proof in `JointTensorRepresentation`, via Mathlib's
diagonal algebra homomorphism and Pi CFC; Tropp 2015, §2.1.11;
atlas `golden-thompson`, `operator-monotone-convex` (helper).
@isnad1 id=eq.0h3v.s7.f24f67528191 from=translated src=- shape=b31e0edd vocab=7fde7542
-/
theorem cfc_diagonal_real (f : ℝ → ℝ) (x : ι → ℝ) :
    cfc f (Matrix.diagonal fun i => (x i : ℂ)) =
      Matrix.diagonal fun i => (f (x i) : ℂ) := by
  let := IsStarNormal.instContinuousFunctionalCalculus (A := ι → ℂ)
  let := IsSelfAdjoint.instContinuousFunctionalCalculus (A := ι → ℂ)
  let z : ι → ℂ := fun i => (x i : ℂ)
  have hx : IsSelfAdjoint z := by ext; simp [z]
  have hd : IsSelfAdjoint (diagonalStarAlgHom z) := hx.map diagonalStarAlgHom
  have hc : ContinuousOn f (spectrum ℝ z) := by
    rw [Pi.spectrum_eq]
    have heq : (⋃ i, spectrum ℝ (z i)) = Set.range x := by
      change (⋃ i, spectrum ℝ (algebraMap ℝ ℂ (x i))) = _
      simp only [spectrum.scalar_eq, Set.iUnion_singleton_eq_range]
    rw [heq]
    exact Set.Finite.continuousOn (Set.finite_range _) _
  have heq := diagonalStarAlgHom.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) f z hc
    (by change Continuous (fun z : ι → ℂ => Matrix.diagonal z); fun_prop) hx hd
  rw [cfc_map_pi (p := IsSelfAdjoint) (q := fun _ => IsSelfAdjoint) (S := ℂ) f z
    (by rwa [← Pi.spectrum_eq]) hx (fun i => by
      change star (x i : ℂ) = (x i : ℂ); simp)] at heq
  change Matrix.diagonal (fun i => cfc f (algebraMap ℝ ℂ (x i))) =
    cfc f (Matrix.diagonal fun i => (x i : ℂ)) at heq
  simp only [cfc_algebraMap] at heq
  exact heq.symm

/-- The exponential acts entrywise on a real diagonal matrix. This reusable
calculus lemma was previously private in `GoldenThompson`.
Source: diagonal CFC; Stahl §1.3.1 and Tropp 2015, §2.1.11;
atlas `trace-exponential-stahl` (partial), `golden-thompson` (partial).
@isnad1 id=eq.0h2v.s5.61782521b85c from=translated src=- shape=3dc29f9f vocab=6de1c833
-/
theorem matrixExp_diagonal_real (h : ι → ℝ) :
    matrixExp (Matrix.diagonal fun i => (h i : ℂ)) =
      Matrix.diagonal fun i => (Real.exp (h i) : ℂ) := by
  have hh : (Matrix.diagonal fun i => (h i : ℂ)).IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
  rw [matrixExp, ← CFC.real_exp_eq_normedSpace_exp hh]
  exact cfc_diagonal_real Real.exp h

omit [DecidableEq ι] in
/-- Equivalent finite labels preserve the complex trace. Source: the private
`trace_reindex` helper in `IntrinsicBernstein`, by reindexing the diagonal sum;
atlas `golden-thompson` (finite-index transport helper).
@isnad1 id=eq.0h4v.s6.2b9373f22049 from=translated src=- shape=821bd72c vocab=acfe728e
-/
theorem trace_reindex {κ : Type*} [Fintype κ] (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    Matrix.trace (Matrix.reindex e e A) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => A i i)

/-- Equivalent finite labels commute with the matrix exponential, with no
Hermitian premise. Source: continuous algebra-isomorphism transport of the
exponential; atlas `golden-thompson` (finite-index transport helper).
@isnad1 id=eq.0h4v.s7.b286903f85ea from=translated src=- shape=72a866a3 vocab=84d42753
-/
theorem matrixExp_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    matrixExp (Matrix.reindex e e A) = Matrix.reindex e e (matrixExp A) := by
  let E := reindexStarAlgEquiv (𝕜 := ℂ) e
  symm
  change E (NormedSpace.exp A) = NormedSpace.exp (E A)
  exact NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) E
    E.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional A
    ((NormedSpace.expSeries_radius_eq_top ℂ (Matrix ι ι ℂ)).symm ▸ edist_lt_top _ _)

/-- Equivalent finite labels preserve the trace exponential, with no Hermitian
premise. Source: exponential transport and invariance of the diagonal sum;
atlas `golden-thompson` (finite-index transport helper).
@isnad1 id=eq.0h4v.s6.bec8deb3f0fd from=translated src=- shape=aee6f8fe vocab=16b58f74
-/
theorem traceExp_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    traceExp (Matrix.reindex e e A) = traceExp A := by
  unfold traceExp
  rw [matrixExp_reindex, trace_reindex]

/-- Equivalent finite labels preserve positive definiteness in both directions.
Source: transport of finite quadratic forms; helper for atlas `matrix-freedman`.
@isnad1 id=iff.0h4v.s6.0c411a16d5fc from=translated src=- shape=01101eb5 vocab=3a28c455
-/
theorem posDef_reindex_iff {n r : Type*} (e : n ≃ r) (A : Matrix n n ℂ) :
    (Matrix.reindex e e A).PosDef ↔ A.PosDef := by
  change (A.submatrix e.symm e.symm).PosDef ↔ A.PosDef
  constructor
  · intro h
    have h' := h.submatrix e.injective
    have heq : (A.submatrix e.symm e.symm).submatrix e e = A := by
      ext i j
      simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rw [heq] at h'
    exact h'
  · intro h
    exact h.submatrix e.symm.injective

/-- Equivalent finite labels commute with the real continuous functional calculus of a Hermitian
matrix: `cfc f (reindex e e A) = reindex e e (cfc f A)` for every `f : ℝ → ℝ` (the spectrum is
finite, so no continuity premise is needed).
Source: star-algebra transport of continuous functional calculus via `reindexStarAlgEquiv`;
atlas `operator-monotone-convex` (helper).
@isnad1 id=eq.1h5v.s8.f5837210e49e from=translated src=- shape=9b977b78 vocab=b9ab45cc
-/
theorem cfc_reindex_of_isHermitian {n : Type*} [Fintype n] [DecidableEq n] {r : Type*}
    [Fintype r] [DecidableEq r] (e : n ≃ r) (f : ℝ → ℝ) (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    cfc f (Matrix.reindex e e A) = Matrix.reindex e e (cfc f A) := by
  cases isEmpty_or_nonempty n with
  | inl h =>
      have : IsEmpty r := e.symm.isEmpty
      exact Subsingleton.elim _ _
  | inr h =>
      let E := reindexStarAlgEquiv (𝕜 := ℂ) e
      have hc : Continuous E :=
        E.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
      symm
      change E (cfc f A) = cfc f (E A)
      exact StarAlgHomClass.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) E f A
        (A.finite_real_spectrum.continuousOn f) hc hA (hA.reindex e)

/-- Equivalent finite labels commute with the matrix logarithm for Hermitian input.
Source: star-algebra transport of continuous functional calculus; helper for
operator rederivations `eq:condlieb` and atlas `matrix-freedman`.
@isnad1 id=eq.1h4v.s7.2b3e7c8f2522 from=translated src=- shape=6435fcce vocab=3263c4ae
-/
theorem matrixLog_reindex_of_isHermitian {n : Type*} [Fintype n] [DecidableEq n] {r : Type*} [Fintype r] [DecidableEq r]
    (e : n ≃ r) (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    matrixLog (Matrix.reindex e e A) = Matrix.reindex e e (matrixLog A) := by
  let E := reindexStarAlgEquiv (𝕜 := ℂ) e
  have hc : Continuous E := E.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hf : ContinuousOn Real.log (spectrum ℝ A) := by
    rw [hA.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).continuousOn _
  symm
  change E (cfc Real.log A) = cfc Real.log (E A)
  exact StarAlgHomClass.map_cfc (p := IsSelfAdjoint) (q := IsSelfAdjoint) E Real.log A
    hf hc hA (hA.reindex e)

/-- The trace exponential of a real diagonal matrix is the sum of the scalar
exponentials. Source: the diagonal exponential series; atlas
`trace-exponential-stahl` (helper).
@isnad1 id=eq.0h2v.s5.6908de1bafde from=translated src=- shape=a41d164d vocab=1eaa6384
-/
theorem traceExp_diagonal_real (a : ι → ℝ) :
    traceExp (Matrix.diagonal (fun i => (a i : ℂ))) = ∑ i, Real.exp (a i) := by
  rw [traceExp_complex, matrixExp_diagonal_real]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_apply_eq,
    Complex.re_sum, Complex.ofReal_re]

/-- Every diagonal node in a unitary congruence belongs to the original real
spectrum. Source: similarity invariance of the spectrum; atlas
`trace-exponential-stahl` (helper).
@isnad1 id=mem.2h5v.s7.c12aa549bbfa from=translated src=- shape=1d04c012 vocab=3ef72505
-/
theorem mem_real_spectrum_of_orthonormal_congruence_diagonal
    (H U : Matrix ι ι ℂ) (b : ι → ℝ) (hU : HasOrthonormalCols U)
    (hH : Uᴴ * H * U = Matrix.diagonal (fun i => (b i : ℂ))) (i : ι) :
    b i ∈ spectrum ℝ H := by
  have hleft : Uᴴ * U = 1 := hU
  have hright : U * Uᴴ = 1 := mul_eq_one_comm.mp hleft
  let V : unitary (Matrix ι ι ℂ) :=
    ⟨Uᴴ, by simpa only [Unitary.mem_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      using And.intro hright hleft⟩
  have hs := spectrum_unitary_conj V H
  have hdiag : (V : Matrix ι ι ℂ) * H * (V : Matrix ι ι ℂ)ᴴ =
      Matrix.diagonal (fun j => (b j : ℂ)) := by
    simpa only [V, Matrix.conjTranspose_conjTranspose] using hH
  rw [hdiag] at hs
  rw [← hs]
  apply (spectrum.algebraMap_mem_iff ℂ).mp
  rw [spectrum_diagonal]
  exact ⟨i, rfl⟩

end NLAlib
