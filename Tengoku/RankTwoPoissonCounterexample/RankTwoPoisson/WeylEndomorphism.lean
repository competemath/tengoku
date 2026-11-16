import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.WeylAlgebra
import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.HigherRank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The explicit endomorphism of the fourth Weyl algebra

The generator images satisfy the defining relations in the universal Weyl
algebra. Intertwining its polynomial action with the Poisson substitution proves
non-surjectivity: a preimage of any multiplication operator, applied to 1, would
supply a polynomial preimage. This argument does not assume PBW or faithfulness
of the operator representation.
-/

set_option maxHeartbeats 400000
namespace RankTwoPoisson
namespace Weyl
noncomputable section
variable (K : Type*) [Field K] [CharZero K]

def dualHamiltonian : Var → Poly K := ![outputK K 2,outputK K 3,-outputK K 0,-outputK K 1]
def delta (i : Var) : Algebra K := hamiltonian K (dualHamiltonian K i)

omit [CharZero K] in
/--
@isnad1 id=eq.0h3v.s7.4f486fd4648b from=translated src=- shape=825fbdfb vocab=c40fab1b
-/
theorem bracket_neg_left (f g : Poly K) : bracketK K (-f) g = -bracketK K f g := by
  simp [bracketK,polyDerivK]; ring

omit [CharZero K] in
/--
@isnad1 id=eq.0h3v.s7.f9a16ec00720 from=translated src=- shape=d86e079a vocab=c40fab1b
-/
theorem bracket_neg_right (f g : Poly K) : bracketK K f (-g) = -bracketK K f g := by
  simp [bracketK,polyDerivK]; ring

/--
@isnad1 id=eq.0h3v.s7.fa7a0f59d979 from=translated src=- shape=0d55eade vocab=9d6c3671
-/
theorem dual_output (i j : Var) :
    bracketK K (dualHamiltonian K i) (outputK K j) = if i=j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [dualHamiltonian,bracket_neg_left,bracketK_outputK_outputK,canonicalMatrixK,canonicalMatrix]

/--
@isnad1 id=eq.0h3v.s7.7a13dc84558f from=translated src=- shape=aa83a8d6 vocab=4ac1d1cd
-/
theorem dual_dual (i j : Var) :
    bracketK K (dualHamiltonian K i) (dualHamiltonian K j) = MvPolynomial.C (canonicalMatrixK K i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [dualHamiltonian,bracket_neg_left,bracket_neg_right,bracketK_outputK_outputK,canonicalMatrixK,canonicalMatrix]

/--
@isnad1 id=eq.0h3v.s6.6f3c8dc25fca from=translated src=- shape=421f102e vocab=bb441112
-/
theorem delta_commute (i j : Var) : delta K i * delta K j = delta K j * delta K i := by
  apply sub_eq_zero.mp
  rw [delta,delta,hamiltonian_commutator,dual_dual,hamiltonian_constant]

/--
@isnad1 id=eq.0h3v.s9.fee2d54f5018 from=translated src=- shape=3da5e0c9 vocab=3e8ddeb7
-/
theorem delta_output (i j : Var) :
    delta K i * polynomial K (outputK K j) =
      polynomial K (outputK K j) * delta K i + if i=j then 1 else 0 := by
  have h := hamiltonian_polynomial K (dualHamiltonian K i) (outputK K j)
  rw [dual_output] at h
  apply sub_eq_iff_eq_add'.mp
  by_cases he : i=j <;> simpa [delta,he] using h

/-- The actual algebra endomorphism induced by the verified Weyl relations.-/
def endomorphism : Algebra K →ₐ[K] Algebra K :=
  lift K (fun i => polynomial K (outputK K i)) (delta K)
    (fun i j => polynomial_commute K (outputK K i) (outputK K j)) (delta_commute K) (delta_output K)

/--
@isnad1 id=eq.0h2v.s9.6dd17e59ac23 from=translated src=- shape=167dc110 vocab=3e84e223
-/
@[simp] theorem endomorphism_X (i : Var) :
    endomorphism K (X K i) = polynomial K (outputK K i) := lift_X _ _ _ _ _ _ _

/--
@isnad1 id=eq.0h2v.s8.3a0e3d35048c from=translated src=- shape=d9d43fe6 vocab=a964a7e3
-/
@[simp] theorem endomorphism_deriv (i : Var) :
    endomorphism K (deriv K i) = delta K i := lift_deriv _ _ _ _ _ _ _

/--
@isnad1 id=eq.0h3v.s9.c04049c0aed8 from=translated src=- shape=126c5e9a vocab=da3fbc40
-/
theorem dual_intertwining (i : Var) (f : Poly K) :
    bracketK K (dualHamiltonian K i) (PhiK K f) = PhiK K (MvPolynomial.pderiv i f) := by
  have hd : dualHamiltonian K i = PhiK K (![MvPolynomial.X 2,MvPolynomial.X 3,
      -MvPolynomial.X 0,-MvPolynomial.X 1] i) := by
    fin_cases i <;> simp [dualHamiltonian]
  rw [hd,PhiK_isPoisson]
  congr 1
  fin_cases i <;> simp [bracketK,polyDerivK]

/--
@isnad1 id=eq.0h3v.s11.cb811b6df077 from=translated src=- shape=0e4af291 vocab=f31cc2ae
-/
theorem representation_intertwining_free (a : Free K) (f : Poly K) :
    representation K (endomorphism K (quotient K a)) (PhiK K f) =
      PhiK K (representation K (quotient K a) f) := by
  induction a using FreeAlgebra.induction generalizing f with
  | grade0 c =>
    simp only [AlgHom.commutes]
    simp
  | grade1 v =>
    cases v with
    | inl i =>
      change representation K (endomorphism K (X K i)) (PhiK K f) =
        PhiK K (representation K (X K i) f)
      simp [representation_polynomial,multiplication_apply]
    | inr i =>
      change representation K (endomorphism K (deriv K i)) (PhiK K f) =
        PhiK K (representation K (deriv K i) f)
      simp only [endomorphism_deriv,delta,representation_hamiltonian,
        representation_deriv,differential_apply,dual_intertwining]
  | add a b ha hb =>
    simp only [map_add,LinearMap.add_apply,ha,hb]
  | mul a b ha hb =>
    simp only [map_mul,Module.End.mul_apply,hb,ha]

/--
@isnad1 id=eq.0h3v.s10.5d87636816b6 from=translated src=- shape=886298c9 vocab=921d6ae4
-/
theorem representation_intertwining (a : Algebra K) (f : Poly K) :
    representation K (endomorphism K a) (PhiK K f) =
      PhiK K (representation K a f) := by
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective K (Relation K) a
  exact representation_intertwining_free K a f

/--
@isnad1 id=not.0h1v.s8.e05e17bc1eb8 from=translated src=- shape=41bcb0cd vocab=386ef884
-/
theorem endomorphism_not_surjective : ¬Function.Surjective (endomorphism K) := by
  intro hs
  apply HigherRank.base_not_surjective K
  intro g
  obtain ⟨a,ha⟩ := hs (polynomial K g)
  refine ⟨representation K a 1, ?_⟩
  have h := representation_intertwining K a 1
  rw [ha,representation_polynomial] at h
  simpa [multiplication_apply] using h.symm

omit [CharZero K] in
/--
@isnad1 id=eq.0h2v.s6.526da73cd792 from=translated src=- shape=5c68212b vocab=4b13a840
-/
theorem hamiltonian_neg (f : Poly K) : hamiltonian K (-f) = -hamiltonian K f := by
  have hh : hCoefficients K (-f) = fun i => -hCoefficients K f i := by
    funext i
    fin_cases i <;> simp [hCoefficients]
  simp only [hamiltonian,hh,vectorField]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact (congrArg (fun w : Algebra K => w * deriv K i)
    ((polynomial K).map_neg (hCoefficients K f i))).trans
      (neg_mul (polynomial K (hCoefficients K f i)) (deriv K i))

/--
@isnad1 id=eq.0h2v.s10.ecf445464578 from=translated src=- shape=03d29cd2 vocab=c0e92e0c
-/
theorem endomorphism_polynomial (f : Poly K) :
    endomorphism K (polynomial K f) = polynomial K (PhiK K f) := by
  have h : (endomorphism K).comp (polynomial K) = (polynomial K).comp (PhiK K) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact congrArg (fun e : Poly K →ₐ[K] Algebra K => e f) h

/--
@isnad1 id=not.0h1v.s9.c95cfa2facac from=translated src=- shape=70654a6f vocab=ba1a36c4
-/
theorem endomorphism_not_automorphism :
    ¬∃ e : Algebra K ≃ₐ[K] Algebra K, e.toAlgHom = endomorphism K := by
  rintro ⟨e,he⟩
  apply endomorphism_not_surjective K
  rw [← he]
  exact e.surjective

/-- The actual fourth Weyl algebra counterexample, over every characteristic-zero field.
@isnad1 id=and.0h1v.s10.85f1e8c4717b from=translated src=- shape=2d94ada2 vocab=6bcf8346
-/
theorem explicit_counterexample :
    (∀ i, endomorphism K (X K i) = polynomial K (outputK K i)) ∧
    (∀ i, endomorphism K (deriv K i) = delta K i) ∧
    ¬Function.Surjective (endomorphism K) ∧
    ¬∃ e : Algebra K ≃ₐ[K] Algebra K, e.toAlgHom = endomorphism K :=
  ⟨endomorphism_X K,endomorphism_deriv K,endomorphism_not_surjective K,
    endomorphism_not_automorphism K⟩

/-- Specialization of the full Weyl conclusion to the manuscript's complex field.
@isnad1 id=and.0h0v.s10.47550a1be9c1 from=translated src=- shape=1a4e5ddf vocab=6e82430d
-/
theorem explicit_counterexample_complex :
    (∀ i, endomorphism ℂ (X ℂ i) = polynomial ℂ (outputC i)) ∧
    (∀ i, endomorphism ℂ (deriv ℂ i) = delta ℂ i) ∧
    ¬Function.Surjective (endomorphism ℂ) ∧
    ¬∃ e : Algebra ℂ ≃ₐ[ℂ] Algebra ℂ, e.toAlgHom = endomorphism ℂ :=
  explicit_counterexample ℂ

end
end Weyl
end RankTwoPoisson
