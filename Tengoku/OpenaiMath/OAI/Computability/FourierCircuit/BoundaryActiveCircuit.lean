import Tengoku.OpenaiMath.OAI.Computability.FourierCircuit.CascadeLimit

namespace OAI

section
/-! Common ordered spatial generators for the active boundary DAG. Scalar
weights may be arbitrarily large and depend on the modulus; every use is charged. -/
namespace ExactFourier.Boundary
open scoped BigOperators
open TensorAxis PolynomialMatrix
variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def activeWeights (t d e : ℕ) (η ℓ : Polynomial ℂ) :
    Matrix (Times t d e) (Times t d e × (Fin (e+1) × Fin (d+1))) ℂ :=
  fun a b => orderedWeight (if a.val.val<t-d then 1 else η) ℓ a.val.val b.1.val.val b.2.1.val b.2.2.val

theorem activeMatrix_blocks (t d e : ℕ) (η ℓ : Polynomial ℂ) (hℓ : ℓ.Monic)
    (J G : Matrix ι ι (Polynomial ℂ))
    (hG : Bounded G d) (hJ : Bounded J e) :
    activeMatrix t d e η ℓ J G = 1 + TypedDAG.blockMatrix (activeWeights t d e η ℓ)
      (fun ij => coefficientMatrix J ij.1.val * coefficientMatrix G ij.2.val) := by
  unfold activeMatrix
  congr 1
  ext a b
  have h := ordered_span (if a.1.val.val<t-d then 1 else η) ℓ hℓ J G hG hJ a.1.val.val b.1.val.val
  have hh := congrFun (congrFun h a.2) b.2
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] at hh
  simp only [Matrix.submatrix_apply,activeCorrection,TypedDAG.blockMatrix,activeWeights,Fintype.sum_prod_type]
  simp only [← Fin.sum_univ_eq_sum_range] at hh
  by_cases ha : a.1.val.val<t-d <;> simpa [ha,coefficientMatrix] using hh

theorem exists_active_dag (t d e sG sJ : ℕ) (η ℓ : Polynomial ℂ) (hℓ : ℓ.Monic)
    (J G : Matrix ι ι (Polynomial ℂ)) (hG : Bounded G d) (hJ : Bounded J e)
    (CG : (j : Fin (d+1)) → TypedDAG ι ι) (CJ : (i : Fin (e+1)) → TypedDAG ι ι)
    (hsG : ∀ j, (CG j).size ≤ sG) (hsJ : ∀ i, (CJ i).size ≤ sJ)
    (heG : ∀ j x, (CG j).eval x=(coefficientMatrix G j.val).mulVec x)
    (heJ : ∀ i x, (CJ i).eval x=(coefficientMatrix J i.val).mulVec x) :
    ∃ C : TypedDAG (Times t d e × ι) (Times t d e × ι),
      C.size ≤ Fintype.card (Times t d e)*((e+1)*(d+1))*(sG+sJ) +
        2*Fintype.card ι*Fintype.card (Times t d e)^2*((e+1)*(d+1)) +
        Fintype.card (Times t d e)*Fintype.card ι ∧
      ∀ x, C.eval x=(activeMatrix t d e η ℓ J G).mulVec x := by
  let Cij := fun ij : Fin (e+1) × Fin (d+1) => (CJ ij.1).comp (CG ij.2)
  refine ⟨(TypedDAG.weightedBlocks (activeWeights t d e η ℓ) Cij).addIdentity,?_,?_⟩
  · rw [TypedDAG.size_addIdentity,TypedDAG.size_weightedBlocks]
    have hs : (∑ ij, (Cij ij).size) ≤ ((e+1)*(d+1))*(sG+sJ) := by
      calc
        _ ≤ ∑ _ : Fin (e+1) × Fin (d+1), (sG+sJ) :=
          Finset.sum_le_sum (fun ij _ => Nat.add_le_add (hsG ij.2) (hsJ ij.1))
        _ = _ := by simp
    simp only [Fintype.card_prod,Fintype.card_fin]
    calc
      _ ≤ Fintype.card (Times t d e)*(((e+1)*(d+1))*(sG+sJ)) +
          2*Fintype.card ι*Fintype.card (Times t d e)*Fintype.card (Times t d e)*((e+1)*(d+1)) +
          Fintype.card (Times t d e)*Fintype.card ι := by gcongr
      _ = _ := by ring
  · intro x
    rw [activeMatrix_blocks t d e η ℓ hℓ J G hG hJ]
    apply TypedDAG.eval_addIdentity
    apply TypedDAG.eval_weightedBlocks
    intro ij v
    rw [TypedDAG.eval_comp,heG,heJ,Matrix.mulVec_mulVec]

end ExactFourier.Boundary

end

section
/-! Uniform sixth-degree active correction bound. No inverse evaluation circuit
and no bound on scalar interpolation weights is used. -/
namespace ExactFourier.Boundary
open TensorAxis PolynomialMatrix
variable {α : Type} [Fintype α] [DecidableEq α]

theorem exists_uniform_active_dag (G J : Matrix α α (Polynomial ℂ))
    (dg dj : ℕ) (hG : Bounded G dg) (hJ : Bounded J dj) :
    ∃ A : ℕ, ∀ k t : ℕ, ∀ η ℓ : Polynomial ℂ, ℓ.Monic →
      ∃ C : TypedDAG (Times t (k*dg) (k*dj) × Space α k) (Times t (k*dg) (k*dj) × Space α k),
        C.size ≤ A*(k+1)^6*Fintype.card α^k ∧
        ∀ x, C.eval x=(activeMatrix t (k*dg) (k*dj) η ℓ (power J k) (power G k)).mulVec x := by
  obtain ⟨BG,hBG⟩ := exists_tensor_coefficient_dag G
  obtain ⟨BJ,hBJ⟩ := exists_tensor_coefficient_dag J
  let a := dj+2*dg
  let b := (dj+1)*(dg+1)
  let A := a*b*(BG+BJ)+2*a^2*b+a
  refine ⟨A,?_⟩
  intro k t η ℓ hℓ
  choose CG hsG heG using fun j : Fin (k*dg+1) => hBG k j.val
  choose CJ hsJ heJ using fun i : Fin (k*dj+1) => hBJ k i.val
  obtain ⟨C,hC,heC⟩ := exists_active_dag t (k*dg) (k*dj)
    (BG*(k+1)^2*Fintype.card α^k) (BJ*(k+1)^2*Fintype.card α^k) η ℓ hℓ
    (power J k) (power G k) (bounded_power G hG k) (bounded_power J hJ k)
    CG CJ hsG hsJ heG heJ
  refine ⟨C,hC.trans ?_,heC⟩
  rw [card_space]
  have hr : Fintype.card (Times t (k*dg) (k*dj)) ≤ a*(k+1) := by
    apply (card_times _ _ _).trans
    dsimp [a]
    nlinarith
  have hg : (k*dj+1)*(k*dg+1) ≤ b*(k+1)^2 := by
    calc
      _ ≤ ((dj+1)*(k+1))*((dg+1)*(k+1)) := by gcongr <;> nlinarith
      _ = _ := by dsimp [b]; ring
  have h5 : (k+1)^5 ≤ (k+1)^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : (k+1)^4 ≤ (k+1)^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : k+1 ≤ (k+1)^6 := Nat.le_self_pow (by omega) _
  calc
    _ ≤ (a*(k+1))*(b*(k+1)^2)*(BG*(k+1)^2*Fintype.card α^k+BJ*(k+1)^2*Fintype.card α^k) +
      2*Fintype.card α^k*(a*(k+1))^2*(b*(k+1)^2) + a*(k+1)*Fintype.card α^k := by gcongr
    _ = a*b*(BG+BJ)*(k+1)^5*Fintype.card α^k +
      (2*a^2*b)*(k+1)^4*Fintype.card α^k + a*(k+1)*Fintype.card α^k := by ring
    _ ≤ a*b*(BG+BJ)*(k+1)^6*Fintype.card α^k +
      (2*a^2*b)*(k+1)^6*Fintype.card α^k + a*(k+1)^6*Fintype.card α^k := by gcongr
    _ = A*(k+1)^6*Fintype.card α^k := by dsimp [A]; ring

end ExactFourier.Boundary

end

section
/-! Uniform scalar-prefix price; the untouched suffix is restored literally. -/
namespace ExactFourier.ScalarConvolution
open CoefficientTime

theorem exists_prefix_dag (t T : ℕ) (ht : 0<t) (f : PowerSeries ℂ) :
    ∃ C : LinearDAG t t, C.size ≤ 52*t*(Nat.log 2 t+1) ∧
      ∀ x, C.eval x=(prefixScalar t T f).mulVec x := by
  obtain ⟨C,hC,he⟩ := exists_truncation_dag t ht f
  let I : LinearDAG t t := LinearDAG.wires Fin.castSucc
  refine ⟨(C.fanout I).withOutputs (fun i => if i.val<T then Fin.castAdd t i else Fin.natAdd t i),?_,?_⟩
  · exact hC
  · intro x
    funext i
    rw [LinearDAG.eval_withOutputs,LinearDAG.eval_fanout]
    simp only [Function.comp_apply]
    by_cases hi : i.val<T
    · simp only [hi,ite_true,Fin.addCases_left,he]
      simp [Matrix.mulVec,dotProduct,prefixScalar,hi]
    · simp only [hi,ite_false,Fin.addCases_right]
      have hm : (prefixScalar t T f).mulVec x i = x i := by
        simp [Matrix.mulVec,dotProduct,prefixScalar,hi,Matrix.one_apply]
      rw [hm]
      simp [I,LinearDAG.eval_wires]

theorem prefix_inv (t T : ℕ) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    (prefixScalar t T f)⁻¹=prefixScalar t T f⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← prefixScalar_mul,PowerSeries.mul_inv_cancel _ hf,prefixScalar_one]

end ExactFourier.ScalarConvolution

end

section
namespace ExactFourier.MatrixPrice
open scoped Kronecker
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem conjugate_le (p : MatrixPrice) (P A : Matrix ι ι ℂ)
    (hP : IsUnit P) (hA : IsUnit A) :
    p.value (P*A*P⁻¹) ≤ 2*p.value P+p.value A := by
  have hPi := Matrix.isUnit_nonsing_inv_iff.mpr hP
  have h1 := p.mul_le P A hP hA
  have h2 := p.mul_le (P*A) P⁻¹ (hP.mul hA) hPi
  rw [p.inverse P hP] at h2
  linarith

theorem le_conjugate (p : MatrixPrice) (P A : Matrix ι ι ℂ)
    (hP : IsUnit P) (hA : IsUnit A) :
    p.value A ≤ 2*p.value P+p.value (P*A*P⁻¹) := by
  have hPi := Matrix.isUnit_nonsing_inv_iff.mpr hP
  have h := p.conjugate_le P⁻¹ (P*A*P⁻¹) hPi ((hP.mul hA).mul hPi)
  have hh : P⁻¹*(P*A*P⁻¹)*(P⁻¹)⁻¹=A := by
    rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hP)]
    calc
      _ = (P⁻¹*P)*A*(P⁻¹*P) := by noncomm_ring
      _ = A := by rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hP)]; simp
  rw [hh,p.inverse P hP] at h
  exact h

theorem scalar (p : MatrixPrice) (A : Matrix ι ι ℂ) (hA : IsUnit A)
    (c : ℂ) (hc : c≠0) : p.value (c • A)=p.value A := by
  have he : c • A = Matrix.diagonal (fun _ : ι => c)*A*1 := by
    ext i j
    simp [Matrix.diagonal_mul,Matrix.smul_apply]
  rw [he]
  exact p.monomial A _ _ hA (MonomialMatrix.diagonal _ (fun _ => hc)) MonomialMatrix.one

theorem scalar_unit (A : Matrix ι ι ℂ) (hA : IsUnit A)
    (c : ℂ) (hc : c≠0) : IsUnit (c • A) := by
  have he : c • A = Matrix.diagonal (fun _ : ι => c)*A := by
    ext i j
    simp [Matrix.diagonal_mul,Matrix.smul_apply]
  rw [he]
  exact (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun _ => isUnit_iff_ne_zero.mpr hc))).mul hA

end ExactFourier.MatrixPrice

end

section
/-! Uniform coefficient-boundary comparison, 06-feedback:20--46. All modulus
coefficients are literal charged constants. The estimate even holds at short
lengths; its intended use is t>k*deg G. -/
namespace ExactFourier.Boundary
open PolynomialMatrix TensorAxis CoefficientTime
open scoped Kronecker
variable {α : Type} [Fintype α] [DecidableEq α]

end ExactFourier.Boundary

end

end OAI
