import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.PoissonCalculus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The fourth Weyl algebra and polynomial Hamiltonians

The algebra is the quotient of the free associative algebra on four coordinate
and four derivative generators by the universal Weyl relations. Polynomial
coordinates embed in it, it acts on polynomials, and the Hamiltonian commutator
identities are proved in the presented algebra itself. Faithfulness of the full
operator representation is a separate obligation; no such assumption is used.
-/

set_option maxHeartbeats 400000
namespace RankTwoPoisson
namespace Weyl
noncomputable section
variable (K : Type*) [Field K]
abbrev Free := FreeAlgebra K (Var ⊕ Var)

def freeX (i : Var) : Free K := FreeAlgebra.ι K (.inl i)
def freeD (i : Var) : Free K := FreeAlgebra.ι K (.inr i)

/-- The defining Weyl relations on the free associative algebra.-/
inductive Relation : Free K → Free K → Prop
  | xx (i j : Var) : Relation (freeX K i * freeX K j) (freeX K j * freeX K i)
  | dd (i j : Var) : Relation (freeD K i * freeD K j) (freeD K j * freeD K i)
  | dx (i j : Var) : Relation (freeD K i * freeX K j)
      (freeX K j * freeD K i + if i=j then 1 else 0)

abbrev Algebra := RingQuot (Relation K)
def quotient : Free K →ₐ[K] Algebra K := RingQuot.mkAlgHom K (Relation K)
def X (i : Var) : Algebra K := quotient K (freeX K i)
def deriv (i : Var) : Algebra K := quotient K (freeD K i)

/--
@isnad1 id=eq.0h3v.s6.b85d086c3fd5 from=translated src=- shape=79c9b724 vocab=09d17d3a
-/
theorem X_commute (i j : Var) : X K i * X K j = X K j * X K i := by
  simpa only [X,quotient,← map_mul] using RingQuot.mkAlgHom_rel K (Relation.xx (K:=K) i j)

/--
@isnad1 id=eq.0h3v.s6.c6d1176e6194 from=translated src=- shape=79c9b724 vocab=ebfa42c6
-/
theorem deriv_commute (i j : Var) : deriv K i * deriv K j = deriv K j * deriv K i := by
  simpa only [deriv,quotient,← map_mul] using RingQuot.mkAlgHom_rel K (Relation.dd (K:=K) i j)

/--
@isnad1 id=eq.0h3v.s7.0d7e1ed90780 from=translated src=- shape=70f3c1f2 vocab=202a0c17
-/
theorem deriv_X (i j : Var) : deriv K i * X K j = X K j * deriv K i + if i=j then 1 else 0 := by
  have h := RingQuot.mkAlgHom_rel K (Relation.dx (K:=K) i j)
  simpa [X,deriv,quotient,map_mul,map_add,apply_ite] using h

variable {A : Type*} [Ring A] [_root_.Algebra K A]

def lift (F D : Var → A)
    (hxx : ∀ i j, F i * F j = F j * F i)
    (hdd : ∀ i j, D i * D j = D j * D i)
    (hdx : ∀ i j, D i * F j = F j * D i + if i=j then 1 else 0) : Algebra K →ₐ[K] A :=
  RingQuot.liftAlgHom K ⟨FreeAlgebra.lift K (Sum.elim F D), by
    intro a b h
    cases h with
    | xx i j => simpa [freeX] using hxx i j
    | dd i j => simpa [freeD] using hdd i j
    | dx i j => simpa [freeD,freeX,apply_ite] using hdx i j⟩

/--
@isnad1 id=eq.3h5v.s8.0f81eb74d118 from=translated src=- shape=655bb03e vocab=16cac33e
-/
theorem lift_X (F D : Var → A) (hxx hdd hdx) (i : Var) :
    lift K F D hxx hdd hdx (X K i) = F i := by
  rw [X,quotient,lift,RingQuot.liftAlgHom_mkAlgHom_apply]
  simp [freeX]

/--
@isnad1 id=eq.3h5v.s8.c7772a502861 from=translated src=- shape=36f1f670 vocab=a9d072d5
-/
theorem lift_deriv (F D : Var → A) (hxx hdd hdx) (i : Var) :
    lift K F D hxx hdd hdx (deriv K i) = D i := by
  rw [deriv,quotient,lift,RingQuot.liftAlgHom_mkAlgHom_apply]
  simp [freeD]

/-- Algebra homomorphisms out of the presentation are determined by its generators.
@isnad1 id=eq.2h4v.s9.6192dbfcabf6 from=translated src=- shape=c1ae3107 vocab=08847147
-/
theorem hom_ext (f g : Algebra K →ₐ[K] A)
    (hx : ∀ i, f (X K i) = g (X K i))
    (hd : ∀ i, f (deriv K i) = g (deriv K i)) : f=g := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext i
  cases i with
  | inl i => exact hx i
  | inr i => exact hd i

/-- The commuting coordinate subalgebra of the actual Weyl presentation.-/
def coordinates : Subalgebra K (Algebra K) := _root_.Algebra.adjoin K (Set.range (X K))

/--
@isnad1 id=ismulcom.0h1v.s9.ac2237289552 from=translated src=- shape=a91acb17 vocab=575ee500
-/
instance coordinates_commutative : IsMulCommutative (coordinates K) :=
  _root_.Algebra.isMulCommutative_adjoin K (by
    rintro a ⟨i,rfl⟩ b ⟨j,rfl⟩
    exact X_commute K i j)

open scoped IsMulCommutative

/-- The polynomial-coordinate homomorphism into the Weyl algebra.-/
def polynomial : MvPolynomial Var K →ₐ[K] Algebra K :=
  (coordinates K).val.comp (MvPolynomial.aeval (fun i =>
    (⟨X K i, _root_.Algebra.subset_adjoin (Set.mem_range_self i)⟩ : coordinates K)))

/--
@isnad1 id=eq.0h2v.s8.6285bb0d4998 from=translated src=- shape=f13f66ed vocab=e7e0d994
-/
@[simp] theorem polynomial_X (i : Var) : polynomial K (MvPolynomial.X i) = X K i := by
  simp [polynomial]

/--
@isnad1 id=eq.0h2v.s9.a03b70716552 from=translated src=- shape=2e45b3f1 vocab=532078a8
-/
@[simp] theorem polynomial_C (c : K) :
    polynomial K (MvPolynomial.C c) = algebraMap K (Algebra K) c := by
  exact (polynomial K).commutes c

/--
@isnad1 id=eq.0h3v.s10.f85a7ad5225e from=translated src=- shape=4b5671a4 vocab=4562e941
-/
theorem polynomial_commute (f g : MvPolynomial Var K) :
    polynomial K f * polynomial K g = polynomial K g * polynomial K f := by
  rw [← map_mul,← map_mul,mul_comm]

/-- Commuting a Weyl derivative past an arbitrary coordinate polynomial.
@isnad1 id=eq.0h3v.s10.5e4599c85fa5 from=translated src=- shape=65cb20b1 vocab=c606872a
-/
theorem deriv_polynomial (i : Var) (f : MvPolynomial Var K) :
    deriv K i * polynomial K f = polynomial K f * deriv K i + polynomial K (MvPolynomial.pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.pderiv_C,map_zero,add_zero]
    rw [polynomial_C]
    exact (_root_.Algebra.commutes c (deriv K i)).symm
  | add f g hf hg =>
    simp only [map_add,mul_add,add_mul,hf,hg]
    abel
  | mul_X f j hf =>
    simp only [map_mul,polynomial_X,MvPolynomial.pderiv_mul,map_add]
    rw [← mul_assoc,hf,add_mul,mul_assoc,deriv_X]
    by_cases h : i=j <;> simp [MvPolynomial.pderiv_X,h] <;> noncomm_ring

abbrev Poly := MvPolynomial Var K

def multiplication : Poly K →ₐ[K] Module.End K (Poly K) := _root_.Algebra.lmul K (Poly K)
def differential (i : Var) : Module.End K (Poly K) := (MvPolynomial.pderiv i).toLinearMap

/--
@isnad1 id=eq.0h3v.s9.dace5bbfaa5f from=translated src=- shape=1e7ffbf6 vocab=9738100e
-/
theorem multiplication_apply (f g : Poly K) : multiplication K f g = f*g := rfl
/--
@isnad1 id=eq.0h3v.s8.500fdeb08e94 from=translated src=- shape=f589b7c7 vocab=5d33bbfc
-/
theorem differential_apply (i : Var) (f : Poly K) : differential K i f = MvPolynomial.pderiv i f := rfl

/--
@isnad1 id=eq.0h3v.s11.3d3a7cb218c7 from=translated src=- shape=be273c43 vocab=977e4335
-/
theorem operator_xx (i j : Var) :
    multiplication K (MvPolynomial.X i) * multiplication K (MvPolynomial.X j) =
      multiplication K (MvPolynomial.X j) * multiplication K (MvPolynomial.X i) := by
  rw [← map_mul,← map_mul,mul_comm]

/--
@isnad1 id=eq.0h3v.s8.bf5b41cdbd15 from=translated src=- shape=36b32b4b vocab=248665c8
-/
theorem operator_dd (i j : Var) : differential K i * differential K j = differential K j * differential K i := by
  apply LinearMap.ext
  intro f
  exact Calculus.pderiv_comm i j f

/--
@isnad1 id=eq.0h3v.s10.f74f4bb45852 from=translated src=- shape=890bb90d vocab=361b2901
-/
theorem operator_dx (i j : Var) :
    differential K i * multiplication K (MvPolynomial.X j) =
      multiplication K (MvPolynomial.X j) * differential K i + if i=j then 1 else 0 := by
  apply LinearMap.ext
  intro f
  by_cases h : i=j <;>
    simp [Module.End.mul_apply,LinearMap.add_apply,multiplication_apply,differential_apply,
      MvPolynomial.pderiv_X,h]

/-- The polynomial differential-operator representation of the presented Weyl algebra.-/
def representation : Algebra K →ₐ[K] Module.End K (Poly K) :=
  lift K (fun i => multiplication K (MvPolynomial.X i)) (differential K)
    (operator_xx K) (operator_dd K) (operator_dx K)

/--
@isnad1 id=eq.0h2v.s9.5dc381bf3a59 from=translated src=- shape=b7be3ac6 vocab=819707ef
-/
@[simp] theorem representation_X (i : Var) :
    representation K (X K i) = multiplication K (MvPolynomial.X i) := lift_X _ _ _ _ _ _ _

/--
@isnad1 id=eq.0h2v.s8.b0c19e8364ba from=translated src=- shape=9ff8a0fb vocab=7bdf7b15
-/
@[simp] theorem representation_deriv (i : Var) :
    representation K (deriv K i) = differential K i := lift_deriv _ _ _ _ _ _ _

/--
@isnad1 id=eq.0h2v.s10.e7f934eccfae from=translated src=- shape=48f97a04 vocab=2ca0e85e
-/
theorem representation_polynomial (f : Poly K) :
    representation K (polynomial K f) = multiplication K f := by
  have he : (representation K).comp (polynomial K) = multiplication K := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact congrArg (fun e : Poly K →ₐ[K] Module.End K (Poly K) => e f) he

/-- Polynomial coordinates embed faithfully in the presented algebra.
@isnad1 id=injectiv.0h1v.s8.af90573c573b from=translated src=- shape=d4db8f43 vocab=f6044b8e
-/
theorem polynomial_injective : Function.Injective (polynomial K) := by
  intro f g h
  have he := congrArg (representation K) h
  rw [representation_polynomial,representation_polynomial] at he
  exact _root_.Algebra.lmul_injective he

/-- Product of two first-order monomials, with all coefficients on the left.
@isnad1 id=eq.0h5v.s10.ed7a838eeb36 from=translated src=- shape=404632ef vocab=d650c110
-/
theorem firstOrder_product (a b : Poly K) (i j : Var) :
    (polynomial K a * deriv K i) * (polynomial K b * deriv K j) =
      polynomial K (a*b) * (deriv K i * deriv K j) +
      polynomial K (a*MvPolynomial.pderiv i b) * deriv K j := by
  calc
    _ = polynomial K a * (deriv K i * polynomial K b) * deriv K j := by noncomm_ring
    _ = _ := by
      rw [deriv_polynomial]
      simp only [map_mul]
      noncomm_ring

/-- Cancellation of order-two terms in a commutator of first-order monomials.
@isnad1 id=eq.0h5v.s11.a310bfa30bd9 from=translated src=- shape=2752767e vocab=c5773385
-/
theorem firstOrder_commutator (a b : Poly K) (i j : Var) :
    (polynomial K a * deriv K i) * (polynomial K b * deriv K j) -
      (polynomial K b * deriv K j) * (polynomial K a * deriv K i) =
      polynomial K (a*MvPolynomial.pderiv i b) * deriv K j -
      polynomial K (b*MvPolynomial.pderiv j a) * deriv K i := by
  rw [firstOrder_product,firstOrder_product,mul_comm b a,deriv_commute K j i]
  abel

/-- A polynomial vector field as an actual element of the Weyl algebra.-/
def vectorField (a : Var → Poly K) : Algebra K := ∑ i, polynomial K (a i) * deriv K i

def vectorBracket (a b : Var → Poly K) (j : Var) : Poly K :=
  ∑ i, (a i * MvPolynomial.pderiv i (b j) - b i * MvPolynomial.pderiv i (a j))

/--
@isnad1 id=eq.0h3v.s7.85e4562c4716 from=translated src=- shape=a3306e75 vocab=8ff40d7c
-/
theorem vectorField_commutator (a b : Var → Poly K) :
    vectorField K a * vectorField K b - vectorField K b * vectorField K a =
      vectorField K (vectorBracket K a b) := by
  unfold vectorField vectorBracket
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun i j => (polynomial K (b j) * deriv K j) * (polynomial K (a i) * deriv K i))]
  simp only [← Finset.sum_sub_distrib,firstOrder_commutator]
  simp only [map_sum,map_sub,sub_mul,Finset.sum_mul,Finset.sum_sub_distrib]
  exact congrArg₂ (· - ·) rfl (Finset.sum_comm)

def hCoefficients (f : Poly K) : Var → Poly K :=
  ![MvPolynomial.pderiv 2 f,MvPolynomial.pderiv 3 f,-MvPolynomial.pderiv 0 f,-MvPolynomial.pderiv 1 f]

/-- The manuscript Hamiltonian vector field as an element of the presented algebra.-/
def hamiltonian (f : Poly K) : Algebra K := vectorField K (hCoefficients K f)

/--
@isnad1 id=eq.0h3v.s5.23f0032f6183 from=translated src=- shape=12ca2922 vocab=19780eb1
-/
theorem vectorBracket_hCoefficients (f g : Poly K) :
    vectorBracket K (hCoefficients K f) (hCoefficients K g) = hCoefficients K (bracketK K f g) := by
  funext j
  fin_cases j <;>
    simp [vectorBracket,hCoefficients,Fin.sum_univ_succ,bracketK,polyDerivK] <;>
    simp only [Calculus.pderiv_comm (1 : Var) 0, Calculus.pderiv_comm (2 : Var) 0,
      Calculus.pderiv_comm (3 : Var) 0, Calculus.pderiv_comm (2 : Var) 1,
      Calculus.pderiv_comm (3 : Var) 1, Calculus.pderiv_comm (3 : Var) 2] <;> ring

/--
@isnad1 id=eq.0h3v.s7.672607d2293e from=translated src=- shape=87685bc2 vocab=2cfdabc1
-/
theorem hamiltonian_commutator (f g : Poly K) :
    hamiltonian K f * hamiltonian K g - hamiltonian K g * hamiltonian K f =
      hamiltonian K (bracketK K f g) := by
  rw [hamiltonian,hamiltonian,vectorField_commutator,vectorBracket_hCoefficients]
  rfl

/--
@isnad1 id=eq.0h2v.s7.2a9bedca9313 from=translated src=- shape=2f145eaf vocab=551e18e1
-/
theorem hamiltonian_constant (c : K) : hamiltonian K (MvPolynomial.C c) = 0 := by
  simp [hamiltonian,vectorField,hCoefficients,Fin.sum_univ_succ]

/--
@isnad1 id=eq.0h3v.s10.7d1f07a3b315 from=translated src=- shape=cd5b04c1 vocab=9e6c9975
-/
theorem vectorField_polynomial (a : Var → Poly K) (f : Poly K) :
    vectorField K a * polynomial K f - polynomial K f * vectorField K a =
      polynomial K (∑ i, a i * MvPolynomial.pderiv i f) := by
  unfold vectorField
  simp only [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib,map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = polynomial K (a i) * (deriv K i * polynomial K f) -
        (polynomial K f * polynomial K (a i)) * deriv K i := by noncomm_ring
    _ = _ := by
      rw [deriv_polynomial,polynomial_commute K f (a i)]
      simp only [map_mul]
      noncomm_ring

/--
@isnad1 id=eq.0h3v.s9.97c861bb2fe8 from=translated src=- shape=3b439ace vocab=576d268e
-/
theorem hamiltonian_polynomial (f g : Poly K) :
    hamiltonian K f * polynomial K g - polynomial K g * hamiltonian K f =
      polynomial K (bracketK K f g) := by
  rw [hamiltonian,vectorField_polynomial]
  congr 1
  simp [hCoefficients,Fin.sum_univ_succ,bracketK,polyDerivK]
  ring

/--
@isnad1 id=eq.0h3v.s9.e52092434cff from=translated src=- shape=bd563f57 vocab=962b2487
-/
theorem representation_vectorField (a : Var → Poly K) (f : Poly K) :
    representation K (vectorField K a) f = ∑ i, a i * MvPolynomial.pderiv i f := by
  simp [vectorField,map_sum,LinearMap.sum_apply,Module.End.mul_apply,
    representation_polynomial,differential_apply,multiplication_apply]

/--
@isnad1 id=eq.0h3v.s9.85032549acaa from=translated src=- shape=893d92f5 vocab=66159979
-/
theorem representation_hamiltonian (f g : Poly K) :
    representation K (hamiltonian K f) g = bracketK K f g := by
  rw [hamiltonian,representation_vectorField]
  simp [hCoefficients,Fin.sum_univ_succ,bracketK,polyDerivK]
  ring

end
end Weyl
end RankTwoPoisson
