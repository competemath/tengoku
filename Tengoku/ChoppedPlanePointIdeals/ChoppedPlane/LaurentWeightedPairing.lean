module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.LaurentPairing
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.PolynomialFactorialWeights
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.HomogeneousTensorCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
Factorial-weighted perfect residue pairings on genuine finite Laurent grades.
Generator shifts are complemented by `g ↦ 2-g`; auxiliary monomials carry the
product of their exponent factorials, making differentiation adjoint to
multiplication by an auxiliary variable.
-/
noncomputable section
namespace ChoppedPlane.LaurentPairing
open Module
variable {K : Type*} [Field K] {ι : Type*}

/-- Diagonal coefficient rescaling is an actual equivalence on a finite
coefficient space whenever every weight is nonzero.-/
def coefficientWeightEquiv [Finite ι] (w : ι → K) (hw : ∀ i, w i ≠ 0) :
    (ι →₀ K) ≃ₗ[K] (ι →₀ K) :=
  (Finsupp.linearEquivFunOnFinite K K ι).trans
    ((LinearEquiv.piCongrRight (fun i => LinearEquiv.smulOfNeZero K K (w i) (hw i))).trans
      (Finsupp.linearEquivFunOnFinite K K ι).symm)

/--
@isnad1 id=eq.1h5v.s9.afacac046e04 from=translated src=- shape=5a7184aa vocab=77da2b47
-/
@[simp] theorem coefficientWeightEquiv_apply [Finite ι] (w : ι → K)
    (hw : ∀ i, w i ≠ 0) (p : ι →₀ K) (i : ι) :
    coefficientWeightEquiv w hw p i = w i * p i := rfl

/-- Complementary Laurent coefficient coordinates with a generator-dependent
nonzero coefficient weight.-/
def weightedNegativeCoordinates [Finite ι] (g : ι → ℤ) (r : ℤ)
    (w : ι → K) (hw : ∀ i, w i ≠ 0) :
    negativeGrade (K := K) g r ≃ₗ[K] (PositiveIndex g r →₀ K) :=
  (negativeCoordinates g r).trans
    (coefficientWeightEquiv (fun e : PositiveIndex g r => w e.val.1) (fun e => hw e.val.1))

/--
@isnad1 id=eq.1h7v.s11.68eb49c97ff4 from=translated src=- shape=794de362 vocab=dbe700f2
-/
@[simp] theorem weightedNegativeCoordinates_apply [Finite ι] (g : ι → ℤ) (r : ℤ)
    (w : ι → K) (hw : ∀ i, w i ≠ 0) (q : negativeGrade (K := K) g r)
    (e : PositiveIndex g r) :
    weightedNegativeCoordinates g r w hw q e = w e.val.1 * q.val (complementIndex g r e).val := rfl

/-- The weighted residue pairing identifies the actual negative Laurent grade
with the full linear dual of its complementary positive polynomial grade.-/
def weightedResidueDualEquiv [Finite ι] (g : ι → ℤ) (r : ℤ)
    (w : ι → K) (hw : ∀ i, w i ≠ 0) :
    negativeGrade (K := K) g r ≃ₗ[K] Module.Dual K (positiveGrade (K := K) g r) := by
  classical
  exact (weightedNegativeCoordinates g r w hw).trans
    ((positiveCoordinates g r).symm.trans (positiveBasis g r).toDualEquiv)

def weightedResiduePair [Finite ι] (g : ι → ℤ) (r : ℤ)
    (w : ι → K) (hw : ∀ i, w i ≠ 0) :
    negativeGrade (K := K) g r →ₗ[K] positiveGrade (K := K) g r →ₗ[K] K :=
  (weightedResidueDualEquiv g r w hw).toLinearMap

/-- Pairing with an actual positive monomial reads its weighted complementary
Laurent coefficient.
@isnad1 id=eq.1h7v.s12.6177d9d580b1 from=translated src=- shape=ae447f3b vocab=b9a89213
-/
@[simp] theorem weightedResiduePair_basis [Finite ι] (g : ι → ℤ) (r : ℤ)
    (w : ι → K) (hw : ∀ i, w i ≠ 0) (q : negativeGrade (K := K) g r)
    (e : PositiveIndex g r) :
    weightedResiduePair g r w hw q (positiveBasis g r e) =
      w e.val.1 * q.val (complementIndex g r e).val := by
  classical
  change (positiveBasis g r).toDualEquiv
    ((positiveCoordinates g r).symm (weightedNegativeCoordinates g r w hw q))
    (positiveBasis g r e) = _
  rw [Basis.toDualEquiv_apply, Basis.toDual_apply_left]
  change positiveCoordinates g r
    ((positiveCoordinates g r).symm (weightedNegativeCoordinates g r w hw q)) e = _
  rw [LinearEquiv.apply_symm_apply]
  exact weightedNegativeCoordinates_apply g r w hw q e

/-- Polynomial coordinate multiplication and projected Laurent coordinate
multiplication remain adjoint under the same generator weight.
@isnad1 id=eq.1h8v.s14.aded96b7eb66 from=translated src=- shape=ba0397ab vocab=c2fbf229
-/
theorem weightedResiduePair_shift [Finite ι] (g : ι → ℤ) (r : ℤ) (m : ℕ × ℕ)
    (w : ι → K) (hw : ∀ i, w i ≠ 0)
    (q : negativeGrade (K := K) g (r+m.1+m.2)) (p : positiveGrade (K := K) g r) :
    weightedResiduePair g (r+m.1+m.2) w hw q (positiveShift g r m p) =
      weightedResiduePair g r w hw (negativeShift g r m q) p := by
  have h : (weightedResiduePair g (r+m.1+m.2) w hw q).comp (positiveShift g r m) =
      weightedResiduePair g r w hw (negativeShift g r m q) := by
    apply (positiveBasis g r).ext
    intro e
    rw [LinearMap.comp_apply, positiveShift_basis, weightedResiduePair_basis,
      weightedResiduePair_basis, negativeShift_apply]
    have hn : -1 - e.val.2.1 < 0 ∧ -1 - e.val.2.2 < 0 := by
      obtain ⟨ha,hb,hab⟩ := e.property
      omega
    change w e.val.1 * q.val (e.val.1,(-1-(e.val.2.1+m.1),-1-(e.val.2.2+m.2))) =
      w e.val.1 * (if -1-e.val.2.1 < 0 ∧ -1-e.val.2.2 < 0 then
        q.val (e.val.1,((-1-e.val.2.1)-m.1,(-1-e.val.2.2)-m.2)) else 0)
    rw [ite_eq_left hn]
    exact congrArg (fun z : ℤ × ℤ => w e.val.1 * q.val (e.val.1,z))
      (Prod.ext (by omega) (by omega))
  exact LinearMap.congr_fun h p

/-- Under the actual free Laurent module identification, exponent translation
is literal multiplication by its coefficient-one Laurent monomial.
@isnad1 id=eq.0h5v.s10.3b688289aca2 from=translated src=- shape=502b1458 vocab=86e99999
-/
theorem freeLaurentEquiv_shift_mul [Finite ι] (m : ℤ × ℤ)
    (p : FreeLaurent K ι) (i : ι) :
    freeLaurentEquiv (shift m p) i =
      AddMonoidAlgebra.single m 1 * freeLaurentEquiv p i := by
  ext e
  simp only [freeLaurentEquiv_coeff, shift_apply,
    AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  exact congrArg (fun z : ℤ × ℤ => p (i,z)) (Prod.ext (by simp; omega) (by simp; omega))

/-- Negative coefficient projection is the actual componentwise negative
Laurent representative map.
@isnad1 id=eq.0h4v.s10.adb92c82d231 from=translated src=- shape=4dbeed66 vocab=cef2108b
-/
theorem freeLaurentEquiv_negativePart [Finite ι] (p : FreeLaurent K ι) (i : ι) :
    freeLaurentEquiv (freeNegativePart p) i = negativePart (freeLaurentEquiv p i) := by
  ext e
  simp

variable {J : Type*}

/-- Auxiliary symmetric monomials retain their coefficient-generator shift.-/
def auxiliaryGeneratorWeights (g : J → ℤ) (n : ℕ) : J × Sym (Fin 3) n → ℤ :=
  fun i => g i.1

/-- The factorial weight of one auxiliary symmetric monomial.-/
def auxiliaryFactorialWeight (n : ℕ) : J × Sym (Fin 3) n → K :=
  fun i => ChoppedPlane.factorialWeight K
    (SymmetricDerivative.homogeneousTensorExponent n i.2)

/--
@isnad1 id=ne.0h4v.s5.e591ca8dabf4 from=translated src=- shape=515da7db vocab=e93bd96e
-/
theorem auxiliaryFactorialWeight_ne_zero [CharZero K] (n : ℕ)
    (i : J × Sym (Fin 3) n) : auxiliaryFactorialWeight (K := K) n i ≠ 0 :=
  ChoppedPlane.factorialWeight_ne_zero K _

/-- The actual factorial-weighted finite perfect pairing required by symmetric
powers of the binary free module, including the complementary shifts `2-g`.-/
def auxiliaryResidueDualEquiv [Finite J] [CharZero K] (g : J → ℤ) (r : ℤ) (n : ℕ) :
    negativeGrade (K := K) (auxiliaryGeneratorWeights g n) r ≃ₗ[K]
      Module.Dual K (positiveGrade (K := K) (auxiliaryGeneratorWeights g n) r) :=
  weightedResidueDualEquiv (auxiliaryGeneratorWeights g n) r
    (auxiliaryFactorialWeight n) (auxiliaryFactorialWeight_ne_zero n)

def auxiliaryResiduePair [Finite J] [CharZero K] (g : J → ℤ) (r : ℤ) (n : ℕ) :
    negativeGrade (K := K) (auxiliaryGeneratorWeights g n) r →ₗ[K]
      positiveGrade (K := K) (auxiliaryGeneratorWeights g n) r →ₗ[K] K :=
  (auxiliaryResidueDualEquiv g r n).toLinearMap

/--
@isnad1 id=eq.0h7v.s13.0e104c3c2bf9 from=translated src=- shape=27778923 vocab=36d7782d
-/
@[simp] theorem auxiliaryResiduePair_basis [Finite J] [CharZero K]
    (g : J → ℤ) (r : ℤ) (n : ℕ)
    (q : negativeGrade (K := K) (auxiliaryGeneratorWeights g n) r)
    (e : PositiveIndex (auxiliaryGeneratorWeights g n) r) :
    auxiliaryResiduePair g r n q (positiveBasis (auxiliaryGeneratorWeights g n) r e) =
      ChoppedPlane.factorialWeight K (SymmetricDerivative.homogeneousTensorExponent n e.val.1.2) *
        q.val (complementIndex (auxiliaryGeneratorWeights g n) r e).val :=
  weightedResiduePair_basis _ _ _ _ _ _

end ChoppedPlane.LaurentPairing
