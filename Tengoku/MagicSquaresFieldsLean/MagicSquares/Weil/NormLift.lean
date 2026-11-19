import Tengoku.MagicSquaresFieldsLean.MagicSquares.Jacobi.Characters
import Tengoku.Seed.FieldTheory.Finite.GaloisField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

variable {F E : Type*} [Field F] [Field E] [Fintype E] [Algebra F E]

/-- A multiplicative character lifted to a finite extension via the norm.-/
noncomputable def normLift (chi : MulChar F ℂ) : MulChar E ℂ where
  toMonoidHom := chi.toMonoidHom.comp (Algebra.norm F)
  map_nonunit' x hx := by
    have hx0 : x = 0 := by simpa only [isUnit_iff_ne_zero, not_not] using hx
    change chi (Algebra.norm F x) = 0
    rw [hx0, Algebra.norm_zero, MulChar.map_zero]

@[simp]
theorem normLift_apply (chi : MulChar F ℂ) (x : E) :
    normLift (E := E) chi x = chi (Algebra.norm F x) := rfl

@[simp]
theorem normLift_one : normLift (F := F) (E := E) 1 = 1 := by
  apply MulChar.ext'
  intro x
  by_cases hx : x = 0
  · simp [hx, MulChar.map_zero]
  · have hn : Algebra.norm F x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
    simp only [normLift_apply, MulChar.one_apply (isUnit_iff_ne_zero.mpr hn),
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]

@[simp]
theorem normLift_mul (chi psi : MulChar F ℂ) :
    normLift (E := E) (chi * psi) = normLift (E := E) chi * normLift (E := E) psi := by
  apply MulChar.ext'
  intro x
  simp

/-- Norm lifting is a group homomorphism on character groups.-/
noncomputable def normLiftHom : MulChar F ℂ →* MulChar E ℂ where
  toFun := normLift
  map_one' := normLift_one
  map_mul' := normLift_mul

@[simp]
theorem normLift_pow (chi : MulChar F ℂ) (n : ℕ) :
    normLift (E := E) (chi ^ n) = normLift (E := E) chi ^ n :=
  map_pow (normLiftHom (F := F) (E := E)) chi n

/-- Surjectivity of the finite-field norm makes lifting injective.-/
theorem normLift_injective : Function.Injective (normLift (F := F) (E := E)) := by
  intro chi psi h
  apply MulChar.ext'
  intro x
  obtain ⟨y, hy⟩ := FiniteField.norm_surjective F E x
  have he := congrArg (fun theta : MulChar E ℂ => theta y) h
  simpa only [normLift_apply, hy] using he

@[simp]
theorem normLift_orderOf (chi : MulChar F ℂ) :
    orderOf (normLift (E := E) chi) = orderOf chi :=
  orderOf_injective (normLiftHom (F := F) (E := E)) normLift_injective chi

/-- A lifted nontrivial character remains nontrivial.-/
theorem normLift_ne_one {chi : MulChar F ℂ} (hchi : chi ≠ 1) :
    normLift (E := E) chi ≠ 1 := by
  intro h
  apply hchi
  apply normLift_injective (E := E)
  simpa using h

variable [Fintype F] [DecidableEq F] [DecidableEq E]

/-- In odd characteristic, the norm lift of the quadratic character is
exactly the quadratic character of the extension field. This permits the
proved Stepánov character estimate to be used on the lifted sums.-/
theorem normLift_quadraticCharC (hodd : ringChar F ≠ 2) :
    normLift (E := E) (quadraticCharC F) = quadraticCharC E := by
  have hoddE : ringChar E ≠ 2 := by rwa [← Algebra.ringChar_eq F E]
  apply mulChar_eq_of_sq_eq_one_of_ne_one (F := E)
    (normLift (E := E) (quadraticCharC F)) (quadraticCharC E)
  · change normLiftHom (F := F) (E := E) (quadraticCharC F) ^ 2 = 1
    rw [← map_pow, quadraticCharC_sq_eq_one, map_one]
  · exact quadraticCharC_sq_eq_one
  · exact normLift_ne_one (quadraticCharC_ne_one hodd)
  · exact quadraticCharC_ne_one hoddE

/-- Pointwise compatibility of the integer-valued quadratic characters
with extension norms.-/
theorem quadraticChar_norm (hodd : ringChar F ≠ 2) (x : E) :
    quadraticChar F (Algebra.norm F x) = quadraticChar E x := by
  have h := congrArg (fun chi : MulChar E ℂ => chi x) (normLift_quadraticCharC (E := E) hodd)
  simpa only [normLift_apply, quadraticCharC_apply, Int.cast_inj] using h

end MagicSquares.LN97
