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

/--
@isnad1 id=eq.0h4v.s7.409cab545d8a from=translated src=- shape=f47c232f vocab=a21b1df0
-/
@[simp]
theorem normLift_apply (chi : MulChar F ℂ) (x : E) :
    normLift (E := E) chi x = chi (Algebra.norm F x) := rfl

/--
@isnad1 id=eq.0h2v.s7.a8518c4d95d6 from=translated src=- shape=48c00b31 vocab=50280835
-/
@[simp]
theorem normLift_one : normLift (F := F) (E := E) 1 = 1 := by
  apply MulChar.ext'
  intro x
  by_cases hx : x = 0
  · simp [hx, MulChar.map_zero]
  · have hn : Algebra.norm F x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
    simp only [normLift_apply, MulChar.one_apply (isUnit_iff_ne_zero.mpr hn),
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]

/--
@isnad1 id=eq.0h4v.s8.73b05c0583ab from=translated src=- shape=f3a09f39 vocab=e675e8d4
-/
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

/--
@isnad1 id=eq.0h4v.s8.7ed22e0632a5 from=translated src=- shape=c7d38b70 vocab=e2fba08b
-/
@[simp]
theorem normLift_pow (chi : MulChar F ℂ) (n : ℕ) :
    normLift (E := E) (chi ^ n) = normLift (E := E) chi ^ n :=
  map_pow (normLiftHom (F := F) (E := E)) chi n

/-- Surjectivity of the finite-field norm makes lifting injective.
@isnad1 id=injectiv.0h2v.s6.8bf4283ece23 from=translated src=- shape=b0d41f7c vocab=f9346f0d
-/
theorem normLift_injective : Function.Injective (normLift (F := F) (E := E)) := by
  intro chi psi h
  apply MulChar.ext'
  intro x
  obtain ⟨y, hy⟩ := FiniteField.norm_surjective F E x
  have he := congrArg (fun theta : MulChar E ℂ => theta y) h
  simpa only [normLift_apply, hy] using he

/--
@isnad1 id=eq.0h3v.s7.d9f64b09429b from=translated src=- shape=54f913af vocab=8a0ac9c9
-/
@[simp]
theorem normLift_orderOf (chi : MulChar F ℂ) :
    orderOf (normLift (E := E) chi) = orderOf chi :=
  orderOf_injective (normLiftHom (F := F) (E := E)) normLift_injective chi

/-- A lifted nontrivial character remains nontrivial.
@isnad1 id=ne.1h3v.s7.9ab1499e5873 from=translated src=- shape=386cdfa6 vocab=50280835
-/
theorem normLift_ne_one {chi : MulChar F ℂ} (hchi : chi ≠ 1) :
    normLift (E := E) chi ≠ 1 := by
  intro h
  apply hchi
  apply normLift_injective (E := E)
  simpa using h

variable [Fintype F] [DecidableEq F] [DecidableEq E]

/-- In odd characteristic, the norm lift of the quadratic character is
exactly the quadratic character of the extension field. This permits the
proved Stepánov character estimate to be used on the lifted sums.
@isnad1 id=eq.1h2v.s6.36ff6d9eb867 from=translated src=- shape=b4e52355 vocab=2c6b871b
-/
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
with extension norms.
@isnad1 id=eq.1h3v.s7.4d0ab6a9c597 from=translated src=- shape=10ceb5bc vocab=bed0e1ce
-/
theorem quadraticChar_norm (hodd : ringChar F ≠ 2) (x : E) :
    quadraticChar F (Algebra.norm F x) = quadraticChar E x := by
  have h := congrArg (fun chi : MulChar E ℂ => chi x) (normLift_quadraticCharC (E := E) hodd)
  simpa only [normLift_apply, quadraticCharC_apply, Int.cast_inj] using h

end MagicSquares.LN97
