import Tengoku.Seed.RingTheory.Frobenius
import Tengoku.Seed.NumberTheory.RamificationInertia.Galois
import Tengoku.Seed.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Tengoku.Seed.LinearAlgebra.Matrix.Trace
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace Matrix

variable {R : Type*} [CommRing R]

/--
@isnad1 id=eq.0h2v.s8.fde14fb5b9c1 from=translated src=- shape=48f608a3 vocab=47a7532c
-/
theorem sq_eq_trace_smul_sub_det_smul_one (M : Matrix (Fin 2) (Fin 2) R) :
    M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
    Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/--
@isnad1 id=eq.0h3v.s9.11b062586957 from=translated src=- shape=c2afba95 vocab=d15b08ed
-/
theorem pow_add_two_eq_trace_smul_sub_det_smul (M : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    M ^ (k + 2) = M.trace • M ^ (k + 1) - M.det • M ^ k := by
  have h : M ^ (k + 2) = M ^ k * M ^ 2 := by rw [← pow_add]
  rw [h, sq_eq_trace_smul_sub_det_smul_one, Matrix.mul_sub, mul_smul_comm, mul_smul_comm,
    mul_one, ← pow_succ]

/--
@isnad1 id=eq.0h3v.s9.bfad2dd2e513 from=translated src=- shape=f43945af vocab=f26931c3
-/
theorem trace_pow_add_two (M : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    (M ^ (k + 2)).trace = M.trace * (M ^ (k + 1)).trace - M.det * (M ^ k).trace := by
  rw [pow_add_two_eq_trace_smul_sub_det_smul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

def HasDistinctRationalEigenvalues (M : Matrix (Fin 2) (Fin 2) R) : Prop :=
  ∃ α β : R, α ≠ β ∧ M.trace = α + β ∧ M.det = α * β

end Matrix

namespace FrobeniusDensity

open NumberField Ideal

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]

abbrev ratPrimeIdeal (ℓ : ℕ) : Ideal ℤ := Ideal.span {(ℓ : ℤ)}

/--
@isnad1 id=ne.1h1v.s4.defbf245cad2 from=translated src=- shape=b9a1ee8a vocab=fe8dca8e
-/
theorem ratPrimeIdeal_ne_bot {ℓ : ℕ} (hℓ : ℓ.Prime) : ratPrimeIdeal ℓ ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hℓ.ne_zero

/--
@isnad1 id=ismaxima.0h1v.s3.eda5aba845f4 from=translated src=- shape=825467dd vocab=fa8046ca
-/
instance isMaximal_ratPrimeIdeal (ℓ : ℕ) [Fact ℓ.Prime] : (ratPrimeIdeal ℓ).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible
    (Nat.prime_iff_prime_int.mp Fact.out).irreducible

variable {L}

omit [IsGalois ℚ L] in

/--
@isnad1 id=finite.1h2v.s7.91f66274c0ed from=translated src=- shape=92964f82 vocab=f901df24
-/
theorem finite_quotient_of_ne_bot {Q : Ideal (𝓞 L)} (hQ : Q ≠ ⊥) : Finite (𝓞 L ⧸ Q) :=
  Ring.HasFiniteQuotients.finiteQuotient hQ

omit [IsGalois ℚ L] in

/--
@isnad1 id=ne.1h3v.s7.48eadff7ed90 from=translated src=- shape=933e0fe6 vocab=b7dbe2e6
-/
theorem ne_bot_of_liesOver_ratPrimeIdeal {ℓ : ℕ} (hℓ : ℓ.Prime) {Q : Ideal (𝓞 L)}
    [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] : Q ≠ ⊥ :=
  Ideal.ne_bot_of_liesOver_of_ne_bot (ratPrimeIdeal_ne_bot hℓ) Q

variable (L)

def RealizesCyclicAt (σ : L ≃ₐ[ℚ] L) (ℓ : ℕ) : Prop :=
  ∃ _ : ℓ.Prime, ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (ratPrimeIdeal ℓ))
    (_ : Finite (𝓞 L ⧸ Q)),
    ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)

def Statement : Prop :=
  ∀ (σ : L ≃ₐ[ℚ] L) (S : Finset ℕ), ∃ ℓ : ℕ, ℓ ∉ S ∧ RealizesCyclicAt L σ ℓ

end FrobeniusDensity

namespace TaylorWiles

open NumberField Ideal FrobeniusDensity

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
variable {𝕜 : Type*} [Field 𝕜]

variable (L) in

abbrev ResidualRep (𝕜 : Type*) [Field 𝕜] := (L ≃ₐ[ℚ] L) →* Matrix (Fin 2) (Fin 2) 𝕜

variable (ρ : ResidualRep L 𝕜) (p n : ℕ)

def IsTaylorWilesPrime (q : ℕ) : Prop :=
  q.Prime ∧ q ≡ 1 [MOD p ^ n] ∧
    ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (ratPrimeIdeal q))
      (_ : Finite (𝓞 L ⧸ Q)),
      (ρ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)).HasDistinctRationalEigenvalues

structure Seed (S : Finset ℕ) where

  σ : L ≃ₐ[ℚ] L

  regular : (ρ σ).HasDistinctRationalEigenvalues

  congruent : ∀ ℓ : ℕ, ℓ ∉ S → RealizesCyclicAt L σ ℓ → ℓ ≡ 1 [MOD p ^ n]

def SeedExists (S : Finset ℕ) : Prop := Nonempty (Seed ρ p n S)

end TaylorWiles
