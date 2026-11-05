module

public import Tengoku.KummerCriterion.KummerCriterion.GaussSum.Basic
public import Tengoku.Seed.Analysis.Fourier.ZMod
public import Tengoku.Seed.NumberTheory.MulChar.Duality

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-Fourier sign invariants for quadratic Gauss sums

This file contains the trace and character-cancellation side of the
finite-Fourier sign-invariant package.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

open scoped BigOperators ComplexConjugate

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

/-- The discrete Fourier transform of the standard basis vector at `x` is the
`x`-th Fourier kernel row.
@isnad1 id=eq.0h3v.s8.7c659b13aa12 from=translated src=- shape=5ed8a822 vocab=d2554df5
-/
theorem dft_basisFun_apply (x k : ZMod p) :
    ZMod.dft (Pi.basisFun ℂ (ZMod p) x) k =
      ZMod.stdAddChar (N := p) (-(x * k)) := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, Pi.basisFun_apply, Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ x (fun y : ZMod p => ZMod.stdAddChar (N := p) (-(y * k)))]
  simp

/-- The DFT sends the delta function at `0` to the constant-one function.
@isnad1 id=eq.0h1v.s8.e742286b4763 from=translated src=- shape=4a5deca8 vocab=3aff00d0
-/
theorem dft_deltaZero_eq_constOne :
    ZMod.dft (Pi.basisFun ℂ (ZMod p) (0 : ZMod p)) = fun _ : ZMod p => (1 : ℂ) := by
  ext k
  rw [dft_basisFun_apply (p := p) (x := (0 : ZMod p)) (k := k)]
  simp

/-- The DFT of the constant-one function is concentrated at `0`.
@isnad1 id=eq.0h2v.s8.93fa43d3916d from=translated src=- shape=ac764f38 vocab=3a223374
-/
theorem dft_constOne (k : ZMod p) :
    ZMod.dft (fun _ : ZMod p => (1 : ℂ)) k = if k = 0 then p else 0 := by
  by_cases hk : k = 0
  · subst hk
    rw [ZMod.dft_apply_zero]
    simp
  · rw [ZMod.dft_apply, ite_eq_right hk]
    have hne : ((ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift (-k)) ≠ 1 := by
      intro hshift
      have heval : (ZMod.stdAddChar (N := p)) (-k) = 1 := by
        simpa [AddChar.mulShift_apply] using
          congrArg (fun ψ : AddChar (ZMod p) ℂ => ψ 1) hshift
      have hzero : (ZMod.stdAddChar (N := p)) (0 : ZMod p) = 1 := AddChar.map_zero_eq_one _
      have hkzero : (-k : ZMod p) = 0 := ZMod.injective_stdAddChar (heval.trans hzero.symm)
      exact hk (by simpa using hkzero)
    have hsum : ∑ j : ZMod p, ((ZMod.stdAddChar : AddChar (ZMod p) ℂ).mulShift (-k)) j = 0 :=
      AddChar.sum_eq_zero_of_ne_one hne
    simpa [AddChar.mulShift_apply, mul_comm, mul_left_comm, mul_assoc] using hsum

/-- Equivalently, the DFT sends the constant-one function to `p • δ₀`.
@isnad1 id=eq.0h1v.s8.53f58f27c316 from=translated src=- shape=2e26977b vocab=7867b1f3
-/
theorem dft_constOne_eq_prime_smul_deltaZero :
    ZMod.dft (fun _ : ZMod p => (1 : ℂ)) =
      (p : ℂ) • Pi.basisFun ℂ (ZMod p) (0 : ZMod p) := by
  ext k
  by_cases hk : k = 0
  · subst hk
    simp [dft_constOne (p := p), Pi.basisFun_apply]
  · simp [dft_constOne (p := p), hk, Pi.basisFun_apply]

/-- Any nontrivial Dirichlet character is sent by the DFT to a scalar multiple
of its inverse character.
@isnad1 id=eq.1h2v.s9.8e2acaf09c38 from=translated src=- shape=4a153ce2 vocab=51f46675
-/
theorem dft_eq_scalar_smul_inv_character {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) :
    ZMod.dft χ =
      (χ⁻¹ (-1) * gaussSum χ (ZMod.stdAddChar (N := p))) •
        (((χ⁻¹ : DirichletCharacter ℂ p) : ZMod p → ℂ)) := by
  have hprim : χ.IsPrimitive := DirichletCharacter.isPrimitive_of_ne_one (p := p) hχ
  ext k
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    ZMod.dft χ k = χ⁻¹ (-k) * gaussSum χ (ZMod.stdAddChar (N := p)) :=
      DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum
        (χ := χ) hprim k
    _ = (χ⁻¹ (-1) * gaussSum χ (ZMod.stdAddChar (N := p))) * χ⁻¹ k := by
      rw [show χ⁻¹ (-k) = χ⁻¹ (-1) * χ⁻¹ k by
        calc
          χ⁻¹ (-k) = χ⁻¹ ((-1 : ZMod p) * k) := by congr; ring
          _ = χ⁻¹ (-1) * χ⁻¹ k := by rw [map_mul]]
      ring

/-- A chosen multiplicative equivalence between complex-valued Dirichlet
characters mod `p` and the unit group `(ZMod p)ˣ`.-/
noncomputable def complexCharacterMulEquivUnits : DirichletCharacter ℂ p ≃* (ZMod p)ˣ := by
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  exact (MulChar.mulEquiv_units (ZMod p) ℂ).some

omit hp in
/-- A self-inverse character squares to the trivial character.
@isnad1 id=eq.1h2v.s7.c456443c46eb from=translated src=- shape=b611f109 vocab=e926b9b3
-/
theorem selfInverse_character_sq_eq_one {χ : DirichletCharacter ℂ p}
    (hχself : χ = χ⁻¹) : χ ^ 2 = 1 := by
  simpa [pow_two] using congrArg (fun ψ : DirichletCharacter ℂ p => ψ * χ) hχself

/-- Under the chosen unit-group equivalence, a self-inverse character maps to
an element of `(ZMod p)ˣ` whose square is `1`.
@isnad1 id=eq.1h2v.s8.06350ac7a1cc from=translated src=- shape=82f17030 vocab=3cc72577
-/
theorem selfInverse_character_image_sq_eq_one {χ : DirichletCharacter ℂ p}
    (hχself : χ = χ⁻¹) :
    (((complexCharacterMulEquivUnits (p := p) χ : (ZMod p)ˣ) : ZMod p) ^ 2) = 1 := by
  have hsq_units : (complexCharacterMulEquivUnits (p := p) χ : (ZMod p)ˣ) ^ 2 = 1 := by
    rw [← map_pow]
    simp [selfInverse_character_sq_eq_one (p := p) (χ := χ) hχself]
  simpa [Units.val_pow_eq_pow_val] using
    congrArg (fun u : (ZMod p)ˣ => ((u : ZMod p))) hsq_units

/-- Hence a self-inverse character maps to `1` or `-1` in `ZMod p`.
@isnad1 id=or.1h2v.s9.e6943c988178 from=translated src=- shape=61edb316 vocab=5934999a
-/
theorem selfInverse_character_image_eq_one_or_neg_one {χ : DirichletCharacter ℂ p}
    (hχself : χ = χ⁻¹) :
    ((complexCharacterMulEquivUnits (p := p) χ : (ZMod p)ˣ) : ZMod p) = 1 ∨
      ((complexCharacterMulEquivUnits (p := p) χ : (ZMod p)ˣ) : ZMod p) = -1 :=
  sq_eq_one_iff.mp <|
    selfInverse_character_image_sq_eq_one (p := p) (χ := χ) hχself

/-- Repackaging the previous lemma back in the unit group.
@isnad1 id=or.1h2v.s9.b6b7e4152cbf from=translated src=- shape=e9437b42 vocab=fbdbc16d
-/
theorem selfInverse_character_image_units_eq_one_or_neg_one {χ : DirichletCharacter ℂ p}
    (hχself : χ = χ⁻¹) :
    complexCharacterMulEquivUnits (p := p) χ = 1 ∨
      complexCharacterMulEquivUnits (p := p) χ = (-1 : (ZMod p)ˣ) := by
  rcases selfInverse_character_image_eq_one_or_neg_one (p := p) (χ := χ) hχself with hχ | hχ
  · left
    apply Units.ext
    simpa using hχ
  · right
    apply Units.ext
    simpa using hχ

/-- Under the chosen equivalence, the quadratic complex Dirichlet character
corresponds to the unit `-1`.
@isnad1 id=eq.1h1v.s8.72d18b4a8038 from=translated src=- shape=d9fc089a vocab=126801c0
-/
theorem complexCharacterMulEquivUnits_quadraticCharComplex (hp₂ : p ≠ 2) :
    complexCharacterMulEquivUnits (p := p) (quadraticCharComplex p) = (-1 : (ZMod p)ˣ) := by
  rcases selfInverse_character_image_units_eq_one_or_neg_one (p := p)
      (χ := quadraticCharComplex p) (quadraticCharComplex_inv (p := p)).symm with hχ | hχ
  · exact absurd ((complexCharacterMulEquivUnits (p := p)).injective (by simpa using hχ))
      (quadraticCharComplex_ne_one (p := p) hp₂)
  · exact hχ

/-- A self-inverse complex Dirichlet character is either trivial or quadratic.
@isnad1 id=or.2h2v.s7.e9974fcd1169 from=translated src=- shape=f2b25257 vocab=0cf7382b
-/
theorem selfInverse_character_eq_one_or_quadratic (hp₂ : p ≠ 2)
    {χ : DirichletCharacter ℂ p} (hχself : χ = χ⁻¹) :
    χ = 1 ∨ χ = quadraticCharComplex p := by
  rcases selfInverse_character_image_units_eq_one_or_neg_one (p := p) (χ := χ)
      hχself with hχ | hχ
  · left
    exact (complexCharacterMulEquivUnits (p := p)).injective (by simpa using hχ)
  · right
    exact (complexCharacterMulEquivUnits (p := p)).injective (by
      calc
        complexCharacterMulEquivUnits (p := p) χ = (-1 : (ZMod p)ˣ) := hχ
        _ = complexCharacterMulEquivUnits (p := p) (quadraticCharComplex p) := by
              symm
              exact complexCharacterMulEquivUnits_quadraticCharComplex (p := p) hp₂)

/-- The only nontrivial self-inverse complex Dirichlet character mod `p` is the
quadratic character.
@isnad1 id=eq.3h2v.s7.456ad9448d23 from=translated src=- shape=f91027a4 vocab=0cf7382b
-/
theorem nontrivial_selfInverse_character_eq_quadratic (hp₂ : p ≠ 2)
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) (hχself : χ = χ⁻¹) :
    χ = quadraticCharComplex p := by
  rcases selfInverse_character_eq_one_or_quadratic (p := p) hp₂ hχself with hχ1 | hχquad
  · exact (hχ hχ1).elim
  · exact hχquad

end SignInvariant

end KummerCriterion
