module

public import Tengoku.Seed.NumberTheory.MulChar.Basic
public import Tengoku
public import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.Seed.Tactic.ENatToNat
import Tengoku.Seed.Tactic.NormNum.Irrational
import Tengoku.Seed.Tactic.NormNum.IsCoprime
import Tengoku.Seed.Tactic.NormNum.IsSquare
import Tengoku.Seed.Tactic.NormNum.LegendreSymbol
import Tengoku.Seed.Tactic.NormNum.ModEq
import Tengoku.Seed.Tactic.NormNum.NatFib
import Tengoku.Seed.Tactic.NormNum.NatLog
import Tengoku.Seed.Tactic.NormNum.NatSqrt
import Tengoku.Seed.Tactic.NormNum.Ordinal
import Tengoku.Seed.Tactic.NormNum.Parity
import Tengoku.Seed.Tactic.NormNum.Prime
import Tengoku.Seed.Tactic.NormNum.RealSqrt
import Tengoku.Seed.Tactic.ReduceModChar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Deleted Fourier matrices on the augmentation subspace

This file proves the finite-group determinant identity behind the real
cyclotomic-unit regulator computation. The statement is abstract: for a
finite abelian group `G`, a function `q: G → ℂ`, and the deleted matrix
`(q (h * k⁻¹) - q h)` indexed by `G \ {1}`, its determinant is the product of
the nontrivial Fourier coefficients.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace KummerCriterion
namespace CyclotomicUnits

/-- The non-identity elements of a group.-/
abbrev Nonidentity (G : Type*) [One G] := {g : G // g ≠ 1}

/-- The nontrivial multiplicative characters of a group.-/
abbrev NontrivChar (G : Type*) [CommMonoid G] :=
  {χ : MulChar G ℂ // χ ≠ 1}

/-- A subtype sum over `x ≠ a₀` as an erased finite-set sum.
@isnad1 id=eq.0h3v.s6.948dbd4ca3f5 from=translated src=- shape=d3d786a4 vocab=d23c3cad
-/
theorem sum_subtype_ne_eq_sum_erase {α : Type*} [Fintype α] [DecidableEq α]
    (a₀ : α) (f : α → ℂ) [Fintype {x : α // x ≠ a₀}] :
    ∑ x : {x : α // x ≠ a₀}, f x.val =
      ∑ x ∈ (Finset.univ : Finset α).erase a₀, f x :=
  (Finset.sum_subtype _ (fun x => by simp) f).symm

section FiniteGroup

variable {G : Type*} [CommGroup G] [Fintype G]

/-- The deleted set has one fewer element than the group.
@isnad1 id=eq.0h1v.s6.24ea6f9e0983 from=translated src=- shape=636fe6fc vocab=3033fa1c
-/
theorem card_nonidentity_add_one [DecidableEq G] :
    Fintype.card (Nonidentity G) + 1 = Fintype.card G := by
  have hnon :
      Fintype.card (Nonidentity G) = Fintype.card G - 1 := by
    simp [Nonidentity]
  rw [hnon]
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨(1 : G)⟩))

/-- The cardinality of a finite group is nonzero as a complex number.
@isnad1 id=ne.0h1v.s4.ee2d6bb53fc8 from=translated src=- shape=6d554f3a vocab=e254b31d
-/
theorem card_group_ne_zero_complex :
    ((Fintype.card G : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(1 : G)⟩).ne'

/-- The restricted sum of a nontrivial character over `G \ {1}` is `-1`.
@isnad1 id=eq.1h2v.s8.f8da0635b901 from=translated src=- shape=c51f75cf vocab=c428515d
-/
theorem sum_nonidentity_mulChar_eq_neg_one
    [DecidableEq G]
    (χ : MulChar G ℂ) (hχ : χ ≠ 1) :
    ∑ h : Nonidentity G, χ h.val = -1 := by
  classical
  have hfull : ∑ g : G, χ g = 0 := MulChar.sum_eq_zero_of_ne_one hχ
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))] at hfull
  rw [← sum_subtype_ne_eq_sum_erase (α := G) (a₀ := 1) (f := fun g => χ g)] at hfull
  have hsplit : (1 : ℂ) + ∑ h : Nonidentity G, χ h.val = 0 := by
    simpa using hfull
  linear_combination hsplit

/-- Orthogonality after deleting the identity row.
@isnad1 id=eq.0h3v.s8.55f6c87d641b from=translated src=- shape=ce7ad5ed vocab=ac42c82a
-/
theorem sum_nonidentity_inv_mulChar_mul
    [DecidableEq G]
    [DecidableEq (MulChar G ℂ)]
    (χ ψ : MulChar G ℂ) :
    ∑ h : Nonidentity G, (χ h.val)⁻¹ * ψ h.val =
      if χ = ψ then (Fintype.card (Nonidentity G) : ℂ) else -1 := by
  classical
  by_cases hχψ : χ = ψ
  · subst hχψ
    rw [ite_eq_left rfl]
    rw [show (∑ h : Nonidentity G, (χ h.val)⁻¹ * χ h.val) =
        ∑ _h : Nonidentity G, (1 : ℂ) from by
      refine Finset.sum_congr rfl ?_
      intro h _
      have h_unit : IsUnit (χ h.val) := IsUnit.map χ.toMonoidHom (Group.isUnit h.val)
      exact inv_mul_cancel₀ h_unit.ne_zero]
    simp
  · rw [ite_eq_right hχψ]
    have hchar : χ⁻¹ * ψ ≠ 1 := by rwa [Ne, inv_mul_eq_one]
    rw [← sum_nonidentity_mulChar_eq_neg_one (G := G) (χ⁻¹ * ψ) hchar]
    refine Finset.sum_congr rfl ?_
    intro h _
    rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv']

/-- Fourier coefficient with the inverse-character convention.-/
def deletedFourierCoeff (q : G → ℂ) (χ : MulChar G ℂ) : ℂ :=
  ∑ h : G, q h * (χ h)⁻¹

/-- The deleted character matrix, with rows reindexed by an equivalence
between nontrivial characters and non-identity elements.-/
def deletedCharacterMatrix
    (ρ : NontrivChar G ≃ Nonidentity G) :
    Matrix (NontrivChar G) (NontrivChar G) ℂ :=
  Matrix.of fun h χ => χ.val (ρ h).val

/-- The corrected left inverse of the deleted character matrix. The `-1`
term is the rank-one correction that appears after deleting the trivial row
and the trivial character.-/
def deletedCharacterMatrixLeftInverse
    (ρ : NontrivChar G ≃ Nonidentity G) :
    Matrix (NontrivChar G) (NontrivChar G) ℂ :=
  Matrix.of fun χ h =>
    ((Fintype.card G : ℕ) : ℂ)⁻¹ * ((χ.val (ρ h).val)⁻¹ - 1)

/-- The corrected deleted character matrix inverse is a left inverse.
@isnad1 id=eq.0h2v.s8.6839f6f55ffa from=translated src=- shape=a9e22a0b vocab=8d18abe1
-/
theorem deletedCharacterMatrix_leftInverse
    [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) :
    deletedCharacterMatrixLeftInverse (G := G) ρ *
        deletedCharacterMatrix (G := G) ρ = 1 := by
  classical
  ext χ ψ
  simp only [deletedCharacterMatrixLeftInverse, deletedCharacterMatrix, Matrix.mul_apply,
    Matrix.of_apply, Matrix.one_apply]
  rw [Equiv.sum_comp ρ (fun h : Nonidentity G =>
    (((Fintype.card G : ℕ) : ℂ)⁻¹ * ((χ.val h.val)⁻¹ - 1)) * ψ.val h.val)]
  rw [show (∑ h : Nonidentity G,
      ((Fintype.card G : ℕ) : ℂ)⁻¹ * ((χ.val h.val)⁻¹ - 1) * ψ.val h.val) =
      ∑ h : Nonidentity G,
        ((Fintype.card G : ℕ) : ℂ)⁻¹ *
          (((χ.val h.val)⁻¹ - 1) * ψ.val h.val) from by
    refine Finset.sum_congr rfl ?_
    intro h _
    ring]
  rw [← Finset.mul_sum]
  have hsplit :
      (∑ h : Nonidentity G, ((χ.val h.val)⁻¹ - 1) * ψ.val h.val) =
        (∑ h : Nonidentity G, (χ.val h.val)⁻¹ * ψ.val h.val) -
          ∑ h : Nonidentity G, ψ.val h.val := by
    simp_rw [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib]
  rw [hsplit]
  rw [sum_nonidentity_inv_mulChar_mul (G := G) χ.val ψ.val]
  rw [sum_nonidentity_mulChar_eq_neg_one (G := G) ψ.val ψ.property]
  by_cases hχψ : χ = ψ
  · subst hχψ
    simp only [ite_true]
    have hcard : ((Fintype.card (Nonidentity G) : ℕ) : ℂ) + 1 =
        ((Fintype.card G : ℕ) : ℂ) := by
      exact_mod_cast card_nonidentity_add_one (G := G)
    have hnz : ((Fintype.card G : ℕ) : ℂ) ≠ 0 :=
      card_group_ne_zero_complex (G := G)
    rw [sub_neg_eq_add, hcard, inv_mul_cancel₀ hnz]
  · have hval : χ.val ≠ ψ.val := fun h =>
      hχψ (Subtype.ext h)
    simp [hval, hχψ]

/-- Full Fourier reindexing for the inverse-character convention.
@isnad1 id=eq.0h4v.s7.d5d0104fc74d from=translated src=- shape=9fdc0100 vocab=0a2cb990
-/
theorem sum_translate_inv_mulChar
    (q : G → ℂ) (χ : MulChar G ℂ) (h : G) :
    ∑ k : G, q (h * k⁻¹) * χ k =
      χ h * deletedFourierCoeff (G := G) q χ := by
  classical
  let e : G ≃ G := (Equiv.inv G).trans (Equiv.mulLeft h)
  have he_apply : ∀ k : G, e k = h * k⁻¹ := by
    intro k
    rfl
  have hsum := Equiv.sum_comp e (fun t : G => q t * χ (t⁻¹ * h))
  have hleft :
      (∑ k : G, q (e k) * χ ((e k)⁻¹ * h)) =
        ∑ k : G, q (h * k⁻¹) * χ k := by
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [he_apply]
    have hk : (h * k⁻¹)⁻¹ * h = k := by group
    rw [hk]
  rw [hleft] at hsum
  rw [hsum]
  unfold deletedFourierCoeff
  have hterm : ∀ t : G, q t * χ (t⁻¹ * h) =
      χ h * (q t * (χ t)⁻¹) := by
    intro t
    rw [map_mul, map_inv]
    ring
  rw [Finset.sum_congr rfl (fun t _ => hterm t)]
  rw [← Finset.mul_sum]

/-- The first summand of the deleted convolution-character product.
@isnad1 id=eq.0h4v.s8.82431a5d69d0 from=translated src=- shape=e7ed8e78 vocab=f04beef1
-/
theorem sum_nonidentity_translate_inv_mulChar
    [DecidableEq G]
    (q : G → ℂ) (χ : MulChar G ℂ) (h : G) :
    ∑ k : Nonidentity G, q (h * k.val⁻¹) * χ k.val =
      χ h * deletedFourierCoeff (G := G) q χ - q h := by
  classical
  have hfull := sum_translate_inv_mulChar (G := G) q χ h
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))] at hfull
  rw [← sum_subtype_ne_eq_sum_erase (α := G) (a₀ := 1)
    (f := fun k : G => q (h * k⁻¹) * χ k)] at hfull
  have hsplit :
      q h + ∑ k : Nonidentity G, q (h * k.val⁻¹) * χ k.val =
        χ h * deletedFourierCoeff (G := G) q χ := by
    simpa using hfull
  linear_combination hsplit

/-- Deleted convolution against a nontrivial character gives the Fourier
coefficient eigenvalue.
@isnad1 id=eq.1h4v.s8.2032d360cfcd from=translated src=- shape=8aaa4548 vocab=f04beef1
-/
theorem sum_nonidentity_deletedConvolution_mulChar
    [DecidableEq G]
    (q : G → ℂ) (χ : MulChar G ℂ) (hχ : χ ≠ 1) (h : G) :
    ∑ k : Nonidentity G, (q (h * k.val⁻¹) - q h) * χ k.val =
      χ h * deletedFourierCoeff (G := G) q χ := by
  classical
  have hfirst := sum_nonidentity_translate_inv_mulChar (G := G) q χ h
  have hchar := sum_nonidentity_mulChar_eq_neg_one (G := G) χ hχ
  have hsplit :
      (∑ k : Nonidentity G, (q (h * k.val⁻¹) - q h) * χ k.val) =
        (∑ k : Nonidentity G, q (h * k.val⁻¹) * χ k.val) -
          q h * ∑ k : Nonidentity G, χ k.val := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsplit, hfirst, hchar]
  ring

/-- The deleted convolution matrix on `G \ {1}`.-/
def deletedConvolutionMatrix
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    Matrix (NontrivChar G) (NontrivChar G) ℂ :=
  Matrix.of fun h k => q ((ρ h).val * (ρ k).val⁻¹) - q (ρ h).val

/-- The same deleted convolution matrix with the literal `G \ {1}` indices.-/
def deletedConvolutionMatrixOnNonidentity (q : G → ℂ) :
    Matrix (Nonidentity G) (Nonidentity G) ℂ :=
  Matrix.of fun h k => q (h.val * k.val⁻¹) - q h.val

omit [Fintype G] in
/-- Reindexing the literal deleted convolution matrix by `ρ` gives the
character-indexed matrix used in the diagonalization proof.
@isnad1 id=eq.0h3v.s8.5c77c3b465dc from=translated src=- shape=0b4ff331 vocab=e532608f
-/
theorem deletedConvolutionMatrix_eq_submatrix
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    deletedConvolutionMatrix (G := G) ρ q =
      (deletedConvolutionMatrixOnNonidentity (G := G) q).submatrix ρ ρ := by
  ext h k
  rfl

/-- Deleted convolution diagonalizes against the deleted character matrix.
@isnad1 id=eq.0h3v.s9.0cc9e2ebdd12 from=translated src=- shape=f297ece9 vocab=7bd1d665
-/
theorem deletedConvolution_mul_deletedCharacter
    [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    deletedConvolutionMatrix (G := G) ρ q *
        deletedCharacterMatrix (G := G) ρ =
      deletedCharacterMatrix (G := G) ρ *
        Matrix.diagonal (fun χ : NontrivChar G =>
          deletedFourierCoeff (G := G) q χ.val) := by
  classical
  ext h χ
  simp only [deletedConvolutionMatrix, deletedCharacterMatrix, Matrix.mul_apply,
    Matrix.of_apply, Matrix.diagonal_apply]
  rw [Equiv.sum_comp ρ (fun k : Nonidentity G =>
    (q ((ρ h).val * k.val⁻¹) - q (ρ h).val) * χ.val k.val)]
  rw [sum_nonidentity_deletedConvolution_mulChar
    (G := G) q χ.val χ.property (ρ h).val]
  rw [Finset.sum_eq_single χ]
  · simp
  · intro ψ _ hψ
    rw [ite_eq_right hψ, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ χ) hmem

/-- Deleted Fourier determinant identity, in the `hk⁻¹` convention.
@isnad1 id=eq.0h3v.s9.a8bf5d8a492a from=translated src=- shape=b0f61067 vocab=3458797f
-/
theorem det_deletedConvolutionMatrix_eq_prod_deletedFourierCoeff
    [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    (deletedConvolutionMatrix (G := G) ρ q).det =
      ∏ χ : NontrivChar G, deletedFourierCoeff (G := G) q χ.val := by
  classical
  have hmul := deletedConvolution_mul_deletedCharacter (G := G) ρ q
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have hP : (deletedCharacterMatrix (G := G) ρ).det ≠ 0 :=
    Matrix.det_ne_zero_of_left_inverse
      (deletedCharacterMatrix_leftInverse (G := G) ρ)
  exact mul_right_cancel₀ hP (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdet)

/-- The deleted Fourier determinant identity in literal `G \ {1}` indices.
@isnad1 id=eq.0h3v.s9.456c308b69f8 from=translated src=- shape=553c2718 vocab=bd81645f
-/
theorem det_deletedConvolutionMatrixOnNonidentity_eq_prod_deletedFourierCoeff
    [DecidableEq G] [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    (deletedConvolutionMatrixOnNonidentity (G := G) q).det =
      ∏ χ : NontrivChar G, deletedFourierCoeff (G := G) q χ.val := by
  have h := det_deletedConvolutionMatrix_eq_prod_deletedFourierCoeff
    (G := G) ρ q
  rw [deletedConvolutionMatrix_eq_submatrix] at h
  rwa [Matrix.det_submatrix_equiv_self] at h

/-- Inversion preserves the deleted index set.-/
def nonidentityInvEquiv : Nonidentity G ≃ Nonidentity G where
  toFun h := ⟨h.val⁻¹, inv_ne_one.mpr h.property⟩
  invFun h := ⟨h.val⁻¹, inv_ne_one.mpr h.property⟩
  left_inv h := by
    ext
    simp
  right_inv h := by
    ext
    simp

/-- The deleted convolution matrix in the `hk` convention used by the real
cyclotomic-unit logarithm matrix.-/
def deletedConvolutionMulMatrixOnNonidentity (q : G → ℂ) :
    Matrix (Nonidentity G) (Nonidentity G) ℂ :=
  Matrix.of fun h k => q (h.val * k.val) - q h.val

/-- The arbitrary-row deleted matrix in the `hk` convention, with rows ordered
as `h = h₀ * r`, `r ∈ G \ {1}`.-/
def deletedConvolutionMulMatrixAtReindexed (h₀ : G) (q : G → ℂ) :
    Matrix (Nonidentity G) (Nonidentity G) ℂ :=
  Matrix.of fun h k => q (h₀ * h.val * k.val) - q (h₀ * h.val)

omit [Fintype G] in
/-- Reindexing rows by `h = h₀ * r` in the `hk` convention translates `q`.
@isnad1 id=eq.0h3v.s6.a485c3edf64d from=translated src=- shape=84e5be72 vocab=ef270e62
-/
theorem deletedConvolutionMulMatrixAtReindexed_eq_translated
    (h₀ : G) (q : G → ℂ) :
    deletedConvolutionMulMatrixAtReindexed (G := G) h₀ q =
      deletedConvolutionMulMatrixOnNonidentity (G := G) (fun h => q (h₀ * h)) := by
  ext h k
  simp [deletedConvolutionMulMatrixAtReindexed, deletedConvolutionMulMatrixOnNonidentity,
    mul_assoc]

omit [Fintype G] in
/-- The `hk` matrix is a row-inversion permutation of the `hk⁻¹` matrix
`x ↦ q(x⁻¹)`.
@isnad1 id=eq.0h2v.s8.d80be42d9c58 from=translated src=- shape=b6fd291f vocab=3a611c86
-/
theorem deletedConvolutionMulMatrix_eq_invRow_submatrix (q : G → ℂ) :
    deletedConvolutionMulMatrixOnNonidentity (G := G) q =
      (deletedConvolutionMatrixOnNonidentity (G := G) (fun x => q x⁻¹)).submatrix
        (nonidentityInvEquiv (G := G)) id := by
  ext h k
  simp [deletedConvolutionMulMatrixOnNonidentity, deletedConvolutionMatrixOnNonidentity,
    nonidentityInvEquiv, mul_comm]

/-- Fourier coefficient for the non-inverse character convention.-/
def deletedFourierCoeffMul (q : G → ℂ) (χ : MulChar G ℂ) : ℂ :=
  ∑ h : G, χ h * q h

omit [Fintype G] in
/-- The product of all character values at a fixed group element has square
one.
@isnad1 id=eq.0h2v.s7.7cd63fe24b7e from=translated src=- shape=42e32021 vocab=acfa0ac6
-/
theorem prod_mulChar_apply_sq_eq_one
    [Fintype (MulChar G ℂ)] (h₀ : G) :
    (∏ χ : MulChar G ℂ, χ h₀) ^ 2 = 1 := by
  classical
  set P : ℂ := ∏ χ : MulChar G ℂ, χ h₀
  have hP_inv : P = P⁻¹ := by
    calc
      P = ∏ χ : MulChar G ℂ, χ h₀ := rfl
      _ = ∏ χ : MulChar G ℂ, (χ⁻¹) h₀ := by
        rw [← Equiv.prod_comp (Equiv.inv (MulChar G ℂ)) (fun χ => χ h₀)]
        rfl
      _ = ∏ χ : MulChar G ℂ, (χ h₀)⁻¹ := by
        refine Finset.prod_congr rfl ?_
        intro χ _
        rw [MulChar.inv_apply_eq_inv']
      _ = P⁻¹ := by
        rw [Finset.prod_inv_distrib]
  have hP_ne : P ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro χ _
    exact (IsUnit.map χ.toMonoidHom (Group.isUnit h₀)).ne_zero
  calc
    P ^ 2 = P * P := pow_two P
    _ = P * P⁻¹ := congrArg (fun z => P * z) hP_inv
    _ = 1 := mul_inv_cancel₀ hP_ne

omit [Fintype G] in
/-- The product of the nontrivial character values at a fixed group element
has square one.
@isnad1 id=eq.0h2v.s8.37945759652e from=translated src=- shape=109a5ed7 vocab=5b847753
-/
theorem prod_nontriv_mulChar_apply_sq_eq_one
    [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)] (h₀ : G) :
    (∏ χ : NontrivChar G, χ.val h₀) ^ 2 = 1 := by
  classical
  have herase :
      (∏ χ : NontrivChar G, χ.val h₀) =
        ∏ χ ∈ (Finset.univ : Finset (MulChar G ℂ)).erase 1, χ h₀ := by
    rw [Finset.prod_subtype
      (p := fun χ : MulChar G ℂ => χ ≠ 1)
      (s := (Finset.univ : Finset (MulChar G ℂ)).erase 1)
      (f := fun χ => χ h₀)]
    intro χ
    simp [Finset.mem_erase]
  rw [herase]
  have hfull := prod_mulChar_apply_sq_eq_one (G := G) h₀
  have htriv : (1 : MulChar G ℂ) h₀ = 1 :=
    MulChar.one_apply (Group.isUnit h₀)
  have herase_full :
      (∏ χ ∈ (Finset.univ : Finset (MulChar G ℂ)).erase 1, χ h₀) =
        ∏ χ : MulChar G ℂ, χ h₀ :=
    Finset.prod_erase (s := (Finset.univ : Finset (MulChar G ℂ)))
      (f := fun χ => χ h₀) (a := 1) htriv
  rw [herase_full]
  exact hfull

omit [Fintype G] in
/-- The product of inverse nontrivial character values at a fixed group
element also has square one.
@isnad1 id=eq.0h2v.s8.5dafccd3d722 from=translated src=- shape=0563e53f vocab=e401b59d
-/
theorem prod_nontriv_mulChar_apply_inv_sq_eq_one
    [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)] (h₀ : G) :
    (∏ χ : NontrivChar G, (χ.val h₀)⁻¹) ^ 2 = 1 := by
  classical
  rw [show (∏ χ : NontrivChar G, (χ.val h₀)⁻¹) =
      (∏ χ : NontrivChar G, χ.val h₀)⁻¹ from by
    rw [Finset.prod_inv_distrib]]
  rw [inv_pow, prod_nontriv_mulChar_apply_sq_eq_one (G := G) h₀, inv_one]

/-- Translating the input of `q` by `h₀` multiplies the non-inverse-character
Fourier coefficient by `(χ h₀)⁻¹`.
@isnad1 id=eq.0h4v.s6.67445ae95eb2 from=translated src=- shape=2defb411 vocab=351c42e5
-/
theorem deletedFourierCoeffMul_mulLeft
    (q : G → ℂ) (χ : MulChar G ℂ) (h₀ : G) :
    deletedFourierCoeffMul (G := G) (fun h => q (h₀ * h)) χ =
      (χ h₀)⁻¹ * deletedFourierCoeffMul (G := G) q χ := by
  classical
  unfold deletedFourierCoeffMul
  have hsum := Equiv.sum_comp (Equiv.mulLeft h₀)
    (fun h : G => χ (h₀⁻¹ * h) * q h)
  have hleft :
      (∑ x : G, χ (h₀⁻¹ * (Equiv.mulLeft h₀) x) *
          q ((Equiv.mulLeft h₀) x)) =
        ∑ x : G, χ x * q (h₀ * x) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    simp
  rw [hleft] at hsum
  rw [hsum]
  have hterm : ∀ h : G, χ (h₀⁻¹ * h) * q h =
      (χ h₀)⁻¹ * (χ h * q h) := by
    intro h
    rw [map_mul, map_inv]
    ring
  rw [Finset.sum_congr rfl (fun h _ => hterm h)]
  rw [← Finset.mul_sum]

/-- Inverting the argument changes the inverse-character coefficient into the
non-inverse-character coefficient.
@isnad1 id=eq.0h3v.s5.852f6d88608c from=translated src=- shape=9ecdae83 vocab=b404b80d
-/
theorem deletedFourierCoeff_invArg_eq_mul
    (q : G → ℂ) (χ : MulChar G ℂ) :
    deletedFourierCoeff (G := G) (fun x => q x⁻¹) χ =
      deletedFourierCoeffMul (G := G) q χ := by
  classical
  unfold deletedFourierCoeff deletedFourierCoeffMul
  have hsum := Equiv.sum_comp (Equiv.inv G)
    (fun h : G => q h * (χ h⁻¹)⁻¹)
  have hleft :
      (∑ x : G, q ((Equiv.inv G) x) * (χ ((Equiv.inv G) x)⁻¹)⁻¹) =
        ∑ x : G, q x⁻¹ * (χ x)⁻¹ := by
    refine Finset.sum_congr rfl ?_
    intro x _
    simp
  rw [hleft] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl ?_
  intro h _
  rw [map_inv]
  rw [inv_inv]
  rw [mul_comm]

/-- Squared determinant identity in the `hk` convention. The square removes
the sign of the row-inversion permutation.
@isnad1 id=eq.0h3v.s9.8e82ec526eb7 from=translated src=- shape=2e176e33 vocab=30c7a20b
-/
theorem det_deletedConvolutionMulMatrixOnNonidentity_sq_eq_prod_deletedFourierCoeffMul_sq
    [DecidableEq G] [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    (deletedConvolutionMulMatrixOnNonidentity (G := G) q).det ^ 2 =
      (∏ χ : NontrivChar G, deletedFourierCoeffMul (G := G) q χ.val) ^ 2 := by
  classical
  rw [deletedConvolutionMulMatrix_eq_invRow_submatrix]
  rw [Matrix.det_permute]
  rw [mul_pow]
  rw [show ((↑↑(Equiv.Perm.sign (nonidentityInvEquiv (G := G))) : ℂ)) ^ 2 = 1 from ?_]
  · rw [one_mul]
    rw [det_deletedConvolutionMatrixOnNonidentity_eq_prod_deletedFourierCoeff
      (G := G) ρ (fun x => q x⁻¹)]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro χ _
    exact deletedFourierCoeff_invArg_eq_mul (G := G) q χ.val
  · have h_sign : (Equiv.Perm.sign (nonidentityInvEquiv (G := G))) ^ 2 = 1 :=
      Int.units_pow_two _
    have h_cast : (((Equiv.Perm.sign (nonidentityInvEquiv (G := G))) ^ 2 : ℤˣ) : ℂ) =
        ((1 : ℤˣ) : ℂ) := by
      rw [h_sign]
    push_cast at h_cast ⊢
    exact_mod_cast h_cast

/-- Arbitrary omitted-row determinant identity in the `hk` convention, squared.
The explicit character factor is kept; in applications it is a sign.
@isnad1 id=eq.0h4v.s9.2eebea81cc29 from=translated src=- shape=b57ce948 vocab=044afbad
-/
theorem det_deletedConvolutionMulMatrixAtReindexed_sq_eq_charFactor_mul_prod_sq
    [DecidableEq G] [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (h₀ : G) (q : G → ℂ) :
    (deletedConvolutionMulMatrixAtReindexed (G := G) h₀ q).det ^ 2 =
      ((∏ χ : NontrivChar G, (χ.val h₀)⁻¹) *
        ∏ χ : NontrivChar G, deletedFourierCoeffMul (G := G) q χ.val) ^ 2 := by
  classical
  rw [deletedConvolutionMulMatrixAtReindexed_eq_translated]
  rw [det_deletedConvolutionMulMatrixOnNonidentity_sq_eq_prod_deletedFourierCoeffMul_sq
    (G := G) ρ (fun h => q (h₀ * h))]
  congr 1
  simp_rw [deletedFourierCoeffMul_mulLeft (G := G) q]
  rw [Finset.prod_mul_distrib]

/-- Arbitrary omitted-row determinant identity in the `hk` convention, squared,
with the harmless character factor removed.
@isnad1 id=eq.0h4v.s9.f27c8518d5f7 from=translated src=- shape=faf67705 vocab=d9867bb0
-/
theorem det_deletedConvolutionMulMatrixAtReindexed_sq_eq_prod_deletedFourierCoeffMul_sq
    [DecidableEq G] [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (h₀ : G) (q : G → ℂ) :
    (deletedConvolutionMulMatrixAtReindexed (G := G) h₀ q).det ^ 2 =
      (∏ χ : NontrivChar G, deletedFourierCoeffMul (G := G) q χ.val) ^ 2 := by
  classical
  rw [det_deletedConvolutionMulMatrixAtReindexed_sq_eq_charFactor_mul_prod_sq
    (G := G) ρ h₀ q]
  rw [mul_pow, prod_nontriv_mulChar_apply_inv_sq_eq_one (G := G) h₀, one_mul]

end FiniteGroup

end CyclotomicUnits
end KummerCriterion
