import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.FirstBlockIndependence
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.Translate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F]

/-!
# Translation of the block relation

For `E(X,Z)`, the translated block polynomial is `E(X+c,Z+c)`.
Over a field with `q` elements, `(X+c)^q = X^q+c`, so substituting
`Z = X^q` commutes with this simultaneous translation.  Its coefficients
retain their `X`-degree bound, and the translation is injective.
-/

noncomputable def blockTranslate (c : F) (E : Polynomial (Polynomial F)) :
    Polynomial (Polynomial F) :=
  Polynomial.taylor (C c) (E.map (Polynomial.taylorAlgHom c).toRingHom)

theorem coeffNatDegreeLE_taylor_constant {D : ℕ}
    {E : Polynomial (Polynomial F)} (hE : CoeffNatDegreeLE D E) (c : F) :
    CoeffNatDegreeLE D (Polynomial.taylor (C c) E) := by
  intro j
  rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_apply,
    Polynomial.sum_def, Polynomial.eval_finsetSum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  rw [Polynomial.eval_monomial]
  calc
    ((↑(k.choose j) * E.coeff k) * (C c) ^ (k - j)).natDegree
        ≤ (↑(k.choose j) * E.coeff k).natDegree + ((C c) ^ (k - j)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (0 + D) + 0 := by
      apply Nat.add_le_add
      · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (by simp) (hE k))
      · simp
    _ = D := by omega

theorem coeffNatDegreeLE_blockTranslate {D : ℕ}
    {E : Polynomial (Polynomial F)} (hE : CoeffNatDegreeLE D E) (c : F) :
    CoeffNatDegreeLE D (blockTranslate c E) := by
  apply coeffNatDegreeLE_taylor_constant
  intro j
  rw [Polynomial.coeff_map]
  change (Polynomial.taylor c (E.coeff j)).natDegree ≤ D
  simpa only [Polynomial.natDegree_taylor] using hE j

theorem blockTranslate_eq_zero_iff (c : F) (E : Polynomial (Polynomial F)) :
    blockTranslate c E = 0 ↔ E = 0 := by
  rw [blockTranslate, Polynomial.taylor_eq_zero]
  exact Polynomial.map_eq_zero_iff (Polynomial.taylor_injective c)

variable [Fintype F]

theorem taylor_X_pow_card (c : F) :
    Polynomial.taylor c (X ^ Fintype.card F) =
      (X : Polynomial F) ^ Fintype.card F + C c := by
  rw [Polynomial.taylor_X_pow]
  have h := (FiniteField.frobeniusAlgHom F (Polynomial F)).map_add X (C c)
  change (X + C c) ^ Fintype.card F =
    (X : Polynomial F) ^ Fintype.card F + (C c) ^ Fintype.card F at h
  simpa only [← Polynomial.C_pow, FiniteField.pow_card] using h

theorem blockEval_blockTranslate (c : F) (E : Polynomial (Polynomial F)) :
    blockEval (Fintype.card F) (blockTranslate c E) =
      Polynomial.taylor c (blockEval (Fintype.card F) E) := by
  unfold blockEval blockTranslate
  rw [Polynomial.taylor_eval]
  have h := Polynomial.eval₂_at_apply
    (Polynomial.taylorAlgHom c).toRingHom (X ^ Fintype.card F) (p := E)
  rw [← Polynomial.eval_map] at h
  change eval (Polynomial.taylor c (X ^ Fintype.card F))
    (E.map (Polynomial.taylorAlgHom c).toRingHom) =
      Polynomial.taylor c (eval (X ^ Fintype.card F) E) at h
  rw [taylor_X_pow_card] at h
  exact h

theorem BlockRelation.blockTranslate {m : ℕ} {g : Polynomial F}
    {E : Fin m → Polynomial (Polynomial F)}
    (hrel : BlockRelation (Fintype.card F) g E) (c : F) :
    BlockRelation (Fintype.card F) (Polynomial.taylor c g)
      (fun i => blockTranslate c (E i)) := by
  have h := congrArg (Polynomial.taylorAlgHom c) hrel
  simp only [BlockRelation, map_sum, map_mul, map_pow, map_zero] at h ⊢
  change (∑ i : Fin m, Polynomial.taylor c (blockEval (Fintype.card F) (E i)) *
    (Polynomial.taylor c g) ^ (i : ℕ)) = 0 at h
  simpa only [blockEval_blockTranslate] using h

end LN97
end MagicSquares
