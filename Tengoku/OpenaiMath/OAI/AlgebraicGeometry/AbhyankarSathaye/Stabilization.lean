import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.AbhyankarSathaye.Fiber
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.AbhyankarSathaye.NonCoordinate
import Tengoku

namespace OAI

/-!
# Adjoining unused variables

For every `n ≥ 4`, renaming `F` into the first four variables gives a quotient
isomorphic to a polynomial algebra in `n - 1` variables. The extended critical
point still has value `-1` and zero gradient, so the polynomial is not a coordinate.
-/

noncomputable section
namespace AbhyankarSathaye
open MvPolynomial

def fourInclusion {n : ℕ} (hn : 4 ≤ n) (i : Fin 4) : Fin n :=
  ⟨i.val, lt_of_lt_of_le i.isLt hn⟩

def extendedF {n : ℕ} (hn : 4 ≤ n) : MvPolynomial (Fin n) ℂ :=
  MvPolynomial.rename (fourInclusion hn) F

def blocksToAmbient {n : ℕ} (hn : 4 ≤ n) : Fin (n-4) ⊕ Fin 4 ≃ Fin n :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))

/--
@isnad1 id=eq.1h2v.s7.ab21ad8424b2 from=translated src=- shape=f95bfc82 vocab=550370dc
-/
theorem blocksToAmbient_original {n : ℕ} (hn : 4 ≤ n) (i : Fin 4) :
    blocksToAmbient hn (Sum.inr i) = fourInclusion hn i := by
  apply Fin.ext
  rfl

/--
@isnad1 id=eq.1h2v.s7.7a426cf6010c from=translated src=- shape=6c95a4fd vocab=17ef0404
-/
theorem blocksToAmbient_symm_original {n : ℕ} (hn : 4 ≤ n) (i : Fin 4) :
    (blocksToAmbient hn).symm (fourInclusion hn i) = Sum.inr i := by
  rw [← blocksToAmbient_original hn i, Equiv.symm_apply_apply]

def splitAmbient {n : ℕ} (hn : 4 ≤ n) :
    MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin (n-4)) R :=
  (renameEquiv ℂ (blocksToAmbient hn).symm).trans
    (sumAlgEquiv ℂ (Fin (n-4)) (Fin 4))

/--
@isnad1 id=eq.1h1v.s10.48025c7e1b7b from=translated src=- shape=3d9fa214 vocab=6f54149a
-/
theorem splitAmbient_comp_original {n : ℕ} (hn : 4 ≤ n) :
    (splitAmbient hn).toAlgHom.comp (rename (fourInclusion hn)) =
      IsScalarTower.toAlgHom ℂ R (MvPolynomial (Fin (n-4)) R) := by
  apply MvPolynomial.algHom_ext
  intro i
  change sumAlgEquiv ℂ (Fin (n-4)) (Fin 4)
    (rename (blocksToAmbient hn).symm (rename (fourInclusion hn) (X i))) = C (X i)
  rw [rename_X, rename_X, blocksToAmbient_symm_original]
  exact sumAlgEquiv_X_inr ℂ (Fin (n-4)) (Fin 4) i

/--
@isnad1 id=eq.1h1v.s9.239bdba8ab90 from=translated src=- shape=62cd6615 vocab=a64fadd9
-/
theorem splitAmbient_F {n : ℕ} (hn : 4 ≤ n) : splitAmbient hn (extendedF hn) = C F :=
  AlgHom.congr_fun (splitAmbient_comp_original hn) F

def blocksToOutput {n : ℕ} (hn : 4 ≤ n) : Fin (n-4) ⊕ Fin 3 ≃ Fin (n-1) :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))

def extendedFiberEquiv {n : ℕ} (hn : 4 ≤ n) :
    (MvPolynomial (Fin n) ℂ ⧸ Ideal.span {extendedF hn}) ≃ₐ[ℂ]
      MvPolynomial (Fin (n-1)) ℂ := by
  let J : Ideal (MvPolynomial (Fin (n-4)) R) := (Ideal.span {F}).map C
  have hi : J = (Ideal.span {extendedF hn}).map (splitAmbient hn : _ →+* _) := by
    simp [J, Ideal.map_span, splitAmbient_F]
  exact (Ideal.quotientEquivAlg (Ideal.span {extendedF hn}) J (splitAmbient hn) hi).trans
    (((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := Fin (n-4))
      (Ideal.span {F})).restrictScalars ℂ).symm.trans
      ((MvPolynomial.mapAlgEquiv (Fin (n-4)) fiberEquiv).trans
        ((sumAlgEquiv ℂ (Fin (n-4)) (Fin 3)).symm.trans
          (renameEquiv ℂ (blocksToOutput hn)))))

def extendedPoint {n : ℕ} (_hn : 4 ≤ n) (i : Fin n) : ℂ :=
  if hi : i.val < 4 then criticalPoint ⟨i.val, hi⟩ else 0

/--
@isnad1 id=eq.1h2v.s4.6731d5d68199 from=translated src=- shape=9dd1f7c5 vocab=c8a5bc15
-/
theorem extendedPoint_original {n : ℕ} (hn : 4 ≤ n) (i : Fin 4) :
    extendedPoint hn (fourInclusion hn i) = criticalPoint i := by
  simp [extendedPoint, fourInclusion, i.isLt]

/--
@isnad1 id=eq.2h2v.s5.413cd0ed9aec from=translated src=- shape=14844e33 vocab=7a271921
-/
theorem extendedPoint_unused {n : ℕ} (hn : 4 ≤ n) (i : Fin n) (hi : 4 ≤ i.val) :
    extendedPoint hn i = 0 := by
  simp [extendedPoint, Nat.not_lt.mpr hi]

/--
@isnad1 id=eq.1h2v.s8.d461ad323497 from=translated src=- shape=b3551111 vocab=bb92eed8
-/
theorem extended_eval {n : ℕ} (hn : 4 ≤ n) (f : R) :
    eval (extendedPoint hn) (rename (fourInclusion hn) f) = eval criticalPoint f := by
  rw [eval_rename]
  have he : extendedPoint hn ∘ fourInclusion hn = criticalPoint := by
    funext i
    exact extendedPoint_original hn i
  rw [he]

/--
@isnad1 id=eq.1h1v.s6.de994ad238ab from=translated src=- shape=8e77f56b vocab=2a2ed967
-/
theorem extendedF_eval {n : ℕ} (hn : 4 ≤ n) : eval (extendedPoint hn) (extendedF hn) = -1 := by
  rw [extendedF, extended_eval, eval_F]

/--
@isnad1 id=eq.1h2v.s8.07fcbdc9fc28 from=translated src=- shape=a8424d10 vocab=1d53fd2e
-/
theorem extendedF_critical {n : ℕ} (hn : 4 ≤ n) (i : Fin n) :
    eval (extendedPoint hn) (pderiv i (extendedF hn)) = 0 := by
  apply critical_of_ambient_identity
    (rename (fourInclusion hn) shiftX) (rename (fourInclusion hn) shiftY)
    (rename (fourInclusion hn) s) (extendedF hn) (extendedPoint hn)
  · simpa only [extendedF, map_add, map_pow, map_mul, map_one] using
      congrArg (rename (fourInclusion hn)) ambient
  · rw [extended_eval, eval_shiftX]
  · rw [extended_eval, eval_shiftY]
  · rw [extended_eval, eval_s]
  · exact extendedF_eval hn

/--
@isnad1 id=not.1h1v.s8.4bc35f14fa30 from=translated src=- shape=d1331688 vocab=de410419
-/
theorem extendedF_not_coordinate {n : ℕ} (hn : 4 ≤ n) :
    ¬ ∃ (e : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) (i : Fin n),
      e (X i) = extendedF hn :=
  no_coordinate_of_critical (extendedF hn) (extendedPoint hn) (extendedF_critical hn)

end AbhyankarSathaye

end

end OAI
