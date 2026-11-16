import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard

set_option autoImplicit false

universe u v

open MvPolynomial

namespace MvPolynomialSmoothEngine

variable (S : Type u) [CommRing S] (ι : Type v)

noncomputable def polyGenerators : Algebra.Generators S (MvPolynomial ι S) ι where
  val := X
  σ' := _root_.id
  aeval_val_σ' s := by simp
  algebra := Algebra.id _
  algebraMap_eq := by
    ext p
    · simp
    · simp

/--
@isnad1 id=eq.0h2v.s9.43d243f0affe from=translated src=- shape=f2647a1c vocab=0eab0fc5
-/
theorem polyGenerators_ker : (polyGenerators S ι).ker = ⊥ := by
  rw [Algebra.Generators.ker_eq_ker_aeval_val]
  refine (RingHom.ker_eq_bot_iff_eq_zero _).mpr fun p hp => ?_
  simpa [polyGenerators] using hp

noncomputable def polyPresentation : Algebra.Presentation S (MvPolynomial ι S) ι PEmpty.{1} where
  toGenerators := polyGenerators S ι
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    rw [polyGenerators_ker]
    simp

noncomputable def polyPreSubmersive :
    Algebra.PreSubmersivePresentation S (MvPolynomial ι S) ι PEmpty.{1} where
  toPresentation := polyPresentation S ι
  map := PEmpty.elim
  map_inj a := a.elim

/--
@isnad1 id=eq.0h2v.s6.d41313d26eb4 from=translated src=- shape=d778523f vocab=095924b1
-/
theorem polyPreSubmersive_jacobian : (polyPreSubmersive S ι).jacobian = 1 := by
  classical
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  have h : (polyPreSubmersive S ι).jacobiMatrix = 1 := Matrix.ext fun i _ => i.elim
  rw [h, Matrix.det_one, map_one]

noncomputable def polySubmersive :
    Algebra.SubmersivePresentation S (MvPolynomial ι S) ι PEmpty.{1} where
  toPreSubmersivePresentation := polyPreSubmersive S ι
  jacobian_isUnit := by rw [polyPreSubmersive_jacobian]; exact isUnit_one

/--
@isnad1 id=isstanda.0h2v.s6.8995eef0a9a1 from=translated src=- shape=23624712 vocab=03071e93
-/
theorem isStandardSmoothOfRelativeDimension_mvPolynomial [Finite ι] :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) S (MvPolynomial ι S) :=
  (polySubmersive S ι).isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension])

end MvPolynomialSmoothEngine

/--
@isnad1 id=isstanda.0h2v.s6.8995eef0a9a1 from=translated src=- shape=23624712 vocab=03071e93
-/
theorem solution
    (S : Type u) [CommRing S] (ι : Type v) [Finite ι] :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) S (MvPolynomial ι S) :=
  MvPolynomialSmoothEngine.isStandardSmoothOfRelativeDimension_mvPolynomial S ι
