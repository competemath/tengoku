import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_finrank_adjoin_aeval_of_transcendental.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_finrank_adjoin_aeval_of_transcendental

set_option autoImplicit false

open Polynomial

namespace GaussPencil
namespace Mu

/--
@isnad1 id=eq.0h5v.s9.618d4d4ecc16 from=translated src=- shape=c2112e46 vocab=a44e337e
-/
theorem finrank_map_algEquiv {F L L' : Type*} [Field F] [Field L] [Field L'] [Algebra F L] [Algebra F L']
    (e : L ≃ₐ[F] L') (S : IntermediateField F L) :
    Module.finrank ↥(S.map (e : L →ₐ[F] L')) L' = Module.finrank ↥S L := by
  refine (Algebra.finrank_eq_of_equiv_equiv (S.equivMap (e : L →ₐ[F] L')).toRingEquiv e.toRingEquiv ?_).symm
  ext x
  rfl

/--
@isnad1 id=eq.1h2v.s11.cbd78e9d110f from=translated src=- shape=412815a1 vocab=36815364
-/
theorem finrank_adjoin_algebraMap_ratFunc (K : Type*) [Field K] (p : K[X]) (hp : 0 < p.natDegree) :
    Module.finrank ↥(IntermediateField.adjoin K ({algebraMap K[X] (RatFunc K) p} : Set (RatFunc K))) (RatFunc K)
      = p.natDegree := by
  rw [RatFunc.finrank_eq_max_natDegree, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, natDegree_one,
    max_eq_left (Nat.zero_le _)]

/--
@isnad1 id=eq.0h4v.s9.506f1888f6af from=translated src=- shape=ef86d9e6 vocab=8a6258e4
-/
theorem algEquiv_algebraMap {K L : Type*} [Field K] [Field L] [Algebra K L] (e : RatFunc K ≃ₐ[K] L) (p : K[X]) :
    e (algebraMap K[X] (RatFunc K) p) = aeval (e RatFunc.X) p := by
  rw [aeval_algHom_apply, RatFunc.aeval_X_left_eq_algebraMap]

end GaussPencil.Mu

/--
@isnad1 id=eq.3h4v.s10.51aee35466b8 from=translated src=- shape=5a75eb5b vocab=235916f0
-/
theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (s : L) (hs : Transcendental K s) (hgen : IntermediateField.adjoin K ({s} : Set L) = ⊤)
    (p : K[X]) (hp : 0 < p.natDegree) :
    Module.finrank ↥(IntermediateField.adjoin K ({Polynomial.aeval s p} : Set L)) L = p.natDegree := by
  obtain ⟨e, heX⟩ : ∃ e : RatFunc K ≃ₐ[K] L, e RatFunc.X = s :=
    ⟨(RatFunc.algEquivOfTranscendental s hs).trans
      ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv), by simp⟩
  have hmap : (IntermediateField.adjoin K ({algebraMap K[X] (RatFunc K) p} : Set (RatFunc K))).map
      (e : RatFunc K →ₐ[K] L) = IntermediateField.adjoin K ({aeval s p} : Set L) := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    show IntermediateField.adjoin K ({e (algebraMap K[X] (RatFunc K) p)} : Set L) = _
    rw [GaussPencil.Mu.algEquiv_algebraMap, heX]
  rw [← hmap, GaussPencil.Mu.finrank_map_algEquiv, GaussPencil.Mu.finrank_adjoin_algebraMap_ratFunc K p hp]
