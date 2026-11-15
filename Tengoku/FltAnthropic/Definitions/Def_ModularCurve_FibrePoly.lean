import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_KroneckerTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open Polynomial

namespace ModularCurve

section FibrePoly

variable {k : Type*} [Field k]

def fibrePoly (Φ : Polynomial (Polynomial ℤ)) (a : k) : Polynomial k :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom k) a)

variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]

/--
@isnad1 id=eq.0h3v.s7.aaeb929c139a from=translated src=- shape=fc5ddd96 vocab=bd48eaaf
-/
theorem eval₂RingHom_intCast_eq_comp (a : k) :
    Polynomial.eval₂RingHom (Int.castRingHom k) a =
      (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl ℓ) k) a).comp
        (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.comp_apply,
    Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]

/--
@isnad1 id=eq.0h4v.s8.85a84e250ed4 from=translated src=- shape=a8755537 vocab=585d40de
-/
theorem fibrePoly_eq_map_reduceModBivar (Φ : Polynomial (Polynomial ℤ)) (a : k) :
    fibrePoly Φ a =
      (reduceModBivar ℓ Φ).map
        (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl ℓ) k) a) := by
  rw [fibrePoly, eval₂RingHom_intCast_eq_comp (ℓ := ℓ),
    show reduceModBivar ℓ Φ
      = Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) from rfl,
    Polynomial.map_map]

end FibrePoly

section Factorization

variable {k : Type*} [Field k] {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ]

/--
@isnad1 id=eq.0h3v.s9.d8c5de26610e from=translated src=- shape=e07b8311 vocab=34f38831
-/
theorem C_sub_X_pow_eq_neg_pow (a : k) :
    Polynomial.C a - Polynomial.X ^ ℓ =
      -((Polynomial.X - Polynomial.C ((frobeniusEquiv k ℓ).symm a)) ^ ℓ) := by
  have hpoly : (Polynomial.X - Polynomial.C ((frobeniusEquiv k ℓ).symm a)) ^ ℓ =
      Polynomial.X ^ ℓ - Polynomial.C ((frobeniusEquiv k ℓ).symm a) ^ ℓ :=
    sub_pow_expChar _ _
  rw [hpoly, ← Polynomial.C_pow, frobeniusEquiv_symm_pow_p, neg_sub]

end Factorization

end ModularCurve
