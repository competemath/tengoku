import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_coeffH1par_map_heckeT_comm.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_coeffH1par_map_heckeT_comm

set_option autoImplicit false

namespace HeckeEis
export _root_.HeckeEis (coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffHeckeFun coeffHeckeFun_apply BinaryForm binarySubst binarySubst_X binarySubst_C binaryFormRepSL binaryFormRepSL_apply_coe binaryFormAlphaAdj binaryFormAlphaAdj_apply_coe)
open _root_.HeckeEis

open MvPolynomial CongruenceSubgroup
open scoped MatrixGroups

namespace CoeffChangeAux

variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')

/--
@isnad1 id=eq.0h5v.s10.308397182d7f from=translated src=- shape=133141e1 vocab=96c9dafe
-/
theorem map_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (binarySubst R M p) = binarySubst R' M (MvPolynomial.map φ p) := by
  have h : (MvPolynomial.map φ).comp (binarySubst R M : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R).toRingHom
      = (binarySubst R' M : MvPolynomial (Fin 2) R' →ₐ[R'] MvPolynomial (Fin 2) R').toRingHom.comp (MvPolynomial.map φ) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp [binarySubst_C]
    · simp [binarySubst_X, Fin.sum_univ_two, map_add, map_mul]
  exact RingHom.congr_fun h p

/--
@isnad1 id=eq.0h6v.s11.0d6d8344fc7c from=translated src=- shape=8064a858 vocab=5cc49f0a
-/
theorem map_binaryFormAlphaAdj (n ℓ : ℕ) (v : ↥(BinaryForm R n)) :
    MvPolynomial.map φ ((binaryFormAlphaAdj R n ℓ v : ↥(BinaryForm R n)) : MvPolynomial (Fin 2) R)
      = binarySubst R' !![(ℓ : ℤ), 0; 0, 1] (MvPolynomial.map φ (v : MvPolynomial (Fin 2) R)) := by
  rw [binaryFormAlphaAdj_apply_coe, map_binarySubst]

/--
@isnad1 id=eq.1h9v.s13.ddf1583480dc from=translated src=- shape=5ad66a4c vocab=4fbd79a9
-/
theorem map_coeffHeckeFun (n N ℓ : ℕ) [NeZero ℓ]
    (z : Gamma0 N → ↥(BinaryForm R n)) (z' : Gamma0 N → ↥(BinaryForm R' n))
    (hz : ∀ g : Gamma0 N, ((z' g : ↥(BinaryForm R' n)) : MvPolynomial (Fin 2) R') = MvPolynomial.map φ ((z g : ↥(BinaryForm R n)) : MvPolynomial (Fin 2) R))
    (g : Gamma0 N) :
    ((coeffHeckeFun N ℓ ((binaryFormRepSL R' n).comp (Gamma0 N).subtype) (binaryFormAlphaAdj R' n ℓ) z' g : ↥(BinaryForm R' n)) :
        MvPolynomial (Fin 2) R')
      = MvPolynomial.map φ ((coeffHeckeFun N ℓ ((binaryFormRepSL R n).comp (Gamma0 N).subtype) (binaryFormAlphaAdj R n ℓ) z g :
        ↥(BinaryForm R n)) : MvPolynomial (Fin 2) R) := by
  rw [coeffHeckeFun_apply, coeffHeckeFun_apply, Submodule.coe_sum, Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  change binarySubst R' _ ((binaryFormAlphaAdj R' n ℓ (z' _) : ↥(BinaryForm R' n)) : MvPolynomial (Fin 2) R')
    = MvPolynomial.map φ (binarySubst R _ ((binaryFormAlphaAdj R n ℓ (z _) : ↥(BinaryForm R n)) : MvPolynomial (Fin 2) R))
  rw [map_binarySubst, map_binaryFormAlphaAdj, binaryFormAlphaAdj_apply_coe, hz]

end CoeffChangeAux

open CoeffChangeAux in

/--
@isnad1 id=eq.3h10v.s20.8235b662b552 from=translated src=- shape=52e68242 vocab=482fbafb
-/
theorem SolMain.C1 {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (n N ℓ : ℕ) [NeZero ℓ]
    (Φ : coeffH1par ((binaryFormRepSL R n).comp (Gamma0 N).subtype) →+ coeffH1par ((binaryFormRepSL R' n).comp (Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp (Gamma0 N).subtype)),
      ∃ w : ↥(coeffParabolicCocycles ((binaryFormRepSL R' n).comp (Gamma0 N).subtype)),
        (∀ g : Gamma0 N, ((w : Gamma0 N → ↥(BinaryForm R' n)) g : MvPolynomial (Fin 2) R')
            = MvPolynomial.map φ (((z : Gamma0 N → ↥(BinaryForm R n)) g : MvPolynomial (Fin 2) R))) ∧
        Φ (coeffH1parMk _ z) = coeffH1parMk _ w)
    (T : coeffH1par ((binaryFormRepSL R n).comp (Gamma0 N).subtype) →ₗ[R] coeffH1par ((binaryFormRepSL R n).comp (Gamma0 N).subtype))
    (hT : ∀ z : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp (Gamma0 N).subtype)),
      ∃ w : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp (Gamma0 N).subtype)),
        (w : Gamma0 N → ↥(BinaryForm R n)) = coeffHeckeFun N ℓ ((binaryFormRepSL R n).comp (Gamma0 N).subtype) (binaryFormAlphaAdj R n ℓ) z ∧
        T (coeffH1parMk _ z) = coeffH1parMk _ w)
    (T' : coeffH1par ((binaryFormRepSL R' n).comp (Gamma0 N).subtype) →ₗ[R'] coeffH1par ((binaryFormRepSL R' n).comp (Gamma0 N).subtype))
    (hT' : ∀ z : ↥(coeffParabolicCocycles ((binaryFormRepSL R' n).comp (Gamma0 N).subtype)),
      ∃ w : ↥(coeffParabolicCocycles ((binaryFormRepSL R' n).comp (Gamma0 N).subtype)),
        (w : Gamma0 N → ↥(BinaryForm R' n)) = coeffHeckeFun N ℓ ((binaryFormRepSL R' n).comp (Gamma0 N).subtype) (binaryFormAlphaAdj R' n ℓ) z ∧
        T' (coeffH1parMk _ z) = coeffH1parMk _ w)
    (x : coeffH1par ((binaryFormRepSL R n).comp (Gamma0 N).subtype)) :
    T' (Φ x) = Φ (T x) := by
  obtain ⟨z, rfl⟩ := coeffH1parMk_surjective _ x
  obtain ⟨w, hw, hTw⟩ := hT z
  obtain ⟨z', hz', hΦz⟩ := hΦ z
  obtain ⟨w', hw', hΦw⟩ := hΦ w
  obtain ⟨w'', hw'', hTz'⟩ := hT' z'
  rw [hTw, hΦw, hΦz, hTz']
  congr 1
  apply Subtype.ext
  funext g
  apply Subtype.ext
  rw [hw'', hw' g, map_coeffHeckeFun φ n N ℓ (z : Gamma0 N → ↥(BinaryForm R n)) z' hz' g, ← hw]

end HeckeEis

open scoped MatrixGroups in
/--
@isnad1 id=eq.3h10v.s20.8235b662b552 from=translated src=- shape=52e68242 vocab=482fbafb
-/
theorem solution {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (n N ℓ : ℕ) [NeZero ℓ]
    (Φ : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+ HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hΦ : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (∀ g : CongruenceSubgroup.Gamma0 N, ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R' n)) g : MvPolynomial (Fin 2) R')
            = MvPolynomial.map φ (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R n)) g : MvPolynomial (Fin 2) R))) ∧
        Φ (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (T : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[R] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hT : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R n)) = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj R n ℓ) z ∧
        T (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (T' : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[R'] HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype))
    (hT' : ∀ z : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
      ∃ w : ↥(HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        (w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R' n)) = HeckeEis.coeffHeckeFun N ℓ ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype) (HeckeEis.binaryFormAlphaAdj R' n ℓ) z ∧
        T' (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w)
    (x : HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)) :
    T' (Φ x) = Φ (T x) :=
  HeckeEis.SolMain.C1 φ n N ℓ Φ hΦ T hT T' hT' x

