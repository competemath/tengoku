import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomologyEigen
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_exists_coeffH1_map_ringHom_binaryFormRepSL

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_exists_coeffH1_map_ringHom_binaryFormRepSL.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_coeffH1_map_ringHom_binaryFormRepSL {R R' : Type*} [CommRing R] [CommRing R']
    (φ : R →+* R') (n N : ℕ) :
    ∃ Φ : HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype) →+
        HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype),
      (∀ z : ↥(HeckeEis.coeffCocycles
          ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        ∃ w : ↥(HeckeEis.coeffCocycles
          ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
          (∀ g : CongruenceSubgroup.Gamma0 N,
              ((w : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R' n)) g : MvPolynomial (Fin 2) R')
                = MvPolynomial.map φ
                    (((z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm R n)) g :
                      MvPolynomial (Fin 2) R))) ∧
          Φ (HeckeEis.coeffH1Mk _ z) = HeckeEis.coeffH1Mk _ w) ∧
      (∀ (c : R) (x : HeckeEis.coeffH1
          ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        Φ (c • x) = φ c • Φ x) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ]
        (T : HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)
          →ₗ[R] HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype))
        (T' : HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)
          →ₗ[R'] HeckeEis.coeffH1 ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)),
        HeckeEis.IsCoeffHeckeOnH1 N ℓ
            ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype)
            (HeckeEis.binaryFormAlphaAdj R n ℓ) T →
          HeckeEis.IsCoeffHeckeOnH1 N ℓ
            ((HeckeEis.binaryFormRepSL R' n).comp (CongruenceSubgroup.Gamma0 N).subtype)
            (HeckeEis.binaryFormAlphaAdj R' n ℓ) T' →
          ∀ x, Φ (T x) = T' (Φ x)) ∧
      (∀ π : R, Function.Surjective φ → (∀ a : R, φ a = 0 ↔ π ∣ a) → IsSMulRegular R π →
        ∀ x : HeckeEis.coeffH1
            ((HeckeEis.binaryFormRepSL R n).comp (CongruenceSubgroup.Gamma0 N).subtype),
          Φ x = 0 ↔ ∃ y, x = π • y) ∧
      (∀ r : R' →+ R, (∀ a : R, r (φ a) = a) → Function.Injective Φ) := by exact @_root_.P2MW.S_HeckeEis_exists_coeffH1_map_ringHom_binaryFormRepSL.solution R R' _ _ φ n N
