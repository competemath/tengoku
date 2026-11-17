import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomologyEigen
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_exists_dividedDeriv_binaryFormRep_eq_det_pow_smul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_exists_dividedDeriv_binaryFormRep_eq_det_pow_smul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MvPolynomial in

/--
@isnad1 id=ex.0h3v.s15.a5e0620db353 from=translated src=- shape=ce9b9567 vocab=091fa285
-/
theorem HeckeEis.exists_dividedDeriv_binaryFormRep_eq_det_pow_smul (p : ℕ) [Fact p.Prime]
    (K : Type*) [Field K] [CharP K p] (a : ℕ) :
    ∃ D : ↥(HeckeEis.BinaryForm K (a + (p - 1))) →ₗ[K] ↥(HeckeEis.BinaryForm K (p - 1 - a)),
      (∀ F : ↥(HeckeEis.BinaryForm K (a + (p - 1))),
        ((D F : ↥(HeckeEis.BinaryForm K (p - 1 - a))) : MvPolynomial (Fin 2) K)
          = ∑ k ∈ Finset.Ico a p,
              monomial (Finsupp.single 0 (k - a) + Finsupp.single 1 (p - 1 - k))
                (coeff (Finsupp.single 0 k + Finsupp.single 1 (a + (p - 1) - k))
                  (F : MvPolynomial (Fin 2) K) * (k.descFactorial a : K))) ∧
      (∀ F : ↥(HeckeEis.BinaryForm K (a + (p - 1))),
        (X 1 : MvPolynomial (Fin 2) K) ^ a
            * ((D F : ↥(HeckeEis.BinaryForm K (p - 1 - a))) : MvPolynomial (Fin 2) K)
          = (fun G : MvPolynomial (Fin 2) K => pderiv 0 G)^[a] (F : MvPolynomial (Fin 2) K)) ∧
      (∀ (M : Matrix (Fin 2) (Fin 2) ℤ) (F : ↥(HeckeEis.BinaryForm K (a + (p - 1)))),
        D (HeckeEis.binaryFormRep K (a + (p - 1)) M F)
          = (((M.det : ℤ) : K) ^ a) • HeckeEis.binaryFormRep K (p - 1 - a) M (D F)) := by exact @_root_.P2MW.S_HeckeEis_exists_dividedDeriv_binaryFormRep_eq_det_pow_smul.solution p _ K _ _ a
