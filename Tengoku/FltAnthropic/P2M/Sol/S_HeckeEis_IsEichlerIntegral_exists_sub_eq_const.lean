import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_IsEichlerIntegral_exists_sub_eq_const.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_IsEichlerIntegral_exists_sub_eq_const

set_option autoImplicit false

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binarySubst binaryFormRepSL binaryFormRepSL_apply_coe IsEichlerIntegral)
open _root_.HeckeEis

open UpperHalfPlane MvPolynomial ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace EichlerIntegralAux

section Expansion

variable {K : Type*} [CommRing K] {n : ℕ}

variable (n) in

def degExps : Finset (Fin 2 →₀ ℕ) :=
  (Finset.range (n + 1)).image fun k => Finsupp.single 0 k + Finsupp.single 1 (n - k)

end Expansion

section Calculus

theorem apply_eq_apply_of_hasDerivAt_zero {D : ℂ → ℂ}
    (hD : ∀ τ : ℍ, HasDerivAt D 0 ↑τ) (z w : ℍ) : D ↑z = D ↑w := by
  have hmem : ∀ σ : ℍ, (↑σ : ℂ) ∈ {c : ℂ | 0 < c.im} := fun σ => σ.2
  refine isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero
    ((convex_halfSpace_im_gt 0).isPreconnected)
    (fun x hx => ((hD ⟨x, hx⟩).differentiableAt).differentiableWithinAt)
    (fun x hx => ?_) (hmem z) (hmem w)
  have h0 := ((hD ⟨x, hx⟩).hasFDerivAt).fderiv
  rw [Pi.zero_apply, h0]
  ext1
  simp

end Calculus

section RepDeriv

variable {n : ℕ}

end RepDeriv

end EichlerIntegralAux

open EichlerIntegralAux in

theorem SolMain.const {n : ℕ} {f : ℍ → ℂ} {F G : ℍ → ↥(BinaryForm ℂ n)}
    (hF : IsEichlerIntegral n f F) (hG : IsEichlerIntegral n f G) :
    ∃ v : ↥(BinaryForm ℂ n), ∀ τ : ℍ, F τ - G τ = v := by
  refine ⟨F I - G I, fun τ => ?_⟩
  apply Subtype.ext
  rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub]
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_sub, coeff_sub]
  have key : ∀ σ : ℍ, HasDerivAt
      (fun z : ℂ => coeff d ((F (ofComplex z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
        - coeff d ((G (ofComplex z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) 0 ↑σ :=
    fun σ => ((hF d σ).sub (hG d σ)).congr_deriv (sub_self _)
  have hc := apply_eq_apply_of_hasDerivAt_zero key τ I
  simpa only [ofComplex_apply] using hc

end HeckeEis

end

open scoped MatrixGroups ModularForm in
theorem solution {n : ℕ} {f : UpperHalfPlane → ℂ}
    {F G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (hG : HeckeEis.IsEichlerIntegral n f G) :
    ∃ v : ↥(HeckeEis.BinaryForm ℂ n), ∀ τ : UpperHalfPlane, F τ - G τ = v :=
  HeckeEis.SolMain.const hF hG

