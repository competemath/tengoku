import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_CompletionBridge
import Tengoku.FltAnthropic.Theorems.Thm_PadicAlgCl_fixingSubgroup_adjoin_rootsOfUnity_coprime
import Tengoku.FltAnthropic.Theorems.Thm_PadicAlgCl_isIntegral_padicInt_iff_norm_le_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_exists_etale_padicInt_integers_of_inertia_le_fixingSubgroup.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_exists_etale_padicInt_integers_of_inertia_le_fixingSubgroup

set_option autoImplicit false

namespace E5ResShape
open Polynomial
section c12

open Polynomial IntermediateField

variable (p : ℕ) [hp : Fact p.Prime]
variable {L : Type} [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]

section generic

variable {E : Type} [Field E] [Algebra ℚ_[p] E] [Algebra ℤ_[p] E] [IsScalarTower ℤ_[p] ℚ_[p] E]
variable {m : ℕ} {ξ : E}

omit [Algebra ℚ_[p] E] [IsScalarTower ℤ_[p] ℚ_[p] E] in
/--
@isnad1 id=eq.1h4v.s9.c5a7dc56ff85 from=translated src=- shape=cb525623 vocab=fe13a2a0
-/
theorem aeval_X_pow_sub_one (hξ : ξ ^ m = 1) : aeval ξ ((X : ℤ_[p][X]) ^ m - C 1) = 0 := by
  simp [hξ]

omit [Algebra ℚ_[p] E] [IsScalarTower ℤ_[p] ℚ_[p] E] in
/--
@isnad1 id=isintegr.2h4v.s6.7b00aff3e33b from=translated src=- shape=ae0f69fa vocab=0f359d04
-/
theorem isIntegral_of_pow_eq_one (hξ : ξ ^ m = 1) (hm0 : 0 < m) : IsIntegral ℤ_[p] ξ :=
  ⟨(X : ℤ_[p][X]) ^ m - C 1, monic_X_pow_sub_C _ hm0.ne', by
    simpa [aeval_def] using aeval_X_pow_sub_one p hξ⟩

end generic

section cyclo

variable {m : ℕ} {ζ : L}

local notation "γ" => AdjoinSimple.gen ℚ_[p] ζ

omit [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L] in
/--
@isnad1 id=eq.1h4v.s9.6424eb316091 from=translated src=- shape=4e948621 vocab=f7192b11
-/
theorem gen_pow_eq_one (hζ : ζ ^ m = 1) : (γ) ^ m = 1 := by
  apply Subtype.ext
  simp [hζ]

/--
@isnad1 id=isintegr.2h4v.s8.be20aa406558 from=translated src=- shape=1f08f32c vocab=ec16e1ae
-/
theorem isIntegral_gen (hζ : ζ ^ m = 1) (hm0 : 0 < m) : IsIntegral ℤ_[p] (γ) :=
  isIntegral_of_pow_eq_one p (gen_pow_eq_one p hζ) hm0

end cyclo

end c12

end E5ResShape

namespace E5ResShape

open Polynomial IntermediateField

variable (p : ℕ) [Fact p.Prime]

local notation "Ω" => AlgebraicClosure ℚ_[p]
local notation "Γ" => (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])

end E5ResShape
