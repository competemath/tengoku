import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_Module_End_eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_End_pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_End_pow_eq_one_of_isNilpotent_pow_sub_one_of_forall_commute_of_forall_isUnit_of_finrank_eq

set_option autoImplicit false

/--
@isnad1 id=eq.4h6v.s9.3a989ca51dd3 from=translated src=- shape=237cea51 vocab=97f2ba08
-/
theorem solution
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {D : Type*} [Ring D] [Algebra F D] (hD : ∀ x : D, x ≠ 0 → IsUnit x)
    (ι : D →ₐ[F] Module.End F V) (hdim : Module.finrank F D = Module.finrank F V)
    {g : Module.End F V} (hcomm : ∀ d : D, Commute (ι d) g) {e : ℕ}
    (he : IsNilpotent (g ^ e - 1)) : g ^ e = 1 :=
  sub_eq_zero.mp <|
    Module.End.eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq hD ι hdim
      (N := g ^ e - 1) (fun d => ((hcomm d).pow_right e).sub_right (Commute.one_right _)) he
