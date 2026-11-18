import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_aeval_const_term_eq_zero_of_forall_pos.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_aeval_const_term_eq_zero_of_forall_pos

namespace P2mAevalConstTerm

open Polynomial

/--
@isnad1 id=eq.0h3v.s7.15aad3004bcc from=translated src=- shape=82632093 vocab=ca75cd3c
-/
theorem pencil_at_zero {R d : ℕ} (M : Fin (d + 1) → Matrix (Fin R) (Fin R) ℂ) :
    (∑ a : Fin (d + 1), (((0 : ℝ) : ℂ) ^ (a : ℕ)) • M a) = M 0 := by
  rw [Fin.sum_univ_succ]
  simp

/--
@isnad1 id=continuo.0h4v.s8.fdd500d634c0 from=translated src=- shape=77695de7 vocab=deaccc32
-/
theorem continuous_pencil_aeval {R d : ℕ} (M : Fin (d + 1) → Matrix (Fin R) (Fin R) ℂ)
    (q : Polynomial ℂ) :
    Continuous fun y : ℝ =>
      Polynomial.aeval (∑ a : Fin (d + 1), ((y : ℂ) ^ (a : ℕ)) • M a) q := by
  have hsum : Continuous fun y : ℝ => ∑ a : Fin (d + 1), ((y : ℂ) ^ (a : ℕ)) • M a := by
    refine continuous_finsetSum _ fun a _ => ?_
    exact ((Complex.continuous_ofReal.pow _).smul continuous_const)
  exact q.continuous_aeval.comp hsum

end P2mAevalConstTerm

open Polynomial in
/--
@isnad1 id=eq.1h4v.s9.a4399212c1d1 from=translated src=- shape=a98a5b34 vocab=386fc84c
-/
theorem solution
    {R d : ℕ} (M : Fin (d + 1) → Matrix (Fin R) (Fin R) ℂ) (q : Polynomial ℂ)
    (h : ∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (d + 1), ((y : ℂ) ^ (a : ℕ)) • M a) q = 0) :
    Polynomial.aeval (M 0) q = 0 := by

  set F : ℝ → Matrix (Fin R) (Fin R) ℂ :=
    fun y => Polynomial.aeval (∑ a : Fin (d + 1), ((y : ℂ) ^ (a : ℕ)) • M a) q with hF
  have hcont : Continuous F := P2mAevalConstTerm.continuous_pencil_aeval M q
  have hclosed : IsClosed (F ⁻¹' {0}) := isClosed_singleton.preimage hcont
  have hsub : Set.Ioi (0 : ℝ) ⊆ F ⁻¹' {0} := fun y hy => h y hy
  have hcl : closure (Set.Ioi (0 : ℝ)) ⊆ F ⁻¹' {0} := hclosed.closure_subset_iff.mpr hsub
  have h0 : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact Set.self_mem_Ici
  have hF0 : F 0 = 0 := hcl h0

  have : F 0 = Polynomial.aeval (M 0) q := by
    simp only [hF]
    rw [P2mAevalConstTerm.pencil_at_zero M]
  rw [← this]
  exact hF0
