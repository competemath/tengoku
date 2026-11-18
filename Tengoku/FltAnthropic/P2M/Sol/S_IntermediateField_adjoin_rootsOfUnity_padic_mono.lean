import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_adjoin_rootsOfUnity_padic_mono.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_adjoin_rootsOfUnity_padic_mono

set_option autoImplicit false
set_option maxHeartbeats 1600000
open IntermediateField

theorem solution (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) {N N' : ℕ} (h : N ∣ N') :
    IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1} ≤
      IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N' - 1) = 1} := by
  apply IntermediateField.adjoin.mono
  intro ζ hζ
  obtain ⟨k, rfl⟩ := h
  obtain ⟨c, hc⟩ : q ^ N - 1 ∣ q ^ (N * k) - 1 := by
    rw [pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one (q ^ N) k
  change ζ ^ (q ^ (N * k) - 1) = 1
  rw [hc, pow_mul, show ζ ^ (q ^ N - 1) = 1 from hζ, one_pow]
