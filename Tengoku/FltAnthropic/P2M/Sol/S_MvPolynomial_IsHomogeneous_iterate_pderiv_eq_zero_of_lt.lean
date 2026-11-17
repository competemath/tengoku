import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt

set_option autoImplicit false

namespace MvPolynomial
export _root_.MvPolynomial (coeff R pderiv_C totalDegree_eq_zero_iff_eq_C C IsHomogeneous pderiv)
namespace DegAux
open _root_.MvPolynomial

open _root_.MvPolynomial open _root_.P2MW.S_MvPolynomial_IsHomogeneous_iterate_pderiv_eq_zero_of_lt.MvPolynomial

theorem isHomogeneous_iterate_pderiv {σ R : Type*} [CommSemiring R] {φ : MvPolynomial σ R} {n : ℕ} (k : σ)
    (hφ : φ.IsHomogeneous n) (j : ℕ) : ((pderiv k)^[j] φ).IsHomogeneous (n - j) := by
  induction j with
  | zero => simpa using hφ
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    simpa [Nat.sub_sub] using ih.pderiv

theorem iterate_pderiv_eq_zero_of_lt {σ R : Type*} [CommSemiring R] {φ : MvPolynomial σ R} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (k : σ) {i : ℕ} (hi : n < i) : (pderiv k)^[i] φ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hi
  rw [show n + m + 1 = m + 1 + n by ring, Function.iterate_add_apply, Function.iterate_succ_apply]
  have h0 : ((pderiv k)^[n] φ).IsHomogeneous 0 := by
    simpa using isHomogeneous_iterate_pderiv k hφ n
  have hC : (pderiv k)^[n] φ = C (coeff 0 ((pderiv k)^[n] φ)) :=
    totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h0.totalDegree_le)
  rw [hC, pderiv_C]
  exact Function.iterate_fixed (map_zero _) m

end MvPolynomial.DegAux

theorem solution {σ R : Type*} [CommSemiring R] {φ : MvPolynomial σ R}
    {n : ℕ} (hφ : φ.IsHomogeneous n) (k : σ) {i : ℕ} (hi : n < i) :
    (MvPolynomial.pderiv k)^[i] φ = 0 :=
  MvPolynomial.DegAux.iterate_pderiv_eq_zero_of_lt hφ k hi

