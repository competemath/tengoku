import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Ideal_exists_eq_smul_one_tmul_and_one_tmul_eq_zero_of_isLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Ideal_exists_eq_smul_one_tmul_and_one_tmul_eq_zero_of_isLocalization.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MvPolynomial TensorProduct

theorem Ideal.exists_eq_smul_one_tmul_and_one_tmul_eq_zero_of_isLocalization
    (R : Type) [CommRing R] {n : ℕ} (M : Submonoid (MvPolynomial (Fin n) R))
    (P : Type) [CommRing P] [Algebra (MvPolynomial (Fin n) R) P] [IsLocalization M P]
    (I J : Ideal (MvPolynomial (Fin n) R)) (𝔞 : Ideal P) (h𝔞 : 𝔞 = I.map (algebraMap (MvPolynomial (Fin n) R) P))
    (K : Type) [CommRing K] [Algebra P K] [Algebra (MvPolynomial (Fin n) R) K]
    [IsScalarTower (MvPolynomial (Fin n) R) P K]
    (hK : Function.Surjective (algebraMap (MvPolynomial (Fin n) R) K))
    (hJK : ∀ j ∈ J, algebraMap (MvPolynomial (Fin n) R) K j = 0) :
    (∀ z : K ⊗[P] ↥𝔞, ∃ (c : K) (a : MvPolynomial (Fin n) R) (ha : a ∈ I),
        z = c • ((1 : K) ⊗ₜ[P] (⟨algebraMap (MvPolynomial (Fin n) R) P a,
          h𝔞 ▸ Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) R) P) ha⟩ : ↥𝔞))) ∧
    (∀ (a : MvPolynomial (Fin n) R) (ha : a ∈ J * I),
        ((1 : K) ⊗ₜ[P] (⟨algebraMap (MvPolynomial (Fin n) R) P a,
          h𝔞 ▸ Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) R) P) (Ideal.mul_le_right ha)⟩ : ↥𝔞) : K ⊗[P] ↥𝔞) = 0) := by exact @_root_.P2MW.S_Ideal_exists_eq_smul_one_tmul_and_one_tmul_eq_zero_of_isLocalization.solution R _ n M P _ _ _ I J 𝔞 h𝔞 K _ _ _ _ hK hJK
