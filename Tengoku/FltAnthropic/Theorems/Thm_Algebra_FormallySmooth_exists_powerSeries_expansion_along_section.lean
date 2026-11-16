import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v

/--
@isnad1 id=ex.1h3v.s10.4c4233812105 from=translated src=- shape=1bff5a8f vocab=edc4c7e9
-/
theorem Algebra.FormallySmooth.exists_powerSeries_expansion_along_section
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FormallySmooth R A]
    (e : A →ₐ[R] R) [Module.Free R (RingHom.ker e.toRingHom).Cotangent]
    (he : Module.finrank R (RingHom.ker e.toRingHom).Cotangent = 1) :
    ∃ θ : A →+* PowerSeries R,
      (∀ r : R, θ (algebraMap R A r) = PowerSeries.C r) ∧
      (∀ (n : ℕ) (a : A), (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = 0) ↔
        a ∈ RingHom.ker e.toRingHom ^ n) ∧
      (∀ (n : ℕ) (p : PowerSeries R), ∃ a : A, ∀ k : ℕ, k < n →
        PowerSeries.coeff k (θ a) = PowerSeries.coeff k p) := by exact @_root_.P2MW.S_Algebra_FormallySmooth_exists_powerSeries_expansion_along_section.solution R A _ _ _ _ e _ he
