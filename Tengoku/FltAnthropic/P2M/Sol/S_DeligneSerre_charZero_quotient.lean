import Tengoku.Seed.RingTheory.Ideal.Quotient.Basic
import Tengoku.Seed.Algebra.CharZero.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_DeligneSerre_charZero_quotient.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_DeligneSerre_charZero_quotient

/--
@isnad1 id=charzero.1h2v.s7.5bf3ff39cd54 from=translated src=- shape=df44767e vocab=dd3755e0
-/
theorem solution {T : Type*} [CommRing T] (𝔭 : Ideal T)
    (h𝔭 : ∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0) : CharZero (T ⧸ 𝔭) := by
  refine ⟨fun m n hmn => ?_⟩
  have h : algebraMap ℤ T ((m : ℤ) - (n : ℤ)) ∈ 𝔭 := by
    rw [map_sub]
    have hcast : ∀ k : ℕ, (Ideal.Quotient.mk 𝔭) (algebraMap ℤ T (k : ℤ)) = (k : T ⧸ 𝔭) := by
      intro k; push_cast; simp
    have hm : (Ideal.Quotient.mk 𝔭) (algebraMap ℤ T (m : ℤ)) =
        (Ideal.Quotient.mk 𝔭) (algebraMap ℤ T (n : ℤ)) := by
      rw [hcast m, hcast n, hmn]
    rwa [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at hm
  have := h𝔭 _ h
  omega
