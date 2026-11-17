import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_DeligneSerre_exists_minimalPrime_le.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_DeligneSerre_exists_minimalPrime_le

theorem solution {T : Type*} [CommRing T] [Module.Finite ℤ T] [Module.IsTorsionFree ℤ T]
    (𝔪 : Ideal T) (h𝔪 : 𝔪.IsPrime) :
    ∃ 𝔭 ∈ minimalPrimes T, 𝔭 ≤ 𝔪 ∧ ∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0 := by
  haveI := h𝔪
  haveI : 𝔪.LiesOver (𝔪.under ℤ) := ⟨rfl⟩
  haveI : (𝔪.under ℤ).IsPrime := Ideal.IsPrime.under ℤ 𝔪
  obtain ⟨P, hP𝔪, hPprime, hPover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal ℤ)) (q := 𝔪.under ℤ) 𝔪 bot_le
  haveI := hPprime
  obtain ⟨𝔭, h𝔭min, h𝔭P⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal T)) (J := P) bot_le
  refine ⟨𝔭, h𝔭min, h𝔭P.trans hP𝔪, fun n hn => ?_⟩
  have hnP : algebraMap ℤ T n ∈ P := h𝔭P hn
  have : n ∈ P.under ℤ := hnP
  rw [← hPover.over] at this
  simpa using this
