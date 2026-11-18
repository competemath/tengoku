import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat

set_option autoImplicit false

open IsDedekindDomain NumberField

/--
@isnad1 id=ex.0h1v.s6.9ce3414d95cf from=translated src=- shape=311f7e17 vocab=aa5606b0
-/
theorem solution
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  refine ⟨Rat.HeightOneSpectrum.natGenerator v, Rat.HeightOneSpectrum.prime_natGenerator v, ?_⟩
  set e : 𝓞 ℚ ≃+* ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) with he
  have h : Ideal.map (e : 𝓞 ℚ →+* ℤ) v.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ)} :=
    (Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v).symm
  have h3 : Ideal.map (e.symm : ℤ →+* 𝓞 ℚ) (Ideal.map (e : 𝓞 ℚ →+* ℤ) v.asIdeal) = v.asIdeal :=
    Ideal.map_of_equiv e
  rw [← h3, h, Ideal.map_span, Set.image_singleton]
  congr 2
  simp
