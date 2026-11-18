import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_eq_of_natCast_prime_mem_asIdeal.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_eq_of_natCast_prime_mem_asIdeal

set_option autoImplicit false

open IsDedekindDomain NumberField

/--
@isnad1 id=iff.0h2v.s7.8afe216250f4 from=translated src=- shape=a59a80cb vocab=46c37ad9
-/
theorem natCast_mem_asIdeal_iff' (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

/--
@isnad1 id=eq.2h2v.s7.120a630996d7 from=translated src=- shape=c0356226 vocab=271b35db
-/
theorem natGenerator_eq_of_prime_mem' {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) : Rat.HeightOneSpectrum.natGenerator v = p :=
  (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp).1
    ((natCast_mem_asIdeal_iff' v p).1 hv)

/--
@isnad1 id=eq.3h3v.s8.0460dc48f2bb from=translated src=- shape=30b05021 vocab=16e39599
-/
theorem solution
    {r : ℕ} (hr : r.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((r : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : w = v := by
  have e1 := natGenerator_eq_of_prime_mem' hr w hw
  have e2 := natGenerator_eq_of_prime_mem' hr v hv
  have : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w = Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v :=
    Subtype.ext (e1.trans e2.symm)
  exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective this
