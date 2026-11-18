import Tengoku.FltAnthropic.Definitions.Def_AdelicDock_LocalEmbedding

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_RankinSelberg_forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_mem_localLevelOne_pow_mul_eq_of_forall_mem_localLevelOne_mul_eq

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace LocalLevelOnePowSol

section Generic

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/--
@isnad1 id=iff.1h6v.s6.e70cdac249b6 from=translated src=- shape=68d2a621 vocab=ad97c4b2
-/
theorem isLocalLevelOne_iff_of_idealBound_eq (v : HeightOneSpectrum R) {N N' : Ideal R}
    (h : AdelicLevel.idealBound R N v = AdelicLevel.idealBound R N' v)
    (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    AdelicDock.IsLocalLevelOne R K v N m ↔ AdelicDock.IsLocalLevelOne R K v N' m := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h ▸ h2, h ▸ h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h.symm ▸ h2, h.symm ▸ h3⟩

/--
@isnad1 id=eq.1h5v.s8.6316b14642e5 from=translated src=- shape=bbc5e826 vocab=036716c5
-/
theorem localLevelOne_eq_of_idealBound_eq (v : HeightOneSpectrum R) {N N' : Ideal R}
    (h : AdelicLevel.idealBound R N v = AdelicLevel.idealBound R N' v) :
    AdelicDock.localLevelOne R K v N = AdelicDock.localLevelOne R K v N' := by
  ext k
  rw [AdelicDock.mem_localLevelOne_iff, AdelicDock.mem_localLevelOne_iff,
    isLocalLevelOne_iff_of_idealBound_eq v h, isLocalLevelOne_iff_of_idealBound_eq v h]

/--
@isnad1 id=eq.3h4v.s9.c3390fe42652 from=translated src=- shape=29586b12 vocab=31a5168a
-/
theorem count_eq_of_pow_dvd_not_pow_succ_dvd (v : HeightOneSpectrum R) {N : Ideal R} (hN : N ≠ ⊥)
    {b : ℕ} (hb : v.asIdeal ^ b ∣ N) (hb' : ¬ v.asIdeal ^ (b + 1) ∣ N) :
    ∀ [DecidableEq (Associates (Ideal R))] [∀ q : Associates (Ideal R), Decidable (Irreducible q)],
      (Associates.mk v.asIdeal).count (Associates.mk N).factors = b := by
  intro _ _
  have hN0 : Associates.mk N ≠ 0 := Associates.mk_ne_zero.mpr hN
  have hirr : Irreducible (Associates.mk v.asIdeal) := Associates.irreducible_mk.mpr v.irreducible
  refine le_antisymm ?_ ?_
  · by_contra hlt
    apply hb'
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow, Associates.prime_pow_dvd_iff_le hN0 hirr]
    exact not_le.mp hlt
  · rw [← Associates.prime_pow_dvd_iff_le hN0 hirr, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
    exact hb

/--
@isnad1 id=eq.0h3v.s6.d7d03d9dc5ea from=translated src=- shape=a23bbb74 vocab=b15a2a0c
-/
theorem idealBound_pow (v : HeightOneSpectrum R) (b : ℕ) :
    AdelicLevel.idealBound R (v.asIdeal ^ b) v = WithZero.exp (-(b : ℤ)) := by
  classical
  rw [AdelicLevel.idealBound_of_ne_bot (pow_ne_zero b v.ne_bot), Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr v.ne_bot) (Associates.irreducible_mk.mpr v.irreducible),
    Associates.count_self (Associates.irreducible_mk.mpr v.irreducible), mul_one]

/--
@isnad1 id=eq.1h4v.s8.13dddd4f3a71 from=translated src=- shape=4bb975f2 vocab=f216a3c5
-/
theorem idealBound_eq_idealBound_pow (v : HeightOneSpectrum R) {N : Ideal R} {b : ℕ}
    (hNb : v.asIdeal ^ b ∣ N ∧ ¬ v.asIdeal ^ (b + 1) ∣ N) :
    AdelicLevel.idealBound R N v = AdelicLevel.idealBound R (v.asIdeal ^ b) v := by
  classical
  have hN : N ≠ ⊥ := by
    rintro rfl
    exact hNb.2 (dvd_zero _)
  rw [idealBound_pow, AdelicLevel.idealBound_of_ne_bot hN, count_eq_of_pow_dvd_not_pow_succ_dvd v hN hNb.1 hNb.2]

/--
@isnad1 id=eq.1h5v.s9.ed55f31d8c4e from=translated src=- shape=159cc11b vocab=58aae931
-/
theorem localLevelOne_eq_localLevelOne_pow (v : HeightOneSpectrum R) {N : Ideal R} {b : ℕ}
    (hNb : v.asIdeal ^ b ∣ N ∧ ¬ v.asIdeal ^ (b + 1) ∣ N) :
    AdelicDock.localLevelOne R K v N = AdelicDock.localLevelOne R K v (v.asIdeal ^ b) :=
  localLevelOne_eq_of_idealBound_eq v (idealBound_eq_idealBound_pow v hNb)

end Generic

end LocalLevelOnePowSol

/--
@isnad1 id=eq.3h6v.s12.a50b8d3534e4 from=translated src=- shape=cdf73ed8 vocab=d9f6f768
-/
theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (N : Ideal (𝓞 ℚ))
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (b : ℕ)
    (hNb : p.asIdeal ^ b ∣ N ∧ ¬ p.asIdeal ^ (b + 1) ∣ N) :
    ∀ (k g : GL (Fin 2) (p.adicCompletion ℚ)),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b) → w₂base (g * k) = w₂base g := by
  intro k g hk
  rw [← LocalLevelOnePowSol.localLevelOne_eq_localLevelOne_pow (K := ℚ) p hNb] at hk
  exact hw₂K k hk g
