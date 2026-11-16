import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_HeckeEigensystem
import Tengoku.FltAnthropic.Theorems.Thm_AutomorphicForm_satakePow_add_pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open IsDedekindDomain NumberField Polynomial

noncomputable section

namespace AutomorphicForm

/--
@isnad1 id=eq.0h3v.s6.7ccf5c61e2e5 from=translated src=- shape=e7533de6 vocab=b4e7c83f
-/
@[simp] theorem satakePow_two {R : Type*} [CommRing R] (s e : R) :
    satakePow 2 s e = s ^ 2 - 2 * e := by
  show s * s - e * 2 = s ^ 2 - 2 * e; ring

variable {R : Type*} [CommRing R]

def heckeLFactorPoly (s e : R) : Polynomial R :=
  1 - C s * X + C e * X ^ 2

/--
@isnad1 id=eq.0h3v.s8.a5e205afad68 from=translated src=- shape=9c6c53a1 vocab=ed4fc9b9
-/
@[simp] theorem heckeLFactorPoly_def (s e : R) :
    heckeLFactorPoly s e = 1 - C s * X + C e * X ^ 2 := rfl

/--
@isnad1 id=eq.0h3v.s5.3c9d56ccdc5b from=translated src=- shape=eea81c95 vocab=5278564b
-/
@[simp] theorem coeff_zero_heckeLFactorPoly (s e : R) :
    (heckeLFactorPoly s e).coeff 0 = 1 := by
  simp [heckeLFactorPoly, coeff_one, coeff_X_pow]

/--
@isnad1 id=eq.0h3v.s5.e8ff214b0183 from=translated src=- shape=32826820 vocab=57e713d9
-/
@[simp] theorem coeff_one_heckeLFactorPoly (s e : R) :
    (heckeLFactorPoly s e).coeff 1 = -s := by
  simp [heckeLFactorPoly, coeff_one, coeff_C_mul, coeff_X_pow]

/--
@isnad1 id=eq.0h3v.s4.53f56146ac2c from=translated src=- shape=ce784aa9 vocab=5278564b
-/
@[simp] theorem coeff_two_heckeLFactorPoly (s e : R) :
    (heckeLFactorPoly s e).coeff 2 = e := by
  simp [heckeLFactorPoly, coeff_one, coeff_C_mul, coeff_X_pow]

/--
@isnad1 id=and.1h5v.s5.f1be98b297ff from=translated src=- shape=599a3c08 vocab=be8adcbb
-/
theorem heckeLFactorPoly_inj {s e s' e' : R}
    (h : heckeLFactorPoly s e = heckeLFactorPoly s' e') : s = s' ∧ e = e' := by
  refine ⟨?_, ?_⟩
  · have h1 := congrArg (fun p => p.coeff 1) h
    simp only [coeff_one_heckeLFactorPoly] at h1
    exact neg_injective h1
  · have h2 := congrArg (fun p => p.coeff 2) h
    simpa only [coeff_two_heckeLFactorPoly] using h2

/--
@isnad1 id=iff.0h5v.s5.29057ed52a1e from=translated src=- shape=ebf6a3b7 vocab=be8adcbb
-/
theorem heckeLFactorPoly_eq_iff {s e s' e' : R} :
    heckeLFactorPoly s e = heckeLFactorPoly s' e' ↔ s = s' ∧ e = e' :=
  ⟨heckeLFactorPoly_inj, fun ⟨hs, he⟩ => by rw [hs, he]⟩

/--
@isnad1 id=eq.0h3v.s8.a511cc6d5918 from=translated src=- shape=a476d619 vocab=2b5f093f
-/
theorem heckeLFactorPoly_split (α β : R) :
    heckeLFactorPoly (α + β) (α * β) = (1 - C α * X) * (1 - C β * X) := by
  simp only [heckeLFactorPoly, map_add, map_mul]
  ring

/--
@isnad1 id=eq.0h5v.s7.5ec86774f13b from=translated src=- shape=05bf21fb vocab=7fab7afb
-/
theorem map_heckeLFactorPoly {S : Type*} [CommRing S] (φ : R →+* S) (s e : R) :
    (heckeLFactorPoly s e).map φ = heckeLFactorPoly (φ s) (φ e) := by
  simp [heckeLFactorPoly, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_one, Polynomial.map_pow, map_C, map_X]

def HeckeEigensystem.localLFactor {F : Type*} [Field F] [NumberField F]
    (π : HeckeEigensystem F R) (v : HeightOneSpectrum (𝓞 F)) : Polynomial R :=
  heckeLFactorPoly (π.a v) (π.b v)

/--
@isnad1 id=eq.0h4v.s6.071c40f3ab91 from=translated src=- shape=2f793d5a vocab=69938c73
-/
@[simp] theorem HeckeEigensystem.localLFactor_def {F : Type*} [Field F] [NumberField F]
    (π : HeckeEigensystem F R) (v : HeightOneSpectrum (𝓞 F)) :
    π.localLFactor v = heckeLFactorPoly (π.a v) (π.b v) := rfl

/--
@isnad1 id=and.1h5v.s6.f083e9f7d0b8 from=translated src=- shape=97aa5725 vocab=2059b656
-/
theorem HeckeEigensystem.satake_eq_of_localLFactor_eq {F : Type*} [Field F] [NumberField F]
    {π π' : HeckeEigensystem F R} {v : HeightOneSpectrum (𝓞 F)}
    (h : π.localLFactor v = π'.localLFactor v) : π.a v = π'.a v ∧ π.b v = π'.b v :=
  heckeLFactorPoly_inj h

section Factoring

variable {E L : Type*} [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)]

/--
@isnad1 id=iff.0h4v.s7.6fdb05402158 from=translated src=- shape=b8d2316e vocab=3324d19d
-/
theorem agreesAwayFromFinite_iff_localLFactor {F : Type*} [Field F] [NumberField F]
    (π π' : HeckeEigensystem F R) :
    HeckeEigensystem.AgreesAwayFromFinite π π' ↔
      ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
        π.localLFactor v = π'.localLFactor v := by
  unfold HeckeEigensystem.AgreesAwayFromFinite
  refine exists_congr fun S => forall_congr' fun v => forall_congr' fun _ => ?_
  exact heckeLFactorPoly_eq_iff.symm

end Factoring

/--
@isnad1 id=eq.0h4v.s9.8f655c55a8bc from=translated src=- shape=a5f1fd9e vocab=1b2cb6a3
-/
theorem heckeLFactorPoly_satakePow_split (f : ℕ) (α β : R) :
    heckeLFactorPoly (satakePow f (α + β) (α * β)) ((α * β) ^ f)
      = (1 - C (α ^ f) * X) * (1 - C (β ^ f) * X) := by
  rw [satakePow_add_pow, mul_pow, heckeLFactorPoly_split]

/--
@isnad1 id=eq.0h3v.s5.9a47c3e4cb2a from=translated src=- shape=43aa74a6 vocab=4cfcf260
-/
theorem heckeLFactorPoly_satakePow_one (s e : R) :
    heckeLFactorPoly (satakePow 1 s e) (e ^ 1) = heckeLFactorPoly s e := by
  rw [satakePow_one, pow_one]

/--
@isnad1 id=eq.0h3v.s9.59d767211e82 from=translated src=- shape=da4893a5 vocab=1b2cb6a3
-/
theorem heckeLFactorPoly_satakePow_two (s e : R) :
    heckeLFactorPoly (satakePow 2 s e) (e ^ 2)
      = 1 - C (s ^ 2 - 2 * e) * X + C (e ^ 2) * X ^ 2 := by
  rw [satakePow_two, heckeLFactorPoly]

section ConductorCarrier

variable {E L : Type*} [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra (𝓞 E) (𝓞 L)] [Algebra.IsIntegral (𝓞 E) (𝓞 L)]

def HasBaseChangeLevelLaw (𝔡 : Ideal (𝓞 L)) (π : HeckeEigensystem E R)
    (Φ : HeckeEigensystem L R) : Prop :=
  Φ.level ∣ 𝔡 * Ideal.map (algebraMap (𝓞 E) (𝓞 L)) π.level

omit [Algebra.IsIntegral (𝓞 E) (𝓞 L)] in

/--
@isnad1 id=hasbasec.0h5v.s6.55bbc3c3488f from=translated src=- shape=1281a7f7 vocab=e0056d0e
-/
theorem hasBaseChangeLevelLaw_sat (π : HeckeEigensystem E R)
    (Φ : HeckeEigensystem L R) : HasBaseChangeLevelLaw Φ.level π Φ :=
  dvd_mul_right Φ.level (Ideal.map (algebraMap (𝓞 E) (𝓞 L)) π.level)

end ConductorCarrier

end AutomorphicForm

end
