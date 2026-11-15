import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_PeriodPair_Uniformization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open UpperHalfPlane

open scoped MatrixGroups

namespace ModularCurve.LevelN

def wp (N : ℕ) (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (PeriodPair.ofTau τ)
      ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))

def fricke (N : ℕ) (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * wp N v τ

def jAnalytic (τ : ℍ) : ℂ :=
  ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

def generators (N : ℕ) : Set (ℍ → ℂ) :=
  insert jAnalytic {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke N v}

def ring (N : ℕ) : Subalgebra ℂ (ℍ → ℂ) :=
  Algebra.adjoin ℂ (generators N)

/--
@isnad1 id=mem.0h1v.s4.95ff4cc9c1bc from=translated src=- shape=ffc6f881 vocab=e35004cf
-/
theorem jAnalytic_mem_generators (N : ℕ) : jAnalytic ∈ generators N :=
  Set.mem_insert _ _

/--
@isnad1 id=mem.1h2v.s6.98a68f96e9a1 from=translated src=- shape=adb8d2e8 vocab=527431f5
-/
theorem fricke_mem_generators (N : ℕ) {v : Fin 2 → ZMod N} (hv : v ≠ 0) :
    fricke N v ∈ generators N :=
  Set.mem_insert_of_mem _ ⟨v, hv, rfl⟩

/--
@isnad1 id=mem.0h1v.s6.6d1d9918f9f9 from=translated src=- shape=db61a821 vocab=953a70b0
-/
theorem jAnalytic_mem (N : ℕ) : jAnalytic ∈ ring N :=
  Algebra.subset_adjoin (jAnalytic_mem_generators N)

/--
@isnad1 id=mem.1h2v.s7.215c3978f217 from=translated src=- shape=d41478e4 vocab=653e9b43
-/
theorem fricke_mem (N : ℕ) {v : Fin 2 → ZMod N} (hv : v ≠ 0) : fricke N v ∈ ring N :=
  Algebra.subset_adjoin (fricke_mem_generators N hv)

def jGen (N : ℕ) : ring N :=
  ⟨jAnalytic, jAnalytic_mem N⟩

/--
@isnad1 id=eq.0h1v.s6.3a5cbdc94726 from=translated src=- shape=5d1e9390 vocab=ef701cdf
-/
@[simp]
theorem coe_jGen (N : ℕ) : ((jGen N : ring N) : ℍ → ℂ) = jAnalytic :=
  rfl

end ModularCurve.LevelN

end
