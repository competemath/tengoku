import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_CubicInduction_Carrier

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Congruence

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

def congruenceK1 (c : ℕ) : Set (GL (Fin 3) (v.adicCompletion K)) :=
  {k | k ∈ localMaximalCompact3 R K v ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 0) ≤ WithZero.exp (-(c : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 1) ≤ WithZero.exp (-(c : ℤ)) ∧
    Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 2 - 1) ≤ WithZero.exp (-(c : ℤ))}

/--
@isnad1 id=iff.0h5v.s11.51561ab8b864 from=translated src=- shape=ff659bdc vocab=7d4d4ad3
-/
theorem mem_congruenceK1_iff {c : ℕ} {k : GL (Fin 3) (v.adicCompletion K)} :
    k ∈ congruenceK1 R K v c ↔
      k ∈ localMaximalCompact3 R K v ∧
      Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 0) ≤ WithZero.exp (-(c : ℤ)) ∧
      Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 1) ≤ WithZero.exp (-(c : ℤ)) ∧
      Valued.v ((k : Matrix (Fin 3) (Fin 3) (v.adicCompletion K)) 2 2 - 1) ≤ WithZero.exp (-(c : ℤ)) :=
  Iff.rfl

/--
@isnad1 id=mem.1h5v.s9.49562273da22 from=translated src=- shape=d23684bd vocab=ce3f112a
-/
theorem mem_localMaximalCompact3_of_mem_congruenceK1 {c : ℕ} {k : GL (Fin 3) (v.adicCompletion K)}
    (hk : k ∈ congruenceK1 R K v c) : k ∈ localMaximalCompact3 R K v :=
  hk.1

/--
@isnad1 id=le.1h5v.s7.ca5b4c6b56fb from=translated src=- shape=cbf500d9 vocab=45f94ed9
-/
theorem congruenceK1_antitone {c c' : ℕ} (h : c ≤ c') :
    congruenceK1 R K v c' ⊆ congruenceK1 R K v c := by
  intro k hk
  obtain ⟨h0, h1, h2, h3⟩ := hk
  have hle : WithZero.exp (-(c' : ℤ)) ≤ WithZero.exp (-(c : ℤ)) :=
    WithZero.exp_le_exp.mpr (by omega)
  exact ⟨h0, h1.trans hle, h2.trans hle, h3.trans hle⟩

/--
@isnad1 id=mem.0h4v.s8.f011cd0a7181 from=translated src=- shape=c6f66345 vocab=e15eb5b1
-/
theorem one_mem_congruenceK1 (c : ℕ) : (1 : GL (Fin 3) (v.adicCompletion K)) ∈ congruenceK1 R K v c := by
  refine ⟨one_mem _, ?_, ?_, ?_⟩ <;> simp

end Congruence

end LanglandsTunnell.CubicInduction
