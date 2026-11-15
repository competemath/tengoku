import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Deligne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace LanglandsTunnell

open Complex

inductive RealArchParam where

  | principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) : RealArchParam

  | discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) : RealArchParam

@[ext]
structure ComplexArchParam where

  u₁ : ℂ

  k₁ : ℤ

  u₂ : ℂ

  k₂ : ℤ

def signShift (a : ZMod 2) : ℂ := if a = 0 then 0 else 1

/--
@isnad1 id=eq.0h0v.s5.458ccc05b4d1 from=translated src=- shape=012516b9 vocab=b01e4e9b
-/
@[simp] theorem signShift_zero : signShift 0 = 0 := by simp [signShift]

/--
@isnad1 id=eq.0h0v.s5.91815f268b83 from=translated src=- shape=012516b9 vocab=b01e4e9b
-/
@[simp] theorem signShift_one : signShift 1 = 1 := by simp [signShift]

namespace RealArchParam

def gammaR : RealArchParam → Multiset ℂ
  | principal u₁ a₁ u₂ a₂ => {u₁ + signShift a₁, u₂ + signShift a₂}
  | discrete _ _ _ => 0

def gammaC : RealArchParam → Multiset ℂ
  | principal _ _ _ _ => 0
  | discrete u k _ => {u + (k : ℂ) / 2}

def archFactor (P : RealArchParam) (s : ℂ) : ℂ :=
  (P.gammaR.map fun μ => Gammaℝ (s + μ)).prod * (P.gammaC.map fun ν => Gammaℂ (s + ν)).prod

def twist : RealArchParam → ℂ → ZMod 2 → RealArchParam
  | principal u₁ a₁ u₂ a₂, u, a => principal (u₁ + u) (a₁ + a) (u₂ + u) (a₂ + a)
  | discrete u₀ k hk, u, _ => discrete (u₀ + u) k hk

def dual : RealArchParam → RealArchParam
  | principal u₁ a₁ u₂ a₂ => principal (-u₁) a₁ (-u₂) a₂
  | discrete u k hk => discrete (-u) k hk

def centralExponent : RealArchParam → ℂ
  | principal u₁ _ u₂ _ => u₁ + u₂
  | discrete u _ _ => 2 * u

def centralSign : RealArchParam → ZMod 2
  | principal _ a₁ _ a₂ => a₁ + a₂
  | discrete _ k _ => (k : ZMod 2) + 1

/--
@isnad1 id=eq.0h1v.s5.a4fa9cd841a9 from=translated src=- shape=251450d4 vocab=8d38fcf9
-/
@[simp] theorem twist_zero (P : RealArchParam) : P.twist 0 0 = P := by
  cases P <;> simp [twist]

/--
@isnad1 id=eq.0h5v.s6.1bf072bdfbaf from=translated src=- shape=a9041f9f vocab=06fa2aee
-/
theorem twist_twist (P : RealArchParam) (u u' : ℂ) (a a' : ZMod 2) :
    (P.twist u a).twist u' a' = P.twist (u + u') (a + a') := by
  cases P <;> simp [twist, add_assoc]

/--
@isnad1 id=eq.0h1v.s3.6d0f80c744b7 from=translated src=- shape=47dcad53 vocab=87fb8db5
-/
@[simp] theorem dual_dual (P : RealArchParam) : P.dual.dual = P := by
  cases P <;> simp [dual]

/--
@isnad1 id=eq.0h3v.s5.d3a6799c7f83 from=translated src=- shape=5c830b2c vocab=1cfe4021
-/
theorem gammaC_twist (P : RealArchParam) (u : ℂ) (a : ZMod 2) :
    (P.twist u a).gammaC = P.gammaC.map (· + u) := by
  cases P <;> simp [twist, gammaC, add_right_comm]

/--
@isnad1 id=eq.0h2v.s6.305eade646ba from=translated src=- shape=44312a50 vocab=63e44135
-/
theorem gammaR_twist_zero (P : RealArchParam) (u : ℂ) :
    (P.twist u 0).gammaR = P.gammaR.map (· + u) := by
  cases P <;> simp [twist, gammaR, add_right_comm]

end RealArchParam

namespace ComplexArchParam

def gammaC (P : ComplexArchParam) : Multiset ℂ :=
  {P.u₁ + (P.k₁.natAbs : ℂ) / 2, P.u₂ + (P.k₂.natAbs : ℂ) / 2}

def archFactor (P : ComplexArchParam) (s : ℂ) : ℂ :=
  (P.gammaC.map fun ν => Gammaℂ (s + ν)).prod

def twist (P : ComplexArchParam) (u : ℂ) (k : ℤ) : ComplexArchParam :=
  ⟨P.u₁ + u, P.k₁ + k, P.u₂ + u, P.k₂ + k⟩

def dual (P : ComplexArchParam) : ComplexArchParam :=
  ⟨-P.u₁, -P.k₁, -P.u₂, -P.k₂⟩

def centralExponent (P : ComplexArchParam) : ℂ := P.u₁ + P.u₂

def centralTwist (P : ComplexArchParam) : ℤ := P.k₁ + P.k₂

/--
@isnad1 id=eq.0h1v.s4.7ecb695965de from=translated src=- shape=01ff8df9 vocab=ae460a0c
-/
@[simp] theorem twist_zero (P : ComplexArchParam) : P.twist 0 0 = P := by
  simp [twist]

/--
@isnad1 id=eq.0h1v.s3.0053df9f1342 from=translated src=- shape=47dcad53 vocab=5bff2545
-/
@[simp] theorem dual_dual (P : ComplexArchParam) : P.dual.dual = P := by
  simp [dual]

/--
@isnad1 id=eq.0h1v.s6.134c0406af8e from=translated src=- shape=89a3f71d vocab=4eca3810
-/
theorem gammaC_dual (P : ComplexArchParam) :
    P.dual.gammaC = {-P.u₁ + (P.k₁.natAbs : ℂ) / 2, -P.u₂ + (P.k₂.natAbs : ℂ) / 2} := by
  simp [dual, gammaC]

/--
@isnad1 id=eq.0h2v.s5.1124b5ea0ec9 from=translated src=- shape=86b0d0d8 vocab=7d12f78b
-/
theorem gammaC_twist_zero (P : ComplexArchParam) (u : ℂ) :
    (P.twist u 0).gammaC = P.gammaC.map (· + u) := by
  simp [twist, gammaC, add_right_comm]

end ComplexArchParam

def RealArchParam.oddArtin : RealArchParam := .principal 0 0 0 1

def ComplexArchParam.trivialArtin : ComplexArchParam := ⟨0, 0, 0, 0⟩

/--
@isnad1 id=eq.0h0v.s4.13a44c591caa from=translated src=- shape=b9c0e9bb vocab=190d4f9b
-/
theorem RealArchParam.gammaR_oddArtin : RealArchParam.oddArtin.gammaR = {0, 1} := by
  simp [oddArtin, gammaR]

/--
@isnad1 id=eq.0h0v.s4.b8223c16d5c9 from=translated src=- shape=b9c0e9bb vocab=4ababa39
-/
theorem ComplexArchParam.gammaC_trivialArtin : ComplexArchParam.trivialArtin.gammaC = {0, 0} := by
  simp [trivialArtin, gammaC]

/--
@isnad1 id=eq.0h1v.s3.70a881e6c047 from=translated src=- shape=25ac9e83 vocab=eea3e2cc
-/
theorem RealArchParam.archFactor_oddArtin (s : ℂ) :
    RealArchParam.oddArtin.archFactor s = Gammaℂ s := by
  simp [oddArtin, archFactor, gammaR, gammaC, Gammaℝ_mul_Gammaℝ_add_one]

/--
@isnad1 id=eq.0h1v.s4.f6e3f6127105 from=translated src=- shape=2031eeeb vocab=b9b50e90
-/
theorem ComplexArchParam.archFactor_trivialArtin (s : ℂ) :
    ComplexArchParam.trivialArtin.archFactor s = Gammaℂ s * Gammaℂ s := by
  simp [trivialArtin, archFactor, gammaC]

end LanglandsTunnell

end
