import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArchParam

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell

open Complex

def signEpsilon (a : ZMod 2) : ℂ := if a = 0 then 1 else I

/--
@isnad1 id=eq.0h0v.s5.76dfa8a54169 from=translated src=- shape=012516b9 vocab=99a48f94
-/
@[simp] theorem signEpsilon_zero : signEpsilon 0 = 1 := by simp [signEpsilon]

/--
@isnad1 id=eq.0h0v.s5.7cef2cb89e30 from=translated src=- shape=fdee698a vocab=4072e01c
-/
@[simp] theorem signEpsilon_one : signEpsilon 1 = I := by simp [signEpsilon]

/--
@isnad1 id=eq.0h1v.s7.49335ffbe3b0 from=translated src=- shape=8766e96a vocab=30e75c36
-/
theorem signEpsilon_sq (a : ZMod 2) : signEpsilon a ^ 2 = if a = 0 then 1 else -1 := by
  by_cases h : a = 0
  · simp [signEpsilon, h]
  · simp [signEpsilon, h, I_sq]

namespace RealArchParam

def epsilonFactor : RealArchParam → ℂ
  | principal _ a₁ _ a₂ => signEpsilon a₁ * signEpsilon a₂
  | discrete _ k _ => I ^ (k + 1)

/--
@isnad1 id=eq.0h4v.s5.69efc072846e from=translated src=- shape=f185049d vocab=507460b6
-/
@[simp] theorem epsilonFactor_principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    (principal u₁ a₁ u₂ a₂).epsilonFactor = signEpsilon a₁ * signEpsilon a₂ := rfl

/--
@isnad1 id=eq.1h2v.s5.bbbb1ca38e9a from=translated src=- shape=47b9fe8b vocab=9ca81e78
-/
@[simp] theorem epsilonFactor_discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (discrete u k hk).epsilonFactor = I ^ (k + 1) := rfl

/--
@isnad1 id=eq.0h4v.s6.de88e0fefc35 from=translated src=- shape=7885d1cb vocab=899fc884
-/
theorem epsilonFactor_principal_sq (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) :
    (principal u₁ a₁ u₂ a₂).epsilonFactor ^ 2 = signEpsilon a₁ ^ 2 * signEpsilon a₂ ^ 2 :=
  mul_pow _ _ _

/--
@isnad1 id=eq.1h2v.s6.b89a46e86dfc from=translated src=- shape=722a95b3 vocab=ffb26cf0
-/
theorem epsilonFactor_discrete_sq (u : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    (discrete u k hk).epsilonFactor ^ 2 = (-1) ^ (k + 1) := by
  rw [epsilonFactor_discrete, ← pow_mul, mul_comm, pow_mul, I_sq]

/--
@isnad1 id=eq.0h0v.s2.526adf52f159 from=translated src=- shape=4b736592 vocab=ec681ce8
-/
theorem epsilonFactor_oddArtin : RealArchParam.oddArtin.epsilonFactor = I := by
  simp [RealArchParam.oddArtin, epsilonFactor]

end RealArchParam

namespace ComplexArchParam

def epsilonFactor (P : ComplexArchParam) : ℂ :=
  I ^ P.k₁.natAbs * I ^ P.k₂.natAbs

/--
@isnad1 id=eq.0h1v.s3.bd22bcca6980 from=translated src=- shape=8d4cac31 vocab=9456ded9
-/
theorem epsilonFactor_dual (P : ComplexArchParam) : P.dual.epsilonFactor = P.epsilonFactor := by
  simp [dual, epsilonFactor, Int.natAbs_neg]

/--
@isnad1 id=eq.0h1v.s5.e495c18f154d from=translated src=- shape=8f5b2c24 vocab=d40e7169
-/
theorem epsilonFactor_mul_epsilonFactor_dual (P : ComplexArchParam) :
    P.epsilonFactor * P.dual.epsilonFactor = (-1) ^ (P.k₁.natAbs + P.k₂.natAbs) := by
  rw [epsilonFactor_dual, epsilonFactor, ← pow_add, ← pow_add,
    show P.k₁.natAbs + P.k₂.natAbs + (P.k₁.natAbs + P.k₂.natAbs) = 2 * (P.k₁.natAbs + P.k₂.natAbs) by ring,
    pow_mul, I_sq]

/--
@isnad1 id=eq.0h0v.s3.9b20d99e5c5d from=translated src=- shape=b0ae1d2b vocab=34b1078d
-/
theorem epsilonFactor_trivialArtin : ComplexArchParam.trivialArtin.epsilonFactor = 1 := by
  simp [ComplexArchParam.trivialArtin, epsilonFactor]

end ComplexArchParam

end LanglandsTunnell

end
