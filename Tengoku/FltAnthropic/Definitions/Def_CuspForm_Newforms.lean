import Tengoku.FltAnthropic.Definitions.Def_FreyPackage_LevelRaising
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_GaloisRep

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine.Point
open ModularFormClass

namespace CuspForm

variable {N : ℕ}

def GoodEigensystemOccursAt (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (M : ℕ) : Prop :=
  ∃ g : CuspForm (CongruenceSubgroup.Gamma0 M) 2, g.IsNormalizedEigenform ∧
    ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → qCoeff g ℓ = qCoeff f ℓ

/--
@isnad1 id=goodeige.1h2v.s7.e362bc96d0db from=translated src=- shape=35e4be59 vocab=4bbaa3e2
-/
lemma GoodEigensystemOccursAt.refl {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hf : f.IsNormalizedEigenform) : GoodEigensystemOccursAt f N :=
  ⟨f, hf, fun _ _ _ => rfl⟩

def IsNewform (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : Prop :=
  f.IsNormalizedEigenform ∧ ∀ M : ℕ, M ∣ N → M ≠ N → ¬ GoodEigensystemOccursAt f M

/--
@isnad1 id=isnormal.1h2v.s7.c7d3f76c2596 from=translated src=- shape=48092916 vocab=bd53889a
-/
lemma IsNewform.isNormalizedEigenform {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNewform) :
    f.IsNormalizedEigenform := hf.1

/--
@isnad1 id=ne.1h2v.s9.bbe8a0a9c949 from=translated src=- shape=3338aea9 vocab=51243f64
-/
lemma IsNewform.ne_zero {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNewform) : f ≠ 0 :=
  hf.1.ne_zero

def IsNewformAt (q : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : Prop :=
  f.IsNormalizedEigenform ∧ q ∣ N ∧ ¬ GoodEigensystemOccursAt f (N / q)

/--
@isnad1 id=isnewfor.4h3v.s7.b7ae65a21564 from=translated src=- shape=02813f3c vocab=4b99dcfe
-/
lemma IsNewform.isNewformAt {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNewform)
    {q : ℕ} (hq : q.Prime) (hqN : q ∣ N) (hN : N ≠ 0) : f.IsNewformAt q :=
  ⟨hf.1, hqN, hf.2 (N / q) (Nat.div_dvd_of_dvd hqN)
    (Nat.div_lt_self (Nat.pos_of_ne_zero hN) hq.one_lt).ne⟩

variable (N) in

def NewformBadPrimeCoeff : Prop :=
  ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2), f.IsNewform →
    ∀ q : ℕ, q.Prime → q ∣ N →
      (¬ q ^ 2 ∣ N → qCoeff f q ^ 2 = 1) ∧ (q ^ 2 ∣ N → qCoeff f q = 0)

end CuspForm

namespace Tengoku.FltAnthropic.FreyPackage

open CuspForm

noncomputable local instance instDecEqQbarNewforms :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def ModularRepOfNewLevelLE (P : FreyPackage) (N M : ℕ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (W : WeierstrassCurve ℤ)
      (𝔪 : Ideal (integralClosure ℤ ℂ)),
    f.IsNewform ∧ W.IsIntegralModelOf P.freyCurve ∧
    𝔪.IsMaximal ∧ (P.p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

def CongruenceEnlargement (P : FreyPackage) : Prop :=
  ∀ N M : ℕ, M ∣ N → 0 < M →
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    P.ModularRepOfNewLevelLE N M → P.ModularRepOfNewLevelLE M M

end Tengoku.FltAnthropic.FreyPackage

end
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
