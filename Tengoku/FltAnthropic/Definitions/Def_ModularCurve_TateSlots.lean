import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_TateFormal
import Tengoku.Seed.RingTheory.MvPowerSeries.Substitution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def tateUnivX : MvPowerSeries (Fin 2) ℤ := fun e =>
  if e 0 = e 1 then -2 * ∑ d ∈ (e 1).divisors, (d : ℤ)
  else if e 1 < e 0 then (if e 0 - e 1 ∣ e 1 then ((e 0 - e 1 : ℕ) : ℤ) else 0)
  else (if e 1 - e 0 ∣ e 1 then ((e 1 - e 0 : ℕ) : ℤ) else 0)

def tateUnivY : MvPowerSeries (Fin 2) ℤ := fun e =>
  if e 0 = e 1 then ∑ d ∈ (e 1).divisors, (d : ℤ)
  else if e 1 < e 0 then (if e 0 - e 1 ∣ e 1 then ((e 0 - e 1).choose 2 : ℤ) else 0)
  else (if e 1 - e 0 ∣ e 1 then -(((e 1 - e 0) + 1).choose 2 : ℤ) else 0)

def slotFamily (K : Type*) [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) : Fin 2 → PowerSeries K :=
  ![PowerSeries.C (c : K) * PowerSeries.X ^ j, PowerSeries.C ((c⁻¹ : Kˣ) : K) * PowerSeries.X ^ (p - j)]

def slotSubst (K : Type*) [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (f : MvPowerSeries (Fin 2) ℤ) :
    PowerSeries K :=
  MvPowerSeries.subst (slotFamily K p c j) f

def nonToricPoint (K : Type*) [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) :
    LaurentSeries K × LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j tateUnivX),
   HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j tateUnivY))

def tateBase (K : Type*) [CommRing K] (p : ℕ) [NeZero p] : WeierstrassCurve (LaurentSeries K) :=
  (tateLaurent K).map (qExpand K p)

end ModularCurve

end
