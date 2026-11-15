import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_TateLocalZeta
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicLevel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.TateLocal

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def higherUnitsAt (n : ℕ) : Set (v.adicCompletion K)ˣ :=
  {u | Valued.v (u : v.adicCompletion K) = 1 ∧
    (n = 0 ∨ Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ)))}

/--
@isnad1 id=iff.0h4v.s10.81eb100eba27 from=translated src=- shape=f5d3c0cd vocab=cc59728e
-/
theorem mem_higherUnitsAt_iff {n : ℕ} {u : (v.adicCompletion K)ˣ} :
    u ∈ higherUnitsAt K v n ↔ Valued.v (u : v.adicCompletion K) = 1 ∧
      (n = 0 ∨ Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ))) :=
  Iff.rfl

/--
@isnad1 id=iff.0h3v.s9.230130abef4a from=translated src=- shape=9307b770 vocab=3beff497
-/
theorem mem_higherUnitsAt_zero_iff {u : (v.adicCompletion K)ˣ} :
    u ∈ higherUnitsAt K v 0 ↔ Valued.v (u : v.adicCompletion K) = 1 := by
  simp [mem_higherUnitsAt_iff]

/--
@isnad1 id=mem.0h3v.s9.2d7a8f55e697 from=translated src=- shape=5d750e08 vocab=00d7d73d
-/
theorem one_mem_higherUnitsAt (n : ℕ) : (1 : (v.adicCompletion K)ˣ) ∈ higherUnitsAt K v n := by
  refine ⟨by simp, ?_⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · exact Or.inl h
  · right
    simp only [Units.val_one, sub_self, map_zero]
    exact zero_le

/--
@isnad1 id=antitone.0h2v.s9.275bede493e6 from=translated src=- shape=1228a534 vocab=218c4217
-/
theorem higherUnitsAt_antitone : Antitone (higherUnitsAt K v) := by
  intro m n hmn u hu
  obtain ⟨hval, hball⟩ := hu
  refine ⟨hval, ?_⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact Or.inl hm
  · right
    rcases hball with hn0 | hle
    · omega
    · exact hle.trans (WithZero.exp_le_exp.mpr (by omega))

def HasConductorExponentAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ) : Prop :=
  (∀ u ∈ higherUnitsAt K v c, χ u = 1) ∧ ∀ m < c, ∃ u ∈ higherUnitsAt K v m, χ u ≠ 1

/--
@isnad1 id=iff.0h3v.s10.2685a9e8568e from=translated src=- shape=68626ac7 vocab=1faddfa5
-/
theorem hasConductorExponentAt_zero_iff {χ : (v.adicCompletion K)ˣ →* ℂˣ} :
    HasConductorExponentAt K v χ 0 ↔
      ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ u = 1 := by
  constructor
  · intro h u hu
    exact h.1 u ((mem_higherUnitsAt_zero_iff K v).mpr hu)
  · intro h
    exact ⟨fun u hu => h u ((mem_higherUnitsAt_zero_iff K v).mp hu),
      fun m hm => absurd hm (Nat.not_lt_zero m)⟩

/--
@isnad1 id=eq.2h5v.s8.dbccf7e2e8bd from=translated src=- shape=8b021dda vocab=dcb37edd
-/
theorem hasConductorExponentAt_unique {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c c' : ℕ}
    (h : HasConductorExponentAt K v χ c) (h' : HasConductorExponentAt K v χ c') : c = c' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨u, hu, hne1⟩ := h'.2 c hlt
    exact hne1 (h.1 u hu)
  · obtain ⟨u, hu, hne1⟩ := h.2 c' hgt
    exact hne1 (h'.1 u hu)

/--
@isnad1 id=hascondu.0h2v.s9.89ad187cb577 from=translated src=- shape=3db8419f vocab=dcb37edd
-/
theorem hasConductorExponentAt_one_zero :
    HasConductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) 0 :=
  (hasConductorExponentAt_zero_iff K v).mpr fun _ _ => rfl

/--
@isnad1 id=not.0h3v.s9.3f7feb40e7cd from=translated src=- shape=06f62bc3 vocab=9cbb4e71
-/
theorem not_hasConductorExponentAt_one_succ (c : ℕ) :
    ¬ HasConductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) (c + 1) := by
  rintro ⟨-, hmin⟩
  obtain ⟨u, -, hne⟩ := hmin c (Nat.lt_succ_self c)
  exact hne rfl

def conductorExponentAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) : ℕ :=
  sInf {c | HasConductorExponentAt K v χ c}

/--
@isnad1 id=eq.1h4v.s8.6db27c90628a from=translated src=- shape=f26ecc70 vocab=bc1590fe
-/
theorem conductorExponentAt_eq_of_hasConductorExponentAt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ}
    (h : HasConductorExponentAt K v χ c) : conductorExponentAt K v χ = c := by
  have hmem : c ∈ {c' | HasConductorExponentAt K v χ c'} := h
  have hle : conductorExponentAt K v χ ≤ c := Nat.sInf_le hmem
  have hge : c ≤ conductorExponentAt K v χ := by
    have hne : {c' | HasConductorExponentAt K v χ c'}.Nonempty := ⟨c, h⟩
    have hmemInf := Nat.sInf_mem hne
    exact (hasConductorExponentAt_unique K v hmemInf h).ge
  omega

/--
@isnad1 id=eq.0h2v.s9.0ba8b0e1cb8f from=translated src=- shape=ef17c9d4 vocab=61e06b56
-/
@[simp] theorem conductorExponentAt_one :
    conductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) = 0 :=
  conductorExponentAt_eq_of_hasConductorExponentAt K v (hasConductorExponentAt_one_zero K v)

open Classical in

def localLFactorAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  if HasConductorExponentAt K v χ 0 then
    (1 - (χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹
  else 1

/--
@isnad1 id=eq.1h4v.s10.f8a4a52c624d from=translated src=- shape=46ff6b40 vocab=ad70c2d3
-/
theorem localLFactorAt_of_hasConductorExponentAt_zero {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ : HasConductorExponentAt K v χ 0) (s : ℂ) :
    localLFactorAt K v χ s
      = (1 - (χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [localLFactorAt, ite_eq_left hχ]

/--
@isnad1 id=eq.1h4v.s8.315a712b789c from=translated src=- shape=2c5669cd vocab=d2232d03
-/
theorem localLFactorAt_of_not_hasConductorExponentAt_zero {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ : ¬ HasConductorExponentAt K v χ 0) (s : ℂ) : localLFactorAt K v χ s = 1 := by
  rw [localLFactorAt, ite_eq_right hχ]

/--
@isnad1 id=eq.0h3v.s10.f825263d8d3b from=translated src=- shape=4850b920 vocab=ac5c3c62
-/
theorem localLFactorAt_one (s : ℂ) :
    localLFactorAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) s
      = (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [localLFactorAt_of_hasConductorExponentAt_zero K v (hasConductorExponentAt_one_zero K v),
    MonoidHom.one_apply, Units.val_one, one_mul]

section Epsilon

variable [MeasurableSpace (v.adicCompletion K)]

def localEpsilonAt (μ : Measure (v.adicCompletion K)) (ψ : AddChar (v.adicCompletion K) ℂ)
    (f : v.adicCompletion K → ℂ) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  localGammaAt μ ψ f χ s * localLFactorAt K v χ s / localLFactorAt K v χ⁻¹ (1 - s)

/--
@isnad1 id=eq.0h7v.s10.0f4b0fea76dc from=translated src=- shape=acfee75f vocab=0824767c
-/
theorem localEpsilonAt_def (μ : Measure (v.adicCompletion K)) (ψ : AddChar (v.adicCompletion K) ℂ)
    (f : v.adicCompletion K → ℂ) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) :
    localEpsilonAt K v μ ψ f χ s
      = localGammaAt μ ψ f χ s * localLFactorAt K v χ s / localLFactorAt K v χ⁻¹ (1 - s) :=
  rfl

/--
@isnad1 id=eq.1h7v.s9.a618c28ff552 from=translated src=- shape=4a5dc817 vocab=bb33539e
-/
theorem localEpsilonAt_of_not_hasConductorExponentAt_zero (μ : Measure (v.adicCompletion K))
    (ψ : AddChar (v.adicCompletion K) ℂ) (f : v.adicCompletion K → ℂ)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hχ : ¬ HasConductorExponentAt K v χ 0) (s : ℂ) :
    localEpsilonAt K v μ ψ f χ s = localGammaAt μ ψ f χ s := by
  have hχ' : ¬ HasConductorExponentAt K v χ⁻¹ 0 := fun h => hχ <| by
    rw [hasConductorExponentAt_zero_iff] at h ⊢
    intro u hu
    have := h u hu
    rwa [MonoidHom.inv_apply, inv_eq_one] at this
  rw [localEpsilonAt, localLFactorAt_of_not_hasConductorExponentAt_zero K v hχ,
    localLFactorAt_of_not_hasConductorExponentAt_zero K v hχ', mul_one, div_one]

/--
@isnad1 id=eq.1h7v.s9.24908c542cac from=translated src=- shape=bdb88ca2 vocab=56e7c344
-/
theorem localEpsilonAt_eq_zero_of_localZeta_eq_zero {μ : Measure (v.adicCompletion K)}
    {ψ : AddChar (v.adicCompletion K) ℂ} {f : v.adicCompletion K → ℂ}
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {s : ℂ} (h : localZeta μ f χ s = 0) :
    localEpsilonAt K v μ ψ f χ s = 0 := by
  rw [localEpsilonAt, localGammaAt_eq_zero_of_localZeta_eq_zero h, zero_mul, zero_div]

end Epsilon

end LanglandsTunnell.TateLocal

end
