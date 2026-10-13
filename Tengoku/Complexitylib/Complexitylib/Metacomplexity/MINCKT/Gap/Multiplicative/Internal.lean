/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINCKT.Gap.Multiplicative.Defs
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.MINCKT.Gap.Internal
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Conditional.Internal

/-!
# Multiplicative-gap conditional MinKT -- proof internals
-/

public section

namespace Complexity

namespace GapMINCKT

namespace Multiplicative

/--
@isnad1 id=iff.0h5v.s5.ba7bdd030759 from=translated src=- shape=f941acdf vocab=16a39e61
-/
theorem isNo_iff_no_relaxedWitness_internal
    {conditionalTapes : ℕ} (inst : GapMINCKT.Instance)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ) :
    IsNo inst conditionalMachine parameters factor ↔
      ¬∃ program,
        IsRelaxedWitness inst conditionalMachine parameters factor program := by
  constructor
  · intro hno ⟨program, hlength, hproduce⟩
    have hcomplexity :=
      (OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_le_internal
        hproduce).trans (WithTop.coe_le_coe.mpr hlength)
    exact (not_lt_of_ge hcomplexity) hno
  · intro hnone
    apply lt_of_not_ge
    intro hcomplexity
    obtain ⟨program, hlength, hproduce⟩ :=
      (OracleTM.randomAccessConditionalTimeBoundedKolmogorovComplexity_le_coe_iff_internal
        conditionalMachine inst.output inst.condition
          (inst.laterTime parameters)
          (factor inst.output.length * inst.threshold +
            inst.logSlack parameters)).mp hcomplexity
    exact hnone ⟨program, hlength, hproduce⟩

/--
@isnad1 id=isno.2h5v.s5.f159decc2fd7 from=translated src=- shape=43a660d0 vocab=affa106b
-/
theorem isNo_implies_additive_internal
    {conditionalTapes : ℕ} {inst : GapMINCKT.Instance}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : GapMINCKT.Parameters} {factor : ℕ → ℕ}
    (hfactor : 1 ≤ factor inst.output.length)
    (hno : IsNo inst conditionalMachine parameters factor) :
    inst.IsNo conditionalMachine parameters := by
  have hthreshold : inst.threshold ≤
      factor inst.output.length * inst.threshold :=
    Nat.le_mul_of_pos_left inst.threshold (by omega)
  exact lt_of_le_of_lt
    (WithTop.coe_le_coe.mpr
      (Nat.add_le_add_right hthreshold (inst.logSlack parameters))) hno

/--
@isnad1 id=isno.2h6v.s5.1257d24556ad from=translated src=- shape=0781b534 vocab=c9a91ba2
-/
theorem isNo_factor_anti_internal
    {conditionalTapes : ℕ} {inst : GapMINCKT.Instance}
    {conditionalMachine : OracleTM conditionalTapes}
    {parameters : GapMINCKT.Parameters} {first second : ℕ → ℕ}
    (hfactor : first inst.output.length ≤ second inst.output.length)
    (hno : IsNo inst conditionalMachine parameters second) :
    IsNo inst conditionalMachine parameters first := by
  exact lt_of_le_of_lt
    (WithTop.coe_le_coe.mpr <|
      Nat.add_le_add_right
        (Nat.mul_le_mul_right inst.threshold hfactor)
        (inst.logSlack parameters)) hno

/--
@isnad1 id=not.3h7v.s5.f70c505a154e from=translated src=- shape=34540a7a vocab=93c6601c
-/
theorem not_isNo_of_isYes_internal
    {ordinaryTapes conditionalTapes : ℕ}
    (inst : GapMINCKT.Instance)
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hwidening : parameters.IsWidening)
    (hfactor : 1 ≤ factor inst.output.length)
    (hyes : inst.IsYes ordinaryMachine conditionalMachine parameters) :
    ¬IsNo inst conditionalMachine parameters factor := by
  intro hno
  exact GapMINCKT.Instance.not_isNo_of_isYes_internal inst ordinaryMachine
    conditionalMachine parameters hwidening hyes
      (isNo_implies_additive_internal hfactor hno)

/--
@isnad1 id=iff.0h5v.s5.99a148f71087 from=translated src=- shape=5b5f738d vocab=846b055f
-/
theorem noLanguage_mem_encode_iff_internal
    {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (inst : GapMINCKT.Instance) :
    inst.encode ∈ noLanguage conditionalMachine parameters factor ↔
      IsNo inst conditionalMachine parameters factor := by
  simp [noLanguage, GapMINCKT.Instance.decode?_encode_internal]

/--
@isnad1 id=le.1h4v.s5.b6f1292ec7a9 from=translated src=- shape=581bb11c vocab=64ed7087
-/
theorem noLanguage_subset_additive_internal
    {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hfactor : ∀ length, 1 ≤ factor length) :
    noLanguage conditionalMachine parameters factor ⊆
      GapMINCKT.noLanguage conditionalMachine parameters := by
  intro bits hno
  cases hdecode : GapMINCKT.Instance.decode? bits with
  | none => simp [noLanguage, hdecode] at hno
  | some inst =>
      have hno' : IsNo inst conditionalMachine parameters factor := by
        simpa [noLanguage, hdecode] using hno
      have hadditive := isNo_implies_additive_internal
        (hfactor inst.output.length) hno'
      simpa [GapMINCKT.noLanguage, hdecode] using hadditive

/--
@isnad1 id=le.1h5v.s5.d89bd5f67b72 from=translated src=- shape=6b43909a vocab=5a987bf5
-/
theorem noLanguage_factor_anti_internal
    {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) {first second : ℕ → ℕ}
    (hfactor : ∀ length, first length ≤ second length) :
    noLanguage conditionalMachine parameters second ⊆
      noLanguage conditionalMachine parameters first := by
  intro bits hno
  cases hdecode : GapMINCKT.Instance.decode? bits with
  | none => simp [noLanguage, hdecode] at hno
  | some inst =>
      have hno' : IsNo inst conditionalMachine parameters second := by
        simpa [noLanguage, hdecode] using hno
      have hfirst := isNo_factor_anti_internal
        (hfactor inst.output.length) hno'
      simpa [noLanguage, hdecode] using hfirst

/--
@isnad1 id=eq.0h3v.s4.f2f24453ba96 from=translated src=- shape=dc05fe07 vocab=a38bc9cd
-/
theorem noLanguage_one_internal
    {conditionalTapes : ℕ}
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) :
    noLanguage conditionalMachine parameters (fun _length => 1) =
      GapMINCKT.noLanguage conditionalMachine parameters := by
  ext bits
  cases hdecode : GapMINCKT.Instance.decode? bits with
  | none => simp [noLanguage, GapMINCKT.noLanguage, hdecode]
  | some inst =>
      simp [noLanguage, GapMINCKT.noLanguage, IsNo, GapMINCKT.Instance.IsNo,
        hdecode]

/--
@isnad1 id=disjoint.2h6v.s6.6c41b031eb6b from=translated src=- shape=9911d478 vocab=a9a132c6
-/
theorem disjoint_yesLanguage_noLanguage_internal
    {ordinaryTapes conditionalTapes : ℕ}
    (ordinaryMachine : TM ordinaryTapes)
    (conditionalMachine : OracleTM conditionalTapes)
    (parameters : GapMINCKT.Parameters) (factor : ℕ → ℕ)
    (hwidening : parameters.IsWidening)
    (hfactor : ∀ length, 1 ≤ factor length) :
    Disjoint (yesLanguage ordinaryMachine conditionalMachine parameters)
      (noLanguage conditionalMachine parameters factor) := by
  exact Set.disjoint_of_subset_right
    (noLanguage_subset_additive_internal conditionalMachine parameters factor
      hfactor)
    (GapMINCKT.disjoint_yesLanguage_noLanguage_internal ordinaryMachine
      conditionalMachine parameters hwidening)

end Multiplicative

end GapMINCKT

end Complexity
