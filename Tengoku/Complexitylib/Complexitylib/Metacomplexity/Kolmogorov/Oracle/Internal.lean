/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Oracle.Defs
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Oracle.OutputSemantics
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.Oracle.Universality
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Defs

/-!
# Oracle-relative Kolmogorov complexity -- proof internals
-/

public section

namespace Complexity

namespace OracleTM

variable {n : ℕ}

/--
@isnad1 id=le.1h5v.s5.550bb8a0f626 from=translated src=- shape=8e049bf4 vocab=acca86f0
-/
theorem plainKolmogorovComplexity_le_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {program output : List Bool}
    (hproduce : machine.Produces oracle program output) :
    machine.plainKolmogorovComplexity oracle output ≤ program.length := by
  apply sInf_le
  exact ⟨program.length, ⟨program, rfl, hproduce⟩, rfl⟩

/--
@isnad1 id=le.1h6v.s5.9d7956fdf32b from=translated src=- shape=70b2f3c2 vocab=caddc801
-/
theorem timeBoundedKolmogorovComplexity_le_internal
    {machine : OracleTM n} {oracle : BooleanOracle}
    {program output : List Bool} {time : ℕ}
    (hproduce : machine.ProducesInTime oracle program output time) :
    machine.timeBoundedKolmogorovComplexity oracle output time ≤
      program.length := by
  apply sInf_le
  exact ⟨program.length, ⟨program, rfl, hproduce⟩, rfl⟩

/--
@isnad1 id=iff.0h5v.s5.460a7b6ca54f from=translated src=- shape=fc41924e vocab=c2eaff9b
-/
theorem timeBoundedKolmogorovComplexity_eq_top_iff_internal
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) (time : ℕ) :
    machine.timeBoundedKolmogorovComplexity oracle output time = ⊤ ↔
      ¬∃ program, machine.ProducesInTime oracle program output time := by
  rw [timeBoundedKolmogorovComplexity, sInf_eq_top]
  constructor
  · intro htop ⟨program, hproduce⟩
    have h := htop (program.length : WithTop ℕ)
      ⟨program.length, ⟨program, rfl, hproduce⟩, rfl⟩
    exact (WithTop.coe_ne_top : (program.length : WithTop ℕ) ≠ ⊤) h
  · intro hnone value hvalue
    obtain ⟨_size, ⟨program, _hlength, hproduce⟩, _hvalue⟩ := hvalue
    exact (hnone ⟨program, hproduce⟩).elim

/--
@isnad1 id=ex.1h5v.s5.48264b443b6e from=translated src=- shape=6fb58d3f vocab=2fafe3c6
-/
theorem timeBoundedKolmogorovComplexity_witness_internal
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) (time : ℕ)
    (hfinite : machine.timeBoundedKolmogorovComplexity oracle output time ≠ ⊤) :
    ∃ program, (program.length : WithTop ℕ) =
        machine.timeBoundedKolmogorovComplexity oracle output time ∧
      machine.ProducesInTime oracle program output time := by
  have hexists : ∃ program,
      machine.ProducesInTime oracle program output time := by
    by_contra hnone
    exact hfinite
      ((timeBoundedKolmogorovComplexity_eq_top_iff_internal
        machine oracle output time).mpr hnone)
  obtain ⟨program₀, hprogram₀⟩ := hexists
  have hset : ((fun size : ℕ => (size : WithTop ℕ)) ''
      machine.timeBoundedProducingProgramSizes oracle output time).Nonempty :=
    ⟨program₀.length, program₀.length,
      ⟨program₀, rfl, hprogram₀⟩, rfl⟩
  obtain ⟨size, ⟨program, hlength, hproduce⟩, hcoe⟩ := csInf_mem hset
  exact ⟨program, hlength ▸ hcoe, hproduce⟩

/--
@isnad1 id=iff.0h6v.s5.4e9368bfeca5 from=translated src=- shape=5106003b vocab=caddc801
-/
theorem timeBoundedKolmogorovComplexity_le_coe_iff_internal
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) (time bound : ℕ) :
    machine.timeBoundedKolmogorovComplexity oracle output time ≤
        (bound : WithTop ℕ) ↔
      ∃ program, program.length ≤ bound ∧
        machine.ProducesInTime oracle program output time := by
  constructor
  · intro hbound
    have hfinite :
        machine.timeBoundedKolmogorovComplexity oracle output time ≠ ⊤ := by
      intro htop
      rw [htop] at hbound
      exact WithTop.not_top_le_coe bound hbound
    obtain ⟨program, hlength, hproduce⟩ :=
      timeBoundedKolmogorovComplexity_witness_internal
        machine oracle output time hfinite
    refine ⟨program, ?_, hproduce⟩
    exact WithTop.coe_le_coe.mp (hlength.trans_le hbound)
  · rintro ⟨program, hlength, hproduce⟩
    exact (timeBoundedKolmogorovComplexity_le_internal hproduce).trans
      (WithTop.coe_le_coe.mpr hlength)

/--
@isnad1 id=le.1h6v.s5.fe2479245da8 from=translated src=- shape=8f216787 vocab=c6628b93
-/
theorem timeBoundedKolmogorovComplexity_mono_internal
    (machine : OracleTM n) (oracle : BooleanOracle)
    (output : List Bool) {first second : ℕ} (hclock : first ≤ second) :
    machine.timeBoundedKolmogorovComplexity oracle output second ≤
      machine.timeBoundedKolmogorovComplexity oracle output first := by
  apply le_sInf
  rintro _value ⟨size, ⟨program, hlength, hproduce⟩, rfl⟩
  subst size
  exact timeBoundedKolmogorovComplexity_le_internal
    (hproduce.mono hclock)

/--
@isnad1 id=ex.3h7v.s7.c5fb80e3bf91 from=translated src=- shape=8075144d vocab=314075cb
-/
theorem polynomialTimeOverhead_kolmogorov_transfer_internal
    {simulatorTapes sourceTapes : ℕ}
    {simulator : OracleTM simulatorTapes} {source : OracleTM sourceTapes}
    {compile : List Bool → List Bool} {constant : ℕ}
    {clock : TM.TimeOverhead}
    (hsim : simulator.SimulatesInTime source compile clock)
    (hlength : TM.HasAdditiveProgramOverhead compile constant)
    (hclock : TM.PolynomialTimeOverhead clock) :
    ∃ coefficient exponent,
      ∀ (oracle : BooleanOracle) (output : List Bool)
        (sourceTime bound : ℕ),
        source.timeBoundedKolmogorovComplexity oracle output sourceTime ≤
            (bound : WithTop ℕ) →
          simulator.timeBoundedKolmogorovComplexity oracle output
              (coefficient * (bound + sourceTime + 1) ^ exponent) ≤
            (bound + constant : ℕ) := by
  obtain ⟨coefficient, exponent, hclock⟩ := hclock
  refine ⟨coefficient, exponent, ?_⟩
  intro oracle output sourceTime bound hsource
  obtain ⟨program, hprogramLength, hproduce⟩ :=
    (timeBoundedKolmogorovComplexity_le_coe_iff_internal
      source oracle output sourceTime bound).mp hsource
  have htime : clock program sourceTime ≤
      coefficient * (bound + sourceTime + 1) ^ exponent := by
    exact (hclock program sourceTime).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) exponent))
  have hcompiled :=
    (hsim.produces oracle program output sourceTime hproduce).mono htime
  have hcompiledLength : (compile program).length ≤ bound + constant :=
    (hlength program).trans (Nat.add_le_add_right hprogramLength constant)
  exact (timeBoundedKolmogorovComplexity_le_internal hcompiled).trans
    (WithTop.coe_le_coe.mpr hcompiledLength)

end OracleTM

namespace TM

/--
@isnad1 id=eq.0h5v.s4.7ad2213bf6c0 from=translated src=- shape=84e4921b vocab=bcb469ad
-/
theorem toOracleTM_timeBoundedKolmogorovComplexity_eq_internal
    (machine : TM n) (oracle : BooleanOracle)
    (output : List Bool) (time : ℕ) :
    machine.toOracleTM.timeBoundedKolmogorovComplexity oracle output time =
      machine.timeBoundedKolmogorovComplexity output time := by
  unfold OracleTM.timeBoundedKolmogorovComplexity
  unfold TM.timeBoundedKolmogorovComplexity
  congr 2
  ext size
  simp only [OracleTM.timeBoundedProducingProgramSizes,
    TM.timeBoundedProducingProgramSizes, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨program, hlength, hproduce⟩
    exact ⟨program, hlength,
      (machine.toOracleTM_producesInTime_iff oracle program output time).mp
        hproduce⟩
  · rintro ⟨program, hlength, hproduce⟩
    exact ⟨program, hlength,
      (machine.toOracleTM_producesInTime_iff oracle program output time).mpr
        hproduce⟩

end TM

end Complexity
