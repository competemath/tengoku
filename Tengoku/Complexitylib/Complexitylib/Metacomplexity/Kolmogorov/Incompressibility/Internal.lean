/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Incompressibility.Defs
import Tengoku.Complexitylib.Complexitylib.Metacomplexity.Kolmogorov.Internal
public import Tengoku

/-!
# Finite incompressibility -- proof internals

The counting argument injects every compressible output into one chosen short
program. Deterministic output uniqueness makes this choice injective.
-/

public section

namespace Complexity

namespace StrictShortProgram

/--
@isnad1 id=eq.1h2v.s4.6a60e2526ef8 from=translated src=- shape=5c553dc8 vocab=cc531a20
-/
theorem toList_ofList_internal (bound : ℕ) (program : List Bool)
    (hlength : program.length < bound) :
    (ofList bound program hlength).toList = program := by
  simp [toList, ofList]

/--
@isnad1 id=injectiv.0h1v.s3.b65a08460014 from=translated src=- shape=995c1cb5 vocab=8fac121e
-/
theorem toList_injective_internal {bound : ℕ} :
    Function.Injective (toList : StrictShortProgram bound → List Bool) := by
  rintro ⟨⟨firstLength, hfirstLength⟩, first⟩
    ⟨⟨secondLength, hsecondLength⟩, second⟩ heq
  have hlength : firstLength = secondLength := by
    simpa only [toList, List.length_ofFn] using congrArg List.length heq
  subst secondLength
  have hcontents : first = second := List.ofFn_injective heq
  subst second
  rfl

/--
@isnad1 id=eq.0h1v.s6.e5ca555535e5 from=translated src=- shape=de3fa9a7 vocab=f0b69334
-/
theorem card_internal (bound : ℕ) :
    Fintype.card (StrictShortProgram bound) = 2 ^ bound - 1 := by
  rw [Fintype.card_sigma]
  simp only [card_finArrowBool]
  induction bound with
  | zero => simp
  | succ bound ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih, pow_succ]
      have hpositive : 0 < 2 ^ bound := Nat.two_pow_pos bound
      omega

end StrictShortProgram

namespace ShortProgram

/--
@isnad1 id=eq.1h2v.s4.71f558a61e21 from=translated src=- shape=5c553dc8 vocab=212066a3
-/
theorem toList_ofList_internal (bound : ℕ) (program : List Bool)
    (hlength : program.length ≤ bound) :
    (ofList bound program hlength).toList = program := by
  simp [toList, ofList]

/--
@isnad1 id=injectiv.0h1v.s3.a7a64ff9ee2d from=translated src=- shape=995c1cb5 vocab=83555d74
-/
theorem toList_injective_internal {bound : ℕ} :
    Function.Injective (toList : ShortProgram bound → List Bool) := by
  rintro ⟨⟨firstLength, hfirstLength⟩, first⟩
    ⟨⟨secondLength, hsecondLength⟩, second⟩ heq
  have hlength : firstLength = secondLength := by
    simpa only [toList, List.length_ofFn] using congrArg List.length heq
  subst secondLength
  have hcontents : first = second := by
    exact List.ofFn_injective heq
  subst second
  rfl

/--
@isnad1 id=eq.0h1v.s7.5a2447c1e01d from=translated src=- shape=3a0cd517 vocab=d6121aaf
-/
theorem card_internal (bound : ℕ) :
    Fintype.card (ShortProgram bound) = 2 ^ (bound + 1) - 1 := by
  rw [Fintype.card_sigma]
  simp only [card_finArrowBool]
  induction bound with
  | zero => simp
  | succ bound ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ih, pow_succ]
      omega

end ShortProgram

namespace TM

variable {tapes : ℕ}

/--
@isnad1 id=iff.0h6v.s6.3b9960752b06 from=translated src=- shape=7953f5cc vocab=459d3086
-/
theorem mem_timeBoundedStrictlyCompressibleStrings_iff_internal
    (machine : TM tapes) (outputLength time threshold : ℕ)
    (output : Fin outputLength → Bool) :
    output ∈ machine.timeBoundedStrictlyCompressibleStrings
        outputLength time threshold ↔
      machine.timeBoundedKolmogorovComplexity (List.ofFn output) time <
        (threshold : WithTop ℕ) := by
  classical
  simp [timeBoundedStrictlyCompressibleStrings]

/--
@isnad1 id=iff.0h6v.s6.1113091fc4a2 from=translated src=- shape=9daad943 vocab=d416aeda
-/
theorem mem_timeBoundedRandomStrings_iff_internal (machine : TM tapes)
    (outputLength time threshold : ℕ) (output : Fin outputLength → Bool) :
    output ∈ machine.timeBoundedRandomStrings outputLength time threshold ↔
      (threshold : WithTop ℕ) ≤
        machine.timeBoundedKolmogorovComplexity (List.ofFn output) time := by
  classical
  simp [timeBoundedRandomStrings,
    mem_timeBoundedStrictlyCompressibleStrings_iff_internal]

/--
@isnad1 id=le.0h5v.s5.d58d06ed67a1 from=translated src=- shape=a1d0e44c vocab=2eb7c841
-/
theorem card_timeBoundedStrictlyCompressibleStrings_le_internal
    (machine : TM tapes) (outputLength time threshold : ℕ) :
    (machine.timeBoundedStrictlyCompressibleStrings
      outputLength time threshold).card ≤ 2 ^ threshold - 1 := by
  classical
  let compressed := machine.timeBoundedStrictlyCompressibleStrings
    outputLength time threshold
  have hexists (output : ↥compressed) :
      ∃ program, program.length < threshold ∧
        machine.ProducesInTime program (List.ofFn output.1) time := by
    apply (timeBoundedKolmogorovComplexity_lt_coe_iff_internal
      machine (List.ofFn output.1) time threshold).mp
    exact (mem_timeBoundedStrictlyCompressibleStrings_iff_internal
      machine outputLength time threshold output.1).mp output.2
  let witness (output : ↥compressed) : List Bool :=
    Classical.choose (hexists output)
  have witness_spec (output : ↥compressed) :
      (witness output).length < threshold ∧
        machine.ProducesInTime (witness output) (List.ofFn output.1) time :=
    Classical.choose_spec (hexists output)
  let encode (output : ↥compressed) : StrictShortProgram threshold :=
    StrictShortProgram.ofList threshold (witness output) (witness_spec output).1
  have hencode : Function.Injective encode := by
    intro first second hequal
    have hprogram : witness first = witness second := by
      have hlist := congrArg StrictShortProgram.toList hequal
      simpa only [encode, StrictShortProgram.toList_ofList_internal] using hlist
    have hfirst := (witness_spec first).2
    rw [hprogram] at hfirst
    have houtput : List.ofFn first.1 = List.ofFn second.1 :=
      hfirst.output_unique (witness_spec second).2
    apply Subtype.ext
    exact List.ofFn_injective houtput
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa only [Fintype.card_coe, StrictShortProgram.card_internal] using hcard

/--
@isnad1 id=le.0h5v.s6.29f3f44f7c80 from=translated src=- shape=71ea7a7f vocab=c4e14991
-/
theorem card_timeBoundedRandomStrings_ge_internal (machine : TM tapes)
    (outputLength time threshold : ℕ) :
    2 ^ outputLength - (2 ^ threshold - 1) ≤
      (machine.timeBoundedRandomStrings outputLength time threshold).card := by
  classical
  rw [timeBoundedRandomStrings, Finset.card_compl, card_finArrowBool]
  have hcompressible := card_timeBoundedStrictlyCompressibleStrings_le_internal
    machine outputLength time threshold
  omega

/--
@isnad1 id=le.0h5v.s6.91623b6341d0 from=translated src=- shape=01f3f98e vocab=8e1f0665
-/
theorem eventProb_timeBoundedStrictlyCompressibleStrings_le_internal
    (machine : TM tapes) (outputLength time threshold : ℕ) :
    eventProb (machine.timeBoundedStrictlyCompressibleStrings
        outputLength time threshold) ≤
      ((2 ^ threshold - 1 : ℕ) : ℚ) / (2 : ℚ) ^ outputLength := by
  unfold eventProb
  have hcard :
      (((machine.timeBoundedStrictlyCompressibleStrings
        outputLength time threshold).card : ℕ) : ℚ) ≤
        ((2 ^ threshold - 1 : ℕ) : ℚ) := by
    exact_mod_cast card_timeBoundedStrictlyCompressibleStrings_le_internal
      machine outputLength time threshold
  gcongr

/--
@isnad1 id=le.0h5v.s6.ec02d4077801 from=translated src=- shape=207eff55 vocab=46551305
-/
theorem eventProb_timeBoundedRandomStrings_ge_internal (machine : TM tapes)
    (outputLength time threshold : ℕ) :
    1 - ((2 ^ threshold - 1 : ℕ) : ℚ) / (2 : ℚ) ^ outputLength ≤
      eventProb (machine.timeBoundedRandomStrings
        outputLength time threshold) := by
  rw [timeBoundedRandomStrings, eventProb_compl]
  exact sub_le_sub_left
    (eventProb_timeBoundedStrictlyCompressibleStrings_le_internal
      machine outputLength time threshold) 1

/--
@isnad1 id=ex.1h5v.s5.454b12030eb6 from=translated src=- shape=c4b3fda8 vocab=995ac661
-/
theorem exists_timeBoundedKolmogorovComplexity_ge_internal
    (machine : TM tapes) (outputLength time threshold : ℕ)
    (hthreshold : threshold ≤ outputLength) :
    ∃ output : Fin outputLength → Bool,
      (threshold : WithTop ℕ) ≤
        machine.timeBoundedKolmogorovComplexity (List.ofFn output) time := by
  classical
  have hpow : 2 ^ threshold ≤ 2 ^ outputLength :=
    Nat.pow_le_pow_right Nat.two_pos hthreshold
  have hpositive : 0 < 2 ^ outputLength - (2 ^ threshold - 1) := by
    have : 0 < 2 ^ threshold := Nat.two_pow_pos _
    omega
  have hcard := card_timeBoundedRandomStrings_ge_internal
    machine outputLength time threshold
  obtain ⟨output, houtput⟩ := Finset.card_pos.mp (hpositive.trans_le hcard)
  exact ⟨output,
    (mem_timeBoundedRandomStrings_iff_internal
      machine outputLength time threshold output).mp houtput⟩

/--
@isnad1 id=iff.0h6v.s6.492794c388c4 from=translated src=- shape=7953f5cc vocab=80a1d88a
-/
theorem mem_timeBoundedCompressibleStrings_iff_internal (machine : TM tapes)
    (outputLength time bound : ℕ) (output : Fin outputLength → Bool) :
    output ∈ machine.timeBoundedCompressibleStrings outputLength time bound ↔
      machine.timeBoundedKolmogorovComplexity (List.ofFn output) time ≤
        (bound : WithTop ℕ) := by
  classical
  simp [timeBoundedCompressibleStrings]

/--
@isnad1 id=iff.0h6v.s6.f72a2aede2bd from=translated src=- shape=9daad943 vocab=5ff9fdd4
-/
theorem mem_timeBoundedIncompressibleStrings_iff_internal (machine : TM tapes)
    (outputLength time bound : ℕ) (output : Fin outputLength → Bool) :
    output ∈ machine.timeBoundedIncompressibleStrings outputLength time bound ↔
      (bound : WithTop ℕ) <
        machine.timeBoundedKolmogorovComplexity (List.ofFn output) time := by
  classical
  simp [timeBoundedIncompressibleStrings,
    mem_timeBoundedCompressibleStrings_iff_internal]

/--
@isnad1 id=le.0h5v.s6.e01a3c690a0b from=translated src=- shape=4f2d8e23 vocab=efc05c43
-/
theorem card_timeBoundedCompressibleStrings_le_internal (machine : TM tapes)
    (outputLength time bound : ℕ) :
    (machine.timeBoundedCompressibleStrings outputLength time bound).card ≤
      2 ^ (bound + 1) - 1 := by
  classical
  let compressed := machine.timeBoundedCompressibleStrings outputLength time bound
  have hexists (output : ↥compressed) :
      ∃ program, program.length ≤ bound ∧
        machine.ProducesInTime program (List.ofFn output.1) time := by
    apply (timeBoundedKolmogorovComplexity_le_coe_iff_internal
      machine (List.ofFn output.1) time bound).mp
    exact (mem_timeBoundedCompressibleStrings_iff_internal
      machine outputLength time bound output.1).mp output.2
  let witness (output : ↥compressed) : List Bool :=
    Classical.choose (hexists output)
  have witness_spec (output : ↥compressed) :
      (witness output).length ≤ bound ∧
        machine.ProducesInTime (witness output) (List.ofFn output.1) time :=
    Classical.choose_spec (hexists output)
  let encode (output : ↥compressed) : ShortProgram bound :=
    ShortProgram.ofList bound (witness output) (witness_spec output).1
  have hencode : Function.Injective encode := by
    intro first second hequal
    have hprogram : witness first = witness second := by
      have hlist := congrArg ShortProgram.toList hequal
      simpa only [encode, ShortProgram.toList_ofList_internal] using hlist
    have hfirst := (witness_spec first).2
    rw [hprogram] at hfirst
    have houtput : List.ofFn first.1 = List.ofFn second.1 :=
      hfirst.output_unique (witness_spec second).2
    apply Subtype.ext
    exact List.ofFn_injective houtput
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa only [Fintype.card_coe, ShortProgram.card_internal] using hcard

/--
@isnad1 id=le.0h5v.s6.4df9d1289ef1 from=translated src=- shape=47c2af87 vocab=5084459a
-/
theorem card_timeBoundedIncompressibleStrings_ge_internal (machine : TM tapes)
    (outputLength time bound : ℕ) :
    2 ^ outputLength - (2 ^ (bound + 1) - 1) ≤
      (machine.timeBoundedIncompressibleStrings outputLength time bound).card := by
  classical
  rw [timeBoundedIncompressibleStrings, Finset.card_compl,
    card_finArrowBool]
  have hcompressible := card_timeBoundedCompressibleStrings_le_internal
    machine outputLength time bound
  omega

/--
@isnad1 id=le.0h5v.s6.6c63a2dd87b6 from=translated src=- shape=04115af9 vocab=0f2e3541
-/
theorem eventProb_timeBoundedCompressibleStrings_le_internal
    (machine : TM tapes) (outputLength time bound : ℕ) :
    eventProb (machine.timeBoundedCompressibleStrings outputLength time bound) ≤
      ((2 ^ (bound + 1) - 1 : ℕ) : ℚ) / (2 : ℚ) ^ outputLength := by
  unfold eventProb
  have hcard :
      (((machine.timeBoundedCompressibleStrings
        outputLength time bound).card : ℕ) : ℚ) ≤
        ((2 ^ (bound + 1) - 1 : ℕ) : ℚ) := by
    exact_mod_cast card_timeBoundedCompressibleStrings_le_internal
      machine outputLength time bound
  gcongr

/--
@isnad1 id=le.0h5v.s6.c157ede50f50 from=translated src=- shape=bb2fbfbf vocab=95b040af
-/
theorem eventProb_timeBoundedIncompressibleStrings_ge_internal
    (machine : TM tapes) (outputLength time bound : ℕ) :
    1 - ((2 ^ (bound + 1) - 1 : ℕ) : ℚ) / (2 : ℚ) ^ outputLength ≤
      eventProb
        (machine.timeBoundedIncompressibleStrings outputLength time bound) := by
  rw [timeBoundedIncompressibleStrings, eventProb_compl]
  exact sub_le_sub_left
    (eventProb_timeBoundedCompressibleStrings_le_internal
      machine outputLength time bound) 1

/--
@isnad1 id=ex.1h5v.s5.7d7881f88001 from=translated src=- shape=c4b3fda8 vocab=a8fecd74
-/
theorem exists_timeBoundedKolmogorovComplexity_gt_internal
    (machine : TM tapes) (outputLength time bound : ℕ)
    (hbound : bound < outputLength) :
    ∃ output : Fin outputLength → Bool,
      (bound : WithTop ℕ) <
        machine.timeBoundedKolmogorovComplexity (List.ofFn output) time := by
  classical
  have hpow : 2 ^ (bound + 1) ≤ 2 ^ outputLength :=
    Nat.pow_le_pow_right Nat.two_pos (Nat.succ_le_of_lt hbound)
  have hpositive : 0 < 2 ^ outputLength - (2 ^ (bound + 1) - 1) := by
    have : 0 < 2 ^ (bound + 1) := Nat.two_pow_pos _
    omega
  have hcard := card_timeBoundedIncompressibleStrings_ge_internal
    machine outputLength time bound
  obtain ⟨output, houtput⟩ := Finset.card_pos.mp (hpositive.trans_le hcard)
  exact ⟨output,
    (mem_timeBoundedIncompressibleStrings_iff_internal
      machine outputLength time bound output).mp houtput⟩

end TM

end Complexity
