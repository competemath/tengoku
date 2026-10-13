/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.RandomAccessMachine.Defs
public import Tengoku

/-!
# Random access machines: operational metatheory (proof internals)

This module proves the structural facts about `RAM.run`, `RAM.logTimeUpto`,
`RAM.unitTimeUpto`, and register support that the surface theorems rely on:

* **Unfolding lemmas** and the fixed-point behaviour of a halted configuration
  (`step_halted`, `run_halted`, `logTimeUpto_halted`, `unitTimeUpto_halted`).
* **Run/cost algebra**: `run_one`, `run_succ_step`, and the additive
  decompositions `run_add`, `logTimeUpto_add`, `unitTimeUpto_add`, giving
  stationarity of the run and cost once halted, and monotonicity of the cost
  in the fuel.
* **Cost lower bounds**: every executed step costs at least one time unit
  (`Instr.one_le_logCost`), so the step count never exceeds the logarithmic
  time (`unitTimeUpto_le_logTimeUpto`).
* **Finite support**: the register file has finite support along any run from
  a finitely-supported start (`run_finiteSupport`), which is what makes the
  `finsum`-based space measures `RAM.Cfg.space` and `RAM.Cfg.workSpace`
  genuine finite sums.

Not intended for human audit: the definitions in `Defs.lean` and the theorem
statements in the surface module carry the mathematical content.
-/

public section

namespace Complexity

namespace RAM

variable (P : Program)

/-! ### Unfolding lemmas -/

/--
@isnad1 id=eq.0h2v.s3.d23521cca524 from=translated src=- shape=0e10026a vocab=31cd78e3
-/
@[simp] theorem run_zero (c : Cfg) : run P 0 c = c := rfl

/--
@isnad1 id=eq.0h2v.s4.43d555661387 from=translated src=- shape=238d4b8f vocab=bb80fe44
-/
@[simp] theorem logTimeUpto_zero (c : Cfg) : logTimeUpto P 0 c = 0 := rfl

/--
@isnad1 id=eq.0h2v.s4.8b9702d4960a from=translated src=- shape=238d4b8f vocab=2979562c
-/
@[simp] theorem unitTimeUpto_zero (c : Cfg) : unitTimeUpto P 0 c = 0 := rfl

/--
@isnad1 id=eq.0h3v.s5.c93b8f6913c4 from=translated src=- shape=bef7962b vocab=288e5379
-/
theorem run_succ (fuel : ℕ) (c : Cfg) :
    run P (fuel + 1) c = if Halted P c then c else run P fuel (step P c) := rfl

/--
@isnad1 id=eq.0h3v.s5.e31063899bed from=translated src=- shape=f2f6d45a vocab=2a4eb43b
-/
theorem logTimeUpto_succ (fuel : ℕ) (c : Cfg) :
    logTimeUpto P (fuel + 1) c =
      if Halted P c then 0 else stepLogCost P c + logTimeUpto P fuel (step P c) := rfl

/--
@isnad1 id=eq.0h3v.s5.808f99f33548 from=translated src=- shape=23cb01cb vocab=0a487aa9
-/
theorem unitTimeUpto_succ (fuel : ℕ) (c : Cfg) :
    unitTimeUpto P (fuel + 1) c =
      if Halted P c then 0 else 1 + unitTimeUpto P fuel (step P c) := rfl

/-! ### Halted configurations are fixed points -/

/-- Stepping a halted configuration is a no-op: `halt` leaves everything fixed.
@isnad1 id=eq.1h2v.s3.cb580e622b40 from=translated src=- shape=05885b17 vocab=1861873a
-/
theorem step_halted {c : Cfg} (h : Halted P c) : step P c = c := by
  unfold step
  rw [show curInstr P c = Instr.halt from h]
  rfl

/-- Running a halted configuration for any amount of fuel leaves it fixed.
@isnad1 id=eq.1h3v.s4.4962c7778ad1 from=translated src=- shape=6eddcd39 vocab=8a7da8a1
-/
theorem run_halted {c : Cfg} (h : Halted P c) (fuel : ℕ) : run P fuel c = c := by
  cases fuel with
  | zero => rfl
  | succ f => rw [run_succ, ite_eq_left h]

/-- A halted configuration accumulates no logarithmic time.
@isnad1 id=eq.1h3v.s4.15085f9cf029 from=translated src=- shape=e05a3b47 vocab=53ad582c
-/
theorem logTimeUpto_halted {c : Cfg} (h : Halted P c) (fuel : ℕ) :
    logTimeUpto P fuel c = 0 := by
  cases fuel with
  | zero => rfl
  | succ f => rw [logTimeUpto_succ, ite_eq_left h]

/-- A halted configuration accumulates no unit time.
@isnad1 id=eq.1h3v.s4.dee08e69abd1 from=translated src=- shape=e05a3b47 vocab=c503f6cd
-/
theorem unitTimeUpto_halted {c : Cfg} (h : Halted P c) (fuel : ℕ) :
    unitTimeUpto P fuel c = 0 := by
  cases fuel with
  | zero => rfl
  | succ f => rw [unitTimeUpto_succ, ite_eq_left h]

/-! ### Run/cost algebra -/

/-- One unit of fuel performs exactly one step (a no-op if already halted).
@isnad1 id=eq.0h2v.s4.490fa3546d9f from=translated src=- shape=ae0171c2 vocab=ac174a29
-/
theorem run_one (c : Cfg) : run P 1 c = step P c := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, run_succ]
  by_cases h : Halted P c
  · rw [ite_eq_left h, step_halted P h]
  · rw [ite_eq_right h, run_zero]

/-- The run decomposes additively: `a + b` steps is `b` steps after `a` steps.
@isnad1 id=eq.0h4v.s4.ca6a0ec5e3f6 from=translated src=- shape=41fc2140 vocab=bf704fa3
-/
theorem run_add (a b : ℕ) (c : Cfg) : run P (a + b) c = run P b (run P a c) := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, run_succ, run_succ]
    by_cases h : Halted P c
    · rw [ite_eq_left h, ite_eq_left h]
      exact (run_halted P h b).symm
    · rw [ite_eq_right h, ite_eq_right h]
      exact ih (step P c)

/-- Running `n + 1` steps is one step after running `n` steps.
@isnad1 id=eq.0h3v.s4.6208634aa6d6 from=translated src=- shape=ed7a8b34 vocab=abd1996a
-/
theorem run_succ_step (n : ℕ) (c : Cfg) : run P (n + 1) c = step P (run P n c) := by
  rw [run_add P n 1, run_one]

/-- Logarithmic time decomposes additively along the run.
@isnad1 id=eq.0h4v.s5.9511ed2cc47d from=translated src=- shape=cdc1393b vocab=cf7296aa
-/
theorem logTimeUpto_add (a b : ℕ) (c : Cfg) :
    logTimeUpto P (a + b) c =
      logTimeUpto P a c + logTimeUpto P b (run P a c) := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, logTimeUpto_succ, logTimeUpto_succ, run_succ]
    by_cases h : Halted P c
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, logTimeUpto_halted P h b]
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, ih (step P c)]
      ring

/-- Unit time decomposes additively along the run.
@isnad1 id=eq.0h4v.s5.e8936953f072 from=translated src=- shape=cdc1393b vocab=fee031b0
-/
theorem unitTimeUpto_add (a b : ℕ) (c : Cfg) :
    unitTimeUpto P (a + b) c =
      unitTimeUpto P a c + unitTimeUpto P b (run P a c) := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, unitTimeUpto_succ, unitTimeUpto_succ, run_succ]
    by_cases h : Halted P c
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, unitTimeUpto_halted P h b]
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, ih (step P c)]
      ring

/-- Once halted after `f` steps, extra fuel does not change the configuration.
@isnad1 id=eq.2h4v.s4.be2a704983a6 from=translated src=- shape=af683508 vocab=7c9af527
-/
theorem run_eq_of_halted_le {c : Cfg} {f f' : ℕ} (hle : f ≤ f')
    (h : Halted P (run P f c)) : run P f' c = run P f c := by
  obtain ⟨g, rfl⟩ := Nat.le.dest hle
  rw [run_add]
  exact run_halted P h g

/-- Once halted after `f` steps, extra fuel does not change the logarithmic time.
@isnad1 id=eq.2h4v.s4.40bf52d15854 from=translated src=- shape=b4bae9bf vocab=46923fa0
-/
theorem logTimeUpto_eq_of_halted_le {c : Cfg} {f f' : ℕ} (hle : f ≤ f')
    (h : Halted P (run P f c)) : logTimeUpto P f' c = logTimeUpto P f c := by
  obtain ⟨g, rfl⟩ := Nat.le.dest hle
  rw [logTimeUpto_add, logTimeUpto_halted P h g, Nat.add_zero]

/-- Logarithmic time is monotone in the fuel.
@isnad1 id=le.1h4v.s4.9cb6397ed92a from=translated src=- shape=a12c4a0e vocab=52fbdf7a
-/
theorem logTimeUpto_mono {c : Cfg} {f f' : ℕ} (hle : f ≤ f') :
    logTimeUpto P f c ≤ logTimeUpto P f' c := by
  obtain ⟨g, rfl⟩ := Nat.le.dest hle
  rw [logTimeUpto_add]
  exact Nat.le_add_right _ _

/-- Unit time is monotone in the fuel.
@isnad1 id=le.1h4v.s4.f7666e9e4b2c from=translated src=- shape=a12c4a0e vocab=311ae060
-/
theorem unitTimeUpto_mono {c : Cfg} {f f' : ℕ} (hle : f ≤ f') :
    unitTimeUpto P f c ≤ unitTimeUpto P f' c := by
  obtain ⟨g, rfl⟩ := Nat.le.dest hle
  rw [unitTimeUpto_add]
  exact Nat.le_add_right _ _

/-! ### Cost lower bounds -/

/-- Every instruction costs at least one time unit under the logarithmic
    measure (the base cost).
@isnad1 id=le.0h2v.s3.f1f6834e44c7 from=translated src=- shape=0d4521f5 vocab=182fc206
-/
theorem Instr.one_le_logCost (i : Instr) (c : Cfg) : 1 ≤ i.logCost c := by
  cases i <;> simp only [Instr.logCost] <;> omega

/-- Every executed step costs at least one time unit.
@isnad1 id=le.0h2v.s3.87c4554e7450 from=translated src=- shape=0d4521f5 vocab=7fd014bd
-/
theorem one_le_stepLogCost (c : Cfg) : 1 ≤ stepLogCost P c :=
  Instr.one_le_logCost _ _

/-- The number of steps taken never exceeds the logarithmic time: each step
    costs at least one time unit, so log-time dominates the step count.
@isnad1 id=le.0h3v.s4.d6c4247d61cf from=translated src=- shape=d4deb5ec vocab=88b0a316
-/
theorem unitTimeUpto_le_logTimeUpto (fuel : ℕ) (c : Cfg) :
    unitTimeUpto P fuel c ≤ logTimeUpto P fuel c := by
  induction fuel generalizing c with
  | zero => simp
  | succ f ih =>
    rw [unitTimeUpto_succ, logTimeUpto_succ]
    by_cases h : Halted P c
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      have h1 : 1 ≤ stepLogCost P c := one_le_stepLogCost P c
      have h2 := ih (step P c)
      omega

/-- If no halt occurs in the first `fuel` steps, the unit time is exactly the
    fuel (every step is counted).
@isnad1 id=eq.1h3v.s4.48e93faefad7 from=translated src=- shape=b15c0270 vocab=d27772eb
-/
theorem unitTimeUpto_eq_of_not_halted (c : Cfg) (fuel : ℕ)
    (h : ∀ j < fuel, ¬ Halted P (run P j c)) : unitTimeUpto P fuel c = fuel := by
  induction fuel generalizing c with
  | zero => simp
  | succ f ih =>
    have h0 : ¬ Halted P c := h 0 (Nat.succ_pos f)
    rw [unitTimeUpto_succ, ite_eq_right h0]
    have hrec : unitTimeUpto P f (step P c) = f := by
      apply ih
      intro j hj
      have hstep : run P j (step P c) = run P (j + 1) c := by
        rw [run_succ, ite_eq_right h0]
      rw [hstep]
      exact h (j + 1) (by omega)
    rw [hrec]
    omega

/-! ### Finite support of the register file -/

/-- The support of an updated function is contained in the support of the
    original with the written index inserted.
@isnad1 id=le.0h3v.s5.935e19595e58 from=translated src=- shape=af8fd5b9 vocab=117a315d
-/
theorem support_update_subset (f : ℕ → ℕ) (i v : ℕ) :
    Function.support (Function.update f i v) ⊆ insert i (Function.support f) := by
  intro j hj
  simp only [Function.mem_support] at hj
  by_cases hji : j = i
  · subst hji; exact Set.mem_insert _ _
  · rw [Function.update_of_ne hji] at hj
    exact Set.mem_insert_of_mem _ hj

/-- The initial register file has finite support: only registers `0 … |x|` can
    be nonzero.
@isnad1 id=finite.0h1v.s3.6ffaf2c301f7 from=translated src=- shape=880cd1df vocab=9d65510b
-/
theorem initRegs_finiteSupport (x : List Bool) :
    (Function.support (initRegs x)).Finite := by
  apply Set.Finite.subset (Finset.range (x.length + 1)).finite_toSet
  intro i hi
  simp only [Function.mem_support] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  rw [not_lt] at hlt
  apply hi
  have hi0 : i ≠ 0 := by omega
  simp only [initRegs, hi0, ite_false, List.getElem?_eq_none (show x.length ≤ i - 1 by omega)]

/-- One instruction preserves finite support of the register file: each
    instruction writes at most one register.
@isnad1 id=finite.1h2v.s4.3a88f1da3225 from=translated src=- shape=afaa2207 vocab=945697a0
-/
theorem stepInstr_finiteSupport (i : Instr) (c : Cfg)
    (h : (Function.support c.regs).Finite) :
    (Function.support (stepInstr i c).regs).Finite := by
  cases i with
  | imm d v => exact (h.insert d).subset (support_update_subset c.regs d v)
  | add d s t => exact (h.insert d).subset (support_update_subset c.regs d _)
  | sub d s t => exact (h.insert d).subset (support_update_subset c.regs d _)
  | mul d s t => exact (h.insert d).subset (support_update_subset c.regs d _)
  | load d a => exact (h.insert d).subset (support_update_subset c.regs d _)
  | store a s => exact (h.insert (c.regs a)).subset (support_update_subset c.regs (c.regs a) _)
  | jz s tgt => dsimp only [stepInstr]; split <;> exact h
  | jmp tgt => exact h
  | halt => exact h

/-- One step preserves finite support of the register file.
@isnad1 id=finite.1h2v.s4.69ab3a9cbcb1 from=translated src=- shape=afaa2207 vocab=6acc296e
-/
theorem step_finiteSupport (c : Cfg) (h : (Function.support c.regs).Finite) :
    (Function.support (step P c).regs).Finite :=
  stepInstr_finiteSupport _ c h

/-- Finite support of the register file is a run invariant.
@isnad1 id=finite.1h3v.s4.54468a970019 from=translated src=- shape=b4ed6b38 vocab=3a32f1db
-/
theorem run_finiteSupport (fuel : ℕ) (c : Cfg)
    (h : (Function.support c.regs).Finite) :
    (Function.support (run P fuel c).regs).Finite := by
  induction fuel generalizing c with
  | zero => simpa using h
  | succ f ih =>
    rw [run_succ]
    split
    · exact h
    · exact ih (step P c) (step_finiteSupport P c h)

/-- Finite support along any run started from an initial configuration. This
    guarantees `RAM.Cfg.space` is a genuine finite sum, not the `finsum`
    fallback value `0`.
@isnad1 id=finite.0h3v.s4.8688bb2f6921 from=translated src=- shape=eec99cf3 vocab=e224e62b
-/
theorem run_initCfg_finiteSupport (fuel : ℕ) (x : List Bool) :
    (Function.support (run P fuel (initCfg x)).regs).Finite :=
  run_finiteSupport P fuel (initCfg x) (initRegs_finiteSupport x)

/-! ### Work space -/

/-- The initial configuration uses no work space: every register still holds
    its input value.
@isnad1 id=eq.0h1v.s3.56b675eff369 from=translated src=- shape=559c5ce3 vocab=881991e6
-/
@[simp] theorem Cfg.workSpace_initCfg (x : List Bool) : (initCfg x).workSpace x = 0 := by
  simp [Cfg.workSpace, initCfg]

/-- Only registers whose content differs from the initial register file are
    charged, so along any run from an initial configuration the work-space
    summand has finite support: `RAM.Cfg.workSpace` is a genuine finite sum.
@isnad1 id=finite.0h3v.s6.eb506e650b86 from=translated src=- shape=4b61f2ce vocab=f7687f64
-/
theorem run_initCfg_workSpace_finiteSupport (fuel : ℕ) (x : List Bool) :
    (Function.support fun i =>
      if (run P fuel (initCfg x)).regs i = initRegs x i then 0
      else bitlen i + bitlen ((run P fuel (initCfg x)).regs i)).Finite := by
  apply ((run_initCfg_finiteSupport P fuel x).union (initRegs_finiteSupport x)).subset
  intro i hi
  simp only [Function.mem_support, ne_eq] at hi
  by_contra hnot
  simp only [Set.mem_union, Function.mem_support, ne_eq, not_or, not_not] at hnot
  exact hi (ite_eq_left (hnot.1.trans hnot.2.symm))

end RAM

end Complexity
