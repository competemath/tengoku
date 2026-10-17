/-
Copyright (c) 2026 Julius Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julius Marx
-/
module

public import Tengoku.LeanPool.LeanPool.MRiscX.Semantics.Run

public import Tengoku
import Tengoku.LeanPool.LeanPool.MRiscX.Util.BasicTheorems
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
Basic theorems

This file contains many small lemmata about the built machine model.
These lemmata help proving
statements about the MRiscX language by simplifying terms.
All these lemmata are added to the simp command with
the `@[simp]`. This can shorten proofs because lean
can apply these theorems with simp automatically.
-/

@[expose] public section
local notation:60 "(" k " ↦ "v"; "m")" => TMap.put k v m


namespace MState

/--
@isnad1 id=eq.0h1v.s4.f91c13e21fb8 from=translated src=- shape=bec27525 vocab=d024877c
-/
@[simp] theorem incPc_increments_pc : ∀ (ms:MState),
  ms.incPc = {ms with pc := ms.pc + 1} := by
  simp [MState.incPc]

/--
@isnad1 id=eq.0h2v.s3.ea77b1e7e9f7 from=translated src=- shape=197a5141 vocab=5e5bcd49
-/
theorem setReg_incPc_symm : ∀(ms:MState) (r:Registers),
  (ms.setRegister r).incPc = ms.incPc.setRegister r := by
  simp [MState.setRegister, MState.incPc]

/--
@isnad1 id=eq.0h3v.s4.550c0667971b from=translated src=- shape=fd2cd16c vocab=96900c81
-/
theorem addReg_incPc_comm : ∀(ms:MState) (r v: UInt64),
  (ms.addRegister r v).incPc = ms.incPc.addRegister r v:= by
  simp [MState.addRegister, MState.incPc]

/--
@isnad1 id=eq.0h3v.s4.fa60a6b0930b from=translated src=- shape=fd2cd16c vocab=8a3d77ea
-/
theorem addMem_incPc_comm : ∀(ms:MState) (r v: UInt64),
  (ms.addMemory r v).incPc = ms.incPc.addMemory r v:= by
  simp [MState.addMemory, MState.incPc]

/--
@isnad1 id=eq.0h1v.s3.4c710714879d from=translated src=- shape=8d4cac31 vocab=d56f4e26
-/
theorem incPc_terminated : ∀(ms:MState),
  ms.incPc.terminated = ms.terminated := by
  simp [MState.incPc]

/--
@isnad1 id=eq.0h2v.s3.31936d116360 from=translated src=- shape=bc45798f vocab=e4ff7c35
-/
@[simp] theorem setPc_terminated : ∀(ms:MState) (p:UInt64),
  (ms.setPc p).terminated = ms.terminated := by
  simp [MState.setPc]

/--
@isnad1 id=eq.0h3v.s3.6f40a12d66ce from=translated src=- shape=38be6c85 vocab=a87eee41
-/
theorem addReg_terminated : ∀(ms:MState) (r v: UInt64),
  (ms.addRegister r v).terminated = ms.terminated := by
  simp [MState.addRegister]

/--
@isnad1 id=eq.0h3v.s3.d5ab0a759e11 from=translated src=- shape=38be6c85 vocab=405f8807
-/
theorem addMem_terminated : ∀(ms:MState) (r v: UInt64),
  (ms.addMemory r v).terminated = ms.terminated := by
  simp [MState.addMemory]

/--
@isnad1 id=eq.1h4v.s4.d024deff12e9 from=translated src=- shape=e8031987 vocab=52ad65c3
-/
theorem addRegister_getRegister_neq :
  ∀(ms:MState) (r1 r2 v : UInt64),
  r1 ≠ r2 →
  ((ms.addRegister r1 v).getRegisterAt r2) = (ms.getRegisterAt r2)
  := by
  intros ms r1 r2 v H
  simp only [MState.addRegister, MState.getRegisterAt]
  exact t_update_neq _ _ _ _ _ _ H

/--
@isnad1 id=eq.1h4v.s4.19e620475cd1 from=translated src=- shape=1053bc4c vocab=52ad65c3
-/
theorem addRegister_getRegister_eq :
  ∀(ms:MState) (r1 r2 v : UInt64),
  r1 = r2 →
  ((ms.addRegister r1 v).getRegisterAt r2) = v
  := by
  intros ms r1 r2 v H
  simp only [MState.addRegister, MState.getRegisterAt, H]
  exact t_update_eq _ _ _ _ _

/--
@isnad1 id=eq.0h3v.s4.fe07ba961a30 from=translated src=- shape=255ba000 vocab=d6399a6f
-/
theorem setPc_getRegister_indep :
  ∀(ms:MState) (i : UInt64) (r : UInt64),
  ((ms.setPc i).getRegisterAt r) = (ms.getRegisterAt r)
  := by
  simp [MState.setPc, MState.getRegisterAt]

/--
@isnad1 id=eq.0h3v.s4.4c1f83931f3e from=translated src=- shape=d1b477fc vocab=88fb49d3
-/
theorem setPc_getRegisterAt_def_indep :
  ∀(ms:MState) (r l: UInt64),
  TMap.get ms.registers r = TMap.get (ms.setPc l).registers r
  := by
  simp [MState.setPc]

/--
@isnad1 id=eq.0h3v.s4.ad737584c886 from=translated src=- shape=255ba000 vocab=6fc1912d
-/
theorem setPc_getMemory_indep :
  ∀(ms:MState) (i : UInt64) (r : UInt64),
  ((ms.setPc i).getMemoryAt r) = (ms.getMemoryAt r)
  := by
  simp [MState.setPc, MState.getMemoryAt]

/--
@isnad1 id=eq.0h3v.s4.4c6d147a9a14 from=translated src=- shape=d1b477fc vocab=76068a0c
-/
theorem setPc_getMemoryAt_def_indep :
  ∀(ms:MState) (m l: UInt64),
  TMap.get ms.memory m = TMap.get (ms.setPc l).memory m
  := by
  simp [MState.setPc]

/--
@isnad1 id=eq.0h2v.s3.f89bab87b637 from=translated src=- shape=3b3fe462 vocab=a0fbf004
-/
@[simp] theorem set_pc :
  ∀(ms:MState) (i : UInt64) ,
  (ms.setPc i).pc = i
  := by
  simp [MState.setPc]

/--
@isnad1 id=eq.0h2v.s3.8789a613d8d2 from=translated src=- shape=6422d269 vocab=c8d5af8c
-/
theorem incPc_getRegister_indep :
  ∀(ms:MState) (r : UInt64),
  ((ms.incPc).getRegisterAt r) = (ms.getRegisterAt r)
  := by
  simp [MState.incPc, MState.getRegisterAt]

/--
@isnad1 id=eq.1h3v.s5.a3a8572fcd4d from=translated src=- shape=ef85a01f vocab=4aabccf4
-/
@[simp] theorem jump_set_pc : ∀ (ms:MState) (s:String) (i:UInt64),
  (ms.code.labels.get s) = i ->
  (ms.jump s) = {ms with pc := i} := by
  intros ms s i H
  unfold MState.jump
  rw [H]

/--
@isnad1 id=eq.0h1v.s4.f049adf98f29 from=translated src=- shape=7fa557a1 vocab=49c5e822
-/
@[simp] theorem currInstruction_unfold : ∀ (ms:MState),
  ms.currInstruction = ms.code.instructionMap.get (ms.pc) := by
  simp [MState.currInstruction]

/--
@isnad1 id=eq.0h2v.s4.f76f05893189 from=translated src=- shape=0028e34d vocab=1bc55b74
-/
theorem runNSteps_currInstruction : ∀ (ms:MState) (n:Nat),
  (ms.runNSteps n).currInstruction = (ms.runNSteps n).code.instructionMap.get ((ms.runNSteps n).pc)
  := by
  simp

/--
@isnad1 id=eq.0h3v.s4.26b05d9a949e from=translated src=- shape=ec466956 vocab=7a4162ca
-/
@[simp] theorem addRegister_unfold (ms : MState) : ∀ (i1 i2:UInt64),
  ms.addRegister i1 i2 = {ms with registers :=
    ((i1) ↦ i2; ms.registers)} := by
  simp [MState.addRegister]

/--
@isnad1 id=eq.0h3v.s4.782d80a9ad43 from=translated src=- shape=4e25b47b vocab=80c213a9
-/
@[simp] theorem addMemory_unfold (ms : MState) : ∀ (i1 i2:UInt64),
  ms.addMemory i1 i2 = {ms with memory :=
    ((i1) ↦ i2; ms.memory)} := by
  simp [MState.addMemory]

/--
@isnad1 id=eq.0h1v.s3.d01e8473c522 from=translated src=- shape=bb0110a5 vocab=028b46f7
-/
@[simp] theorem run_zero_steps (ms : MState) :
  ms.runNSteps 0 = ms := by
  unfold MState.runNSteps
  rfl

/--
@isnad1 id=eq.0h2v.s4.1b475d9c62fb from=translated src=- shape=a51cfd88 vocab=99db1ed9
-/
theorem run_n_run_one : ∀ (ms:MState) (n:Nat),
  (ms.runNSteps n).runOneStep = ms.runNSteps (n+1) := by
  intros ms n
  revert ms
  induction n
  case zero =>
    intros ms
    rw [MState.run_zero_steps]
    unfold MState.runNSteps
    rw [MState.run_zero_steps]
  case succ n' IHN' =>
    intros ms
    unfold MState.runNSteps
    rw [IHN']

/--
@isnad1 id=eq.0h2v.s3.77f38b63b877 from=translated src=- shape=197a5141 vocab=c2f0633e
-/
theorem run_n_run_one_comm : ∀ (ms:MState) (n:Nat),
  (ms.runNSteps n).runOneStep = ms.runOneStep.runNSteps n := by
  intros ms n
  revert ms
  induction n
  case zero =>
    simp_all
  case succ n' IHN' =>
    intros ms
    unfold MState.runNSteps
    rw [IHN']

/--
@isnad1 id=eq.0h1v.s3.f8f477d7e43e from=translated src=- shape=b1919357 vocab=c2f0633e
-/
@[simp] theorem run_one_step_eq_run_n_1 : ∀ (ms:MState),
  ms.runOneStep = ms.runNSteps 1 := by
  intros ms
  unfold MState.runNSteps
  simp

/--
@isnad1 id=eq.0h3v.s4.2e7dc469723c from=translated src=- shape=a7080d31 vocab=028b46f7
-/
theorem run_N_comm : ∀ (ms:MState) (n m:Nat),
  (ms.runNSteps n).runNSteps m = (ms.runNSteps m).runNSteps n := by
  intros ms n
  revert ms
  induction n
  case zero =>
    simp_all
  case succ n IHN' =>
    intros ms m
    rw [<- MState.run_n_run_one, <- MState.run_n_run_one]
    rw [<- IHN']
    rw [<- MState.run_n_run_one_comm]

/--
@isnad1 id=eq.0h3v.s4.77864d2096fe from=translated src=- shape=69b0a24e vocab=1f024b10
-/
@[simp] theorem run_n_m_steps_comp : ∀ (ms:MState) (n m:Nat),
  (ms.runNSteps n).runNSteps m = ms.runNSteps (n + m) := by
  intros ms n
  revert ms
  induction n
  case zero =>
    simp_all
  case succ n' IHN' =>
    intros ms m
    rw [<- MState.run_n_run_one, Nat.add_assoc, <- IHN', Nat.add_comm,
      <- MState.run_n_run_one, <- MState.run_n_run_one_comm]

/--
@isnad1 id=eq.0h3v.s3.c8395dc2d49d from=translated src=- shape=38be6c85 vocab=3bc8902b
-/
theorem add_reg_code_no_change : ∀ (ms:MState) (r v:UInt64),
  (ms.addRegister r v).code = ms.code := by
  simp [MState.addRegister]

/--
@isnad1 id=eq.0h3v.s3.81cef7101feb from=translated src=- shape=38be6c85 vocab=55ae21e8
-/
theorem add_mem_code_no_change : ∀ (ms:MState) (r v:UInt64),
  (ms.addMemory r v).code = ms.code := by
  simp [MState.addMemory]

/--
@isnad1 id=eq.0h2v.s3.f7f718ef56fc from=translated src=- shape=bc45798f vocab=424436b2
-/
@[simp] theorem set_pc_code_no_change : ∀ (ms:MState) (v:UInt64),
  (ms.setPc v).code = ms.code := by
  simp [MState.setPc]

/--
@isnad1 id=eq.0h2v.s3.367a71513c1c from=translated src=- shape=bc45798f vocab=bd00da59
-/
@[simp] theorem set_termianted_code_no_change : ∀ (ms:MState) (v:Bool),
  (ms.setTerminated v).code = ms.code := by
  simp [MState.setTerminated]

/--
@isnad1 id=eq.0h5v.s5.abc01c6b7777 from=translated src=- shape=ef790982 vocab=8dcbd50c
-/
@[simp] theorem jump_register_indep : ∀ (ms:MState) (m:Memory) (r:Registers) (c:Code) (s:String),
  ({ms with registers := r, memory := m, code := c}.jump s).pc
    = ({ms with code := c}.jump s).pc := by
  intros ms m r c s
  unfold MState.jump
  simp
  cases PMap.get c.labels s
  · dsimp
  · simp

/--
@isnad1 id=eq.0h6v.s4.26580e5c2dd7 from=translated src=- shape=5862e5a9 vocab=f2e0c28f
-/
theorem get_register_only_register :
    ∀ (m:Memory) (r:Registers) (c:Code) (terminated:Bool) (i p:UInt64),
  {registers := r, memory := m, code := c, pc := p,
    terminated := terminated : MState}.getRegisterAt i =
  TMap.get r i := by
  simp [MState.getRegisterAt]

/--
@isnad1 id=eq.0h7v.s5.4410be187b2d from=translated src=- shape=1d658920 vocab=9a267a94
-/
theorem get_register_only_register' :
    ∀ (ms:MState) (m:Memory) (r:Registers) (c:Code) (terminated:Bool) (i p:UInt64),
  {ms with memory := m, registers := r, pc := p, code := c, terminated := terminated }.getRegisterAt
    i =
  {ms with registers := r}.getRegisterAt i := by
  simp [MState.getRegisterAt]

/--
@isnad1 id=eq.0h6v.s4.358a501e66be from=translated src=- shape=58909563 vocab=67dd73a2
-/
theorem get_register_only_memory :
    ∀ (m:Memory) (r:Registers) (c:Code) (terminated:Bool) (i p:UInt64),
  {registers := r, memory := m, code := c, pc := p,
    terminated := terminated : MState}.getMemoryAt i =
  TMap.get m i := by
  simp [MState.getMemoryAt]

/--
@isnad1 id=eq.0h7v.s5.c9e1e02dfc6a from=translated src=- shape=7c1317aa vocab=058f1988
-/
theorem get_register_only_memory' :
    ∀ (ms:MState) (m:Memory) (r:Registers) (c:Code) (terminated:Bool) (i p:UInt64),
  {ms with memory := m, registers := r, pc := p, code := c, terminated := terminated }.getMemoryAt
    i =
  {ms with memory := m}.getMemoryAt i := by
  simp [MState.getMemoryAt]

/--
@isnad1 id=eq.0h3v.s5.788498ed7235 from=translated src=- shape=f992b885 vocab=63c01122
-/
@[simp] theorem get_label_from_code : ∀(ms : MState) (s : String) (l : UInt64),
  (ms.getLabelAt s = l) = (PMap.get ms.code.labels s = l)
  := by
  simp [MState.getLabelAt]

/--
@isnad1 id=eq.0h2v.s4.3d3e811a6c67 from=translated src=- shape=93ab8979 vocab=125e7374
-/
@[simp] theorem getRegisterAt_def : ∀ (ms : MState) (l : UInt64),
  ms.getRegisterAt l = TMap.get ms.registers l := by
  simp [MState.getRegisterAt]

/--
@isnad1 id=eq.0h2v.s4.a931290578a8 from=translated src=- shape=93ab8979 vocab=7e9ee395
-/
@[simp] theorem getMemoryAt_def : ∀ (ms : MState) (l : UInt64),
  ms.getMemoryAt l = TMap.get ms.memory l := by
  simp [MState.getMemoryAt]

/--
@isnad1 id=eq.0h2v.s5.db525f8c29b4 from=translated src=- shape=f985799a vocab=7d3779bc
-/
theorem TMap_register_le_zero_eq_zero : ∀(ms:MState) (l : UInt64),
    (TMap.get ms.registers l ≤ 0) = (TMap.get ms.registers l = 0) := by
  simp

/--
@isnad1 id=eq.0h2v.s4.c9bd9a942782 from=translated src=- shape=3305f0fe vocab=0ce3eb0a
-/
theorem register_le_zero_eq_zero : ∀(ms:MState) (l : UInt64),
    (ms.getRegisterAt l ≤ 0) = (ms.getRegisterAt l = 0) := by
  simp

/--
@isnad1 id=eq.0h1v.s3.92b6c6c0f0ad from=translated src=- shape=8d4cac31 vocab=768259fc
-/
theorem runOneSteps_code_remains : ∀ (ms:MState),
  (ms.runOneStep).code = ms.code
  := by
  intros ms
  unfold MState.runOneStep
  cases ms.terminated
  case true => simp
  case false =>
    simp only [Bool.false_eq_true, ↓reduceIte, currInstruction_unfold, addRegister_unfold,
      incPc_increments_pc, getRegisterAt_def, getMemoryAt_def, addMemory_unfold, gt_iff_lt, ne_eq,
      decide_not]
    cases TMap.get ms.code.instructionMap ms.pc <;> simp only [set_termianted_code_no_change]
    case Jump s =>
      unfold MState.jump
      cases PMap.get ms.code.labels s <;> simp
    case JumpEq reg1 reg2 lbl | JumpNeq reg1 reg2 lbl
      | JumpGt reg1 reg2 lbl | JumpLe reg1 reg2 lbl =>
      unfold MState.jif' MState.getRegisterAt MState.jump
      simp
      split_ifs with h
      all_goals cases PMap.get ms.code.labels lbl <;> simp
    case JumpEqZero reg lbl | JumpNeqZero reg lbl =>
      unfold MState.jif MState.jump
      simp
      split_ifs with h
      all_goals cases PMap.get ms.code.labels lbl <;> simp

/--
@isnad1 id=eq.0h2v.s3.eb41f9707112 from=translated src=- shape=bc45798f vocab=25f570bb
-/
@[simp] theorem runNSteps_code_remains : ∀ (ms:MState) (n:Nat),
  (ms.runNSteps n).code = ms.code
  := by
  intros ms n
  unfold MState.runNSteps
  induction n with
  | zero =>
    simp
  | succ n' IHn' =>
    dsimp
    rw [<- run_n_run_one_comm, runOneSteps_code_remains]
    unfold MState.runNSteps
    exact IHn'

/--
@isnad1 id=eq.2h4v.s4.817b09c11b75 from=translated src=- shape=7386f1d5 vocab=25f570bb
-/
theorem code_remains_same : ∀ (ms ms' : MState) (code : Code) (n : ℕ),
  ms.code = code →
  ms.runNSteps n = ms' →
  ms'.code = code
  := by
  intros ms ms' code n h_code h_run
  rw [←h_run]
  simp [h_code]

/--
@isnad1 id=not.2h4v.s5.90bd1ea980cc from=translated src=- shape=fb2378b2 vocab=453fa921
-/
theorem runNSteps_diff : ∀ (s : MState) (n : Nat) (L1 L2 : Set UInt64),
  L2 ⊆ L1 →
  (s.runNSteps n).pc ∉ L1 →
  (s.runNSteps n).pc ∉ L2
  := by
  intros s n L1 L2 HSub H
  exact Set.notMem_subset HSub H

/--
@isnad1 id=mem.2h4v.s5.945d98aff07e from=translated src=- shape=2af3eab4 vocab=453fa921
-/
theorem runNSteps_pc_in_superset : ∀ (s : MState) (n : Nat) (L1 L2 : Set UInt64),
  L2 ⊆ L1 →
  (s.runNSteps n).pc ∈ L2 →
  (s.runNSteps n).pc ∈ L1
  := by
  intros s n L1 L2 HSub H
  exact Set.mem_of_subset_of_mem HSub H

/--
@isnad1 id=eq.2h5v.s5.efec15aae64f from=translated src=- shape=e4383597 vocab=1f024b10
-/
theorem runNSteps_add : ∀ (s s' s'':MState) (n n' : Nat),
  s.runNSteps n = s' →
  s'.runNSteps n' = s'' →
  s.runNSteps (n + n') = s'' := by
  intros s s' s'' n n' HRun HRun'
  rw [← run_n_m_steps_comp, HRun]
  exact HRun'

/--
@isnad1 id=not.4h6v.s6.067e57065484 from=translated src=- shape=53566971 vocab=141f3731
-/
theorem runNSteps_pc_nin : ∀ (s s' s'': MState) (n n' : Nat) (L : Set UInt64),
  s.runNSteps n = s' →
  s'.runNSteps n' = s'' →
  (s.runNSteps n).pc ∉ L →
  (s'.runNSteps n').pc ∉ L →
  (s.runNSteps (n + n')).pc ∉ L
  := by
  intros s s' s'' n n' L HRun HRun' _ HNin'
  rw [runNSteps_add s s' s'' n n' HRun HRun', ← HRun']
  exact HNin'

/--
@isnad1 id=not.4h5v.s6.6906efb3be2f from=translated src=- shape=81ccd8be vocab=756571e6
-/
theorem runNSteps_pc_nin_extra_step : ∀ (s s' : MState) (n : Nat) (L : Set UInt64),
  s.runNSteps n = s' →
  s'.pc ∉ L →
  (∀ (n' : Nat), 0 < n' ∧ n' < n → (s.runNSteps n').pc ∉ L) →
  ∀ (n'' : Nat), 0 < n'' ∧ n'' <= n → (s.runNSteps n'').pc ∉ L
  := by
  intros s s' n L HRun HPc HRunLTNin n'' Hn''
  rcases Hn'' with ⟨HN''GtZ, HN''LeN'⟩
  rw [← HRun] at HPc
  cases Nat.lt_or_eq_of_le HN''LeN' with
  | inl hlt =>
    simp_all
  | inr heq =>
    simp_all

/-- For `m < n'' < m + m'` and `s.runNSteps m = s'`, the `n''`-step run of `s`
equals an `n'`-step run of `s'` for some `0 < n' < m'`. -/
private theorem exists_tail_run (s s' : MState) (m m' n'' : Nat)
    (h_eq : s.runNSteps m = s') (h : m < n'') (hnlt : n'' < m + m') :
    ∃ n', (0 < n' ∧ n' < m') ∧ s.runNSteps n'' = s'.runNSteps n' := by
  refine ⟨n'' - m, ⟨Nat.sub_pos_of_lt h, ?_⟩, ?_⟩
  · exact Nat.lt_sub_left _ _ _ h hnlt
  · rw [← h_eq]
    simp only [run_n_m_steps_comp]
    rw [← Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
    apply Nat.le_of_lt h

/--
@isnad1 id=not.4h6v.s6.41a74092a3d5 from=translated src=- shape=a454288c vocab=0bf6f9b0
-/
theorem run_n_plus_m_pc_not_in_set :
  ∀ (s s' : MState) (m m' : Nat) (set : Set UInt64),
  s.runNSteps m = s' →
  (∀ (n : ℕ), 0 < n ∧ n ≤ m → (s.runNSteps n).pc ∉ set) →
  (∀ (n' : ℕ), 0 < n' ∧ n' < m' → (s'.runNSteps n').pc ∉ set) →
  ∀ (n'' : ℕ), 0 < n'' ∧ n'' < m + m' → (s.runNSteps n'').pc ∉ set := by
  intros s s' m m' set h_eq hL_b hL_b' n'' hn
  rcases hn with ⟨hn0, hnlt⟩
  by_cases h : n'' ≤ m
  · exact hL_b n'' ⟨hn0, h⟩
  · push Not at h
    obtain ⟨n', hn'_pre, h_run_eq⟩ := exists_tail_run s s' m m' n'' h_eq h hnlt
    simp_all

/--
@isnad1 id=not.4h7v.s6.bbdb9fe52382 from=translated src=- shape=b6b915c2 vocab=c049adb0
-/
theorem run_n_plus_m_diff_set :
  ∀ (s s' : MState) (m m' : Nat) (L_b L_b' : Set UInt64),
  s.runNSteps m = s' →
  (∀ (n : ℕ), 0 < n ∧ n ≤ m → (s.runNSteps n).pc ∉ L_b) →
  (∀ (n' : ℕ), 0 < n' ∧ n' < m' → (s'.runNSteps n').pc ∉ L_b') →
  ∀ (n'' : ℕ), 0 < n'' ∧ n'' < m + m' → (s.runNSteps n'').pc ∉ L_b ∩ L_b'
:= by
  intros s s' m m' L_b L_b' h_eq hL_b hL_b' n'' hn
  rcases hn with ⟨hn0, hnlt⟩
  by_cases h : n'' ≤ m
  · simp_all
  · push Not at h
    obtain ⟨n', hn'_pre, h_run_eq⟩ := exists_tail_run s s' m m' n'' h_eq h hnlt
    simp_all

/--
@isnad1 id=not.7h9v.s7.7788e2073001 from=translated src=- shape=effb4125 vocab=f8d17391
-/
theorem run_n_plus_m_intersect : ∀ (s s' : MState) (m m' : Nat) (L_w L_b L_w' L_b' : Set UInt64),
  (L_w' ⊆ L_b ∧ L_w ∩ L_w' = ∅) →
  s.runNSteps m = s' →
  s'.pc ∈ L_w →
  s'.pc ∉ L_b →
  (∀ (n : ℕ), 0 < n ∧ n < m → (s.runNSteps n).pc ∉ L_w ∪ L_b) →
  (∀ (n' : ℕ), 0 < n' ∧ n' < m' → (s'.runNSteps n').pc ∉ L_w' ∪ L_b') →
  ∀ (n'' : ℕ), 0 < n'' ∧ n'' < m + m' → (s.runNSteps n'').pc ∉ L_w' ∪ L_b ∩ L_b'
:= by
  intros s s' m m' L_w L_b L_w' L_b' h_sets h_run1 h_pc_w h_pc_not_b h_safe1 h_safe2 n'' HN''
  rcases HN'' with ⟨h_pos, h_lt⟩
  rcases h_sets with ⟨h_Lw'SubL_b, h_LwInterLw'⟩
  -- n'' ≤ m → s.runNSteps n'' ∉ L_b ∧ s.runNSteps n'' ∈ L_w
  -- → s.runNSteps n'' ∉ (L_w' ∪ L_b), da L_w ∩ L_w' = ∅
  -- n'' > m → s.runNSteps n'' ∉ L_w' ∪ L_b'
  rw [Set.union_inter_distrib_left]
  by_cases h: n'' ≤ m
  · cases Nat.lt_or_eq_of_le h with
    | inl hlt =>
      have h_n'': 0 < n'' ∧ n'' < m := And.intro h_pos hlt
      specialize h_safe1 n'' h_n''
      have h_safe1_NinLw': (s.runNSteps n'').pc ∉ L_w' ∪ L_b:= by
        rw [Set.mem_union]
        simp only [not_or]
        rw [Set.mem_union] at h_safe1
        simp only [not_or] at h_safe1
        rcases h_safe1 with ⟨_, h_safe1_r⟩
        exact ⟨Set.notMem_subset h_Lw'SubL_b h_safe1_r, h_safe1_r⟩
      simp_all
    | inr heq =>
      have h_pc_not_b' : (s.runNSteps m).pc ∉ L_b := h_run1 ▸ h_pc_not_b
      have h_safe1_m: (s.runNSteps n'').pc ∉ L_w' ∪ L_b := by
        rw [heq, Set.mem_union]
        simpa only [not_or]
          using ⟨Set.notMem_subset h_Lw'SubL_b h_pc_not_b', h_pc_not_b'⟩
      simp_all
  · push Not at h
    obtain ⟨n', hn'_pre, h_run_eq⟩ := exists_tail_run s s' m m' n'' h_run1 h h_lt
    simp_all

end MState
