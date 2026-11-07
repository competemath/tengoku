/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Tengoku.Cslib.Cslib.Computability.URM.Defs
public import Tengoku.Seed.Data.List.MinMax

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
--public import Mathlib.Data.List.Fold

/-! # URM Basic Lemmas

This file contains basic lemmas and helper operations for URM types.

## Main definitions

- `Instr.IsJump`: predicate for jump instructions
- `Instr.JumpsBoundedBy`: checks if jump targets are bounded
- `Instr.capJump`: caps jump targets to a given length

## Main results

- `Regs.write_read_self`, `Regs.write_read_of_ne`: register read/write lemmas
- `State.isHalted_iff`, `State.ext`: state lemmas
- `JumpsBoundedBy.mono`: bounded jumps are monotonic in the bound
- `JumpsBoundedBy.shiftJumps`: shifting preserves bounded jumps
- `Program.mem_maxRegister`: instruction maxRegister bounded by program maxRegister
-/

@[expose] public section

namespace Cslib.URM

/-! ## Register Lemmas -/

namespace Regs

/--
@isnad1 id=eq.0h3v.s3.3cca24d55601 from=translated src=- shape=fca3beb9 vocab=ed1eff53
-/
@[simp, scoped grind =]
theorem write_read_self (σ : Regs) (n v : ℕ) : (σ.write n v).read n = v := by
  simp only [write, read, Function.update_self]

/--
@isnad1 id=eq.1h4v.s4.84bf4257e0f2 from=translated src=- shape=3411860c vocab=ed1eff53
-/
@[simp, scoped grind =]
theorem write_read_of_ne (σ : Regs) (m n v : ℕ) (h : m ≠ n) :
    (σ.write n v).read m = σ.read m := by
  simp only [write, read, Function.update_of_ne h]

end Regs

/-! ## State Lemmas -/

namespace State

/--
@isnad1 id=iff.0h2v.s4.352dfe1d6e25 from=translated src=- shape=bd078cad vocab=7bcedf45
-/
@[simp]
theorem isHalted_iff (s : State) (p : Program) : s.isHalted p ↔ p.length ≤ s.pc := Iff.rfl

/-- Extensionality for State: two states are equal iff their components are equal.
@isnad1 id=eq.2h2v.s4.52cfd502433c from=translated src=- shape=9ffad87c vocab=10f73a25
-/
@[ext]
theorem ext {s₁ s₂ : State} (hpc : s₁.pc = s₂.pc) (hregs : s₁.regs = s₂.regs) : s₁ = s₂ := by
  cases s₁; cases s₂; simp only at hpc hregs; simp [hpc, hregs]

end State

/-! ## Instruction Lemmas -/

namespace Instr

/-! ## Jump Instructions -/

/-- An instruction is a jump instruction.-/
def IsJump : Instr → Prop
  | J _ _ _ => True
  | _ => False

instance (instr : Instr) : Decidable instr.IsJump := by
  cases instr <;> simp only [IsJump] <;> infer_instance

/-- Z instruction is not a jump.
@isnad1 id=not.0h1v.s2.16ca11ba4516 from=translated src=- shape=36b3d148 vocab=c87b7ab5
-/
@[simp]
theorem Z_nonJump (n : ℕ) : ¬(Z n).IsJump := not_false

/-- S instruction is not a jump.
@isnad1 id=not.0h1v.s2.77cc5f13fe01 from=translated src=- shape=36b3d148 vocab=4be2c763
-/
@[simp]
theorem S_nonJump (n : ℕ) : ¬(S n).IsJump := not_false

/-- T instruction is not a jump.
@isnad1 id=not.0h2v.s3.031b1b204cf7 from=translated src=- shape=bd194212 vocab=666fc93e
-/
@[simp]
theorem T_nonJump (m n : ℕ) : ¬(T m n).IsJump := not_false

/-- J instruction is a jump.
@isnad1 id=isjump.0h3v.s3.b01853087dc4 from=translated src=- shape=eba0c72b vocab=bd66296d
-/
@[simp]
theorem J_IsJump (m n q : ℕ) : (J m n q).IsJump := trivial

/-- shiftJumps is identity for non-jumping instructions.
@isnad1 id=eq.1h2v.s3.358a6c54dfb4 from=translated src=- shape=15818b39 vocab=e177155d
-/
theorem shiftJumps_of_nonJump {instr : Instr}
    (h : ¬instr.IsJump) (offset : ℕ) : instr.shiftJumps offset = instr := by
  cases instr with
  | Z _ | S _ | T _ _ => rfl
  | J _ _ _ => exact absurd trivial h

/-! ## Bounded Jump Targets -/

/-- An instruction's jump target is bounded by a given length.
Non-jump instructions trivially satisfy this.-/
def JumpsBoundedBy (len : ℕ) : Instr → Prop
  | J _ _ q => q ≤ len
  | _ => True

instance (len : ℕ) (instr : Instr) : Decidable (instr.JumpsBoundedBy len) := by
  cases instr <;> simp only [JumpsBoundedBy] <;> infer_instance

/-- Non-jumping instructions have bounded jumps for any length.
@isnad1 id=jumpsbou.1h2v.s3.bcb5c17b8262 from=translated src=- shape=77e8a961 vocab=4f1577e5
-/
theorem jumpsBoundedBy_of_nonJump {instr : Instr} (h : ¬instr.IsJump)
    (len : ℕ) : instr.JumpsBoundedBy len := by
  cases instr with
  | J _ _ _ => exact absurd trivial h
  | _ => trivial

/-- JumpsBoundedBy is monotonic: if bounded for len1, then bounded for any len2 ≥ len1.
@isnad1 id=jumpsbou.2h3v.s4.f56481fecd90 from=translated src=- shape=5ebe7325 vocab=f95eede9
-/
theorem JumpsBoundedBy.mono {instr : Instr} {len1 len2 : ℕ}
    (h : instr.JumpsBoundedBy len1) (hle : len1 ≤ len2) :
    instr.JumpsBoundedBy len2 := by
  grind [JumpsBoundedBy]

/-- shiftJumps preserves bounded jumps with adjusted bound.
@isnad1 id=jumpsbou.1h3v.s4.a14fbaf1fb53 from=translated src=- shape=97428cb1 vocab=49c5f28e
-/
theorem JumpsBoundedBy.shiftJumps {instr : Instr} {len offset : ℕ}
    (h : instr.JumpsBoundedBy len) :
    (instr.shiftJumps offset).JumpsBoundedBy (offset + len) := by
  cases instr with
  | J _ _ q => simp only [Instr.shiftJumps, JumpsBoundedBy] at h ⊢; omega
  | _ => trivial

/-! ## Jump Target Capping -/

/-- Cap a jump target to be at most `len`. Non-jump instructions are unchanged.-/
@[scoped grind =]
def capJump (len : ℕ) : Instr → Instr
  | Z n => Z n
  | S n => S n
  | T m n => T m n
  | J m n q => J m n (min q len)

/--
@isnad1 id=eq.0h2v.s3.8007846ec9cc from=translated src=- shape=303fa963 vocab=72095305
-/
@[simp]
theorem capJump_Z (len n : ℕ) : (Z n).capJump len = Z n := rfl

/--
@isnad1 id=eq.0h2v.s3.262b05ba13f2 from=translated src=- shape=303fa963 vocab=7fe17c26
-/
@[simp]
theorem capJump_S (len n : ℕ) : (S n).capJump len = S n := rfl

/--
@isnad1 id=eq.0h3v.s4.dae4a6f9616e from=translated src=- shape=92f275b0 vocab=89a7d302
-/
@[simp]
theorem capJump_T (len m n : ℕ) : (T m n).capJump len = T m n := rfl

/--
@isnad1 id=eq.0h4v.s4.6568cbe0260d from=translated src=- shape=a4a03661 vocab=82172f9b
-/
@[simp]
theorem capJump_J (len m n q : ℕ) :
    (J m n q).capJump len = J m n (min q len) := rfl

/-- capJump always produces an instruction with bounded jump.
@isnad1 id=jumpsbou.0h2v.s3.e8d2eaaa7b46 from=translated src=- shape=6e160329 vocab=4f2df481
-/
theorem JumpsBoundedBy.capJump (len : ℕ) (instr : Instr) :
    (instr.capJump len).JumpsBoundedBy len := by
  cases instr with
  | J _ _ q => exact Nat.min_le_right q len
  | _ => trivial

/-- capJump is idempotent: capping twice is the same as capping once.
@isnad1 id=eq.0h2v.s3.49b2f3cb6d92 from=translated src=- shape=503e9be1 vocab=06712779
-/
@[simp]
theorem capJump_idempotent (len : ℕ) (instr : Instr) :
    (instr.capJump len).capJump len = instr.capJump len := by
  cases instr with
  | Z | S | T => rfl
  | J m n q => simp [capJump]

end Instr

namespace Program

/-- Any instruction in a program has maxRegister at most the program's maxRegister.
@isnad1 id=le.1h2v.s4.37e5d6ce9654 from=translated src=- shape=7b2fd23e vocab=fcb7c2fd
-/
theorem mem_maxRegister {p : Program} {instr : Instr} (h : instr ∈ p) :
    instr.maxRegister ≤ p.maxRegister := by
  unfold maxRegister
  rw [List.foldl_map.symm, ←List.foldr_eq_foldl]
  exact List.le_max_of_le' 0 (List.mem_map.mpr ⟨instr, h, rfl⟩) (le_refl _)

end Program

end Cslib.URM

end
