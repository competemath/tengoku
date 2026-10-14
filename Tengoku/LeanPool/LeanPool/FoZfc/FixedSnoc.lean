/-
Copyright (c) 2026 Tetsuya Ishiu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Ishiu
-/
module

public import Tengoku

/-!
# The version of Fin.snoc for the fixed type.

## Main Definitions

- A `FirstOrder.ZFC.FixedSnoc.fixedSnoc` defines the version of Fin.snoc for the fixed type V.

## Main Statements

- A `FirstOrder.ZFC.FixedSnoc.snoc_conv` proves the relationship between Fin.snoc and fixedSnoc.
- `FirstOrder.ZFC.FixedSnoc.snoc_last` and `FirstOrder.ZFC.FixedSnoc.snoc_init` are
  to compute the values of fixedSnoc

## Implimentation notes

- Many theorems that make simp work better are proved.

-/

@[expose] public section

universe u

namespace FirstOrder.ZFC.FixedSnoc

variable {V : Type u}

/-- Fin.snoc for the type V. -/
def fixedSnoc {n : ℕ} (xs : Fin n → V) (b : V) :=
    (fun (k : Fin (n + 1)) => if h : k.val < n then xs (Fin.castLT k h) else b)

/-- Fin.snoc = fixedSnoc when applied to V.
@isnad1 id=eq.0h4v.s5.6763f2c8aa60 from=translated src=- shape=456701fa vocab=b52cd813
-/
@[simp]
theorem snoc_conv {n : ℕ} {xs : Fin n → V} {b : V} : Fin.snoc xs b = fixedSnoc xs b := by
  exact rfl

/-- fixedSnoc xs a n = a when xs : Fin n → V
@isnad1 id=eq.0h4v.s4.9decf2c2be5e from=translated src=- shape=641a37b0 vocab=674c677e
-/
@[simp]
theorem snoc_last {n : ℕ} (xs : Fin n → V) (a : V) : (fixedSnoc xs a) (Fin.last n) = a := by
  rw [← snoc_conv]
  simp

/-- fixedSnoc xs a k.castSucc = xs k when xs : Fin n → V and k : Fin n.
@isnad1 id=eq.0h5v.s4.dd1892413530 from=translated src=- shape=c84a1f48 vocab=1c7b9e7e
-/
@[simp]
theorem snoc_init {V : Type u} {n : ℕ} {xs : Fin n → V} {a : V} {k : Fin n} :
    fixedSnoc xs a k.castSucc = xs k := by
  rw [← snoc_conv]
  simp

/-- Rewrite castAdd by using castAdd with one castSucc.
@isnad1 id=eq.0h3v.s5.3565f9aeac0e from=translated src=- shape=2b0ea626 vocab=3315a273
-/
@[simp]
theorem castAdd_to_castSucc {n m : ℕ} {k : Fin n} : k.castAdd (m+1) = (k.castAdd m).castSucc := by
  apply Fin.eq_of_val_eq
  simp

/-- ofNat written by using Fin.last and castAdd.
@isnad1 id=eq.0h2v.s6.d2c030c02829 from=translated src=- shape=32b990d7 vocab=94de6171
-/
theorem coe_to_cast_add {n n' : ℕ} : Fin.ofNat (n+1+n') n = (Fin.last n).castAdd n' := by
  apply Fin.eq_of_val_eq
  simp only [Fin.ofNat_eq_cast, Fin.val_natCast, Fin.val_castAdd, Fin.val_last]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- ofNat n + ofNat m = ofNat (n + m).
@isnad1 id=eq.0h3v.s7.2f639079f8c5 from=translated src=- shape=0470b8f3 vocab=a1b58926
-/
theorem add_coe_eq_coe_add {n k m : ℕ} [NeZero (n + m)] :
    (Fin.ofNat (n+m) n + Fin.ofNat (n+m) k) = Fin.ofNat (n+m) (n+k) := by
  apply Fin.eq_of_val_eq
  rw [Fin.val_add]
  simp

/-- Describes the cancellation of fixedSnoc and castSucc with Sum.elim.
@isnad1 id=eq.0h5v.s6.1904b6cb305a from=translated src=- shape=9689ebb3 vocab=509b1ecd
-/
@[simp]
theorem sum_fixedSnoc_castSucc {n : ℕ} {s : ℕ → V} {xs : Fin n → V} {a : V} :
    (Sum.elim s (fixedSnoc xs a) ∘ Sum.map id fun (i : Fin n) ↦ i.castSucc) = Sum.elim s xs := by
  funext i
  rcases i with k | k <;> simp

/-- Describes the cancellation of fixedSnoc and castSucc with Sum.elim.
@isnad1 id=eq.0h4v.s5.528020f7dd6f from=translated src=- shape=89e24ebf vocab=73516a10
-/
@[simp]
theorem fixedSnoc_castSucc {n : ℕ} {xs : Fin n → V} {a : V} :
    (fixedSnoc xs a ∘ Fin.castSucc) = xs := by
  funext k
  simp

/-- `![a] 0 = a`.
@isnad1 id=eq.0h2v.s5.f8091f74f9f0 from=translated src=- shape=b5329f93 vocab=4e3792ea
-/
theorem Fintuple_1_0 {a : V} : ![a] 0 = a := by rfl

/-- `![a, b] (0 : Fin 2) = a`.
@isnad1 id=eq.0h3v.s5.66d45b5b682a from=translated src=- shape=69d77ee7 vocab=4e3792ea
-/
theorem Fintuple_2_0 {a b : V} : ![a, b] (0 : Fin 2) = a := by rfl

/-- `![a] 0 = a` via `Nat.cast`.
@isnad1 id=eq.0h2v.s5.3d815ab85c4e from=translated src=- shape=b4990301 vocab=4dcf969f
-/
theorem Fintuple_1_0' {a : V} :
    ![a] (@Nat.cast (Fin 1) (Fin.NatCast.instNatCast 1) 0) = a := by rfl

/-- `![a, b] 0 = a` via `Nat.cast`.
@isnad1 id=eq.0h3v.s5.1c31c24ab218 from=translated src=- shape=04882345 vocab=3995cc05
-/
theorem Fintuple_2_0' {a b : V} :
    ![a, b] (@Nat.cast (Fin 2) (Fin.NatCast.instNatCast 2) 0) = a := by rfl

/-- `![a, b, c] 0 = a` via `Nat.cast`.
@isnad1 id=eq.0h4v.s5.3915409b62e7 from=translated src=- shape=fef80fec vocab=3995cc05
-/
theorem Fintuple_3_0' {a b c : V} :
    ![a, b, c] (@Nat.cast (Fin 3) (Fin.NatCast.instNatCast 3) 0) = a := by rfl

/-- `![a, b, c] 1 = b` via `Nat.cast`.
@isnad1 id=eq.0h4v.s5.2270d133e65b from=translated src=- shape=a68487bf vocab=3995cc05
-/
@[simp]
theorem Fintuple_3_1' {a b c : V} :
    ![a, b, c] (@Nat.cast (Fin 3) (Fin.NatCast.instNatCast 3) 1) = b := by rfl

/-- `![a, b, c] 2 = c` via `Nat.cast`.
@isnad1 id=eq.0h4v.s5.028c10084174 from=translated src=- shape=1b5fd83c vocab=3995cc05
-/
theorem Fintuple_3_2' {a b c : V} :
    ![a, b, c] (@Nat.cast (Fin 3) (Fin.NatCast.instNatCast 3) 2) = c := by rfl

/-- `![a, b, c, d] 0 = a` via `Nat.cast`.
@isnad1 id=eq.0h5v.s6.ae3ba6bfcfa7 from=translated src=- shape=a9fde342 vocab=3995cc05
-/
theorem Fintuple_4_0' {a b c d : V} :
    ![a, b, c, d] (@Nat.cast (Fin 4) (Fin.NatCast.instNatCast 4) 0) = a := by rfl

/-- `![a, b, c, d] 1 = b` via `Nat.cast`.
@isnad1 id=eq.0h5v.s6.00c959ecdd16 from=translated src=- shape=3e3d623a vocab=3995cc05
-/
@[simp]
theorem Fintuple_4_1' {a b c d : V} :
    ![a, b, c, d] (@Nat.cast (Fin 4) (Fin.NatCast.instNatCast 4) 1) = b := by rfl

/-- `![a, b, c, d] 2 = c` via `Nat.cast`.
@isnad1 id=eq.0h5v.s6.31e2632c8c08 from=translated src=- shape=ffd1f5d7 vocab=3995cc05
-/
theorem Fintuple_4_2' {a b c d : V} :
    ![a, b, c, d] (@Nat.cast (Fin 4) (Fin.NatCast.instNatCast 4) 2) = c := by rfl

/-- `![a, b, c, d] 3 = d` via `Nat.cast`.
@isnad1 id=eq.0h5v.s6.ea32299fb11b from=translated src=- shape=0527a82a vocab=3995cc05
-/
theorem Fintuple_4_3' {a b c d : V} :
    ![a, b, c, d] (@Nat.cast (Fin 4) (Fin.NatCast.instNatCast 4) 3) = d := by rfl

/-- `fixedSnoc (fixedSnoc xs a) b 0 = a` over `Fin 0`.
@isnad1 id=eq.0h4v.s6.bccc65f66fbd from=translated src=- shape=33d6d2a1 vocab=5ff94478
-/
@[simp]
theorem FixedSnoc_2_0 {xs : Fin 0 → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b 0 = a := by rfl

/-- `fixedSnoc (fixedSnoc xs a) b 1 = b` over `Fin 0`.
@isnad1 id=eq.0h4v.s6.0642949e45d5 from=translated src=- shape=1a978ef5 vocab=5ff94478
-/
@[simp]
theorem FixedSnoc_2_1 {xs : Fin 0 → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b 1 = b := by rfl

/-- `fixedSnoc (fixedSnoc xs a) b 0 = a` over `Fin (0 + 2)`.
@isnad1 id=eq.0h4v.s6.c7e70c33a181 from=translated src=- shape=e68f3c74 vocab=5ff94478
-/
theorem FixedSnoc_0_2_0 {xs : Fin 0 → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b (@OfNat.ofNat (Fin (0 + 2)) 0 Fin.instOfNat) = a := by
  simp [fixedSnoc]

/-- `fixedSnoc (fixedSnoc xs a) b 1 = b` over `Fin (0 + 2)`.
@isnad1 id=eq.0h4v.s6.00b86f004465 from=translated src=- shape=0d5a1471 vocab=5ff94478
-/
theorem FixedSnoc_0_2_1 {xs : Fin 0 → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b (@OfNat.ofNat (Fin (0 + 2)) 1 Fin.instOfNat) = b := by
  simp [fixedSnoc]

/-- `fixedSnoc^3 ... 0 = a` over `Fin (0 + 3)`.
@isnad1 id=eq.0h5v.s7.b8143f70cb6f from=translated src=- shape=55ee400f vocab=5ff94478
-/
@[simp]
theorem FixedSnoc_0_3_0 {xs : Fin 0 → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@OfNat.ofNat (Fin (0 + 3)) 0 Fin.instOfNat) = a := by
  simp [fixedSnoc]

/-- `fixedSnoc^3 ... 1 = b` over `Fin (0 + 3)`.
@isnad1 id=eq.0h5v.s7.f9cbc8d4fa52 from=translated src=- shape=4d9cb54c vocab=5ff94478
-/
@[simp]
theorem FixedSnoc_0_3_1 {xs : Fin 0 → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@OfNat.ofNat (Fin (0 + 3)) 1 Fin.instOfNat) = b := by
  simp [fixedSnoc]

/-- `fixedSnoc^3 ... 2 = c` over `Fin (0 + 3)`.
@isnad1 id=eq.0h5v.s7.282de1c4b7d4 from=translated src=- shape=87644cd8 vocab=5ff94478
-/
@[simp]
theorem FixedSnoc_0_3_2 {xs : Fin 0 → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@OfNat.ofNat (Fin (0 + 3)) 2 Fin.instOfNat) = c := by
  simp [fixedSnoc]

/-- `fixedSnoc^4 ... 0 = a` over `Fin (0 + 4)`.
@isnad1 id=eq.0h6v.s7.7671176f9324 from=translated src=- shape=c4cfd6a5 vocab=5ff94478
-/
@[simp]
theorem FixedSnoc_0_4_0 {xs : Fin 0 → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@OfNat.ofNat (Fin (0 + 4)) 0 Fin.instOfNat) = a := by
  simp [fixedSnoc]

/-- `fixedSnoc^4 ... 1 = b` over `Fin (0 + 4)`.
@isnad1 id=eq.0h6v.s7.4162d6a6d756 from=translated src=- shape=9d7b91e3 vocab=5ff94478
-/
@[simp]
theorem FixedSnoc_0_4_1 {xs : Fin 0 → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
      (@OfNat.ofNat (Fin (0 + 4)) 1 Fin.instOfNat) = b := by
  simp [fixedSnoc]

/-- `fixedSnoc^4 ... 2 = c` over `Fin (0 + 4)`.
@isnad1 id=eq.0h6v.s7.0005e817a59d from=translated src=- shape=93200fee vocab=5ff94478
-/
@[simp]
theorem FixedSnoc_0_4_2 {xs : Fin 0 → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@OfNat.ofNat (Fin (0 + 4)) 2 Fin.instOfNat) = c := by
  simp [fixedSnoc]

/-- `fixedSnoc^4 ... 3 = d` over `Fin (0 + 4)`.
@isnad1 id=eq.0h6v.s7.b9a2146a14f7 from=translated src=- shape=744281d1 vocab=5ff94478
-/
@[simp]
theorem FixedSnoc_0_4_3 {xs : Fin 0 → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@OfNat.ofNat (Fin (0 + 4)) 3 Fin.instOfNat) = d := by
  simp [fixedSnoc]

/-- `fixedSnoc^2 ... (n+1) = b` over `Fin (n + 2)`.
@isnad1 id=eq.0h5v.s6.ee97bca24012 from=translated src=- shape=77493e9a vocab=2996f84b
-/
theorem FixedSnoc_n_2_1 {n : ℕ} {xs : Fin n → V} {a b : V} :
    fixedSnoc (fixedSnoc xs a) b (@Nat.cast (Fin (n + 1 + 1))
    (Fin.NatCast.instNatCast (n + 1 + 1)) (n + 1)) = b := by
  simp_all

/-- `fixedSnoc^3 ... (n+2) = c` over `Fin (n + 3)`.
@isnad1 id=eq.0h6v.s6.1e1abe157d14 from=translated src=- shape=044d0355 vocab=2996f84b
-/
theorem FixedSnoc_n_3_2 {n : ℕ} {xs : Fin n → V} {a b c : V} :
    fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c
    (@Nat.cast (Fin (n + 3)) (Fin.NatCast.instNatCast (n+3)) (n+2)) = c := by
  simp_all

/-- `fixedSnoc^4 ... (n+3) = d` over `Fin (n + 4)`.
@isnad1 id=eq.0h7v.s7.66881e5524f8 from=translated src=- shape=2c8c0fe1 vocab=2996f84b
-/
theorem FixedSnoc_n_4_3 {n : ℕ} {xs : Fin n → V} {a b c d : V} :
    fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    (@Nat.cast (Fin (n + 4)) (Fin.NatCast.instNatCast (n + 4)) (n + 3)) = d := by
  simp_all

/-- `fixedSnoc^2 ... ∘ castSucc^2 = xs`.
@isnad1 id=eq.0h5v.s6.486a62fcb51c from=translated src=- shape=d1d21bd0 vocab=73516a10
-/
@[simp]
theorem fixedSnoc_castSucc_2 {n : ℕ} {xs : Fin n → V} {a b : V} :
    (fixedSnoc (fixedSnoc xs a) b ∘ fun (i : Fin n) ↦ i.castSucc.castSucc)
    = xs := by
  funext k
  simp

/-- `fixedSnoc^3 ... ∘ castSucc^3 = xs`.
@isnad1 id=eq.0h6v.s7.6f571a015c87 from=translated src=- shape=881293a7 vocab=73516a10
-/
@[simp]
theorem fixedSnoc_castSucc_3 {n : ℕ} {xs : Fin n → V} {a b c : V} :
    (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c ∘ fun i ↦ i.castSucc.castSucc.castSucc) = xs := by
  funext k
  simp

/-- `fixedSnoc^4 ... ∘ castSucc^4 = xs`.
@isnad1 id=eq.0h7v.s7.ed8668d630b7 from=translated src=- shape=dbf2fc4c vocab=73516a10
-/
@[simp]
theorem fixedSnoc_castSucc_4 {n : ℕ} {xs : Fin n → V} {a b c d : V} :
    (fixedSnoc (fixedSnoc (fixedSnoc (fixedSnoc xs a) b) c) d
    ∘ fun i ↦ i.castSucc.castSucc.castSucc.castSucc) = xs := by
  funext k
  simp

/-- `fixedSnoc ∘ (castAdd ∘ castSucc) = xs ∘ castAdd`.
@isnad1 id=eq.0h5v.s6.271b70f9bd5b from=translated src=- shape=d7b290dc vocab=e06b91a2
-/
@[simp]
theorem fixedSnoc_castAdd_castSucc {n n' : ℕ} {xs : Fin (n + n') → V} {x : V} :
  (fixedSnoc xs x ∘ fun (i : Fin n) ↦ (Fin.castAdd n' i).castSucc) =
  (xs ∘ fun i ↦ Fin.castAdd n' i) := by
  funext k
  simp

end FirstOrder.ZFC.FixedSnoc
