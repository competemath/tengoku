/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.Incompleteness.Foundation.Vorspiel.Vorspiel

/-! # Arith -/

@[expose] public section

open Mathlib List.Vector Part

namespace Nat

/--
@isnad1 id=lt.1h1v.s4.273ef99774af from=translated src=- shape=9ffb0ad4 vocab=7f9bb019
-/
lemma pos_of_eq_one (h : n = 1) : 0 < n := by simp[h]

/-- Imported declaration from the Incompleteness formalization. -/
def isEqNat (n m : ℕ) : ℕ := if n = m then 1 else 0

/-- Imported declaration from the Incompleteness formalization. -/
def isLtNat (n m : ℕ) : ℕ := if n < m then 1 else 0

/-- Imported declaration from the Incompleteness formalization. -/
def isLeNat (n m : ℕ) : ℕ := if n ≤ m then 1 else 0

/-- Imported declaration from the Incompleteness formalization. -/
def isDvdNat (n m : ℕ) : ℕ := if n ∣ m then 1 else 0

/--
@isnad1 id=iff.0h2v.s4.064cf0955742 from=translated src=- shape=172c9742 vocab=2a10540b
-/
@[simp] lemma isEqNat_pos_iff :
    0 < isEqNat n m ↔ n = m := by simp[isEqNat]; by_cases n = m <;> simp[*]

/--
@isnad1 id=iff.0h2v.s4.a5f0158a4cd2 from=translated src=- shape=056e6171 vocab=4cd99d15
-/
@[simp] lemma isLtNat_pos_iff :
    0 < isLtNat n m ↔ n < m := by simp[isLtNat]; by_cases n < m <;> simp[*]

/--
@isnad1 id=iff.0h2v.s4.af2df45a96a9 from=translated src=- shape=172c9742 vocab=11ecaea1
-/
@[simp] lemma isLeNat_pos_iff :
    0 < isLeNat n m ↔ n ≤ m := by simp[isLeNat]; by_cases n ≤ m <;> simp[*]

/--
@isnad1 id=iff.0h2v.s4.eb42b911679e from=translated src=- shape=172c9742 vocab=6297d51e
-/
@[simp] lemma isDvdNat_pos_iff :
    0 < isDvdNat n m ↔ n ∣ m := by simp[isDvdNat]; by_cases n ∣ m <;> simp[*]

/-- Imported declaration from the Incompleteness formalization. -/
def inv (n : ℕ) : ℕ := isEqNat n 0

/-- Imported declaration from the Incompleteness formalization. -/
def pos (n : ℕ) : ℕ := isLtNat 0 n

/--
@isnad1 id=eq.0h0v.s3.41f1fec4aeb2 from=translated src=- shape=3c26ae4f vocab=63906a70
-/
@[simp] lemma inv_zero : inv 0 = 1 := rfl

/--
@isnad1 id=iff.0h1v.s4.f9005e0293fb from=translated src=- shape=f5a24860 vocab=e2b7d8ec
-/
@[simp] lemma inv_iff_ne_zero : inv n = 0 ↔ 0 < n := by simp[inv, isEqNat, zero_lt_iff]

/--
@isnad1 id=eq.1h1v.s4.4bc4d10c1660 from=translated src=- shape=278e0375 vocab=63906a70
-/
@[simp] lemma inv_ne_zero (h : n ≠ 0) : inv n = 0 := by simp[inv, isEqNat, h]

/--
@isnad1 id=eq.0h0v.s3.f98c047bec13 from=translated src=- shape=3c26ae4f vocab=ab552698
-/
@[simp] lemma pos_zero : pos 0 = 0 := rfl

/--
@isnad1 id=eq.1h1v.s4.39ccb99d039e from=translated src=- shape=278e0375 vocab=ab552698
-/
@[simp] lemma pos_ne_zero (h : n ≠ 0) : pos n = 1 := by simp[pos, isLtNat, h]

/-- Imported declaration from the Incompleteness formalization. -/
def and (n m : ℕ) : ℕ := isLtNat 0 (n * m)

/-- Imported declaration from the Incompleteness formalization. -/
def or (n m : ℕ) : ℕ := isLtNat 0 (n + m)

/--
@isnad1 id=eq.0h2v.s6.65d84b6a65b6 from=translated src=- shape=67c9c6aa vocab=440ac11e
-/
lemma and_eq (n m : ℕ) :
    and n m = if 0 < n ∧ 0 < m then 1 else 0 := by simp [mul_pos_iff, and, isLtNat]

/--
@isnad1 id=iff.0h2v.s5.55b2f74f3b5f from=translated src=- shape=c7a32ebf vocab=747eb876
-/
lemma and_eq_one (n m : ℕ) :
    and n m = 1 ↔ 0 < n ∧ 0 < m := by simp[and_eq, imp_false, Nat.pos_iff_ne_zero]

/--
@isnad1 id=eq.0h2v.s6.a6a0a2b26cad from=translated src=- shape=67c9c6aa vocab=f7b8e4f9
-/
lemma or_eq (n m : ℕ) : or n m = if 0 < n ∨ 0 < m then 1 else 0 := by simp[or, isLtNat]

/--
@isnad1 id=iff.0h2v.s5.25bc669f42d1 from=translated src=- shape=ad0aef16 vocab=747eb876
-/
@[simp] lemma and_pos_iff (n m : ℕ) :
    0 < and n m ↔ 0 < n ∧ 0 < m := by simp[and_eq]; by_cases 0 < n ∧ 0 < m <;> simp[*]

/--
@isnad1 id=iff.0h2v.s5.f8ab5c81e9d0 from=translated src=- shape=ad0aef16 vocab=eb4ea332
-/
@[simp] lemma or_pos_iff' (n m : ℕ) :
    0 < or n m ↔ 0 < n ∨ 0 < m := by simp[or_eq]; by_cases 0 < n ∨ 0 < m <;> simp[*]

/--
@isnad1 id=iff.0h1v.s4.a00c52628cb6 from=translated src=- shape=07dd86de vocab=e2b7d8ec
-/
@[simp] lemma inv_pos_iff (n : ℕ) : 0 < inv n ↔ ¬0 < n := by simp[inv]

/--
@isnad1 id=iff.0h1v.s4.843d61b32e6d from=translated src=- shape=57f73327 vocab=d076d9e9
-/
@[simp] lemma pos_pos_iff (n : ℕ) : 0 < pos n ↔ 0 < n := by simp[pos]

/-- Imported declaration from the Incompleteness formalization. -/
inductive ArithPart₁ : ∀ {n}, (List.Vector ℕ n →. ℕ) → Prop
  | zero {n} : @ArithPart₁ n (fun _ => 0)
  | one {n} : @ArithPart₁ n (fun _ => 1)
  | add {n} (i j : Fin n) : @ArithPart₁ n (fun v => v.get i + v.get j : List.Vector ℕ n → ℕ)
  | mul {n} (i j : Fin n) : @ArithPart₁ n (fun v => v.get i * v.get j : List.Vector ℕ n → ℕ)
  | proj {n} (i : Fin n) : @ArithPart₁ n (fun v => v.get i : List.Vector ℕ n → ℕ)
  | equal {n} (i j : Fin n) : @ArithPart₁ n (fun v =>
    isEqNat (v.get i) (v.get j) : List.Vector ℕ n → ℕ)
  | lt {n} (i j : Fin n) : @ArithPart₁ n (fun v =>
    isLtNat (v.get i) (v.get j) : List.Vector ℕ n → ℕ)
  | comp {m n f} (g : Fin n → List.Vector ℕ m →. ℕ) :
    ArithPart₁ f → (∀ i, ArithPart₁ (g i)) → ArithPart₁ fun v =>
      (List.Vector.mOfFn fun i => g i v) >>= f
  | rfind {n} {f : List.Vector ℕ (n + 1) → ℕ} :
    ArithPart₁ (n := n + 1) f → ArithPart₁ (fun v => rfind fun n => Part.some (f (n ::ᵥ v) = 0))

/-- Imported declaration from the Incompleteness formalization. -/
def Arith₁ (f : List.Vector ℕ n → ℕ) := ArithPart₁ (n := n) f

end Nat

namespace Nat.ArithPart₁

open _root_.Nat.Primrec

/--
@isnad1 id=partrec.1h2v.s3.3316e3e3f145 from=translated src=- shape=bc0c2d8f vocab=4d6042a7
-/
lemma to_partrec' {n} {f : List.Vector ℕ n →. ℕ} (hf : ArithPart₁ f) : Partrec' f := by
  induction hf
  case zero => exact Partrec'.of_part (Partrec.const' 0)
  case one  => exact Partrec'.of_part (Partrec.const' 1)
  case add n i j =>
    exact (Partrec'.of_part ((Primrec.nat_add.comp
      (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i))
      (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const j))).to_comp.partrec))
  case mul n i j =>
    exact (Partrec'.of_part ((Primrec.nat_mul.comp
      (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i))
      (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const j))).to_comp.partrec))
  case proj n i =>
    exact Partrec'.of_part
      (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i)).to_comp.partrec
  case equal n i j =>
    have : Primrec (fun (v : List.Vector ℕ n) => if v.get i = v.get j then 1 else 0) :=
      Primrec.ite
        (Primrec.eq.comp
          (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i))
          (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const j)))
        (_root_.Primrec.const 1)
        (_root_.Primrec.const 0)
    exact Partrec'.of_part this.to_comp.partrec
  case lt n i j =>
    have : Primrec (fun (v : List.Vector ℕ n) => if v.get i < v.get j then 1 else 0) :=
      Primrec.ite
        (Primrec.nat_lt.comp
          (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const i))
          (Primrec.vector_get.comp _root_.Primrec.id (_root_.Primrec.const j)))
        (_root_.Primrec.const 1)
        (_root_.Primrec.const 0)
    exact Partrec'.of_part this.to_comp.partrec
  case comp m n f g _ _ hf hg => exact Partrec'.comp g hf hg
  case rfind f _ hf => exact Partrec'.rfind hf

/--
@isnad1 id=arithpar.2h3v.s5.109119c9a967 from=translated src=- shape=ee7b6e94 vocab=f300c1c4
-/
lemma of_eq {n} {f g : List.Vector ℕ n →. ℕ} (hf : ArithPart₁ f) (H : ∀ i, f i = g i) :
    ArithPart₁ g :=
  (funext H : f = g) ▸ hf

/--
@isnad1 id=arithpar.2h3v.s6.8c05a2aa6dce from=translated src=- shape=aad40f18 vocab=8b45cc20
-/
lemma bind (f : List.Vector ℕ n → ℕ →. ℕ) (hf :
    @ArithPart₁ (n + 1) fun v => f v.tail v.head) {g} (hg :
    @ArithPart₁ n g) :
    @ArithPart₁ n fun v => (g v).bind (f v) :=
  (hf.comp (g :> fun i v =>
    v.get i) (fun i => by
      cases i using Fin.cases
      · simpa using hg
      · exact proj _)).of_eq (by
    intro v
    rcases Part.eq_none_or_eq_some (g v) with (hgv | ⟨x, hgv⟩)
    · have hm : List.Vector.mOfFn
          (fun i => (g :> fun j v => v.get j) i v) = Part.none := by
        apply Part.eq_none_iff.mpr
        intro w hw
        have hall := mem_vector_mOfFn.mp hw
        have hx : w.get 0 ∈ g v := hall 0
        rw [hgv] at hx
        exact Part.notMem_none _ hx
      calc
        (List.Vector.mOfFn fun i => (g :> fun j v => v.get j) i v) >>=
            (fun w => f w.tail w.head) =
          Part.none.bind (fun w : List.Vector ℕ (n + 1) => f w.tail w.head) :=
            congrArg
              (fun p => p.bind (fun w : List.Vector ℕ (n + 1) => f w.tail w.head)) hm
        _ = Part.none := Part.bind_none _
        _ = Part.none.bind (f v) := (Part.bind_none (f v)).symm
        _ = (g v).bind (f v) :=
          congrArg (fun p => p.bind (f v)) hgv.symm
    · have hm : List.Vector.mOfFn
          (fun i => (g :> fun j v => v.get j) i v) = Part.some (x ::ᵥ v) := by
        apply Part.eq_some_iff.mpr
        apply mem_vector_mOfFn.mpr
        intro i
        cases i using Fin.cases with
        | zero =>
            have hx : x ∈ g v := Part.eq_some_iff.mp hgv
            exact hx
        | succ i =>
            exact Part.mem_some_iff.mpr (get_cons_succ (a := x) (v := v) i).symm
      have hf : (fun w => f w.tail w.head : List.Vector ℕ (n + 1) →. ℕ) (x ::ᵥ v) =
          f v x := by
        rfl
      calc
        (List.Vector.mOfFn fun i => (g :> fun j v => v.get j) i v) >>=
            (fun w => f w.tail w.head) =
          (Part.some (x ::ᵥ v)).bind
            (fun w : List.Vector ℕ (n + 1) => f w.tail w.head) :=
            congrArg
              (fun p => p.bind (fun w : List.Vector ℕ (n + 1) => f w.tail w.head)) hm
        _ = (fun w => f w.tail w.head : List.Vector ℕ (n + 1) →. ℕ) (x ::ᵥ v) :=
          Part.bind_some _ _
        _ = f v x := hf
        _ = (Part.some x).bind (f v) := (Part.bind_some x (f v)).symm
        _ = (g v).bind (f v) :=
          congrArg (fun p => p.bind (f v)) hgv.symm)

/--
@isnad1 id=arithpar.2h3v.s6.232f236dadca from=translated src=- shape=47a66018 vocab=68fc541b
-/
lemma map (f : List.Vector ℕ n → ℕ → ℕ) (hf : @Arith₁ (n + 1) fun v => f v.tail v.head) {g} (hg :
    @ArithPart₁ n g) :
    @ArithPart₁ n fun v => (g v).map (f v) :=
  (bind (Part.some <| f · ·) (hf.of_eq <| by simp) hg).of_eq <| by
  intro v; rcases Part.eq_none_or_eq_some (g v) with (_ | ⟨x, _⟩) <;> simp[*]

/--
@isnad1 id=arithpar.2h3v.s6.453cf1e1bebb from=translated src=- shape=821c5030 vocab=3aed6f7c
-/
lemma comp₁ (f : ℕ →. ℕ) (hf : @ArithPart₁ 1 fun v => f (v.get 0)) {n g} (hg : @Arith₁ n g) :
    @ArithPart₁ n fun v => f (g v) :=
  (hf.comp _ fun _ => hg).of_eq (by simp)

/--
@isnad1 id=arithpar.3h4v.s6.f1f1ac60903a from=translated src=- shape=3d2dcdaf vocab=3aed6f7c
-/
lemma comp₂ (f : ℕ → ℕ →. ℕ) (hf : @ArithPart₁ 2 fun v => f (v.get 0) (v.get 1)) {n g h} (hg :
    @Arith₁ n g) (hh :
    @Arith₁ n h) :
    @ArithPart₁ n fun v => f (g v) (h v) :=
  (hf.comp ![g, h] (fun i => i.cases hg (fun i => by simpa [Arith₁] using hh))).of_eq
    (by intro i
        have : (fun j =>
          (![↑g, h] : Fin 2 → List.Vector ℕ n →. ℕ) j i) = (fun j => pure (![g i, h i] j)) := by
          funext j; cases j using Fin.cases <;> simp[Fin.eq_zero]
        simp[]; simp[this] )

/--
@isnad1 id=arithpar.1h2v.s6.d0ff9d839c18 from=translated src=- shape=99bd4b5d vocab=01e272a8
-/
lemma rfind' {n} {f : ℕ → List.Vector ℕ n → ℕ} (h :
    Arith₁ (n :=
  n + 1) (fun v => f v.head v.tail)) :
    ArithPart₁ (fun v => Nat.rfind fun n => Part.some (f n v = 0)) := rfind h

/--
@isnad1 id=arithpar.1h3v.s6.c1d6ad0a6925 from=translated src=- shape=083c433d vocab=5651b8cc
-/
lemma rfind'₁ {n} (i : Fin n) {f : ℕ → ℕ → ℕ} (h :
    Arith₁ (n :=
  2) (fun v => f (v.get 0) (v.get 1))) :
    ArithPart₁ (fun v => Nat.rfind fun n => Part.some (f n (v.get i) = 0)) :=
  (rfind h).comp₁ (fun m => Nat.rfind fun n => Part.some (f n m = 0)) (proj i)

end Nat.ArithPart₁

namespace Nat.Arith₁

/--
@isnad1 id=arith.2h3v.s5.d2027b87cf9d from=translated src=- shape=4fcd5569 vocab=10f07774
-/
lemma of_eq {n} {f g : List.Vector ℕ n → ℕ} (hf : Arith₁ f) (H : ∀ i, f i = g i) : Arith₁ g :=
  (funext H : f = g) ▸ hf

/--
@isnad1 id=arith.0h1v.s3.5f04d620d0da from=translated src=- shape=3387b5fa vocab=10f07774
-/
lemma zero {n} : @Arith₁ n (fun _ => 0 : List.Vector ℕ n → ℕ) := Nat.ArithPart₁.zero

/--
@isnad1 id=arith.0h1v.s3.d6e20b538e15 from=translated src=- shape=3387b5fa vocab=10f07774
-/
lemma one {n} : @Arith₁ n (fun _ => 1 : List.Vector ℕ n → ℕ) := Nat.ArithPart₁.one

/--
@isnad1 id=arith.0h3v.s4.63f0e8321e1e from=translated src=- shape=52d1352a vocab=94a93475
-/
lemma add {n} (i j : Fin n) : @Arith₁ n (fun v => v.get i + v.get j) := Nat.ArithPart₁.add i j

/--
@isnad1 id=arith.0h3v.s4.6245a8df58bc from=translated src=- shape=52d1352a vocab=7e5f555f
-/
lemma mul {n} (i j : Fin n) : @Arith₁ n (fun v => v.get i * v.get j) := Nat.ArithPart₁.mul i j

/--
@isnad1 id=arith.0h2v.s4.375ad9d6b2a6 from=translated src=- shape=ff75c9e3 vocab=4124ecfe
-/
lemma proj {n} (i : Fin n) : @Arith₁ n (fun v => v.get i) := Nat.ArithPart₁.proj i

/--
@isnad1 id=arith.0h1v.s5.723b5ac65d5e from=translated src=- shape=28e640e2 vocab=4a6de1b5
-/
lemma head {n} : @Arith₁ (n + 1) (fun v => v.head) := (Nat.ArithPart₁.proj 0).of_eq <| by simp

/--
@isnad1 id=arith.0h3v.s4.d25f251e4495 from=translated src=- shape=13e61d84 vocab=a3c7af2b
-/
lemma equal {n} (i j : Fin n) :
    @Arith₁ n (fun v => isEqNat (v.get i) (v.get j)) :=
  Nat.ArithPart₁.equal i j

/--
@isnad1 id=arith.0h3v.s4.9cba55d5bca4 from=translated src=- shape=13e61d84 vocab=4f66ede2
-/
lemma lt {n} (i j : Fin n) :
    @Arith₁ n (fun v => isLtNat (v.get i) (v.get j)) :=
  Nat.ArithPart₁.lt i j

/--
@isnad1 id=arith.2h4v.s5.a4559200682e from=translated src=- shape=4faf96ca vocab=6f9377e0
-/
lemma comp {m n f} (g : Fin n → List.Vector ℕ m → ℕ) (hf : Arith₁ f) (hg : ∀ i, Arith₁ (g i)) :
    Arith₁ fun v => f (List.Vector.ofFn fun i => g i v) :=
  (Nat.ArithPart₁.comp (fun i => g i : Fin n → List.Vector ℕ m →. ℕ) hf hg).of_eq <| by
    intro v
    let w := List.Vector.ofFn fun i => g i v
    have hgi : (fun i => (g i : List.Vector ℕ m →. ℕ) v) =
        fun i => Part.some (g i v) := by
      funext i
      exact PFun.coe_val (g i) v
    have hm : (List.Vector.mOfFn fun i => (g i : List.Vector ℕ m →. ℕ) v) =
        Part.some w := by
      rw [hgi]
      simpa only [w] using Vector.mOfFn_part_some (fun i => g i v)
    calc
      (List.Vector.mOfFn fun i => (g i : List.Vector ℕ m →. ℕ) v) >>=
          (f : List.Vector ℕ n →. ℕ) =
        (Part.some w).bind (f : List.Vector ℕ n →. ℕ) :=
          congrArg (fun p => p.bind (f : List.Vector ℕ n →. ℕ)) hm
      _ = (f : List.Vector ℕ n →. ℕ) w := Part.bind_some _ _
      _ = Part.some (f w) := PFun.coe_val f w
      _ = ((fun v => f (List.Vector.ofFn fun i => g i v)) :
          List.Vector ℕ m →. ℕ) v := by
        exact (PFun.coe_val (fun v => f (List.Vector.ofFn fun i => g i v)) v).symm

/-- Imported declaration from the Incompleteness formalization. -/
def Vec {n m} (f : List.Vector ℕ n → List.Vector ℕ m) : Prop := ∀ i, Arith₁ fun v => (f v).get i

/--
@isnad1 id=vec.0h1v.s3.1a971019c136 from=translated src=- shape=bfbdc0d0 vocab=62ecfb18
-/
protected lemma nil {n} : @Vec n 0 (fun _ => nil) := fun i => i.elim0

/--
@isnad1 id=vec.2h4v.s5.f707588ddb59 from=translated src=- shape=5f493133 vocab=e8da5f9a
-/
protected lemma cons {n m f g} (hf : @Arith₁ n f) (hg : @Vec n m g) :
    Vec (fun v => f v ::ᵥ g v) := fun i => Fin.cases (by simp [*]) (fun i => by simp [hg i]) i

/--
@isnad1 id=arith.1h2v.s4.8ac301552bbe from=translated src=- shape=5c7a0dd6 vocab=a1aee9a9
-/
lemma tail {n f} (hf : @Arith₁ n f) : @Arith₁ n.succ fun v => f v.tail :=
  (hf.comp _ fun i => @proj _ i.succ).of_eq fun v => by
    rw[←ofFn_get v.tail]; congr; funext i; exact (List.Vector.get_tail_succ v i).symm

/--
@isnad1 id=arith.2h4v.s5.a3a3234b1044 from=translated src=- shape=373c5ae5 vocab=66fbaeef
-/
lemma comp' {n m f g} (hf : @Arith₁ m f) (hg : @Vec n m g) : Arith₁ fun v => f (g v) :=
  (hf.comp _ hg).of_eq fun v => by simp

/--
@isnad1 id=arith.2h3v.s6.21b03d19e639 from=translated src=- shape=eb32c472 vocab=4124ecfe
-/
lemma comp₁ (f : ℕ → ℕ) (hf : @Arith₁ 1 fun v => f (v.get 0)) {n g} (hg : @Arith₁ n g) :
    @Arith₁ n fun v => f (g v) :=
  (hf.comp _ fun _ => hg).of_eq (by simp)

/--
@isnad1 id=arith.3h4v.s6.9a33c1e547aa from=translated src=- shape=aa23a412 vocab=4124ecfe
-/
lemma comp₂ (f : ℕ → ℕ → ℕ) (hf : @Arith₁ 2 fun v => f (v.get 0) (v.get 1)) {n g h} (hg :
    @Arith₁ n g) (hh :
    @Arith₁ n h) :
    @Arith₁ n fun v => f (g v) (h v) :=
  (hf.comp ![g, h] (fun i =>
    i.cases hg (fun i => by simpa using hh))).of_eq (by intro i; simp[])

/--
@isnad1 id=arith.0h2v.s4.312d5eadb053 from=translated src=- shape=01eec12f vocab=94a93475
-/
lemma succ {n} (i : Fin n) : Arith₁ (fun v => v.get i + 1) := (add 0 1).comp₂ _ (proj i) one

/--
@isnad1 id=arith.0h2v.s3.e50951b27af9 from=translated src=- shape=857bbd65 vocab=10f07774
-/
lemma const {n} : ∀ m, @Arith₁ n fun _ => m
  | 0     => zero
  | m + 1 => (succ 0).comp₁ _ (const m)

/--
@isnad1 id=arith.0h2v.s4.484aa07af59a from=translated src=- shape=6d3dca8d vocab=801699e2
-/
lemma inv {n} (i : Fin n) : Arith₁ (fun v => inv (v.get i)) := (equal 0 1).comp₂ _ (proj i) zero

/--
@isnad1 id=arith.0h2v.s4.350d016170b1 from=translated src=- shape=6d3dca8d vocab=f5352982
-/
lemma pos {n} (i : Fin n) : Arith₁ (fun v => pos (v.get i)) := (lt 0 1).comp₂ _ zero (proj i)

/--
@isnad1 id=arith.0h3v.s4.895b1bf186da from=translated src=- shape=13e61d84 vocab=c6c0fd29
-/
lemma and {n} (i j : Fin n) :
    Arith₁ (fun v => and (v.get i) (v.get j)) :=
  (lt 0 1).comp₂ _ zero (mul i j)

/--
@isnad1 id=arith.0h3v.s4.21ab5d312181 from=translated src=- shape=13e61d84 vocab=8146ac05
-/
lemma or {n} (i j : Fin n) :
    Arith₁ (fun v => or (v.get i) (v.get j)) :=
  (lt 0 1).comp₂ _ zero (add i j)

/--
@isnad1 id=arith.0h3v.s4.ef18a33a63ef from=translated src=- shape=13e61d84 vocab=3bf967b4
-/
lemma le {n} (i j : Fin n) : @Arith₁ n (fun v => isLeNat (v.get i) (v.get j)) :=
  ((or 0 1).comp₂ _ (lt i j) (equal i j)).of_eq <| by simp[Nat.or_eq, Nat.le_iff_lt_or_eq, isLeNat]

/--
@isnad1 id=arith.3h4v.s6.f4351032cb5c from=translated src=- shape=e5a544fb vocab=4e66c643
-/
lemma if_pos {n} {f g h : List.Vector ℕ n → ℕ} (hf : Arith₁ f) (hg : Arith₁ g) (hh : Arith₁ h) :
    Arith₁ (fun v => if 0 < f v then g v else h v) := by
  have : Arith₁ (fun v => (f v).pos * (g v) + (f v).inv * (h v)) :=
    (add 0 1).comp₂ _
      ((mul 0 1).comp₂ _ ((pos 0).comp₁ _ hf) hg)
      ((mul 0 1).comp₂ _ ((inv 0).comp₁ _ hf) hh)
  exact this.of_eq <| by
    intro i; by_cases hf : f i = 0 <;> simp[hf, zero_lt_iff]

/--
@isnad1 id=arithpar.1h2v.s4.db372d9a1688 from=translated src=- shape=c783b5ec vocab=610467e6
-/
lemma to_arith₁ {f : List.Vector ℕ n → ℕ} (h : Arith₁ f) : @ArithPart₁ n (fun x => f x) := h

end Nat.Arith₁

namespace Nat.ArithPart₁

/--
@isnad1 id=arithpar.1h2v.s6.173c7827878c from=translated src=- shape=d1b4f0d4 vocab=aabd0328
-/
lemma rfindPos {n} {f : List.Vector ℕ (n + 1) → ℕ} (h : Arith₁ f) :
    ArithPart₁ (fun v => Nat.rfind fun n => Part.some (0 < f (n ::ᵥ v))) :=
  (ArithPart₁.rfind ((Arith₁.inv 0).comp₁ _ ((Arith₁.lt 0 1).comp₂ _ zero h))).of_eq <| by simp

/--
@isnad1 id=arithpar.1h3v.s6.812683c8cee4 from=translated src=- shape=44098b03 vocab=5390cc07
-/
lemma rfindPos₁ {n} (i : Fin n) {f : ℕ → ℕ → ℕ} (h :
    Arith₁ (n :=
  2) (fun v => f (v.get 0) (v.get 1))) :
    ArithPart₁ (fun v => Nat.rfind fun n => Part.some (0 < f n (v.get i))) :=
  (rfindPos h).comp₁ (fun m => Nat.rfind fun n => Part.some (0 < f n m)) (proj i)

/--
@isnad1 id=arithpar.1h3v.s7.2c41d120f035 from=translated src=- shape=90baffdd vocab=400aaa71
-/
lemma inv_fun {n} (i : Fin n) (f : ℕ → ℕ) (hf : Arith₁ (n := 1) (fun v => f (v.get 0))) :
    ArithPart₁ (fun v => Nat.rfind (fun x => Part.some (f x ≤ v.get i ∧ v.get i < f (x + 1)))) := by
  let F : ℕ → ℕ → ℕ := fun x y => (isLeNat (f x) y).and (isLtNat y (f (x + 1)))
  have := rfindPos₁ i (f := F) <| (Arith₁.and 0 1).comp₂ _
      ((Arith₁.le 0 1).comp₂ _ (hf.comp₁ _ (proj 0)) (proj 1))
      ((Arith₁.lt 0 1).comp₂ _ (proj 1) (hf.comp₁ _ <| (Arith₁.succ 0).comp₁ _ <| proj 0))
  exact this.of_eq <| by intro v; simp [F]

/--
@isnad1 id=arithpar.1h3v.s7.33957114db30 from=translated src=- shape=03057582 vocab=d06fd1ba
-/
lemma implicit_fun {n} (i : Fin n) (f : List.Vector ℕ n → ℕ → ℕ)
  (hf : Arith₁ (n := n + 1) (fun v => f v.tail v.head)) :
    ArithPart₁ (fun v =>
      Nat.rfind (fun x => Part.some (f v x ≤ v.get i ∧ v.get i < f v (x + 1)))) := by
  let F : List.Vector ℕ (n + 1) → ℕ :=
    fun v =>
      (isLeNat (f v.tail v.head) (v.get i.succ)).and (isLtNat (v.get i.succ) (f v.tail (v.head +
        1)))
  have : Arith₁ F :=
    (Arith₁.and 0 1).comp₂ _
      ((Arith₁.le 0 1).comp₂ _ hf (proj i.succ))
      ((Arith₁.lt 0 1).comp₂ _ (proj i.succ)
        (Arith₁.comp' hf (Arith₁.cons
          ((Arith₁.add 0 1).comp₂ _ Arith₁.head one) (fun i => Arith₁.tail (proj i)))))
  have := rfindPos this
  exact this.of_eq <| by intro v; simp [F]

end Nat.ArithPart₁

namespace Nat.Arith₁

/--
@isnad1 id=arith.0h2v.s4.eba2495d00f4 from=translated src=- shape=6d3dca8d vocab=a4ecf425
-/
protected lemma sqrt {n} (i : Fin n) : Arith₁ (fun v => sqrt (v.get i)) := by
  have := ArithPart₁.implicit_fun i (fun _ x => x * x) ((mul 0 1).comp₂ _ head head)
  exact this.of_eq <| by
    intro v; simp only [Bool.decide_and, PFun.coe_val, eq_some_iff]
    refine Nat.mem_rfind.mpr ?_
    simp only [mem_some_iff]
    constructor
    · symm; simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor
      · exact sqrt_le (List.Vector.get v i)
      · exact lt_succ_sqrt (List.Vector.get v i)
    · intro m hm; symm
      simp only [Bool.and_eq_false_eq_eq_false_or_eq_false, decide_eq_false_iff_not, not_le, not_lt]
      right; exact Iff.mp le_sqrt hm

/--
@isnad1 id=arith.0h3v.s4.218c2d90e999 from=translated src=- shape=52d1352a vocab=720e5e16
-/
lemma sub {n} (i j : Fin n) : Arith₁ (fun v => v.get i - v.get j) := by
  let F : List.Vector ℕ (n + 1) → ℕ := fun v =>
    (isEqNat (v.head + v.get j.succ) (v.get i.succ)).or
    ((isLtNat (v.get i.succ) (v.get j.succ)).and (isEqNat v.head 0))
  have : Arith₁ F :=
    (or 0 1).comp₂ _
      ((equal 0 1).comp₂ _ ((add 0 1).comp₂ _ head (proj j.succ)) (proj i.succ))
      ((and 0 1).comp₂ _ ((lt 0 1).comp₂ _ (proj i.succ) (proj j.succ)) ((equal 0 1).comp₂ _ head
        zero))
  exact (ArithPart₁.rfindPos this).of_eq <| by
    intro v
    simp only [head_cons, get_cons_succ, or_pos_iff', isEqNat_pos_iff, and_pos_iff,
      isLtNat_pos_iff, Bool.decide_or, Bool.decide_and, PFun.coe_val, eq_some_iff, F]
    refine Nat.mem_rfind.mpr ?_
    simp only [mem_some_iff]
    constructor
    · symm; simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
      have : v.get i < v.get j ∨ v.get j ≤ v.get i := Nat.lt_or_ge _ _
      rcases this with (hv | hv)
      · right; exact ⟨hv, Nat.sub_eq_zero_of_le (Nat.le_of_lt hv)⟩
      · left; exact Nat.sub_add_cancel hv
    · intro m hm; symm
      simp only [Bool.or_eq_false_eq_eq_false_and_eq_false,
        decide_eq_false_iff_not, Bool.and_eq_false_eq_eq_false_or_eq_false, not_lt]
      have : m + v.get j < v.get i := add_lt_of_lt_sub hm
      exact ⟨ne_of_lt this, by left; exact le_trans le_add_self (le_of_lt this)⟩

/--
@isnad1 id=arith.0h3v.s4.6b8499c96968 from=translated src=- shape=13e61d84 vocab=e99a910d
-/
protected lemma pair {n} (i j : Fin n) : Arith₁ (fun v => (v.get i).pair (v.get j)) := by
  have := if_pos (lt i j)
    ((add 0 1).comp₂ _ (mul j j) (proj i))
    ((add 0 1).comp₂ _ ((add 0 1).comp₂ _ (mul i i) (proj i)) (proj j))
  exact this.of_eq <| by
    intro v; simp[pair]

/--
@isnad1 id=arith.0h2v.s4.a58631255379 from=translated src=- shape=f1f86807 vocab=4f4fcd13
-/
lemma unpair₁ {n} (i : Fin n) : Arith₁ (fun v => (v.get i).unpair.1) := by
  have hf : Arith₁ (fun v => isLtNat (v.get i - (v.get i).sqrt * (v.get i).sqrt) (v.get i).sqrt) :=
    (lt 0 1).comp₂ _
      ((Arith₁.sub 0 1).comp₂ _ (proj i) ((mul 0 1).comp₂ _ (Arith₁.sqrt i) (Arith₁.sqrt i)))
      (Arith₁.sqrt i)
  have hg : Arith₁ (fun v => v.get i - (v.get i).sqrt * (v.get i).sqrt) :=
    (sub 0 1).comp₂ _ (proj i) ((mul 0 1).comp₂ _ (Arith₁.sqrt i) (Arith₁.sqrt i))
  have hh : Arith₁ (fun v => sqrt (v.get i)) := Arith₁.sqrt i
  have := if_pos hf hg hh
  exact this.of_eq <| by
    intro v; simp only [isLtNat_pos_iff, unpair]
    by_cases v.get i - (v.get i).sqrt * (v.get i).sqrt < sqrt (v.get i) <;> simp[*]

/--
@isnad1 id=arith.0h2v.s4.d4dbaa2b8c2d from=translated src=- shape=f1f86807 vocab=a31cca88
-/
lemma unpair₂ {n} (i : Fin n) : Arith₁ (fun v => (v.get i).unpair.2) := by
  have hf : Arith₁ (fun v => isLtNat (v.get i - (v.get i).sqrt * (v.get i).sqrt) (v.get i).sqrt) :=
    (lt 0 1).comp₂ _
      ((Arith₁.sub 0 1).comp₂ _ (proj i) ((mul 0 1).comp₂ _ (Arith₁.sqrt i) (Arith₁.sqrt i)))
      (Arith₁.sqrt i)
  have hg : Arith₁ (fun v => sqrt (v.get i)) := Arith₁.sqrt i
  have hh : Arith₁ (fun v => v.get i - (v.get i).sqrt * (v.get i).sqrt - (v.get i).sqrt) :=
    (sub 0 1).comp₂ _ ((sub 0 1).comp₂ _ (proj i) ((mul 0 1).comp₂ _ (Arith₁.sqrt i) (Arith₁.sqrt
      i))) (Arith₁.sqrt i)
  have := if_pos hf hg hh
  exact this.of_eq <| by
    intro v; simp only [isLtNat_pos_iff, unpair]
    by_cases v.get i - (v.get i).sqrt * (v.get i).sqrt < sqrt (v.get i) <;> simp[*]

/-- Imported declaration from the Incompleteness formalization. -/
def recSequence (f : List.Vector ℕ n → ℕ) (g : List.Vector ℕ (n + 2) → ℕ) (z : ℕ) (v :
    List.Vector ℕ n) :
    List ℕ :=
  List.ofFn fun i : Fin (z + 1) => Nat.recOn i (f v) (fun y IH => g (y ::ᵥ IH ::ᵥ v))

/--
@isnad1 id=eq.1h6v.s6.d5c89c7ed3ae from=translated src=- shape=791ce274 vocab=23f37b3d
-/
lemma beta_unbeta_recSequence_eq (f : List.Vector ℕ n → ℕ) (g : List.Vector ℕ (n + 2) → ℕ) (z :
    ℕ) (v :
    List.Vector ℕ n)
  (m : ℕ) (hm : m < z + 1) :
    Nat.beta (unbeta (recSequence f g z v)) m = m.rec (f v) (fun y IH => g (y ::ᵥ IH ::ᵥ v)) := by
  have : (unbeta (recSequence f g z v)).beta m = (recSequence f g z v).get ⟨m, _⟩ :=
    Nat.beta_unbeta_coe (recSequence f g z v) ⟨m, by simp[recSequence, hm]⟩
  rw [this]; simp [List.get_ofFn, recSequence, -List.get_eq_getElem]

/--
@isnad1 id=eq.0h5v.s5.fa5966bb5496 from=translated src=- shape=91b49b1e vocab=490af79b
-/
lemma beta_unbeta_recSequence_zero (f : List.Vector ℕ n → ℕ) (g : List.Vector ℕ (n + 2) → ℕ) (z :
    ℕ) (v :
    List.Vector ℕ n) :
    Nat.beta (unbeta (recSequence f g z v)) 0 = f v := by
  simpa using beta_unbeta_recSequence_eq f g z v 0 (inv_iff_ne_zero.mp rfl)

/--
@isnad1 id=eq.1h6v.s6.03ec0c4f38ce from=translated src=- shape=7123a2d1 vocab=027afdeb
-/
lemma beta_unbeta_recSequence_succ (f : List.Vector ℕ n → ℕ) (g : List.Vector ℕ (n + 2) → ℕ) (z :
    ℕ) (v :
    List.Vector ℕ n)
  {m : ℕ} (hm : m < z) :
    Nat.beta (unbeta (recSequence f g z v)) (m + 1) =
        g (m ::ᵥ Nat.beta (unbeta (recSequence f g z v)) m ::ᵥ v) := by
  rw [beta_unbeta_recSequence_eq f g z v m (Nat.lt_add_right 1 hm),
    beta_unbeta_recSequence_eq f g z v (m + 1) (Nat.add_lt_add_right hm 1)]

/--
@isnad1 id=eq.2h6v.s7.5720cf451d31 from=translated src=- shape=9e35b9a1 vocab=df8168ff
-/
lemma beta_eq_rec (f : List.Vector ℕ n → ℕ) (g : List.Vector ℕ (n + 2) → ℕ) {z : ℕ} {v}
  (h0 : z.beta 0 = f v) (hs : ∀ i < m, z.beta (i + 1) = g (i ::ᵥ z.beta i ::ᵥ v)) :
    z.beta m = m.rec (f v) (fun y IH => g (y ::ᵥ IH ::ᵥ v)) := by
  induction m with
  | zero => simp [h0]
  | succ m ih =>
    simp only
    rw [hs m (Nat.lt_add_one m), ←ih (fun i hi => hs i (Nat.lt_succ_of_lt hi))]

end Nat.Arith₁

namespace Nat.ArithPart₁

/-- Imported declaration from the Incompleteness formalization. -/
inductive Code : ℕ → Type
  | zero (n) : Code n
  | one (n) : Code n
  | add {n} (i j : Fin n) : Code n
  | mul {n} (i j : Fin n) : Code n
  | proj {n} (i : Fin n) : Code n
  | equal {n} (i j : Fin n) : Code n
  | lt {n} (i j : Fin n) : Code n
  | comp {m n} : Code n → (Fin n → Code m) → Code m
  | rfind {n} : Code (n + 1) → Code n

instance (k) : Inhabited (Code k) := ⟨Code.zero k⟩

/-- Imported declaration from the Incompleteness formalization. -/
inductive _root_.Nat.ArithPart₁.Code.eval : {n : ℕ} → Code n → (List.Vector ℕ n →. ℕ) → Prop
  | zero {n} : Code.eval (Code.zero n) (fun _ => 0)
  | one  {n} : Code.eval (Code.one n)  (fun _ => 1)
  | add  {n} (i j : Fin n) : Code.eval (Code.add i j) (fun v => ↑(v.get i + v.get j))
  | mul  {n} (i j : Fin n) : Code.eval (Code.mul i j) (fun v => ↑(v.get i * v.get j))
  | proj {n} (i : Fin n)   : Code.eval (Code.proj i) (fun v => v.get i)
  | equal {n} (i j : Fin n)   : Code.eval (Code.equal i j) (fun v => isEqNat (v.get i) (v.get j))
  | lt {n} (i j : Fin n) : Code.eval (Code.lt i j) (fun v => isLtNat (v.get i) (v.get j))
  | comp {m n} (c : Code n) (d : Fin n → Code m) (f : List.Vector ℕ n →. ℕ) (g : Fin n →
    (List.Vector ℕ m →. ℕ)) :
      Code.eval c f → (∀ i, Code.eval (d i) (g i)) →
      Code.eval (c.comp d) (fun v => (List.Vector.mOfFn fun i => g i v) >>= f)
  | rfind {n} (c : Code (n + 1)) (f : List.Vector ℕ (n + 1) → ℕ) :
      Code.eval c f → Code.eval c.rfind (fun v => Nat.rfind fun n => Part.some (f (n ::ᵥ v) = 0))

end Nat.ArithPart₁
