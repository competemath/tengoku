/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku

/-!
 # Some stuff on dites
-/

@[expose] public section

/--
@isnad1 id=iff.0h4v.s5.f4178baac6c2 from=translated src=- shape=42cc94e6 vocab=af84458f
-/
theorem ite_eq_ite_iff {α : Type _} (a b c : α) :
    (∀ {p : Prop} [hp : Decidable p], @ite α p hp a c
      = @ite α p hp b c) ↔ a = b := by
  constructor
  · intro h
    exact h (p := True)
  · simp_all

/--
@isnad1 id=iff.0h5v.s6.dc8b294a19fa from=translated src=- shape=efd869de vocab=af6386f8
-/
theorem ite_eq_ite_iff_of_pi {n α : Type _} [DecidableEq n] (a b c : n → α) :
    (∀ i j : n, ite (i = j) (a i) (c i) = ite (i = j) (b i) (c i)) ↔ a = b := by
  constructor
  · intro h
    funext i
    specialize h i i
    simpa using h
  · simp_all

/--
@isnad1 id=eq.0h5v.s6.907d0876d734 from=translated src=- shape=42e2682f vocab=a170f1af
-/
theorem hMul_dite {α : Type _} [Mul α] (P : Prop) [Decidable P] (a : α) (b : P → α) (c : ¬P → α) :
    (a * dite P (fun x => b x) fun x => c x) = dite P (fun x => a * b x) fun x => a * c x := by
  simp_all

/--
@isnad1 id=eq.0h5v.s6.f99100cadd6b from=translated src=- shape=e69e64bc vocab=a170f1af
-/
theorem dite_hMul {α : Type _} [Mul α] (P : Prop) [Decidable P] (a : α) (b : P → α) (c : ¬P → α) :
    (dite P (fun x => b x) fun x => c x) * a = dite P (fun x => b x * a) fun x => c x * a := by
  simp_all

/--
@isnad1 id=eq.0h4v.s6.3179e05facda from=translated src=- shape=a4174c52 vocab=a684fd06
-/
theorem dite_boole_add {α : Type _} [AddZeroClass α] (P : Prop) [Decidable P] (a b : P → α) :
    (dite P (fun x => a x + b x) fun _ => 0) =
      (dite P (fun x => a x) fun _ => 0) + dite P (fun x => b x) fun _ => 0 :=
  by rw [dite_add_dite, add_zero]

/--
@isnad1 id=eq.0h5v.s6.c261828ad25f from=translated src=- shape=3d15a899 vocab=3e9a132d
-/
theorem dite_boole_smul {α β : Type _} [Zero α] [SMulZeroClass β α] (P : Prop) [Decidable P]
    (a : P → α) (r : β) :
    (dite P (fun x => r • a x) fun _ => 0) = r • dite P (fun x => a x) fun _ => 0 := by
  rw [smul_dite, smul_zero]

/--
@isnad1 id=eq.0h4v.s6.ed500962979d from=translated src=- shape=4255f53b vocab=874ef1e1
-/
theorem star_dite (P : Prop) [Decidable P] {α : Type _} [InvolutiveStar α] (a : P → α)
    (b : ¬P → α) :
    star (dite P (fun i => a i) fun i => b i) = dite P (fun i => star (a i)) fun i => star (b i) :=
  by
  rw [eq_comm, dite_eq_iff']
  simp_all

/--
@isnad1 id=eq.0h6v.s7.e627a174cee5 from=translated src=- shape=6a43ea13 vocab=53c13356
-/
theorem dite_tmul {R N₁ N₂ : Type _} [CommSemiring R] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module R N₁] [Module R N₂] (P : Prop) [Decidable P] (x₁ : P → N₁) (x₂ : N₂) :
    (dite P (fun h => x₁ h) fun _ => 0) ⊗ₜ[R] x₂ = dite P (fun h => x₁ h ⊗ₜ[R] x₂) fun _ => 0 := by
  split_ifs <;> simp

/--
@isnad1 id=eq.0h6v.s7.183e8d95756f from=translated src=- shape=9122449d vocab=53c13356
-/
theorem tmul_dite {R N₁ N₂ : Type _} [CommSemiring R] [AddCommGroup N₁] [AddCommGroup N₂]
    [Module R N₁] [Module R N₂] (P : Prop) [Decidable P] (x₁ : N₁) (x₂ : P → N₂) :
    (x₁ ⊗ₜ[R] dite P (fun h => x₂ h) fun _ => 0) = dite P (fun h => x₁ ⊗ₜ[R] x₂ h) fun _ => 0 := by
  split_ifs <;> simp

/--
@isnad1 id=eq.0h7v.s7.c18f0dfea848 from=translated src=- shape=f58372a9 vocab=cc042461
-/
theorem LinearMap.apply_dite {R H₁ H₂ : Type _} [Semiring R] [AddCommMonoid H₁] [AddCommMonoid H₂]
    [Module R H₁] [Module R H₂] (f : H₁ →ₗ[R] H₂) (P : Prop) [Decidable P] (a : P → H₁)
    (b : ¬P → H₁) :
    f (dite P (fun h => a h) fun h => b h) = dite P (fun h => f (a h)) fun h => f (b h) := by
  split_ifs <;> simp

/--
@isnad1 id=eq.0h7v.s6.18e6b7150fdb from=translated src=- shape=53f8eeb6 vocab=ffea5244
-/
lemma dite_apply' {i β : Type*} {α : i → Type*} (P : Prop) [Decidable P]
  {j : i} (f : P → (β → α j)) [Zero (α j)] (a : β) :
  (if h : P then (f h) else 0) a = if h : P then f h a else 0 :=
by aesop
