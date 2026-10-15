/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Prod
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Basic
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Prop

/-!
# LeanPool.QuasiBorelSpaces.Nat

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Nat`.
-/

@[expose] public section

namespace QuasiBorelSpace.Nat

variable
  {A : Type*} [QuasiBorelSpace A]
  {B : Type*} [QuasiBorelSpace B]
  {C : Type*} [QuasiBorelSpace C]

/--
@isnad1 id=ishom.3h5v.s6.62ecc62ab4e3 from=translated src=- shape=8ffa170b vocab=2a9f78c6
-/
@[fun_prop]
lemma isHom_rec
    {f : A → B} (hf : IsHom f)
    {g : A → ℕ → B → B} (hg : IsHom fun (x, y, z) ↦ g x y z)
    {h : A → ℕ} (hh : IsHom h)
    : IsHom (fun x ↦ (Nat.rec (f x) (g x) (h x) : B)) := by
  apply isHom_cases (ix := h) (f := fun n x ↦ (Nat.rec (f x) (g x) n : B)) hh
  intro n
  induction n with
    | zero =>
      simp only [Nat.rec_zero]
      fun_prop
    | succ n ih =>
      simp only
      fun_prop

/--
@isnad1 id=ishom.0h0v.s4.c6dd97e5a55e from=translated src=- shape=e0cc2553 vocab=3060bd3a
-/
@[local fun_prop]
lemma isHom_lt : IsHom (fun x : ℕ × ℕ ↦ x.1 < x.2) := by
  simp only [isHom_of_discrete_countable]

/--
@isnad1 id=ishom.2h3v.s5.3f0157d84f84 from=translated src=- shape=813f2e22 vocab=62c0f09e
-/
@[fun_prop]
lemma isHom_lt'
    {f : A → ℕ} (hf : IsHom f)
    {g : A → ℕ} (hg : IsHom g)
    : IsHom (fun x ↦ f x < g x) := by
  fun_prop

/--
@isnad1 id=ishom.0h0v.s4.79d14506a171 from=translated src=- shape=0fef64f0 vocab=e6f16ef9
-/
@[local fun_prop]
lemma isHom_add : IsHom (fun x : ℕ × ℕ ↦ x.1 + x.2) := by
  simp only [isHom_of_discrete_countable]

/--
@isnad1 id=ishom.2h3v.s5.e05f89f96a83 from=translated src=- shape=11826004 vocab=9b107a1a
-/
@[fun_prop]
lemma isHom_add'
    {f : A → ℕ} (hf : IsHom f)
    {g : A → ℕ} (hg : IsHom g)
    : IsHom (fun x ↦ f x + g x) := by
  fun_prop

/--
@isnad1 id=ishom.2h2v.s5.c24a0d2e7305 from=translated src=- shape=e7218a58 vocab=b3dcc7e5
-/
@[fun_prop]
lemma isHom_find
    {p : A → ℕ → Prop}
    [∀ x, DecidablePred (p x)]
    {q : ∀ x, ∃ n, p x n}
    (hp : ∀ n, IsHom (p · n))
    : IsHom fun x ↦ Nat.find (q x) := by
  rw [isHom_def,]
  intro φ hφ
  simp only [isHom_ofMeasurableSpace]
  intro X hX
  have : (fun r ↦ Nat.find (q (φ r))) ⁻¹' X
       = {r | ∃n ∈ X, p (φ r) n ∧ ∀{m}, m < n → ¬p (φ r) m} := by
    ext r
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    apply Iff.intro
    · intro h
      use Nat.find (q (φ r))
      use h
      use Nat.find_spec (q (φ r))
      use Nat.find_min (q (φ r))
    · rintro ⟨n, hn₁, hn₂, hn₃⟩
      suffices Nat.find (q (φ r)) = n by simp_all only [MeasurableSpace.measurableSet_top]
      rw [Nat.find_eq_iff]
      grind
  rw [this, measurableSet_setOfPred, ←isHom_iff_measurable]
  apply Prop.isHom_exists fun n ↦ Prop.isHom_and ?_ (Prop.isHom_and ?_ ?_)
  · simp only [isHom_const']
  · fun_prop
  · apply Prop.isHom_forall fun m ↦ ?_
    apply Prop.isHom_forall fun hmn ↦ ?_
    fun_prop

end QuasiBorelSpace.Nat

namespace QuasiBorelSpace.Fin

@[simps!]
instance {n} : QuasiBorelSpace (Fin n) := ofMeasurableSpace

end QuasiBorelSpace.Fin
