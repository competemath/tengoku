/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Tengoku

@[expose] public section

variable {M M₀ : Type*} {r m : M} {k : ℕ}

section Monoid
variable [Monoid M]

def Powerfree (k : ℕ) (m : M) : Prop :=
  ∀ ⦃x : M⦄, x ^ k ∣ m → IsUnit x

/--
@isnad1 id=powerfre.2h4v.s4.a5374d1f6fb5 from=translated src=- shape=51356940 vocab=1864f8e8
-/
theorem Powerfree.of_le {a b : ℕ} (hab : a ≤ b) (hm : Powerfree a m) :
  Powerfree b m := fun x hx => hm (dvd_of_mul_right_dvd (pow_mul_pow_sub x hab ▸ hx))

/--
@isnad1 id=powerfre.2h4v.s5.73116a82fab8 from=translated src=- shape=d2b473b6 vocab=7654be04
-/
theorem Powerfree.of_dvd (hrm : r ∣ m) (hm : Powerfree k m) :
    Powerfree k r := fun _ hx => hm (hx.trans hrm)

/--
@isnad1 id=iff.1h4v.s4.dee60f90d9eb from=translated src=- shape=9e941558 vocab=445652f1
-/
theorem powerfree_congr (hrm : Associated r m) : Powerfree k r ↔ Powerfree k m :=
  ⟨fun h => h.of_dvd hrm.dvd', fun h => h.of_dvd hrm.dvd⟩

/--
@isnad1 id=iff.0h3v.s5.6dff09825d0f from=translated src=- shape=086ea056 vocab=41ac4de8
-/
@[simp]
theorem powerfree_neg [HasDistribNeg M] : Powerfree k (-m) ↔ Powerfree k m :=
  powerfree_congr (Associated.refl m).neg_left

/--
@isnad1 id=iff.0h2v.s4.fb5c11096c12 from=translated src=- shape=1b1fedbb vocab=cf1690de
-/
@[simp]
theorem powerfree_two {m : M} : Powerfree 2 m ↔ Squarefree m where
  mp h x hx := h (sq x ▸ hx)
  mpr h x hx := h x (sq x ▸ hx)

end Monoid

section CommMonoid
variable [CommMonoid M]

/--
@isnad1 id=powerfre.2h3v.s5.18923724ab39 from=translated src=- shape=546fd51c vocab=a47fb6c3
-/
theorem IsUnit.powerfree (h : IsUnit m) (hk : k ≠ 0) :
    Powerfree k m := fun _ hx => (isUnit_pow_iff hk).1 (isUnit_of_dvd_unit hx h)

/--
@isnad1 id=powerfre.1h2v.s5.59346d6cf6c4 from=translated src=- shape=f4c132f8 vocab=76b25422
-/
@[simp]
theorem powerfree_one (hk : k ≠ 0) : Powerfree k (1 : M) :=
  isUnit_one.powerfree hk

/--
@isnad1 id=powerfre.2h3v.s5.be87492bb6d2 from=translated src=- shape=c50e5af1 vocab=63477343
-/
theorem Irreducible.powerfree (h : Irreducible m) (hk : 2 ≤ k) :
    Powerfree k m := by
  rintro y ⟨z, hz⟩
  induction k with
  | zero => grind
  | succ n ih =>
  rw [pow_succ, mul_assoc] at hz
  rcases h.isUnit_or_isUnit hz with (hu | hu)
  · exact (isUnit_pow_iff (by linarith)).1 hu
  · apply isUnit_of_mul_isUnit_left hu

end CommMonoid

/--
@isnad1 id=not.0h2v.s4.7fd3669ce3fd from=translated src=- shape=40b48f0a vocab=fa482347
-/
@[simp]
theorem not_powerfree_zero [MonoidWithZero M₀] [Nontrivial M₀] (k : ℕ) :
    ¬ Powerfree k (0 : M₀) := by
  rw [Powerfree, not_forall]
  exact ⟨0, by simp⟩

/--
@isnad1 id=powerfre.2h3v.s5.63b0eeff94f0 from=translated src=- shape=89c54149 vocab=40cb9660
-/
theorem Prime.powerfree [CommMonoidWithZero M₀] [IsCancelMulZero M₀] {m : M₀} (h : Prime m)
    (hk : 2 ≤ k) : Powerfree k m := h.irreducible.powerfree hk
