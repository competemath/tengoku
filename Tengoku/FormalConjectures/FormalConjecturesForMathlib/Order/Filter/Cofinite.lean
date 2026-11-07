/-
Copyright 2025 The Formal Conjectures Authors.

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

open Set

namespace Filter

/--
@isnad1 id=hasbasis.0h1v.s5.64cee734d485 from=translated src=- shape=624c7904 vocab=740448c2
-/
lemma cofinite_hasBasis_Ioi {α : Type*} [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] :
    cofinite.HasBasis (fun (_ : α) ↦ True) (Set.Ioi ·) := by
  constructor
  intro A
  simp only [mem_cofinite, true_and]
  constructor
  · intro hA
    obtain ⟨a, ha⟩ := Set.Finite.bddAbove hA
    use a
    rw [← Set.compl_subset_compl, compl_Ioi]
    exact ha
  · rintro ⟨a, ha⟩
    rw [← Set.compl_subset_compl, compl_Ioi] at ha
    apply Set.Finite.subset _ ha
    exact finite_Iic a

/--
Note(csonne): According to a TODO in `Mathlib.Order.Interval.Finset.Defs`, Assuming `SuccOrder α`
should not be necessary as an instance should follow from `[LocallyFiniteOrder α] [OrderBot α]`.
This has not been implemented in mathlib however.
@isnad1 id=hasbasis.0h1v.s6.1e439d95d7cd from=translated src=- shape=dfc4e78b vocab=c4ade76b
-/
lemma cofinite_hasBasis_Ici {α : Type*} [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α]
    [SuccOrder α] [NoMaxOrder α] : cofinite.HasBasis (fun (_ : α) ↦ True) (Set.Ici ·) := by
  constructor
  intro A
  simp only [mem_cofinite, true_and]
  constructor
  · intro hA
    obtain ⟨a, ha⟩ := Set.Finite.bddAbove hA
    use Order.succ a
    rw [← Set.compl_subset_compl, compl_Ici]
    exact Set.Subset.trans ha (Order.Iic_subset_Iio_succ a)
  · rintro ⟨a, ha⟩
    rw [← Set.compl_subset_compl, compl_Ici] at ha
    apply Set.Finite.subset _ ha
    exact finite_Iio a

/--
@isnad1 id=eq.0h1v.s6.ca09c2168acd from=translated src=- shape=e54dd848 vocab=072dc46f
-/
theorem cofinite_eq_atTop {α : Type*} [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α]
  [SuccOrder α] [NoMaxOrder α] :
    @cofinite α = atTop := by
  simp only [atTop_eq_generate_Ici, HasBasis.eq_generate cofinite_hasBasis_Ici, true_and]
  rfl

end Filter
