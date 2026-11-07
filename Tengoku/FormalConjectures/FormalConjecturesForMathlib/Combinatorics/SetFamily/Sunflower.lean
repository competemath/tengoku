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

/-!
# Sunflowers

This file defines sunflowers of set families.
-/

variable {α : Type*}

/--
A sunflower `F` with kernel `S` is a collection of sets in which all possible distinct pairs of sets
share the same intersection `S`.-/
def IsSunflowerWithKernel (F : Set (Set α)) (S : Set α) : Prop :=
  F.Pairwise (fun A B => A ∩ B = S)

/--
@isnad1 id=issunflo.0h2v.s3.43c7f7ad9b8c from=translated src=- shape=3ccc6e1c vocab=5be6ba7c
-/
theorem isSunflowerWithKernel_empty (S : Set α) : IsSunflowerWithKernel {} S := by
  simp [IsSunflowerWithKernel]

/--
@isnad1 id=issunflo.0h3v.s4.00cdecae6338 from=translated src=- shape=fa8cb659 vocab=69cb5f1a
-/
theorem isSunflowerWithKernel_singleton (S : Set α) (A : Set α) :
    IsSunflowerWithKernel {A} S := by
  simp [IsSunflowerWithKernel]

/--
A sunflower `F` is a collection of sets in which all possible distinct pairs of sets share the
same intersection.-/
def IsSunflower (F : Set (Set α)) : Prop := ∃ S, IsSunflowerWithKernel F S

/--
@isnad1 id=issunflo.0h1v.s3.5fdca5869dbe from=translated src=- shape=d684173f vocab=182ed4e6
-/
theorem isSunflower_empty : IsSunflower (∅ : Set (Set α)) := by
  simp [IsSunflower, isSunflowerWithKernel_empty]

/--
@isnad1 id=issunflo.0h2v.s4.d17d1f638b29 from=translated src=- shape=cb0303a9 vocab=2a094e06
-/
theorem isSunflower_singleton (A : Set α) : IsSunflower {A} := by
  simp [IsSunflower, isSunflowerWithKernel_singleton]
