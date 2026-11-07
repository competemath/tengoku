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

/- A bijection between discrete topological spaces induces a homeomorphism. -/
def Homeomorph.OfDiscrete {X  Y : Type*} [TopologicalSpace X] [DiscreteTopology X]
    [TopologicalSpace Y] [DiscreteTopology Y] (f : X ≃ Y) : X ≃ₜ Y where
  toEquiv := f
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- A bijection between discrete topological spaces is a homeomorphism.
@isnad1 id=ishomeom.0h3v.s5.486cfa5717fa from=translated src=- shape=21e4185b vocab=51a0fe70
-/
theorem IsHomeomorph.equiv_of_discreteTopology {X  Y : Type*} [TopologicalSpace X]
    [DiscreteTopology X] [TopologicalSpace Y] [DiscreteTopology Y] (f : X ≃ Y) : IsHomeomorph f :=
  (Homeomorph.OfDiscrete f).isHomeomorph
