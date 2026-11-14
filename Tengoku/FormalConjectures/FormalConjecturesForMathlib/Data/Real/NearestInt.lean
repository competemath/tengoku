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
namespace Tengoku.FormalConjectures end Tengoku.FormalConjectures open Tengoku.FormalConjectures 
/-- The distance from a real number to the nearest integer.-/
noncomputable def _root_.Tengoku.FormalConjectures.distToNearestInt (x : ℝ) : ℝ := |x - round x|

/-- The distance to the nearest integer is nonnegative.
@isnad1 id=le.0h1v.s3.1975b5ecb613 from=translated src=- shape=8a62b088 vocab=6bc70d28
-/
@[simp]
theorem _root_.Tengoku.FormalConjectures.distToNearestInt_nonneg (x : ℝ) : 0 ≤ distToNearestInt x := abs_nonneg _
-- Tengoku: root names of this library moved to Tengoku.FormalConjectures so they do not collide with other libraries (generated)
