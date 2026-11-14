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
namespace Tengoku.FormalConjectures end Tengoku.FormalConjectures open Tengoku.FormalConjectures 
open Filter

/-- Say a sequence is lacunary if there exists some $\lambda > 1$ such that
$a_{n+1}/a_n > \lambda$ for all sufficiently large $n$.-/
def _root_.Tengoku.FormalConjectures.IsLacunary (n : ℕ → ℕ) : Prop := ∃ c > (1 : ℝ), ∀ᶠ k in atTop, c * n k < n (k + 1)

/-- Every lacunary sequence is eventually strictly increasing.
@isnad1 id=eventual.1h1v.s5.b019ef1832ab from=translated src=- shape=0bec5403 vocab=c951eaf8
-/
lemma Tengoku.FormalConjectures.IsLacunary.eventually_lt {n : ℕ → ℕ} (hn : IsLacunary n) : ∀ᶠ k in atTop, n k < n (k + 1) := by
  obtain ⟨c, hc, h⟩ := hn
  obtain ⟨N, h⟩ := eventually_atTop.1 h
  refine eventually_atTop.2 ⟨N, fun b hb ↦ ?_⟩
  grw [hc] at h
  simpa using h _ hb

/-- The real-valued analogue of `IsLacunary`.-/
def _root_.Tengoku.FormalConjectures.IsLacunaryReal (a : ℕ → ℝ) : Prop :=
  ∃ c > (1 : ℝ), ∀ᶠ k in atTop, c * a k < a (k + 1)

/-- An ℕ-valued sequence is lacunary iff its real cast is lacunary as a real sequence.
@isnad1 id=iff.0h1v.s4.caca190c1655 from=translated src=- shape=9c7c88e3 vocab=f06c2ae5
-/
lemma _root_.Tengoku.FormalConjectures.isLacunary_iff_isLacunaryReal {n : ℕ → ℕ} :
    IsLacunary n ↔ IsLacunaryReal (fun k => (n k : ℝ)) := Iff.rfl

/-- A positive lacunary real-valued sequence is eventually strictly increasing.
@isnad1 id=eventual.2h1v.s5.6c3c70873057 from=translated src=- shape=70e6f06b vocab=2eb5bd3a
-/
lemma Tengoku.FormalConjectures.IsLacunaryReal.eventually_lt {a : ℕ → ℝ} (ha : IsLacunaryReal a)
    (hpos : ∀ᶠ k in atTop, 0 < a k) : ∀ᶠ k in atTop, a k < a (k + 1) := by
  obtain ⟨c, hc, hlac⟩ := ha
  filter_upwards [hlac, hpos] with k hk hp using by nlinarith

def _root_.Tengoku.FormalConjectures.IsSublacunary (m : ℕ → ℕ) : Prop :=
  Filter.Tendsto (fun n => (m (n + 1) : ℝ) / m n) Filter.atTop (nhds 1)
-- Tengoku: root names of this library moved to Tengoku.FormalConjectures so they do not collide with other libraries (generated)
