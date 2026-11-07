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

public import Tengoku.FormalConjectures.FormalConjecturesForMathlib.Order.Filter.atTopBot.Finset
public import Tengoku

@[expose] public section

open Filter

namespace GromovPolynomialGrowth

variable {G : Type*} [Group G]

/-- The `CayleyBall` is the ball of radius `n` in the Cayley graph of a group `G` with generating
set `S`.-/
def CayleyBall (S : Set G) (n : ℕ) : Set G :=
  {g : G | ∃ (l : List G), l.length ≤ n ∧ (∀ s ∈ l, s ∈ S ∨ s⁻¹ ∈ S) ∧ l.prod = g}

/--
@isnad1 id=eq.0h2v.s5.847247db21de from=translated src=- shape=c8862f55 vocab=7f167572
-/
theorem cayleyBall_zero (S : Set G) :
    CayleyBall S 0 = {1} := by
  simp [CayleyBall]

/--
@isnad1 id=finite.1h3v.s4.11a1f56441b0 from=translated src=- shape=fc8d1601 vocab=cc6e11fb
-/
lemma cayleyBall_finite {S : Set G} (hS : S.Finite) (n : ℕ) : (CayleyBall S n).Finite := by
  have hu : (S ∪ (·)⁻¹ '' S).Finite := hS.union (by simpa using hS.preimage inv_injective.injOn)
  have hf (m : ℕ) : {f : Fin m → G | ∀ i, f i ∈ S ∨ (f i)⁻¹ ∈ S}.Finite := by
    simpa using Set.Finite.pi' fun _ ↦ hu
  have : {l : List G | l.length ≤ n ∧ ∀ s ∈ l, s ∈ S ∨ s⁻¹ ∈ S}.Finite :=
    ((Set.finite_le_nat n).biUnion fun m _ ↦ (hf m).image List.ofFn).subset
      fun l ⟨hl, hlS⟩ ↦ Set.mem_biUnion hl ⟨fun i ↦ l[i], by aesop⟩
  exact (this.image List.prod).subset fun _ _ ↦ by aesop (add simp [CayleyBall])

/-- The `GrowthFunction` of a group `G` with respect to a set `S` counts the number of group
elements that can be reached by words of length at most `n` in `S`.-/
noncomputable def GrowthFunction (S : Set G) (n : ℕ) : ℕ :=
  (CayleyBall S n).ncard

/--
@isnad1 id=eq.0h2v.s4.c998078db5e6 from=translated src=- shape=4f51cd3b vocab=6a8e5826
-/
theorem growthFunction_zero (S : Set G) :
    GrowthFunction S 0 = 1 := by
  simp [GrowthFunction, CayleyBall]

/-- The identity is always in the Cayley ball.
@isnad1 id=mem.0h3v.s5.af4086f5e3cc from=translated src=- shape=ff473627 vocab=0994bd6e
-/
lemma one_mem_cayleyBall (S : Set G) (n : ℕ) :
    1 ∈ CayleyBall S n := by
  simp only [CayleyBall, Set.mem_ofPred_eq]
  use ∅
  simp

/-- The Cayley ball is monotonic in its radius.
@isnad1 id=le.1h4v.s5.ac66a56aed60 from=translated src=- shape=947265ab vocab=d0999cce
-/
lemma cayleyBall_monotone (S : Set G) {m n : ℕ} (h : m ≤ n) :
    CayleyBall S m ⊆ CayleyBall S n := by
  simp only [CayleyBall, Set.ofPred_subset_ofPred, forall_exists_index, and_imp]
  exact fun g l lLength LSubS lProdG ↦ ⟨l, by linarith, LSubS, lProdG⟩

/-- Closure property: if `g ∈ CayleyBall S m` and `h ∈ CayleyBall S n`, then
`g * h ∈ CayleyBall S (m + n)`.
@isnad1 id=mem.2h6v.s6.c41eb4465c55 from=translated src=- shape=61fb17b8 vocab=fede563e
-/
lemma cayleyBall_mul (S : Set G) {g h : G} {m n : ℕ}
    (hg : g ∈ CayleyBall S m) (hh : h ∈ CayleyBall S n) :
    g * h ∈ CayleyBall S (m + n) := by
  simp only [CayleyBall, Set.mem_ofPred_eq] at hg hh ⊢
  obtain ⟨lg, lgLength, lgSubS, lgProd⟩ := hg
  obtain ⟨lh, lhLength, lhSubS, lhProd⟩ := hh
  refine ⟨lg ++ lh, ?_, ?_, by simp [lhProd, lgProd]⟩
  · simp only [List.length_append]
    linarith
  · intro s sIn
    simp only [List.mem_append] at sIn
    cases sIn with
    | inl h => simp [lgSubS s h]
    | inr h => simp [lhSubS s h]

/-- If `g ∈ CayleyBall S n`, then `g⁻¹ ∈ CayleyBall S n`.
@isnad1 id=mem.1h4v.s5.e34b53b3b23e from=translated src=- shape=faf740d1 vocab=5fec22b2
-/
lemma cayleyBall_inv (S : Set G) {g : G} {n : ℕ}
    (hg : g ∈ CayleyBall S n) :
    g⁻¹ ∈ CayleyBall S n := by
  simp only [CayleyBall, Set.mem_ofPred_eq] at hg ⊢
  obtain ⟨lg, lgLength, lgSubS, lgProd⟩ := hg
  refine ⟨lg.reverse.map (·⁻¹), by simp [lgLength], ?_,
    by simp [List.prod_inv_reverse, lgProd.symm]⟩
  intro s sIn
  simp only [List.map_reverse, List.mem_reverse, List.mem_map, inv_involutive,
    Function.Involutive.exists_mem_and_apply_eq_iff] at sIn
  have := lgSubS s⁻¹ sIn
  simp only [inv_inv] at this
  exact this.symm

/--
@isnad1 id=mem.1h3v.s5.082db49b7b97 from=translated src=- shape=9849d8ef vocab=0994bd6e
-/
lemma mem_cayleyBall_one_of_mem {S : Set G} {g : G} (hg : g ∈ S) : g ∈ CayleyBall S 1 :=
  ⟨[g], by simp_all⟩

/--
@isnad1 id=ex.1h3v.s5.80d12fa8e777 from=translated src=- shape=8c34bee8 vocab=849c16c2
-/
lemma exists_cayleyBall_mem_of_closure_eq_top {S : Set G} (h : Subgroup.closure S = ⊤) (g : G) :
    ∃ n, g ∈ CayleyBall S n := by
  induction h ▸ Subgroup.mem_top g using Subgroup.closure_induction with
  | mem => exact ⟨1, mem_cayleyBall_one_of_mem ‹_›⟩
  | one => exact ⟨0, one_mem_cayleyBall ..⟩
  | mul _ _ _ _ hg₁ hg₂ =>
    obtain ⟨n₁, hn₁⟩ := hg₁
    obtain ⟨n₂, hn₂⟩ := hg₂
    exact ⟨n₁ + n₂, cayleyBall_mul S hn₁ hn₂⟩
  | inv _ _ hg =>
    obtain ⟨n, hn⟩ := hg
    exact ⟨n, cayleyBall_inv S hn⟩

/-- In an infinite group, the growth function with respect to a finite generating set is
unbounded.
@isnad1 id=tendsto.2h2v.s5.3919aec0fde1 from=translated src=- shape=e09ac5bc vocab=40ef4856
-/
theorem tendsto_atTop_growthFunction_of_infinite [Infinite G] {S : Set G} (hS : S.Finite)
    (h : Subgroup.closure S = ⊤) : atTop.Tendsto (GrowthFunction S) atTop := by
  delta GrowthFunction
  have (n : ℕ) : Fintype (CayleyBall S n) := (cayleyBall_finite hS n).fintype
  apply ((Finset.tendsto_card_atTop).comp (f := fun n ↦ (CayleyBall S n).toFinset) ?_).congr
    (by simp)
  apply tendsto_atTop_atTop_of_monotone fun _ _ ↦ by simpa using cayleyBall_monotone S
  intro A
  obtain rfl | hA := A.eq_empty_or_nonempty
  · aesop
  · choose n hn using fun (a : A) ↦ exists_cayleyBall_mem_of_closure_eq_top h a
    let N : ℕ := (Set.range n).toFinset.max' (by simp [hA])
    refine ⟨N, fun a ha ↦ ?_⟩
    simpa using cayleyBall_monotone S (Finset.le_max' _ _ (by aesop)) (hn ⟨a, ha⟩)

/-- A group has polynomial growth if there exists a finite generating set whose growth function is
bounded above by a polynomial.-/
def HasPolynomialGrowth (G : Type*) [Group G] : Prop :=
  ∃ (S : Set G), Set.Finite S ∧ Subgroup.closure S = ⊤ ∧
    ∃ (C : ℝ) (d : ℕ), C > 0 ∧
    ∀ n > 0, (GrowthFunction S n : ℝ) ≤ C * (n : ℝ) ^ d

/-- A group has superpolynomial growth if there exists a finite generating set whose growth
function eventually dominates every polynomial in the growth-function preorder, up to linearly
rescaling the radius.-/
def HasSuperPolynomialGrowth (G : Type*) [Group G] : Prop :=
  ∃ (S : Set G), Set.Finite S ∧ Subgroup.closure S = ⊤ ∧
    ∀ d : ℕ, ∃ C : ℕ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ d ≤ (GrowthFunction S (C * n) : ℝ)

end GromovPolynomialGrowth
