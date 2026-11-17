import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Algebra.FullPolarization
import Tengoku.Seed.Data.Fintype.Perm
import Tengoku.Seed.Data.Fintype.EquivFin
import Tengoku.Seed.LinearAlgebra.Quotient.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Grouping the expansion of a diagonal by word orbits

The orbit of a word `a : Fin d → J` is the set of its distinct rearrangements. We choose one
representative per orbit and give it the sum of `M` over the orbit as coefficient; other words
get coefficient zero. Expanding `M (fun _ => ∑ j ∈ s, x j • b j)` in these coefficients needs
no factorial. Over an infinite field, every coefficient lies in any submodule containing the
diagonal of `M`. The coefficient lifts of Theorem 4.5 on c₀ and ℓ¹ use this grouping.
-/

noncomputable section

open scoped BigOperators Classical

namespace FiniteWord

section

variable {J : Type*} {d : ℕ}

/-- The finite set of distinct rearrangements of a word.-/
def wordOrbit (a : Fin d → J) : Finset (Fin d → J) := by
  classical
  exact Finset.univ.image (fun σ : Equiv.Perm (Fin d) => a ∘ σ)

/--
@isnad1 id=iff.0h4v.s6.cf5ffdd4b8f3 from=translated src=- shape=23eee32f vocab=04201253
-/
theorem mem_wordOrbit_iff {a u : Fin d → J} :
    u ∈ wordOrbit a ↔ ∃ σ : Equiv.Perm (Fin d), a ∘ σ = u := by
  classical
  simp [wordOrbit]

/--
@isnad1 id=mem.0h3v.s5.f8252d9b7b78 from=translated src=- shape=88453919 vocab=004148c4
-/
@[simp]
theorem mem_wordOrbit_self (a : Fin d → J) : a ∈ wordOrbit a := by
  exact mem_wordOrbit_iff.mpr ⟨Equiv.refl _, rfl⟩

/--
@isnad1 id=mem.1h4v.s6.618fe02664ac from=translated src=- shape=33b46327 vocab=004148c4
-/
theorem mem_wordOrbit_symm {a u : Fin d → J} (h : u ∈ wordOrbit a) :
    a ∈ wordOrbit u := by
  obtain ⟨σ, rfl⟩ := mem_wordOrbit_iff.mp h
  apply mem_wordOrbit_iff.mpr
  refine ⟨σ.symm, ?_⟩
  funext i
  simp

/--
@isnad1 id=mem.2h5v.s6.e6855a7c9d9a from=translated src=- shape=49c486e8 vocab=004148c4
-/
theorem mem_wordOrbit_trans {a u v : Fin d → J}
    (hu : u ∈ wordOrbit a) (hv : v ∈ wordOrbit u) : v ∈ wordOrbit a := by
  obtain ⟨σ, rfl⟩ := mem_wordOrbit_iff.mp hu
  obtain ⟨τ, rfl⟩ := mem_wordOrbit_iff.mp hv
  exact mem_wordOrbit_iff.mpr ⟨τ.trans σ, rfl⟩

/--
@isnad1 id=eq.1h4v.s5.4f04a8e9639f from=translated src=- shape=fa0ef6a6 vocab=004148c4
-/
theorem wordOrbit_eq_of_mem {a u : Fin d → J} (h : u ∈ wordOrbit a) :
    wordOrbit u = wordOrbit a := by
  ext v
  exact ⟨mem_wordOrbit_trans h, mem_wordOrbit_trans (mem_wordOrbit_symm h)⟩

/--
@isnad1 id=nonempty.0h3v.s4.2053f58b6539 from=translated src=- shape=d4400b87 vocab=77bdee12
-/
theorem wordOrbit_nonempty (a : Fin d → J) : (wordOrbit a).Nonempty :=
  ⟨a, mem_wordOrbit_self a⟩

/-- A representative of the orbit of `a`, depending only on the orbit.-/
def wordRepresentative (a : Fin d → J) : Fin d → J :=
  (wordOrbit_nonempty a).choose

/--
@isnad1 id=mem.0h3v.s5.62823a4845f3 from=translated src=- shape=e4f5c77b vocab=ac93ddaa
-/
theorem wordRepresentative_mem (a : Fin d → J) :
    wordRepresentative a ∈ wordOrbit a :=
  (wordOrbit_nonempty a).choose_spec

/--
@isnad1 id=eq.1h4v.s5.8ba686e65dd2 from=translated src=- shape=9da1815b vocab=ac93ddaa
-/
theorem wordRepresentative_eq_of_mem {a u : Fin d → J} (h : u ∈ wordOrbit a) :
    wordRepresentative u = wordRepresentative a := by
  unfold wordRepresentative
  congr 1
  rw [wordOrbit_eq_of_mem h]

/--
@isnad1 id=eq.0h3v.s4.f2f9d3e1f1ad from=translated src=- shape=b71fd9f8 vocab=4b8af13b
-/
@[simp]
theorem wordRepresentative_idempotent (a : Fin d → J) :
    wordRepresentative (wordRepresentative a) = wordRepresentative a :=
  wordRepresentative_eq_of_mem (wordRepresentative_mem a)

/--
@isnad1 id=eq.0h3v.s4.af1108991eab from=translated src=- shape=7602bd37 vocab=2e6232ad
-/
@[simp]
theorem wordOrbit_representative (a : Fin d → J) :
    wordOrbit (wordRepresentative a) = wordOrbit a :=
  wordOrbit_eq_of_mem (wordRepresentative_mem a)

/--
@isnad1 id=le.0h3v.s4.51c6d7832bba from=translated src=- shape=41a37044 vocab=88e8e750
-/
theorem card_wordOrbit_le (a : Fin d → J) : (wordOrbit a).card ≤ d.factorial := by
  classical
  calc
    (wordOrbit a).card ≤ (Finset.univ : Finset (Equiv.Perm (Fin d))).card :=
      Finset.card_image_le
    _ = d.factorial := by simp [Fintype.card_perm]

/--
@isnad1 id=eq.1h6v.s6.fc5436220922 from=translated src=- shape=05420cec vocab=1620f491
-/
theorem prod_eq_of_mem_wordOrbit {R : Type*} [CommMonoid R]
    (x : J → R) {a u : Fin d → J} (h : u ∈ wordOrbit a) :
    (∏ i, x (u i)) = ∏ i, x (a i) := by
  obtain ⟨σ, rfl⟩ := mem_wordOrbit_iff.mp h
  exact Equiv.prod_comp σ (fun i => x (a i))

/--
@isnad1 id=mem.2h6v.s6.ca3b729673a6 from=translated src=- shape=0fcbf60f vocab=004148c4
-/
theorem forall_mem_of_mem_wordOrbit {s : Finset J} {a u : Fin d → J}
    (ha : ∀ i, a i ∈ s) (h : u ∈ wordOrbit a) : ∀ i, u i ∈ s := by
  obtain ⟨σ, rfl⟩ := mem_wordOrbit_iff.mp h
  exact fun i => ha (σ i)

/--
@isnad1 id=eq.0h4v.s5.39b28ffee53f from=translated src=- shape=93d24873 vocab=c7a66175
-/
@[simp]
theorem wordOrbit_comp_perm (a : Fin d → J) (σ : Equiv.Perm (Fin d)) :
    wordOrbit (a ∘ σ) = wordOrbit a :=
  wordOrbit_eq_of_mem (mem_wordOrbit_iff.mpr ⟨σ, rfl⟩)

/--
@isnad1 id=eq.0h4v.s5.c807fdc0b84d from=translated src=- shape=1ec6af31 vocab=fc4c7cf9
-/
@[simp]
theorem wordRepresentative_comp_perm (a : Fin d → J) (σ : Equiv.Perm (Fin d)) :
    wordRepresentative (a ∘ σ) = wordRepresentative a :=
  wordRepresentative_eq_of_mem (mem_wordOrbit_iff.mpr ⟨σ, rfl⟩)

/--
@isnad1 id=iff.0h4v.s5.26c9758ffdda from=translated src=- shape=f6886421 vocab=ac93ddaa
-/
theorem wordRepresentative_eq_iff_mem_wordOrbit {a u : Fin d → J} :
    wordRepresentative u = wordRepresentative a ↔ u ∈ wordOrbit a := by
  constructor
  · intro h
    have hu : u ∈ wordOrbit (wordRepresentative u) :=
      mem_wordOrbit_symm (wordRepresentative_mem u)
    rw [h, wordOrbit_representative] at hu
    exact hu
  · exact wordRepresentative_eq_of_mem

end

section

variable {J : Type*} {d : ℕ}

/-- The number of coordinates carrying a given label.-/
def wordMultiplicity (a : Fin d → J) (j : J) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => a i = j)).card

/--
@isnad1 id=eq.0h4v.s5.a0695c508968 from=translated src=- shape=4c88b207 vocab=618b5b2b
-/
@[simp]
theorem wordMultiplicity_comp_perm (a : Fin d → J) (σ : Equiv.Perm (Fin d)) :
    wordMultiplicity (a ∘ σ) = wordMultiplicity a := by
  classical
  funext j
  exact Finset.card_equiv σ (by simp)

/--
@isnad1 id=iff.0h4v.s6.38c84f70f540 from=translated src=- shape=6c0c318b vocab=618b5b2b
-/
theorem wordMultiplicity_eq_iff_exists_perm (u a : Fin d → J) :
    wordMultiplicity u = wordMultiplicity a ↔ ∃ σ : Equiv.Perm (Fin d), a ∘ σ = u := by
  classical
  constructor
  · intro h
    let e (j : J) : { i : Fin d // u i = j } ≃ { i : Fin d // a i = j } :=
      Fintype.equivOfCardEq (by simpa [Fintype.card_subtype, wordMultiplicity] using congrFun h j)
    exact ⟨Equiv.ofFiberEquiv e, funext (Equiv.ofFiberEquiv_map e)⟩
  · rintro ⟨σ, rfl⟩
    exact wordMultiplicity_comp_perm a σ

/--
@isnad1 id=eq.0h3v.s4.e4f29f03cdef from=translated src=- shape=9dc2fa94 vocab=f41469fb
-/
@[simp]
theorem selectionType_eq_wordMultiplicity [Fintype J] (a : Fin d → J) :
    Polarization.selectionType a = wordMultiplicity a := rfl

/-- Two words have the same multiplicities iff they lie in the same orbit.
@isnad1 id=iff.0h4v.s5.1e241af22817 from=translated src=- shape=f8332414 vocab=13f26444
-/
theorem wordMultiplicity_eq_iff_mem_wordOrbit (u a : Fin d → J) :
    wordMultiplicity u = wordMultiplicity a ↔ u ∈ wordOrbit a := by
  rw [wordMultiplicity_eq_iff_exists_perm, mem_wordOrbit_iff]

/-- For finite `J`, `selectionType` fibers are word orbits.
@isnad1 id=iff.0h4v.s5.776cd26f47dd from=translated src=- shape=5fea9053 vocab=2c99a66f
-/
theorem selectionType_eq_iff_mem_wordOrbit [Fintype J] (u a : Fin d → J) :
    Polarization.selectionType u = Polarization.selectionType a ↔ u ∈ wordOrbit a :=
  wordMultiplicity_eq_iff_mem_wordOrbit u a

/-- The orbit of `a` is the set of words with the same `selectionType`.
@isnad1 id=eq.0h3v.s6.9d7528263f14 from=translated src=- shape=fb51cdb7 vocab=e54251ce
-/
theorem wordOrbit_eq_selectionType_fiber [Fintype J] (a : Fin d → J) :
    wordOrbit a = Finset.univ.filter
      (fun u => Polarization.selectionType u = Polarization.selectionType a) := by
  classical
  ext u
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    (selectionType_eq_iff_mem_wordOrbit u a).symm

end

section

variable {J J' : Type*} {d : ℕ}

/-- Relabeling commutes with taking orbits.
@isnad1 id=eq.0h5v.s6.73170f714220 from=translated src=- shape=cd3d9a2c vocab=489d155a
-/
theorem wordOrbit_map (f : J → J') (a : Fin d → J) :
    (wordOrbit a).image (fun u => f ∘ u) = wordOrbit (f ∘ a) := by
  classical
  simp only [wordOrbit, Finset.image_image, Function.comp_assoc]
  rfl

section Algebra

variable {K E Z : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup Z] [Module K Z]

/-- The orbit sum is the grouped sum `sumOfType` at the multiplicities of `a`.
@isnad1 id=eq.0h8v.s7.6ca425f5d3d5 from=translated src=- shape=36b0a24e vocab=1b2401e9
-/
theorem sum_wordOrbit_eq_sumOfType [Fintype J]
    (M : MultilinearMap K (fun _ : Fin d => E) Z) (b : J → E) (a : Fin d → J) :
    (∑ u ∈ wordOrbit a, M (fun i => b (u i))) =
      M.sumOfType b (Polarization.selectionType a) := by
  classical
  rw [wordOrbit_eq_selectionType_fiber]
  rfl

end Algebra

end

section

variable {K J E Z : Type*} {d : ℕ}
  [Field K] [AddCommGroup E] [Module K E] [AddCommGroup Z] [Module K Z]

/-- The orbit sum at the chosen representative, and zero at other words.-/
def groupedCoefficient (M : MultilinearMap K (fun _ : Fin d => E) Z)
    (b : J → E) (a : Fin d → J) : Z := by
  classical
  exact if wordRepresentative a = a then
    ∑ u ∈ wordOrbit a, M (fun i => b (u i)) else 0

/--
@isnad1 id=eq.1h8v.s7.9909b1cf5de8 from=translated src=- shape=5c89db4f vocab=ec01ec47
-/
@[simp]
theorem groupedCoefficient_of_representative
    (M : MultilinearMap K (fun _ : Fin d => E) Z) (b : J → E)
    {a : Fin d → J} (ha : wordRepresentative a = a) :
    groupedCoefficient M b a = ∑ u ∈ wordOrbit a, M (fun i => b (u i)) := by
  classical
  simp [groupedCoefficient, ha]

/--
@isnad1 id=eq.1h8v.s7.27e5dd19f7d5 from=translated src=- shape=2cbdabed vocab=f7a74bdb
-/
@[simp]
theorem groupedCoefficient_of_not_representative
    (M : MultilinearMap K (fun _ : Fin d => E) Z) (b : J → E)
    {a : Fin d → J} (ha : wordRepresentative a ≠ a) :
    groupedCoefficient M b a = 0 := by
  classical
  simp [groupedCoefficient, ha]

/-- At the representative, the grouped coefficient is the orbit sum.
@isnad1 id=eq.0h8v.s7.57f782475553 from=translated src=- shape=165ad227 vocab=ec01ec47
-/
@[simp]
theorem groupedCoefficient_representative
    (M : MultilinearMap K (fun _ : Fin d => E) Z) (b : J → E) (a : Fin d → J) :
    groupedCoefficient M b (wordRepresentative a) =
      ∑ u ∈ wordOrbit a, M (fun i => b (u i)) := by
  rw [groupedCoefficient_of_representative M b (wordRepresentative_idempotent a),
    wordOrbit_representative]

private theorem representative_fiber_of_fixed
    (S : Finset (Fin d → J))
    (hS : ∀ a ∈ S, ∀ u ∈ wordOrbit a, u ∈ S)
    {a : Fin d → J} (haS : a ∈ S) (ha : wordRepresentative a = a) :
    S.filter (fun u => wordRepresentative u = a) = wordOrbit a := by
  classical
  ext u
  simp only [Finset.mem_filter]
  constructor
  · intro hu
    exact mem_wordOrbit_symm (hu.2 ▸ wordRepresentative_mem u)
  · intro hu
    exact ⟨hS a haS u hu, (wordRepresentative_eq_of_mem hu).trans ha⟩

private theorem representative_fiber_of_not_fixed
    (S : Finset (Fin d → J)) {a : Fin d → J} (ha : wordRepresentative a ≠ a) :
    S.filter (fun u => wordRepresentative u = a) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  apply ha
  have hu' := (Finset.mem_filter.mp hu).2
  rw [← hu', wordRepresentative_idempotent]

private theorem sum_groupedCoefficient_of_orbit_closed
    (M : MultilinearMap K (fun _ : Fin d => E) Z) (b : J → E)
    (S : Finset (Fin d → J))
    (hS : ∀ a ∈ S, ∀ u ∈ wordOrbit a, u ∈ S) (x : J → K) :
    ∑ a ∈ S, (∏ i, x (a i)) • groupedCoefficient M b a =
      ∑ a ∈ S, (∏ i, x (a i)) • M (fun i => b (a i)) := by
  classical
  have hmaps : ∀ a ∈ S, wordRepresentative a ∈ S :=
    fun a ha => hS a ha _ (wordRepresentative_mem a)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun a => (∏ i, x (a i)) • M (fun i => b (a i)))]
  apply Finset.sum_congr rfl
  intro a haS
  by_cases ha : wordRepresentative a = a
  · rw [representative_fiber_of_fixed S hS haS ha,
      groupedCoefficient_of_representative M b ha, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [prod_eq_of_mem_wordOrbit x hu]
  · rw [representative_fiber_of_not_fixed S ha,
      groupedCoefficient_of_not_representative M b ha]
    simp

private theorem sum_piFinset_eq_sum_subtype
    {A : Type*} [AddCommMonoid A] (s : Finset J) (f : (Fin d → J) → A) :
    (∑ a ∈ Fintype.piFinset (fun _ : Fin d => s), f a) =
      ∑ a : Fin d → s, f (fun i => (a i : J)) := by
  classical
  symm
  refine Finset.sum_bij (fun a _ i => (a i : J)) ?_ ?_ ?_ ?_
  · intro a ha
    exact Fintype.mem_piFinset.mpr (fun i => (a i).property)
  · intro a ha a' ha' haa'
    funext i
    exact Subtype.ext (congrFun haa' i)
  · intro a ha
    exact ⟨fun i => ⟨a i, Fintype.mem_piFinset.mp ha i⟩, Finset.mem_univ _, rfl⟩
  · intro a ha
    rfl

/-- Expansion of the diagonal at a finite combination in terms of grouped coefficients.
@isnad1 id=eq.0h9v.s8.acc235f2f3cc from=translated src=- shape=ac15d814 vocab=9ebb68f4
-/
theorem finite_diagonal_grouping
    (M : MultilinearMap K (fun _ : Fin d => E) Z) (b : J → E)
    (s : Finset J) (x : J → K) :
    M (fun _ => ∑ j ∈ s, x j • b j) =
      ∑ a : Fin d → s,
        (∏ i, x (a i)) • groupedCoefficient M b (fun i => (a i : J)) := by
  classical
  rw [M.map_sum_finset (fun _ j => x j • b j) (fun _ => s)]
  have hS : ∀ a ∈ Fintype.piFinset (fun _ : Fin d => s),
      ∀ u ∈ wordOrbit a, u ∈ Fintype.piFinset (fun _ : Fin d => s) := by
    intro a ha u hu
    exact Fintype.mem_piFinset.mpr
      (forall_mem_of_mem_wordOrbit (Fintype.mem_piFinset.mp ha) hu)
  calc
    _ = ∑ a ∈ Fintype.piFinset (fun _ : Fin d => s),
        (∏ i, x (a i)) • M (fun i => b (a i)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact M.map_smul_univ (fun i => x (a i)) (fun i => b (a i))
    _ = ∑ a ∈ Fintype.piFinset (fun _ : Fin d => s),
        (∏ i, x (a i)) • groupedCoefficient M b a :=
      (sum_groupedCoefficient_of_orbit_closed M b _ hS x).symm
    _ = _ := sum_piFinset_eq_sum_subtype s _

end

section

variable {K J E Z : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup Z] [Module K Z] {d : ℕ}

end

end FiniteWord
