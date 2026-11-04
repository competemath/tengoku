/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Tengoku.T3ModelCompanion.T3.GroupTheory.Free.NormalForm
public import Tengoku.Seed.Data.Finsupp.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite generating supports in free exponent-three groups

Every element comes from the free group on a finite subset of the generating set, and that
finite free group embeds in the original group. Restriction of the coordinate model recovers
the coordinates before such an inclusion. These facts allow finite-rank normal-form results
to be applied without assuming that the whole generating set is finite.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.
-/

@[expose] public section

namespace T3

namespace Free

variable {I J : Type*}

/-- An injective map of generators induces an injective homomorphism, including the empty case.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.
@isnad1 id=injectiv.1h3v.s7.e4768724e938 from=translated src=- shape=f8e28d5a vocab=f73778cd
-/
theorem map_injective {f : I → J} (hf : Function.Injective f) :
    Function.Injective (map f) := by
  classical
  let r : Free J →* Free I := lift pow_three (Function.extend f of fun _ => 1)
  have hr : r.comp (map f) = MonoidHom.id (Free I) := by
    apply hom_ext
    intro i
    simp [r, hf.extend_apply]
  exact (show Function.LeftInverse r (map f) from DFunLike.congr_fun hr).injective

/-- Every element uses only finitely many of the free generators.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.
@isnad1 id=ex.0h2v.s9.f0cfe6ba39f9 from=translated src=- shape=4cbecfbb vocab=8a580a0f
-/
theorem exists_finset_map (g : Free I) :
    ∃ s : Finset I, ∃ h : Free s, map (Subtype.val : s → I) h = g := by
  classical
  have hg : g ∈ Subgroup.closure (Set.range (of : I → Free I)) := by
    rw [closure_range_of]
    exact Subgroup.mem_top _
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨{i}, of ⟨i, Finset.mem_singleton_self i⟩, map_of _ _⟩
  | one => exact ⟨∅, 1, map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, a, rfl⟩ := hx
    obtain ⟨t, b, rfl⟩ := hy
    let fs : s → (s ∪ t : Finset I) := fun i => ⟨i, Finset.mem_union_left t i.property⟩
    let ft : t → (s ∪ t : Finset I) := fun i => ⟨i, Finset.mem_union_right s i.property⟩
    refine ⟨s ∪ t, map fs a * map ft b, ?_⟩
    rw [map_mul]
    have hs := DFunLike.congr_fun (map_comp fs (Subtype.val : (s ∪ t : Finset I) → I)) a
    have ht := DFunLike.congr_fun (map_comp ft (Subtype.val : (s ∪ t : Finset I) → I)) b
    exact congrArg₂ (· * ·) hs ht
  | inv x _ hx =>
    obtain ⟨s, a, rfl⟩ := hx
    exact ⟨s, a⁻¹, map_inv _ _⟩

end Free

namespace LvdW

variable {I J : Type*}

/-- Restrict all coordinate functions along a map of index sets.
The multiplication law is local in its indices, so restriction is a homomorphism.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.-/
def restrict (f : I → J) : LvdW J →* LvdW I where
  toFun x := ⟨fun i => x.gen (f i), fun i j => x.pair (f i) (f j),
    fun i j k => x.triple (f i) (f j) (f k)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Restriction along an injection recovers the corresponding model generator.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.
@isnad1 id=eq.1h4v.s6.0cb532e23933 from=translated src=- shape=b982d390 vocab=e1c2bd25
-/
@[simp]
theorem restrict_of [DecidableEq I] [DecidableEq J] {f : I → J}
    (hf : Function.Injective f) (i : I) : restrict f (of (f i)) = of i := by
  ext j k l <;> simp [restrict, of_gen, hf.eq_iff]

end LvdW

namespace Free

variable {I J : Type*} [DecidableEq I] [DecidableEq J]

/-- Restriction of the coordinate comparison recovers the comparison before an inclusion.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.
@isnad1 id=eq.1h4v.s8.cdbd85cee48c from=translated src=- shape=c4ca65c5 vocab=4578f07d
-/
theorem restrict_toLvdW_map {f : I → J} (hf : Function.Injective f) (g : Free I) :
    LvdW.restrict f (toLvdW (map f g)) = toLvdW g := by
  have h : (LvdW.restrict f).comp ((toLvdW (I := J)).comp (map f)) = toLvdW := by
    apply hom_ext
    intro i
    simp [hf]
  exact DFunLike.congr_fun h g

end Free

namespace Free

variable {I : Type*} [LinearOrder I]

/-- Vanishing collected coordinates imply that an element is one, with no rank restriction.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.-/
theorem eq_one_of_toLvdW_coords {g : Free I}
    (hgen : ∀ i, (toLvdW g).gen i = 0)
    (hpair : ∀ p : IncreasingPair I, (toLvdW g).pair p.first p.second = 0)
    (htriple : ∀ t : IncreasingTriple I, (toLvdW g).triple t.first t.second t.third = 0) :
    g = 1 := by
  obtain ⟨s, h, hh⟩ := exists_finset_map g
  let : DecidableEq s := (inferInstance : LinearOrder s).toDecidableEq
  have hr := restrict_toLvdW_map (f := (Subtype.val : s → I)) Subtype.val_injective h
  rw [hh] at hr
  have he : h = 1 := by
    apply eq_one_of_toLvdW_coords_of_finite
    · intro i
      rw [← hr]
      exact hgen i
    · intro p
      rw [← hr]
      exact hpair ⟨p.first, p.second, p.first_lt_second⟩
    · intro t
      rw [← hr]
      exact htriple ⟨t.first, t.second, t.third, t.first_lt_second, t.second_lt_third⟩
  rw [he, map_one] at hh
  exact hh.symm

/-- The coordinate comparison is injective for an arbitrary ordered generating set.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.
@isnad1 id=injectiv.0h1v.s6.a20379a6daae from=translated src=- shape=c5bed54c vocab=d96070bc
-/
theorem toLvdW_injective : Function.Injective (toLvdW (I := I)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_bot]
  refine eq_one_of_toLvdW_coords (fun i => ?_) (fun p => ?_) (fun t => ?_) <;>
    simp [hg]

/-- Increasing coordinates distinguish elements in every rank.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.
@isnad1 id=injectiv.0h1v.s7.f6c6311a72f1 from=translated src=- shape=fd31ffcd vocab=63504da3
-/
theorem collect_toLvdW_injective :
    Function.Injective fun g : Free I => LvdW.collect (toLvdW g) := by
  intro g h hgh
  have hgen : (toLvdW g).gen = (toLvdW h).gen := congrArg Prod.fst hgh
  have hpair : ∀ p : IncreasingPair I,
      (toLvdW g).pair p.first p.second = (toLvdW h).pair p.first p.second :=
    fun p => congrFun (congrArg (fun z => z.2.1) hgh) p
  have htriple : ∀ t : IncreasingTriple I,
      (toLvdW g).triple t.first t.second t.third =
        (toLvdW h).triple t.first t.second t.third :=
    fun t => congrFun (congrArg (fun z => z.2.2) hgh) t
  have key : h⁻¹ * g = 1 := by
    refine eq_one_of_toLvdW_coords (fun i => ?_) (fun p => ?_) (fun t => ?_)
    · rw [map_mul, map_inv]
      exact LvdW.gen_inv_mul_eq_zero hgen i
    · rw [map_mul, map_inv]
      exact LvdW.pair_inv_mul_eq_zero hgen (hpair p)
    · rw [map_mul, map_inv]
      exact LvdW.triple_inv_mul_eq_zero hgen (htriple t)
  exact (inv_mul_eq_one.mp key).symm

end Free

namespace LvdW

variable {I : Type*}

/-- Coordinate systems whose nonzero coordinates use only indices in the specified set.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.-/
def supportedOn (s : Set I) : Subgroup (LvdW I) where
  carrier := {x | (∀ i, i ∉ s → x.gen i = 0) ∧
    (∀ i j, i ∉ s ∨ j ∉ s → x.pair i j = 0) ∧
    (∀ i j k, i ∉ s ∨ j ∉ s ∨ k ∉ s → x.triple i j k = 0)}
  one_mem' := by simp
  mul_mem' := by
    rintro x y ⟨hx₁, hx₂, hx₃⟩ ⟨hy₁, hy₂, hy₃⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp [hx₁ i hi, hy₁ i hi]
    · intro i j hij
      rcases hij with hi | hj <;> simp_all
    · intro i j k hijk
      rcases hijk with hi | hj | hk <;> simp_all
  inv_mem' := by
    let : AddCommGroup (ZMod 3) := (ZMod.commRing 3).toAddCommGroup
    rintro x ⟨hx₁, hx₂, hx₃⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      simp [hx₁ i hi]
    · intro i j hij
      rcases hij with hi | hj <;> simp_all
    · intro i j k hijk
      rcases hijk with hi | hj | hk <;> simp_all

/-- A model generator is supported on every set containing its index.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.
@isnad1 id=mem.1h3v.s5.112f218f4695 from=translated src=- shape=f15c7b77 vocab=0d521299
-/
theorem of_mem_supportedOn [DecidableEq I] {s : Set I} {i : I} (hi : i ∈ s) :
    of i ∈ supportedOn s := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    simp only [of_gen]
    split_ifs with hij
    · exact False.elim (hj (hij ▸ hi))
    · rfl
  · intros
    rfl
  · intros
    rfl

end LvdW

namespace Free

variable {I : Type*} [LinearOrder I]

/-- An element on finitely many generators has no coordinates involving any other index.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.
@isnad1 id=mem.0h3v.s9.e0a4634d67ed from=translated src=- shape=67db54f9 vocab=e4eb5ae6
-/
theorem toLvdW_map_mem_supportedOn (s : Finset I) (g : Free s) :
    toLvdW (map (Subtype.val : s → I) g) ∈ LvdW.supportedOn s := by
  have hg : g ∈ Subgroup.closure (Set.range (of : s → Free s)) := by
    rw [closure_range_of]
    exact Subgroup.mem_top _
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [map_of, toLvdW_of]
    exact LvdW.of_mem_supportedOn i.property
  | one => simp
  | mul x y _ _ hx hy => simpa using (LvdW.supportedOn (s : Set I)).mul_mem hx hy
  | inv x _ hx => simpa using (LvdW.supportedOn (s : Set I)).inv_mem hx

/-- The coordinates of every free-group element involve only a finite set of indices.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.
@isnad1 id=ex.0h2v.s7.672d2ab8e9de from=translated src=- shape=330be1c9 vocab=4eb0e26e
-/
theorem exists_finset_supportedOn (g : Free I) :
    ∃ s : Finset I, toLvdW g ∈ LvdW.supportedOn s := by
  obtain ⟨s, h, rfl⟩ := exists_finset_map g
  exact ⟨s, toLvdW_map_mem_supportedOn s h⟩

/-- Degree-one coordinates have finite support in every rank.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.
@isnad1 id=finite.0h2v.s7.6d972f6e34aa from=translated src=- shape=fd2fc0d0 vocab=ae647f0c
-/
theorem finite_support_gen (g : Free I) : (Function.support (toLvdW g).gen).Finite := by
  obtain ⟨s, hs⟩ := exists_finset_supportedOn g
  apply s.finite_toSet.subset
  intro i hi
  by_contra hn
  exact hi (hs.1 i hn)

/-- Increasing degree-two coordinates have finite support in every rank.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.
@isnad1 id=finite.0h2v.s7.c160dfff9275 from=translated src=- shape=88db5ac1 vocab=04c2a5f9
-/
theorem finite_support_pair (g : Free I) :
    (Function.support fun p : IncreasingPair I => (toLvdW g).pair p.first p.second).Finite := by
  obtain ⟨s, hs⟩ := exists_finset_supportedOn g
  apply Set.Finite.of_injOn (f := fun p : IncreasingPair I => (p.first, p.second))
    (t := (s : Set I) ×ˢ (s : Set I)) ?_ ?_ (s.finite_toSet.prod s.finite_toSet)
  · intro p hp
    constructor
    · by_contra hn
      exact hp (hs.2.1 _ _ (Or.inl hn))
    · by_contra hn
      exact hp (hs.2.1 _ _ (Or.inr hn))
  · intro p _ q _ hpq
    exact IncreasingPair.ext (congrArg Prod.fst hpq) (congrArg Prod.snd hpq)

/-- Increasing degree-three coordinates have finite support in every rank.

Paper-ID: preliminaries.infinite_normal_form
TeX: T3_modelcompanion_v9.tex, `remark:infinite dim`, v9 Remark 2.28.
@isnad1 id=finite.0h2v.s8.4aaebf4ca2e4 from=translated src=- shape=51e6cbf2 vocab=29caac6b
-/
theorem finite_support_triple (g : Free I) :
    (Function.support fun t : IncreasingTriple I =>
      (toLvdW g).triple t.first t.second t.third).Finite := by
  obtain ⟨s, hs⟩ := exists_finset_supportedOn g
  apply Set.Finite.of_injOn (f := fun t : IncreasingTriple I => (t.first, t.second, t.third))
    (t := (s : Set I) ×ˢ (s : Set I) ×ˢ (s : Set I)) ?_ ?_
    (s.finite_toSet.prod (s.finite_toSet.prod s.finite_toSet))
  · intro t ht
    refine ⟨?_, ?_, ?_⟩
    · by_contra hn
      exact ht (hs.2.2 _ _ _ (Or.inl hn))
    · by_contra hn
      exact ht (hs.2.2 _ _ _ (Or.inr (Or.inl hn)))
    · by_contra hn
      exact ht (hs.2.2 _ _ _ (Or.inr (Or.inr hn)))
  · intro p _ q _ hpq
    exact IncreasingTriple.ext (congrArg Prod.fst hpq)
      (congrArg (fun z => z.2.1) hpq) (congrArg (fun z => z.2.2) hpq)

end Free

end T3
