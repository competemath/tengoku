import Tengoku.TdaLib.TDA.Persistence.RankProjective
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite hook-sum deflations on finite posets

Choose a basis at each grade and in every structure-map kernel. Principal
upsets carry the first bases; finite-death hooks carry the second. Their
finite biproduct maps onto the module and lifts every dying element without
changing its death grade. Its actual kernel sequence is rank exact.

This proves enough rank projectives in the finite-poset part of BOOS,
arXiv:2208.00300v3, Theorem 2.7. The deflation is generally redundant and
is not asserted to be a minimal projective cover. Minimal resolutions with the
`2n−2` degree bound are constructed in
`TDA.Persistence.FiniteRankProjectiveResolutionDimension`
(`finitelyPresented_exists_minimalFiniteRankProjectiveResolution_with_bound`), using
the real-coordinate Kan transfer of `TDA.Persistence.FiniteRankProjectiveResolutionKan`;
the kernel comparisons and the pushout closure law are in `TDA.Persistence.RankExactKernel`
and `TDA.Persistence.RankExactPushout`. No `ExactCategory` instance is asserted.
-/

set_option autoImplicit false

universe u

namespace TDA.Persistence.FiniteHookDeflation

open CategoryTheory CategoryTheory.Limits
open scoped Classical

variable {k : Type u} [Field k] {P : Type} [PartialOrder P] [Fintype P]

private instance : HasFiniteBiproducts (PModule.{u,0,u} k P) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Comparable distinct birth and death grades.-/
abbrev StrictPair (P : Type) [PartialOrder P] := {ab : P × P // ab.1 < ab.2}

variable (M : PModule.{u,0,u} k P)

/-- Occurrences retain every kernel-basis and fiber-basis vector separately.-/
abbrev Index :=
  (Σ ab : StrictPair P,
    Fin (Module.finrank k (LinearMap.ker (structureMapLinear M ab.property.le)))) ⊕
  (Σ a : P, Fin (Module.finrank k (M.obj a)))

noncomputable instance indexFintype : Fintype (Index M) := by
  classical
  unfold Index
  infer_instance

/-- The number of hook occurrences counts all kernel and fiber basis vectors.
@isnad1 id=eq.0h3v.s11.a614978b6f01 from=translated src=- shape=be5c1d11 vocab=2ef3727a
-/
theorem card_index : Fintype.card (Index M) =
    (∑ ab : StrictPair P, Module.finrank k (LinearMap.ker (structureMapLinear M ab.property.le))) +
      ∑ a : P, Module.finrank k (M.obj a) := by
  classical
  simp [Index, Fintype.card_sigma]

/-- Each kernel vector contributes its finite-death hook; each fiber vector
contributes an infinite-death principal upset.-/
noncomputable def family : Index M → PModule.{u,0,u} k P
  | .inl t => Hook.module t.1.val.1 t.1.val.2
  | .inr t => HookInfinity.module t.1

/-- The existing categorical biproduct of the selected hook occurrences.-/
noncomputable def module : PModule.{u,0,u} k P := ⨁ family M

omit [Fintype P] in
/-- Every occurrence is rank projective by the proved hook lifting laws.
@isnad1 id=isrankpr.0h4v.s5.954cec957e79 from=translated src=- shape=0443680d vocab=6228c581
-/
theorem family_isRankProjective (t : Index M) : IsRankProjective (family M t) := by
  cases t with
  | inl t => exact Hook.isRankProjective t.1.property
  | inr t => exact HookInfinity.isRankProjective t.1

omit [Fintype P] in
/-- Each summand fiber is finite-dimensional.
@isnad1 id=finitedi.0h5v.s7.68d20c476869 from=translated src=- shape=bf6a3457 vocab=a2d22eaa
-/
@[instance] theorem family_finiteDimensional (t : Index M) (p : P) :
    FiniteDimensional k ((family M t).obj p) := by
  cases t with
  | inl t =>
    change FiniteDimensional k (SupportInterval.fiber (k := k) (Hook.support t.1.val.1 t.1.val.2) p)
    infer_instance
  | inr t =>
    change FiniteDimensional k (GradedFree.fiber (R := k) (HookInfinity.generators t.1) p)
    infer_instance

/-- The finite hook sum has finite-dimensional fibers.
@isnad1 id=finitedi.0h4v.s7.26b80150cf59 from=translated src=- shape=62dd5a1c vocab=acdd5c21
-/
@[instance] theorem finiteDimensional (p : P) : FiniteDimensional k ((module M).obj p) := by
  exact FiniteBiproduct.finiteDimensional (family M) p

/-- The entire finite hook sum is rank projective.
@isnad1 id=isrankpr.0h3v.s5.8c150dac3287 from=translated src=- shape=ec95b8a3 vocab=26fae37a
-/
theorem isRankProjective : IsRankProjective (module M) :=
  IsRankProjective.biproduct (family M) (family_isRankProjective M)

variable [∀ p, FiniteDimensional k (M.obj p)]

private noncomputable def kernelBasis (ab : StrictPair P) :=
  Module.finBasis k (LinearMap.ker (structureMapLinear M ab.property.le))

private noncomputable def fiberBasis (p : P) := Module.finBasis k (M.obj p)

/-- Each basis vector defines an actual natural transformation from its hook.-/
noncomputable def summandMap : ∀ t : Index M, family M t ⟶ M
  | .inl t => Hook.fromGenerator t.1.property M (kernelBasis M t.1 t.2).val
      (kernelBasis M t.1 t.2).property
  | .inr t => HookInfinity.fromBirth t.1 M (fiberBasis M t.1 t.2)

/-- The natural map assembled from the actual hook morphisms.-/
noncomputable def π : module M ⟶ M := biproduct.desc (summandMap M)

/-- The summand inclusion followed by the deflation is the chosen hook map.
@isnad1 id=eq.0h4v.s8.2a4d5368f39b from=translated src=- shape=b6413d65 vocab=10c069b1
-/
theorem ι_π (t : Index M) : biproduct.ι (family M) t ≫ π M = summandMap M t :=
  biproduct.ι_desc _ _

/-- The inclusion/deflation equation at any grade and vector.
@isnad1 id=eq.0h6v.s11.48bf3bda1a05 from=translated src=- shape=8a80b21f vocab=b87a3a94
-/
theorem π_ι_app (t : Index M) (p : P) (x : (family M t).obj p) :
    ((π M).app p).hom (((biproduct.ι (family M) t).app p).hom x) =
      ((summandMap M t).app p).hom x :=
  congrArg (fun f : family M t ⟶ M => (f.app p).hom x) (ι_π M t)

private theorem π_fiber_basis (a : P) (i : Fin (Module.finrank k (M.obj a))) :
    ((π M).app a).hom
      (((biproduct.ι (family M) (.inr ⟨a, i⟩)).app a).hom (HookInfinity.birth a)) =
      fiberBasis M a i :=
  (π_ι_app M (.inr ⟨a, i⟩) a (HookInfinity.birth a)).trans
    (HookInfinity.fromBirth_birth a M _)

private theorem π_kernel_basis (ab : StrictPair P)
    (i : Fin (Module.finrank k (LinearMap.ker (structureMapLinear M ab.property.le)))) :
    ((π M).app ab.val.1).hom
      (((biproduct.ι (family M) (.inl ⟨ab, i⟩)).app ab.val.1).hom
        (SupportInterval.one (Hook.support ab.val.1 ab.val.2) (Hook.birth_mem ab.property))) =
      (kernelBasis M ab i).val :=
  (π_ι_app M (.inl ⟨ab, i⟩) ab.val.1 _).trans
    (Hook.fromGenerator_birth ab.property M (kernelBasis M ab i).val
      (kernelBasis M ab i).property)

/-- Fiber-basis summands make the natural map surjective at every grade.
@isnad1 id=surjecti.0h4v.s9.30c9a9821e41 from=translated src=- shape=63775511 vocab=3822d300
-/
theorem surjective (a : P) : Function.Surjective ((π M).app a).hom := by
  intro n
  let B := fiberBasis M a
  let w : (module M).obj a := ∑ i, B.repr n i •
    ((biproduct.ι (family M) (.inr ⟨a, i⟩)).app a).hom (HookInfinity.birth a)
  refine ⟨w, ?_⟩
  calc
    _ = ∑ i, ((π M).app a).hom (B.repr n i •
        ((biproduct.ι (family M) (.inr ⟨a, i⟩)).app a).hom (HookInfinity.birth a)) :=
      map_sum ((π M).app a).hom _ _
    _ = ∑ i, B.repr n i • B i := by
      apply Finset.sum_congr rfl
      intro i _
      exact (map_smul ((π M).app a).hom (B.repr n i) _).trans
        (congrArg (fun x => B.repr n i • x) (π_fiber_basis M a i))
    _ = n := B.sum_repr n

/-- Every dying element lifts to an element dying at the same grade.
@isnad1 id=ex.2h6v.s11.e979a727b41b from=translated src=- shape=ac68223a vocab=36d17391
-/
theorem lift_kernel {a b : P} (hab : a ≤ b) (n : M.obj a)
    (hn : structureMapLinear M hab n = 0) :
    ∃ m : (module M).obj a, ((π M).app a).hom m = n ∧
      structureMapLinear (module M) hab m = 0 := by
  rcases lt_or_eq_of_le hab with hab' | he
  · let ab : StrictPair P := ⟨(a, b), hab'⟩
    let B := kernelBasis M ab
    let n' : LinearMap.ker (structureMapLinear M hab) := ⟨n, hn⟩
    let w : (module M).obj a := ∑ i, B.repr n' i •
      ((biproduct.ι (family M) (.inl ⟨ab, i⟩)).app a).hom
        (SupportInterval.one (Hook.support a b) (Hook.birth_mem hab'))
    refine ⟨w, ?_, ?_⟩
    · calc
        _ = ∑ i, ((π M).app a).hom (B.repr n' i •
            ((biproduct.ι (family M) (.inl ⟨ab, i⟩)).app a).hom
              (SupportInterval.one (Hook.support a b) (Hook.birth_mem hab'))) :=
          map_sum ((π M).app a).hom _ _
        _ = ∑ i, B.repr n' i • (B i).val := by
          apply Finset.sum_congr rfl
          intro i _
          exact (map_smul ((π M).app a).hom (B.repr n' i) _).trans
            (congrArg (fun x => B.repr n' i • x) (π_kernel_basis M ab i))
        _ = n := by
          simpa only [Submodule.coe_sum, Submodule.coe_smul] using
            congrArg Subtype.val (B.sum_repr n')
    · calc
        _ = ∑ i, structureMapLinear (module M) hab (B.repr n' i •
            ((biproduct.ι (family M) (.inl ⟨ab, i⟩)).app a).hom
              (SupportInterval.one (Hook.support a b) (Hook.birth_mem hab'))) :=
          map_sum (structureMapLinear (module M) hab) _ _
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          exact (LinearMap.ker (structureMapLinear (module M) hab)).smul_mem (B.repr n' i)
            (Hook.generator_dies hab' (biproduct.ι (family M) (.inl ⟨ab, i⟩)))
  · subst b
    have hn0 : n = 0 := by simpa using hn
    subst n
    exact ⟨0, by simp, by simp⟩

/-- The actual categorical kernel sequence of the finite hook-sum map is rank exact.
@isnad1 id=isrankex.0h3v.s8.277431bed2ad from=translated src=- shape=8b312460 vocab=3373df27
-/
theorem rankExact : IsRankExact (kernel.ι (π M)) (π M) := by
  exact RankKernel.rankExact (π M) (surjective M) (lift_kernel M)

/-- The kernel term of the rank-exact deflation has finite-dimensional fibers.
@isnad1 id=finitedi.0h4v.s8.a0cad5e58d28 from=translated src=- shape=9bca3101 vocab=6d071589
-/
theorem kernel_finiteDimensional (p : P) :
    FiniteDimensional k ((kernel (π M)).obj p) := by
  exact RankKernel.finiteDimensional (π M) p

/-- A rank-projective finite-poset module is a retract of this finite hook sum.
@isnad1 id=ex.1h3v.s8.208a18a1e420 from=translated src=- shape=5fcbb775 vocab=f5f0b2d3
-/
theorem exists_retract (hM : IsRankProjective M) :
    ∃ s : M ⟶ module M, s ≫ π M = 𝟙 M :=
  hM _ _ _ _ _ (rankExact M) (𝟙 M)

/-- Rank projectivity is equivalent to splitting the constructed deflation.
The finite-poset hook-sum classification of these retracts is proved in
`FiniteRankProjectiveClassification`.
@isnad1 id=iff.0h3v.s8.cc3050a3cc7e from=translated src=- shape=04551c63 vocab=f5f0b2d3
-/
theorem isRankProjective_iff_retract :
    IsRankProjective M ↔ ∃ s : M ⟶ module M, s ≫ π M = 𝟙 M := by
  constructor
  · exact exists_retract M
  · rintro ⟨s, hs⟩
    exact (isRankProjective M).of_retract s (π M) hs

end TDA.Persistence.FiniteHookDeflation
