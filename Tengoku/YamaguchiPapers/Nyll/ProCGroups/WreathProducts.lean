/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.GroupTheory.SemidirectProduct
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ProC.Subgroups.Products
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ReidemeisterSchreier.RightQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pro C Groups / Wreath Products

This module formalizes permutational wreath products.
-/

open scoped Pointwise

namespace ProCGroups.WreathProducts

universe u v w

section RightCosets

variable {G : Type u} [Group G]

/-- Right multiplication on right cosets, expressed as a left action by
`g • [a] = [a * g⁻¹]`.-/
@[reducible]
def rightCosetMulAction (H : Subgroup G) :
    MulAction G (Quotient (QuotientGroup.rightRel H)) :=
  _root_.ReidemeisterSchreier.rightCosetMulAction H

/-- Acting on a represented right coset multiplies its representative by the inverse on the
right.
@isnad1 id=eq.0h4v.s6.cea865b32aca from=translated src=- shape=48daaf87 vocab=978d100c
-/
@[simp 900] theorem rightCosetMulAction_mk_smul
    (H : Subgroup G) (g a : G) :
    letI := rightCosetMulAction H
    g • (Quotient.mk'' a : Quotient (QuotientGroup.rightRel H)) =
      Quotient.mk'' (a * g⁻¹) :=
  rfl

/-- Acting by an inverse on a represented right coset multiplies its representative on the
right.
@isnad1 id=eq.0h4v.s6.514ae41c9ded from=translated src=- shape=b3fc57ba vocab=978d100c
-/
@[simp 900] theorem rightCosetMulAction_inv_mk_smul
    (H : Subgroup G) (g a : G) :
    letI := rightCosetMulAction H
    g⁻¹ • (Quotient.mk'' a : Quotient (QuotientGroup.rightRel H)) =
      Quotient.mk'' (a * g) := by
  rw [rightCosetMulAction_mk_smul (H := H) g⁻¹ a]
  simp only [inv_inv]

end RightCosets

section RightCosetTopology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For an open subgroup, the orbit map to the discrete right-coset space is continuous.
@isnad1 id=continuo.1h3v.s7.f2fffbac4ca1 from=translated src=- shape=2392ec80 vocab=1687182c
-/
theorem continuous_rightCosetMulAction_inv_smul_of_open
    (H : Subgroup G) (hH : IsOpen (H : Set G))
    [TopologicalSpace (Quotient (QuotientGroup.rightRel H))]
    [DiscreteTopology (Quotient (QuotientGroup.rightRel H))]
    (q : Quotient (QuotientGroup.rightRel H)) :
    letI := rightCosetMulAction H
    Continuous fun g : G => g⁻¹ • q := by
  rw [continuous_discrete_rng]
  intro q'
  classical
  let a : G := q.out
  let b : G := q'.out
  have hpre :
      (fun g : G => g⁻¹ • q) ⁻¹' (Set.singleton q') =
        (fun g : G => b * g⁻¹ * a⁻¹) ⁻¹' (H : Set G) := by
    ext g
    constructor
    · intro hg
      have hEq :
          (Quotient.mk'' (a * g) : Quotient (QuotientGroup.rightRel H)) =
            Quotient.mk'' b := by
        calc
          (Quotient.mk'' (a * g) : Quotient (QuotientGroup.rightRel H))
              = g⁻¹ • (Quotient.mk'' a : Quotient (QuotientGroup.rightRel H)) := by
                  rw [rightCosetMulAction_inv_mk_smul (H := H) g a]
          _ = g⁻¹ • q := by rw [Quotient.out_eq' q]
          _ = q' := by
            change g⁻¹ • q = q' at hg
            exact hg
          _ = Quotient.mk'' b := by simp only [Quotient.out_eq, b]
      have hrel : QuotientGroup.rightRel H (a * g) b := Quotient.eq''.mp hEq
      simpa [mul_inv_rev, mul_assoc] using (QuotientGroup.rightRel_apply.mp hrel)
    · intro hg
      have hrel : QuotientGroup.rightRel H (a * g) b := by
        rw [QuotientGroup.rightRel_apply]
        simpa [mul_inv_rev, mul_assoc] using hg
      calc
        g⁻¹ • q = g⁻¹ • (Quotient.mk'' a : Quotient (QuotientGroup.rightRel H)) := by
          rw [Quotient.out_eq' q]
        _ = Quotient.mk'' (a * g) := by
          rw [rightCosetMulAction_inv_mk_smul (H := H) g a]
        _ = Quotient.mk'' b := Quotient.eq''.mpr hrel
        _ = q' := Quotient.out_eq' q'
  change
    (fun g : G => g⁻¹ • q) ⁻¹'
      ({q'} : Set (Quotient (QuotientGroup.rightRel H))) =
        (fun g : G => b * g⁻¹ * a⁻¹) ⁻¹' (H : Set G) at hpre
  rw [hpre]
  exact hH.preimage ((continuous_const.mul continuous_inv).mul continuous_const)

end RightCosetTopology

section BasicDefinitions

variable (A : Type u) (S : Type v) (G : Type w)
variable [Group A] [Group G] [MulAction G S]

/-- The permutational wreath product attached to a `G`-set `Σ`.-/
abbrev PermutationalWreathProduct :=
  (S → A) ⋊[(mulAutArrow (G := G) (A := S) (M := A))] G

end BasicDefinitions

section Topology

variable {A : Type u} {S : Type v} {G : Type w}
variable [Group A] [Group G] [MulAction G S]
variable [TopologicalSpace A] [TopologicalSpace G]

/-- Give a permutational wreath product the topology transported from its product
representation.-/
instance instTopologicalSpacePermutationalWreathProduct :
    TopologicalSpace (PermutationalWreathProduct A S G) :=
  TopologicalSpace.induced
    (SemidirectProduct.equivProd :
      PermutationalWreathProduct A S G ≃ (S → A) × G)
    inferInstance

/-- The topology on a permutational wreath product is the one transported from the product of the
function factor and the right factor.-/
@[simps!]
def permutationalWreathProductHomeomorphProd :
    PermutationalWreathProduct A S G ≃ₜ (S → A) × G where
  toEquiv := SemidirectProduct.equivProd
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    rw [continuous_induced_rng]
    simpa using (continuous_id : Continuous fun x : (S → A) × G => x)

/-- The canonical equivalence from a permutational wreath product to its two factors is
continuous.
@isnad1 id=continuo.0h3v.s8.37c10b563a32 from=translated src=- shape=7e414df2 vocab=130cb5ca
-/
@[continuity] theorem continuous_permutationalWreathProduct_equivProd :
    Continuous
      (SemidirectProduct.equivProd :
        PermutationalWreathProduct A S G → (S → A) × G) :=
  continuous_induced_dom

/-- Projection to the function factor of a permutational wreath product is continuous.
@isnad1 id=continuo.0h3v.s6.c80cbbccab1c from=translated src=- shape=7b552b95 vocab=132c7133
-/
@[continuity] theorem continuous_permutationalWreathProduct_left :
    Continuous (fun x : PermutationalWreathProduct A S G => x.left) :=
  continuous_fst.comp continuous_permutationalWreathProduct_equivProd

/-- Projection to the acting-group factor of a permutational wreath product is continuous.
@isnad1 id=continuo.0h3v.s6.07aa0495189d from=translated src=- shape=63535425 vocab=24c66b68
-/
@[continuity] theorem continuous_permutationalWreathProduct_right :
    Continuous (fun x : PermutationalWreathProduct A S G => x.right) :=
  continuous_snd.comp continuous_permutationalWreathProduct_equivProd

/-- Evaluation of the function factor at a fixed index is continuous.
@isnad1 id=continuo.0h4v.s6.c3fe9805952e from=translated src=- shape=9835fa0d vocab=132c7133
-/
@[continuity] theorem continuous_permutationalWreathProduct_left_apply (s : S) :
    Continuous (fun x : PermutationalWreathProduct A S G => x.left s) :=
  (continuous_apply s).comp continuous_permutationalWreathProduct_left

/-- A permutational wreath product is Hausdorff when both group factors are Hausdorff.
@isnad1 id=t2space.0h3v.s5.e69198c09bea from=translated src=- shape=e3b91ed4 vocab=f44413de
-/
instance instT2SpacePermutationalWreathProduct [T2Space A] [T2Space G] :
    T2Space (PermutationalWreathProduct A S G) :=
  (permutationalWreathProductHomeomorphProd (A := A) (S := S) (G := G)).symm.t2Space

/-- Precomposition by the inverse permutation coming from the `G`-action on `S`. This is the
action appearing in `mulAutArrow`.-/
def functionPrecomp (g : G) (f : S → A) : S → A :=
  fun s => f (g⁻¹ • s)

omit [Group A] [TopologicalSpace A] [TopologicalSpace G] in
/-- Precomposition by the action evaluates at the inverse translate of the index.
@isnad1 id=eq.0h6v.s6.14b4ee30ae31 from=translated src=- shape=f7185d9b vocab=dbe1c2aa
-/
@[simp] theorem functionPrecomp_apply (g : G) (f : S → A) (s : S) :
    functionPrecomp g f s = f (g⁻¹ • s) :=
  rfl

omit [TopologicalSpace A] [TopologicalSpace G] in
/-- Mathlib's action on the function factor is precomposition by the inverse permutation.
@isnad1 id=eq.0h5v.s9.83863c39358f from=translated src=- shape=ba644dc9 vocab=f622d4fe
-/
@[simp] theorem mulAutArrow_apply_eq_functionPrecomp (g : G) (f : S → A) :
    mulAutArrow (G := G) (A := S) (M := A) g f = functionPrecomp g f :=
  rfl

section DiscreteIndex

variable [TopologicalSpace S] [DiscreteTopology S]
variable [ContinuousSMul G S] [ContinuousInv G]

omit [Group A] in
/-- Evaluation is jointly continuous on the product of a function space with a discrete index
space.
@isnad1 id=continuo.0h2v.s5.4f9a00278ad0 from=translated src=- shape=f8289338 vocab=15680bf2
-/
theorem continuous_eval_of_discreteIndex :
    Continuous (fun p : (S → A) × S => p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  have hs :
      Prod.snd ⁻¹' ({p.2} : Set S) ∈ nhds p := by
    refine IsOpen.mem_nhds ((isOpen_discrete ({p.2} : Set S)).preimage continuous_snd) ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
  have hEq :
      (fun q : (S → A) × S => q.1 q.2) =ᶠ[nhds p] fun q => q.1 p.2 := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨Prod.snd ⁻¹' ({p.2} : Set S), hs, ?_⟩
    intro q hq
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hq
    simp only [hq]
  exact ContinuousAt.congr
    (((continuous_apply p.2).comp continuous_fst).continuousAt) hEq.symm

omit [Group A] in
/-- The precomposition action on the function factor is continuous when the index space is
discrete.
@isnad1 id=continuo.0h3v.s6.ae73ea813dbf from=translated src=- shape=3414ca1c vocab=086dd034
-/
theorem continuous_functionPrecomp :
    Continuous (fun p : G × (S → A) => functionPrecomp p.1 p.2) := by
  refine continuous_pi ?_
  intro s
  change Continuous (fun p : G × (S → A) => p.2 (p.1⁻¹ • s))
  have h :=
    (continuous_eval_of_discreteIndex (A := A) (S := S)).comp
      (continuous_snd.prodMk
        (((continuous_inv.comp continuous_fst).smul continuous_const) :
          Continuous (fun p : G × (S → A) => p.1⁻¹ • s)))
  change Continuous (fun p : G × (S → A) => p.2 (p.1⁻¹ • s)) at h
  exact h

omit [TopologicalSpace A] [TopologicalSpace G] [TopologicalSpace S] [DiscreteTopology S]
    [ContinuousSMul G S] [ContinuousInv G] in
/-- The function factor of a product is the first function times the translate of the second.
@isnad1 id=eq.0h5v.s7.563da2bb1b75 from=translated src=- shape=2972e475 vocab=52b522f8
-/
@[simp 900] theorem permutationalWreathProduct_mul_left
    (x y : PermutationalWreathProduct A S G) :
    (x * y).left = x.left * functionPrecomp x.right y.left :=
  rfl

omit [TopologicalSpace A] [TopologicalSpace G] [TopologicalSpace S] [DiscreteTopology S]
    [ContinuousSMul G S] [ContinuousInv G] in
/-- The function factor of an inverse is the translated pointwise inverse.
@isnad1 id=eq.0h4v.s7.0e40fd37a2aa from=translated src=- shape=3e7450bf vocab=56ad4051
-/
@[simp 900] theorem permutationalWreathProduct_inv_left
    (x : PermutationalWreathProduct A S G) :
    x⁻¹.left = functionPrecomp x.right⁻¹ x.left⁻¹ :=
  rfl

end DiscreteIndex

/-- The canonical inclusion of the function factor is continuous.-/
def permutationalWreathProductInlContinuousHom :
    (S → A) →ₜ* PermutationalWreathProduct A S G where
  toMonoidHom := SemidirectProduct.inl
  continuous_toFun := by
    refine continuous_induced_rng.2 ?_
    change Continuous
      (fun f : S → A =>
        ((SemidirectProduct.inl f : PermutationalWreathProduct A S G).left,
          (SemidirectProduct.inl f : PermutationalWreathProduct A S G).right))
    simpa using (continuous_id.prodMk continuous_const)

/-- The canonical inclusion of the right factor is continuous.-/
def permutationalWreathProductInrContinuousHom :
    G →ₜ* PermutationalWreathProduct A S G where
  toMonoidHom := SemidirectProduct.inr
  continuous_toFun := by
    refine continuous_induced_rng.2 ?_
    change Continuous
      (fun g : G =>
        ((SemidirectProduct.inr g : PermutationalWreathProduct A S G).left,
          (SemidirectProduct.inr g : PermutationalWreathProduct A S G).right))
    simpa using (continuous_const.prodMk continuous_id)

/-- The projection to the right factor is a continuous homomorphism.-/
def permutationalWreathProductRightContinuousHom :
    PermutationalWreathProduct A S G →ₜ* G where
  toMonoidHom := SemidirectProduct.rightHom
  continuous_toFun := continuous_permutationalWreathProduct_right

end Topology

section ProCStructure

open ProCGroups.ProC

variable {C : FiniteGroupClass.{u}}
variable {A : Type u} {S : Type u} {G : Type u}
variable [Group A] [Group G] [MulAction G S] [Fintype S]
variable [TopologicalSpace A] [TopologicalSpace S] [TopologicalSpace G]
variable [IsTopologicalGroup A] [IsTopologicalGroup G]
variable [ContinuousSMul G S]

/-- The kernel of the right projection on a permutational wreath product.-/
abbrev permutationalWreathProductRightKernel :
    Subgroup (PermutationalWreathProduct A S G) :=
  (SemidirectProduct.rightHom : PermutationalWreathProduct A S G →* G).ker

/-- The canonical inclusion of the function factor, with codomain restricted to the kernel of the
right projection.-/
def permutationalWreathProductInlToKernelContinuousHom :
    (S → A) →ₜ* permutationalWreathProductRightKernel (A := A) (S := S) (G := G) where
  toMonoidHom :=
    { toFun := fun f => ⟨SemidirectProduct.inl f, by simp only
        [permutationalWreathProductRightKernel, MonoidHom.mem_ker,
        SemidirectProduct.rightHom_inl]⟩
      map_one' := by
        apply Subtype.ext
        simp only [map_one, OneMemClass.coe_one]
      map_mul' := by
        intro f g
        apply Subtype.ext
        simp only [map_mul, MulMemClass.mk_mul_mk]}
  continuous_toFun :=
    by
      exact Continuous.subtype_mk
        (permutationalWreathProductInlContinuousHom (A := A) (S := S) (G := G)).continuous_toFun
        (by
          intro f
          change (permutationalWreathProductInlContinuousHom (A := A) (S := S) (G := G) f).right = 1
          rfl)

omit [Fintype S] [TopologicalSpace S] [IsTopologicalGroup A] [IsTopologicalGroup G]
    [ContinuousSMul G S] in
/-- Inclusion of the function factor is a bijection onto the kernel of the right projection.
@isnad1 id=bijectiv.0h3v.s10.fea0cfa85608 from=translated src=- shape=02b8ad67 vocab=da06f9cd
-/
theorem permutationalWreathProductInlToKernel_bijective :
    Function.Bijective
      ((permutationalWreathProductInlToKernelContinuousHom (A := A) (S := S) (G := G)) :
        (S → A) → permutationalWreathProductRightKernel (A := A) (S := S) (G := G)) := by
  constructor
  · intro f g hfg
    funext s
    have hs := congrArg
      (fun x : permutationalWreathProductRightKernel (A := A) (S := S) (G := G) =>
        ((x : PermutationalWreathProduct A S G).left s)) hfg
    change f s = g s at hs
    exact hs
  · intro x
    refine ⟨x.1.left, ?_⟩
    have hmem :
        (SemidirectProduct.rightHom : PermutationalWreathProduct A S G →* G)
          x.1 = 1 := by
      exact x.2
    have hright : x.1.right = 1 := by
      simpa using hmem
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · change (SemidirectProduct.inl x.1.left : PermutationalWreathProduct A S G).right =
          x.1.right
      simp only [SemidirectProduct.right_inl, hright]

/-- The kernel of the right projection is topologically isomorphic to the function factor.-/
noncomputable def permutationalWreathProductInlKernelContinuousMulEquiv
    [CompactSpace A] [T2Space A]
    [T2Space G] :
    (S → A) ≃ₜ* permutationalWreathProductRightKernel (A := A) (S := S) (G := G) :=
  ContinuousMulEquiv.ofBijectiveCompactToT2
    (permutationalWreathProductInlToKernelContinuousHom (A := A) (S := S) (G := G))
    (permutationalWreathProductInlToKernelContinuousHom (A := A) (S := S) (G := G)).continuous_toFun
    (permutationalWreathProductInlToKernel_bijective (A := A) (S := S) (G := G))

end ProCStructure

section BasicLemmas

variable {A : Type u} {S : Type v} {G : Type w}
variable [Group A] [Group G] [MulAction G S]

/-- Pointwise multiplication formula in the permutational wreath product.
@isnad1 id=eq.0h6v.s8.74cad2e6eb0e from=translated src=- shape=97565064 vocab=7e5dc9ad
-/
@[simp] theorem permutationalWreathProduct_mul_left_apply
    (x y : PermutationalWreathProduct A S G) (s : S) :
    (x * y).left s = x.left s * y.left (x.right⁻¹ • s) :=
  rfl

/-- Pointwise inversion formula in the permutational wreath product.
@isnad1 id=eq.0h5v.s7.0a210c3243c9 from=translated src=- shape=180286c0 vocab=cdc65be3
-/
@[simp] theorem permutationalWreathProduct_inv_left_apply
    (x : PermutationalWreathProduct A S G) (s : S) :
    x⁻¹.left s = (x.left (x.right • s))⁻¹ := by
  change ((mulAutArrow (G := G) (A := S) (M := A) x.right⁻¹) (x.left⁻¹)) s =
      (x.left (x.right • s))⁻¹
  change x.left⁻¹ ((x.right⁻¹)⁻¹ • s) = (x.left (x.right • s))⁻¹
  simp only [inv_inv, Pi.inv_apply]

/-- The function coordinate of the left-factor inclusion is the included function.
@isnad1 id=eq.0h5v.s8.0f5bad12cffe from=translated src=- shape=0e6670d3 vocab=ee6e3581
-/
@[simp] theorem permutationalWreathProduct_inl_left_apply
    (f : S → A) (s : S) :
    (SemidirectProduct.inl f : PermutationalWreathProduct A S G).left s = f s :=
  rfl

/-- The function coordinate of the right-factor inclusion is constantly one.
@isnad1 id=eq.0h5v.s8.ec89deea0acf from=translated src=- shape=b8330aa6 vocab=6356a974
-/
@[simp] theorem permutationalWreathProduct_inr_left_apply
    (g : G) (s : S) :
    (SemidirectProduct.inr g : PermutationalWreathProduct A S G).left s = 1 :=
  rfl

/-- The right projection is a retraction of the right-factor inclusion.
@isnad1 id=eq.0h3v.s8.1037fa4f4b00 from=translated src=- shape=a7d3ae84 vocab=a930bba1
-/
@[simp] theorem permutationalWreathProduct_rightHom_comp_inr :
    (SemidirectProduct.rightHom :
        PermutationalWreathProduct A S G →* G).comp SemidirectProduct.inr =
      MonoidHom.id G := by
  ext g
  rfl

end BasicLemmas

section LeftFactorFunctoriality

variable {A : Type u} {B : Type v} {S : Type w} {G : Type*}
variable [Group A] [Group B] [Group G] [MulAction G S]

/-- Pointwise application of a group homomorphism to the function factor of a wreath product.-/
def permutationalWreathProductMapFun (α : A →* B) : (S → A) →* (S → B) where
  toFun f := α ∘ f
  map_one' := by
    funext s
    simp only [Function.comp_apply, Pi.one_apply, map_one]
  map_mul' f g := by
    funext s
    simp only [Function.comp_apply, Pi.mul_apply, map_mul]

/-- Functoriality of the permutational wreath product in the left factor.-/
def permutationalWreathProductMapLeft (α : A →* B) :
    PermutationalWreathProduct A S G →* PermutationalWreathProduct B S G :=
  SemidirectProduct.map (permutationalWreathProductMapFun (S := S) α) (MonoidHom.id G) fun g => by
    ext f s
    rfl

/-- Mapping the left factor applies the given homomorphism pointwise to the function
coordinate.
@isnad1 id=eq.0h7v.s8.78f9d8e5cbe7 from=translated src=- shape=7f07a26c vocab=c3e8aec8
-/
@[simp] theorem permutationalWreathProductMapLeft_left_apply
    (α : A →* B) (x : PermutationalWreathProduct A S G) (s : S) :
    (permutationalWreathProductMapLeft (S := S) (G := G) α x).left s = α (x.left s) :=
  rfl

/-- Mapping the left factor leaves the acting-group coordinate unchanged.
@isnad1 id=eq.0h6v.s8.604a459a1a2f from=translated src=- shape=45973c92 vocab=39efbc6c
-/
@[simp] theorem permutationalWreathProductMapLeft_right
    (α : A →* B) (x : PermutationalWreathProduct A S G) :
    (permutationalWreathProductMapLeft (S := S) (G := G) α x).right = x.right :=
  rfl

end LeftFactorFunctoriality

section LeftFactorFunctorialityTopological

variable {A : Type u} {B : Type v} {S : Type w} {G : Type*}
variable [Group A] [Group B] [Group G] [MulAction G S]
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace G]

/-- Functoriality of the permutational wreath product in the left factor, upgraded to a continuous
homomorphism.-/
def permutationalWreathProductMapLeftContinuous
    (α : A →ₜ* B) :
    PermutationalWreathProduct A S G →ₜ* PermutationalWreathProduct B S G where
  toMonoidHom := permutationalWreathProductMapLeft (S := S) (G := G) α.toMonoidHom
  continuous_toFun := by
    refine continuous_induced_rng.2 ?_
    change Continuous
      (fun x : PermutationalWreathProduct A S G =>
        ((permutationalWreathProductMapLeft (S := S) (G := G) α.toMonoidHom x).left,
          (permutationalWreathProductMapLeft (S := S) (G := G) α.toMonoidHom x).right))
    have hleft :
        Continuous
          (fun x : PermutationalWreathProduct A S G =>
            (permutationalWreathProductMapLeft (S := S) (G := G) α.toMonoidHom x).left) := by
      refine continuous_pi ?_
      intro s
      change Continuous (fun x : PermutationalWreathProduct A S G => α (x.left s))
      have h := α.continuous_toFun.comp
        (continuous_permutationalWreathProduct_left_apply
          (A := A) (S := S) (G := G) s)
      change Continuous (fun x : PermutationalWreathProduct A S G => α (x.left s)) at h
      exact h
    have hright :
        Continuous
          (fun x : PermutationalWreathProduct A S G =>
            (permutationalWreathProductMapLeft (S := S) (G := G) α.toMonoidHom x).right) := by
      simpa using continuous_permutationalWreathProduct_right
    exact hleft.prodMk hright

end LeftFactorFunctorialityTopological

section StandardEmbedding

variable {G : Type u} [Group G]
variable (H : Subgroup G)

/--
The right-coset standard embedding carries the natural multiplication action used in the
wreath-product construction.-/
instance instMulActionRightCosetStandardEmbedding :
    MulAction G (Quotient (QuotientGroup.rightRel H)) :=
  rightCosetMulAction H

attribute [-instance] instMulActionRightCosetStandardEmbedding

/-- The underlying section attached to a right transversal.-/
noncomputable def rightTransversalSection {T : Set G}
    (hT : Subgroup.IsComplement (H : Set G) T) :
    Quotient (QuotientGroup.rightRel H) → G :=
  fun q => (hT.rightQuotientEquiv q : G)

/-- The representative selected by a right transversal lies over the prescribed right coset.
@isnad1 id=eq.1h4v.s5.646b34b917d6 from=translated src=- shape=58f2c519 vocab=4fa1a4dd
-/
@[simp] theorem rightTransversalSection_spec {T : Set G}
    (hT : Subgroup.IsComplement (H : Set G) T)
    (q : Quotient (QuotientGroup.rightRel H)) :
    Quotient.mk'' (rightTransversalSection (H := H) hT q) = q :=
  hT.mk''_rightQuotientEquiv q

/-- The cocycle attached to a section of the right quotient by `H`.-/
noncomputable def rightQuotientSectionCocycle
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q)
    (g : G) :
    Quotient (QuotientGroup.rightRel H) → H := by
  intro q
  refine ⟨τ q * g * (τ (g⁻¹ • q))⁻¹, ?_⟩
  have hq :
      Quotient.mk'' (τ q * g) = g⁻¹ • q := by
    calc
      Quotient.mk'' (τ q * g)
          = g⁻¹ • (Quotient.mk'' (τ q) : Quotient (QuotientGroup.rightRel H)) := by
              symm
              rw [rightCosetMulAction_inv_mk_smul (H := H) g (τ q)]
      _ = g⁻¹ • q := by rw [hτ q]
  have hEq :
      (Quotient.mk'' (τ q * g) : Quotient (QuotientGroup.rightRel H)) =
        Quotient.mk'' (τ (g⁻¹ • q)) := by
    calc
      (Quotient.mk'' (τ q * g) : Quotient (QuotientGroup.rightRel H))
          = g⁻¹ • q := hq
      _ = Quotient.mk'' (τ (g⁻¹ • q)) := by symm; exact hτ (g⁻¹ • q)
  have hrel : QuotientGroup.rightRel H (τ q * g) (τ (g⁻¹ • q)) := Quotient.exact' hEq
  rw [QuotientGroup.rightRel_apply] at hrel
  simpa [mul_inv_rev] using H.inv_mem hrel

/-- The standard wreath-product embedding attached to a section of the right quotient by `H`.-/
noncomputable def rightQuotientSectionEmbedding
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q) :
    G →* PermutationalWreathProduct H (Quotient (QuotientGroup.rightRel H)) G where
  toFun g := ⟨rightQuotientSectionCocycle (H := H) τ hτ g, g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · funext q
      apply Subtype.ext
      simp only [rightQuotientSectionCocycle, mul_one, inv_one, one_smul, mul_inv_cancel,
  SemidirectProduct.one_left, Pi.one_apply, OneMemClass.coe_one]
    · rfl
  map_mul' g₁ g₂ := by
    apply SemidirectProduct.ext
    · funext q
      apply Subtype.ext
      simp only [rightQuotientSectionCocycle, mul_inv_rev, mul_smul, mul_assoc,
          SemidirectProduct.mk_eq_inl_mul_inr,
  permutationalWreathProduct_mul_left_apply, permutationalWreathProduct_inl_left_apply,
      SemidirectProduct.right_inl,
  inv_one, one_smul, permutationalWreathProduct_inr_left_apply, SemidirectProduct.right_inr,
      mul_one, one_mul,
  MulMemClass.mk_mul_mk, inv_mul_cancel_left]
    · rfl

/-- Pointwise formula for the standard wreath-product embedding attached to a right-quotient
section.
@isnad1 id=eq.1h5v.s9.98a0455f5eff from=translated src=- shape=ef276058 vocab=31335c30
-/
@[simp] theorem rightQuotientSectionEmbedding_left_apply
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q)
    (g : G) (q : Quotient (QuotientGroup.rightRel H)) :
    (rightQuotientSectionEmbedding (H := H) τ hτ g).left q =
      rightQuotientSectionCocycle (H := H) τ hτ g q :=
  rfl

/-- The standard wreath-product embedding preserves the acting-group coordinate.
@isnad1 id=eq.1h4v.s9.c6fa2c5a1cf3 from=translated src=- shape=39cd44eb vocab=de86e942
-/
@[simp] theorem rightQuotientSectionEmbedding_right
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q)
    (g : G) :
    (rightQuotientSectionEmbedding (H := H) τ hτ g).right = g :=
  rfl

/-- The right projection is a retraction of the standard right-quotient embedding.
@isnad1 id=eq.1h3v.s10.010ff7d13a9b from=translated src=- shape=cc5db9eb vocab=594bf50e
-/
@[simp] theorem rightQuotientSectionEmbedding_rightHom
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q) :
    (SemidirectProduct.rightHom :
        PermutationalWreathProduct H (Quotient (QuotientGroup.rightRel H)) G →* G).comp
        (rightQuotientSectionEmbedding (H := H) τ hτ) = MonoidHom.id G := by
  ext g
  rfl

end StandardEmbedding

section StandardEmbeddingTopological

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G)

/--
The topological right-coset standard embedding carries the natural multiplication action used in
the wreath-product construction.-/
instance instMulActionRightCosetStandardEmbeddingTopological :
    MulAction G (Quotient (QuotientGroup.rightRel H)) :=
  rightCosetMulAction H

attribute [-instance] instMulActionRightCosetStandardEmbeddingTopological

end StandardEmbeddingTopological

section CocycleFormulas

variable {A : Type u} {S : Type v} {G : Type w}
variable [Group A] [Group G] [MulAction G S]

/-- The left coordinate of an element of a wreath product, viewed as a function of the group
element on the source.-/
def wreathLeftCoordinate
    (ψ : G →* PermutationalWreathProduct A S G) (s : S) : G → A :=
  fun g => (ψ g).left s

/-- The cocycle formula for the left coordinates of a homomorphism into a wreath product whose
right factor is the identity.
@isnad1 id=eq.1h7v.s8.fcd0894840fb from=translated src=- shape=f543c398 vocab=fbccd504
-/
theorem wreathLeftCoordinate_mul
    (ψ : G →* PermutationalWreathProduct A S G)
    (hψ :
      (SemidirectProduct.rightHom : PermutationalWreathProduct A S G →* G).comp ψ =
        MonoidHom.id G)
    (s : S) (g₁ g₂ : G) :
    wreathLeftCoordinate ψ s (g₁ * g₂) =
      wreathLeftCoordinate ψ s g₁ *
        wreathLeftCoordinate ψ (g₁⁻¹ • s) g₂ := by
  have hright : (ψ g₁).right = g₁ := by
    simpa using congrArg (fun f : G →* G => f g₁) hψ
  simp only [wreathLeftCoordinate, map_mul, permutationalWreathProduct_mul_left_apply, hright]

end CocycleFormulas

section RightQuotientCoordinateRecovery

variable {A : Type u} {G : Type v}
variable [Group A] [Group G]
variable (H : Subgroup G)

/--
The coordinate-recovery map for the right-coset standard embedding is compatible with the
natural multiplication action.-/
instance instMulActionRightCosetCoordinateRecovery :
    MulAction G (Quotient (QuotientGroup.rightRel H)) :=
  rightCosetMulAction H

attribute [-instance] instMulActionRightCosetCoordinateRecovery

/-- Basepoint evaluation on the stabilizer subgroup of the trivial right coset, expressed for a
homomorphism into the wreath product whose right factor is the identity.-/
def rightQuotientBasepointProjectionHom
    (ψ : G →* PermutationalWreathProduct A (Quotient (QuotientGroup.rightRel H)) G)
    (hψ :
      (SemidirectProduct.rightHom :
          PermutationalWreathProduct A (Quotient (QuotientGroup.rightRel H)) G →* G).comp ψ =
        MonoidHom.id G) :
    H →* A where
  toFun h :=
    wreathLeftCoordinate ψ
      (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) h.1
  map_one' := by
    simp only [wreathLeftCoordinate, OneMemClass.coe_one, map_one, SemidirectProduct.one_left,
        Pi.one_apply]
  map_mul' a b := by
    change
      wreathLeftCoordinate ψ
          (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H))
          (a.1 * b.1) =
        wreathLeftCoordinate ψ
            (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) a.1 *
          wreathLeftCoordinate ψ
            (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) b.1
    rw [wreathLeftCoordinate_mul (ψ := ψ) hψ
      (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) a.1 b.1]
    have ha :
        a.1⁻¹ • (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) =
          (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) := by
      rw [rightCosetMulAction_inv_mk_smul (H := H) a.1 1]
      apply Quotient.sound'
      rw [QuotientGroup.rightRel_apply]
      simp only [one_mul, H.inv_mem a.2]
    simp only [ha]

end RightQuotientCoordinateRecovery

section StabilizerProjection

variable {A : Type u} {S : Type v} {G : Type w}
variable [Group A] [Group G] [MulAction G S]

/-- Evaluation at a fixed point is a homomorphism on the wreath product over the stabilizer of
that point.-/
def wreathStabilizerProjection (s : S) :
    PermutationalWreathProduct A S (MulAction.stabilizer G s) →* A where
  toFun x := x.left s
  map_one' := rfl
  map_mul' x y := by
    have hx : x.right⁻¹ • s = s := by
      exact MulAction.mem_stabilizer_iff.mp x.right⁻¹.2
    simp only [permutationalWreathProduct_mul_left_apply, hx]

/-- The stabilizer projection evaluates the function coordinate at the fixed point.
@isnad1 id=eq.0h5v.s9.01b55b1bb3b7 from=translated src=- shape=221aa766 vocab=accd039b
-/
@[simp] theorem wreathStabilizerProjection_apply
    (s : S) (x : PermutationalWreathProduct A S (MulAction.stabilizer G s)) :
    wreathStabilizerProjection (A := A) (G := G) s x = x.left s :=
  rfl

/-- The stabilizer projection is natural in the left factor.
@isnad1 id=eq.0h7v.s11.b38a05917be7 from=translated src=- shape=120276ca vocab=93646ac8
-/
@[simp] theorem wreathStabilizerProjection_mapLeft
    {B : Type*} [Group B]
    (α : A →* B) (s : S)
    (x : PermutationalWreathProduct A S (MulAction.stabilizer G s)) :
    wreathStabilizerProjection (A := B) (G := G) s
        (permutationalWreathProductMapLeft
          (S := S) (G := MulAction.stabilizer G s) α x) =
      α (wreathStabilizerProjection (A := A) (G := G) s x) := by
  rfl

section RightQuotientBasepoint

variable {H : Subgroup G}

/-- Basepoint form: on the subgroup `H`, the left coordinate of the standard
embedding at the trivial right coset is the given element, provided the section is normalized at
the basepoint.
@isnad1 id=eq.3h4v.s10.37c27ced0031 from=translated src=- shape=70df8a3f vocab=e624bc82
-/
@[simp 900] theorem rightQuotientSectionEmbedding_left_basepoint_of_mem
    (τ : Quotient (QuotientGroup.rightRel H) → G)
    (hτ : ∀ q, Quotient.mk'' (τ q) = q)
    (hτ1 : τ (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) = 1)
    {g : G} (hg : g ∈ H) :
    (rightQuotientSectionEmbedding (H := H) τ hτ g).left
        (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) =
      ⟨g, hg⟩ := by
  apply Subtype.ext
  have hq :
      (g⁻¹ •
          (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H))) =
        (Quotient.mk'' (1 : G) : Quotient (QuotientGroup.rightRel H)) := by
    rw [rightCosetMulAction_mk_smul (H := H) g⁻¹ 1]
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    simpa using hg
  simp only [rightQuotientSectionEmbedding, SemidirectProduct.mk_eq_inl_mul_inr, MonoidHom.coe_mk,
  OneHom.coe_mk, permutationalWreathProduct_mul_left_apply,
      permutationalWreathProduct_inl_left_apply,
  rightQuotientSectionCocycle, hτ1, one_mul, hq, inv_one, mul_one, SemidirectProduct.right_inl,
      one_smul,
  permutationalWreathProduct_inr_left_apply]

end RightQuotientBasepoint

end StabilizerProjection

end ProCGroups.WreathProducts
