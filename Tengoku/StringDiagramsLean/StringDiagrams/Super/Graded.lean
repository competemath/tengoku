import Tengoku.StringDiagramsLean.StringDiagrams.Super.Supernatural
import Tengoku.StringDiagramsLean.StringDiagrams.Super.Underlying

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Graded supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
§6, Definition 6.1.

A *graded superspace* is a `ℤ`-graded superspace `V = ⨁ₙ Vₙ = ⨁ₙ (V_{n,0} ⊕ V_{n,1})`, the
`ℤ`- and `ℤ/2`-gradings being independent. A *graded supercategory* is a category enriched in
the symmetric monoidal category `GSVec` of graded superspaces and degree-preserving even
linear maps.

## Encoding

As `StringDiagrams.Supercategory` unpacks `SVec`-enrichment, we unpack `GSVec`-enrichment on
top of a supercategory: `StringDiagrams.GradedSupercategory R C` adds submodules
`degree X Y n` of each morphism module such that

* the morphism module is the internal direct sum of the `degree X Y n` (`isInternal_degree`);
* each `degree X Y n` is a sub-superspace, i.e. stable under the parity projections
  (`proj_mem_degree`), so that `degree X Y n = V_{n,0} ⊕ V_{n,1}` with
  `V_{n,p} = degree X Y n ⊓ parity X Y p`;
* identities have degree `0` and composition adds degrees.

Together with the axioms of `Supercategory` (identities even, composition adds parities),
this says exactly that each morphism space is the bigraded module `⨁_{(n,p)} V_{n,p}`
(`GradedSupercategory.isInternal_bigrading`) and that composition is bihomogeneous, i.e.
the enriched definition.

## Main definitions

* `GradedSupercategory R C` (Definition 6.1), degree projections `dproj R n`.
* `GradedSupercategory.IsGradedSuperfunctor R F`: a superfunctor preserving degrees
  (Definition 6.1).
* `GradedSupercategory.IsGradedSupernatural R p n x`: a supernatural transformation
  homogeneous of parity `p` and degree `n` (Definition 6.1).
* `GradedSupercategory.GradedSuperNatTrans R F G`: a graded supernatural transformation, a
  finite sum of homogeneous ones (Definition 6.1).
* `GradedSupercategory.GradedSuperequivalence R F`: a graded superfunctor with a graded
  quasi-inverse and even unit and counit isomorphisms of degree zero;
  `GradedSuperequivalence.ofFullyFaithful`.
* `GradedSupercategory.DegreeZero R C`: the supercategory of morphisms of degree zero;
  the *underlying category* of the paper (even morphisms of degree zero) is
  `Underlying R (DegreeZero R C)` (`GradedSupercategory.GUnderlying`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w w₁ w₂ w₃ w₄ w₅ w₆

/-- A graded supercategory (Brundan–Ellis, Definition 6.1), in unpacked form: a
supercategory together with a `ℤ`-grading of each morphism module by sub-superspaces, with
identities of degree `0` and composition adding degrees. See the module documentation.-/
class GradedSupercategory (R : Type w) [CommRing R] (C : Type w₁) [Category.{w₂} C]
    [Preadditive C] [Linear R C] [Supercategory R C] where
  /-- The morphisms of degree `n`.-/
  degree : ∀ X Y : C, ℤ → Submodule R (X ⟶ Y)
  /-- Every morphism is uniquely a finite sum of homogeneous morphisms.-/
  isInternal_degree : ∀ X Y : C, DirectSum.IsInternal (degree X Y)
  /-- Each homogeneous component is a sub-superspace.-/
  proj_mem_degree : ∀ {X Y : C} {n : ℤ} {f : X ⟶ Y} (p : ZMod 2),
    f ∈ degree X Y n → proj R p f ∈ degree X Y n
  /-- Identities have degree zero.-/
  id_mem_degree : ∀ X : C, 𝟙 X ∈ degree X X 0
  /-- Composition adds degrees.-/
  comp_mem_degree : ∀ {X Y Z : C} {m n : ℤ} {f : X ⟶ Y} {g : Y ⟶ Z},
    f ∈ degree X Y m → g ∈ degree Y Z n → f ≫ g ∈ degree X Z (m + n)

namespace GradedSupercategory

variable {R : Type w} [CommRing R]
  {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [Supercategory R C]
  [GradedSupercategory R C]
  {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [Supercategory R D]
  [GradedSupercategory R D]
  {E : Type w₅} [Category.{w₆} E] [Preadditive E] [Linear R E] [Supercategory R E]
  [GradedSupercategory R E]

/-! ## Degree projections -/

section Proj

variable (R) in
/-- The decomposition of a morphism module into homogeneous components.-/
@[instance_reducible]
def degreeDecomposition (X Y : C) : DirectSum.Decomposition (degree (R := R) X Y) :=
  (isInternal_degree X Y).chooseDecomposition

variable (R) in
/-- The degree-`n` component of morphisms `X ⟶ Y`.-/
def dproj (n : ℤ) {X Y : C} : (X ⟶ Y) →ₗ[R] (X ⟶ Y) :=
  letI := degreeDecomposition R X Y
  (degree (R := R) X Y n).subtype ∘ₗ
    (DirectSum.component R ℤ (fun m => degree (R := R) X Y m) n) ∘ₗ
      (DirectSum.decomposeLinearEquiv (degree (R := R) X Y)).toLinearMap

/--
@isnad1 id=eq.0h6v.s12.3ff21682bf58 from=translated src=- shape=7e745e6b vocab=da27c4f3
-/
theorem dproj_apply (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    letI := degreeDecomposition R X Y
    dproj R n f = (DirectSum.decompose (degree (R := R) X Y) f n : X ⟶ Y) := rfl

/--
@isnad1 id=mem.0h6v.s8.665a42e1c726 from=translated src=- shape=50688999 vocab=d9a0d32c
-/
theorem dproj_mem (n : ℤ) {X Y : C} (f : X ⟶ Y) : dproj R n f ∈ degree (R := R) X Y n :=
  letI := degreeDecomposition R X Y
  (DirectSum.decompose (degree (R := R) X Y) f n).2

/--
@isnad1 id=eq.1h6v.s8.771cbfe9eebb from=translated src=- shape=1dce3dde vocab=d9a0d32c
-/
theorem dproj_of_mem {n : ℤ} {X Y : C} {f : X ⟶ Y} (hf : f ∈ degree (R := R) X Y n) :
    dproj R n f = f :=
  letI := degreeDecomposition R X Y
  DirectSum.decompose_of_mem_same _ hf

/--
@isnad1 id=eq.2h7v.s9.0da39ef39e6a from=translated src=- shape=3730b388 vocab=d9a0d32c
-/
theorem dproj_of_mem_ne {m n : ℤ} {X Y : C} {f : X ⟶ Y} (hf : f ∈ degree (R := R) X Y m)
    (h : m ≠ n) : dproj R n f = 0 :=
  letI := degreeDecomposition R X Y
  DirectSum.decompose_of_mem_ne _ hf h

/-- Induction on morphisms via homogeneous ones.
@isnad1 id=var.0h9v.s8.2489f68a08e9 from=translated src=- shape=3c467f27 vocab=eb0392a8
-/
@[elab_as_elim]
theorem induction_on_degree {X Y : C} {P : (X ⟶ Y) → Prop} (f : X ⟶ Y) (zero : P 0)
    (hom : ∀ (n : ℤ) (g : X ⟶ Y), g ∈ degree (R := R) X Y n → P g)
    (add : ∀ g h, P g → P h → P (g + h)) : P f :=
  letI := degreeDecomposition R X Y
  DirectSum.Decomposition.inductionOn (degree (R := R) X Y) zero (fun g => hom _ _ g.2) add f

/-- A morphism all of whose components other than the degree-`n` one vanish has degree
`n`.
@isnad1 id=mem.1h6v.s9.7ac0ff004356 from=translated src=- shape=b3eb0c9b vocab=d9a0d32c
-/
theorem mem_degree_of_dproj {n : ℤ} {X Y : C} {f : X ⟶ Y}
    (h : ∀ m, m ≠ n → dproj R m f = 0) : f ∈ degree (R := R) X Y n := by
  let := degreeDecomposition R X Y
  have e : DirectSum.decompose (degree (R := R) X Y) f =
      DirectSum.of (fun m => degree (R := R) X Y m) n
        (DirectSum.decompose (degree (R := R) X Y) f n) := by
    ext m : 1
    by_cases hm : m = n
    · subst hm; simp
    · rw [DirectSum.of_eq_of_ne _ _ _ hm]
      exact Subtype.ext (h m hm)
  have := congrArg (DirectSum.decompose (degree (R := R) X Y)).symm e
  rw [Equiv.symm_apply_apply, DirectSum.decompose_symm_of] at this
  rw [this]; exact Submodule.coe_mem _

/-- The parity projections preserve the degree projections.
@isnad1 id=eq.0h7v.s9.2ae508cca653 from=translated src=- shape=a6b50092 vocab=e797921c
-/
theorem proj_dproj (p : ZMod 2) (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    proj R p (dproj R n f) = dproj R n (proj R p f) := by
  refine induction_on_degree (R := R) f (by simp) (fun m g hg => ?_) (fun g h hg hh => ?_)
  · by_cases h : m = n
    · subst h
      rw [dproj_of_mem hg, dproj_of_mem (proj_mem_degree p hg)]
    · rw [dproj_of_mem_ne hg h, dproj_of_mem_ne (proj_mem_degree p hg) h, map_zero]
  · rw [map_add, map_add, hg, hh, map_add, map_add]

/--
@isnad1 id=mem.1h7v.s9.fa39aef94409 from=translated src=- shape=013831d4 vocab=c2fb1bf1
-/
theorem twist_mem_degree (p : ZMod 2) {n : ℤ} {X Y : C} {f : X ⟶ Y}
    (hf : f ∈ degree (R := R) X Y n) : twist R p f ∈ degree (R := R) X Y n := by
  rw [twist_apply]
  exact Submodule.add_mem _ (proj_mem_degree 0 hf)
    (Submodule.smul_mem _ _ (proj_mem_degree 1 hf))

/--
@isnad1 id=mem.0h5v.s7.78049dc57abb from=translated src=- shape=c0c91d10 vocab=3dab98bc
-/
theorem zero_mem_degree {X Y : C} (n : ℤ) : (0 : X ⟶ Y) ∈ degree (R := R) X Y n :=
  Submodule.zero_mem _

/-- The inverse of an isomorphism of degree `n` has degree `-n`.
@isnad1 id=mem.1h6v.s8.1e992c68e3b7 from=translated src=- shape=bb5c9f3b vocab=fe320837
-/
theorem inv_mem_degree {n : ℤ} {X Y : C} (e : X ≅ Y) (he : e.hom ∈ degree (R := R) X Y n) :
    e.inv ∈ degree (R := R) Y X (-n) := by
  apply mem_degree_of_dproj
  intro m hm
  have key : ∀ g : Y ⟶ X, ∀ k, dproj R (n + k) (e.hom ≫ g) = e.hom ≫ dproj R k g := by
    intro g k
    refine induction_on_degree (R := R) g (by simp) (fun j g hg => ?_) (fun g h hg hh => ?_)
    · by_cases hj : j = k
      · subst hj; rw [dproj_of_mem (comp_mem_degree he hg), dproj_of_mem hg]
      · rw [dproj_of_mem_ne (comp_mem_degree he hg) (fun h => hj (add_left_cancel h)),
          dproj_of_mem_ne hg hj, Limits.comp_zero]
    · rw [Preadditive.comp_add, map_add, hg, hh, map_add, Preadditive.comp_add]
  have h1 : e.hom ≫ dproj R m e.inv = 0 := by
    rw [← key, e.hom_inv_id, dproj_of_mem_ne (id_mem_degree X)]
    omega
  calc dproj R m e.inv = e.inv ≫ e.hom ≫ dproj R m e.inv := by
        rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
    _ = 0 := by rw [h1, Limits.comp_zero]

/-- The morphisms of parity `p` and degree `n`.-/
def bidegree (X Y : C) (np : ℤ × ZMod 2) : Submodule R (X ⟶ Y) :=
  degree (R := R) X Y np.1 ⊓ parity (R := R) X Y np.2

/-- **Definition 6.1.** The encoding is that of `GSVec`-enrichment: each morphism module is
the internal direct sum of the bihomogeneous parts `V_{n,p} = degree n ⊓ parity p`.
@isnad1 id=isintern.0h4v.s7.4bade9c919ac from=translated src=- shape=fca10094 vocab=75c948f8
-/
theorem isInternal_bigrading (X Y : C) : DirectSum.IsInternal (bidegree (R := R) X Y) := by
  classical
  let := degreeDecomposition R X Y
  let := decomposition R X Y
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨?_, ?_⟩
  · -- independence, via the linear map `f ↦ proj_p (dproj_n f)` for each index
    rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hpi : ∀ j : ℤ × ZMod 2, j ≠ i → ∀ y ∈ bidegree (R := R) X Y j,
        proj R i.2 (dproj R i.1 y) = 0 := by
      intro j hj y hy
      by_cases h1 : j.1 = i.1
      · have h2 : j.2 ≠ i.2 := fun h2 => hj (Prod.ext h1 h2)
        rw [dproj_of_mem (h1 ▸ hy.1), proj_of_mem_ne hy.2 h2]
      · rw [dproj_of_mem_ne hy.1 h1, map_zero]
    have h0 : proj R i.2 (dproj R i.1 x) = 0 := by
      refine Submodule.iSup_induction (fun j : {j // j ≠ i} => bidegree (R := R) X Y j)
        (motive := fun y => proj R i.2 (dproj R i.1 y) = 0) ?_ ?_ ?_ ?_
      · simpa [iSup_subtype'] using hx'
      · intro j y hy; exact hpi j j.2 y hy
      · simp
      · intro y z hy hz; rw [map_add, map_add, hy, hz, add_zero]
    rwa [dproj_of_mem hx.1, proj_of_mem hx.2] at h0
  · rw [eq_top_iff]
    intro f _
    refine induction_on_degree (R := R) f (Submodule.zero_mem _) (fun n g hg => ?_)
      (fun g h hg hh => Submodule.add_mem _ hg hh)
    rw [← proj_add_proj (R := R) g]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_iSup_of_mem (n, (0 : ZMod 2)) ⟨proj_mem_degree 0 hg, proj_mem 0 g⟩
    · exact Submodule.mem_iSup_of_mem (n, (1 : ZMod 2)) ⟨proj_mem_degree 1 hg, proj_mem 1 g⟩

end Proj

/-! ## Graded superfunctors -/

section Functor

variable (R) in
/-- A graded superfunctor (Brundan–Ellis, Definition 6.1): a superfunctor preserving degrees
of morphisms.-/
class IsGradedSuperfunctor (F : C ⥤ D) [F.Additive] [F.Linear R] : Prop
    extends IsSuperfunctor R F where
  /-- `F` preserves degrees.-/
  map_mem_degree : ∀ {X Y : C} {n : ℤ} {f : X ⟶ Y}, f ∈ degree (R := R) X Y n →
    F.map f ∈ degree (R := R) (F.obj X) (F.obj Y) n

/--
@isnad1 id=isgraded.0h2v.s5.2adb031fd59e from=translated src=- shape=8750e5e8 vocab=c2fc1106
-/
instance IsGradedSuperfunctor.id : IsGradedSuperfunctor R (𝟭 C) where
  map_mem_degree hf := hf

/--
@isnad1 id=isgraded.0h6v.s7.237d2db2d8d4 from=translated src=- shape=2da02037 vocab=bfd74721
-/
instance IsGradedSuperfunctor.comp (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [F.Linear R]
    [G.Additive] [G.Linear R] [IsGradedSuperfunctor R F] [IsGradedSuperfunctor R G] :
    IsGradedSuperfunctor R (F ⋙ G) where
  map_mem_degree hf := IsGradedSuperfunctor.map_mem_degree (R := R) (F := G)
    (IsGradedSuperfunctor.map_mem_degree (F := F) hf)

/--
@isnad1 id=mem.1h8v.s9.a7eaefcb8ff4 from=translated src=- shape=bb2dacbc vocab=c2689770
-/
theorem map_mem_degree (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]
    {X Y : C} {n : ℤ} {f : X ⟶ Y} (hf : f ∈ degree (R := R) X Y n) :
    F.map f ∈ degree (R := R) (F.obj X) (F.obj Y) n :=
  IsGradedSuperfunctor.map_mem_degree hf

/--
@isnad1 id=eq.0h8v.s9.d0a0f870aa02 from=translated src=- shape=88b70d0e vocab=8dd10f98
-/
theorem map_dproj (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] (n : ℤ)
    {X Y : C} (f : X ⟶ Y) : F.map (dproj R n f) = dproj R n (F.map f) := by
  refine induction_on_degree (R := R) f (by simp) (fun m g hg => ?_) (fun g h hg hh => ?_)
  · by_cases h : m = n
    · subst h; rw [dproj_of_mem hg, dproj_of_mem (map_mem_degree F hg)]
    · rw [dproj_of_mem_ne hg h, dproj_of_mem_ne (map_mem_degree F hg) h, F.map_zero]
  · rw [map_add, F.map_add, hg, hh, F.map_add, map_add]

/-- Faithful graded superfunctors reflect degrees.
@isnad1 id=mem.1h8v.s9.6073bea141af from=translated src=- shape=966119b4 vocab=97e7200c
-/
theorem mem_degree_of_map_mem (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]
    [F.Faithful] {X Y : C} {n : ℤ} {f : X ⟶ Y}
    (hf : F.map f ∈ degree (R := R) (F.obj X) (F.obj Y) n) : f ∈ degree (R := R) X Y n :=
  mem_degree_of_dproj fun m hm => F.map_injective (by
    rw [map_dproj, F.map_zero, dproj_of_mem_ne hf (Ne.symm hm)])

end Functor

/-! ## Homogeneous graded supernatural transformations -/

section NatTrans

variable (R) in
/-- A supernatural transformation homogeneous of parity `p` and of degree `n` (Brundan–Ellis,
Definition 6.1): every component `x X` has degree `n`.-/
structure IsGradedSupernatural (p : ZMod 2) (n : ℤ) {F G : C ⥤ D}
    (x : ∀ X, F.obj X ⟶ G.obj X) : Prop extends IsSupernatural R p x where
  mem_degree : ∀ X, x X ∈ degree (R := R) (F.obj X) (G.obj X) n

variable {F G H : C ⥤ D}

omit [GradedSupercategory R C] in
/--
@isnad1 id=isgraded.0h4v.s7.b778e759fb19 from=translated src=- shape=a79982c8 vocab=1dfa713c
-/
theorem isGradedSupernatural_id [F.Linear R] :
    IsGradedSupernatural R 0 0 fun X => 𝟙 (F.obj X) :=
  ⟨isSupernatural_id, fun _ => id_mem_degree _⟩

variable (R) in
/-- A graded supernatural transformation `F ⇒ G` (Brundan–Ellis, Definition 6.1): an element
of `⨁ₙ Hom(F, G)ₙ`, where `Hom(F, G)ₙ` is the superspace of supernatural transformations
homogeneous of degree `n`. It is given by its bihomogeneous components `app n p`, finitely
many degrees being nonzero.-/
@[ext]
structure GradedSuperNatTrans (F G : C ⥤ D) where
  /-- The component of degree `n` and parity `p`.-/
  app : ℤ → ZMod 2 → ∀ X, F.obj X ⟶ G.obj X
  isGradedSupernatural : ∀ n p, IsGradedSupernatural R p n (app n p)
  /-- A finite set of degrees outside of which the components vanish.-/
  support : Finset ℤ
  app_eq_zero : ∀ n, n ∉ support → ∀ p, app n p = 0

/-- The morphism `x_X = ∑_{n,p} x_{X,n,p}`.-/
def GradedSuperNatTrans.total (x : GradedSuperNatTrans R F G) (X : C) : F.obj X ⟶ G.obj X :=
  ∑ n ∈ x.support, (x.app n 0 X + x.app n 1 X)

/-- A homogeneous supernatural transformation of parity `p` and degree `n` as a graded
supernatural transformation.-/
def IsGradedSupernatural.toGraded [DecidableEq ℤ] {p : ZMod 2} {n : ℤ}
    {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsGradedSupernatural R p n x) :
    GradedSuperNatTrans R F G where
  app m q := if m = n ∧ q = p then x else 0
  isGradedSupernatural m q := by
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact hx
    · exact ⟨⟨fun X => Submodule.zero_mem _, fun _ => by simp⟩, fun X => Submodule.zero_mem _⟩
  support := {n}
  app_eq_zero m hm q := by
    rw [Finset.mem_singleton] at hm
    simp [hm]

end NatTrans

/-! ## Graded superequivalences -/

section Equivalence

variable (R) in
/-- A graded superequivalence: a graded superfunctor `F` with a graded quasi-inverse and even
unit and counit isomorphisms of degree zero.-/
structure GradedSuperequivalence (F : C ⥤ D) extends Superequivalence R F where
  [inverse_isGraded : IsGradedSuperfunctor R inverse]
  unitIso_mem_degree : ∀ X, unitIso.hom.app X ∈ degree (R := R) X (inverse.obj (F.obj X)) 0
  counitIso_mem_degree : ∀ Y, counitIso.hom.app Y ∈ degree (R := R) (F.obj (inverse.obj Y)) Y 0

attribute [instance] GradedSuperequivalence.inverse_isGraded

variable (R) in
/-- Every object of the target is isomorphic to an object in the image via an even
isomorphism of degree zero.-/
def GradedEvenlyDense (F : C ⥤ D) : Prop :=
  ∀ Y : D, ∃ (X : C) (e : F.obj X ≅ Y),
    e.hom ∈ parity (R := R) (F.obj X) Y 0 ∧ e.hom ∈ degree (R := R) (F.obj X) Y 0

/--
@isnad1 id=gradedev.0h5v.s6.706faf6f4474 from=translated src=- shape=bb8bfe14 vocab=87ed4914
-/
theorem GradedSuperequivalence.gradedEvenlyDense {F : C ⥤ D} (e : GradedSuperequivalence R F) :
    GradedEvenlyDense R F := fun Y =>
  ⟨e.inverse.obj Y, e.counitIso.app Y, e.counitIso_mem Y, e.counitIso_mem_degree Y⟩

section OfFullyFaithful

variable (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] [F.Full] [F.Faithful]
  (hF : GradedEvenlyDense R F)

/-- The object chosen by graded even density.-/
def GradedEvenlyDense.obj (Y : D) : C := (hF Y).choose

/-- The isomorphism chosen by graded even density.-/
def GradedEvenlyDense.iso (Y : D) : F.obj (hF.obj F Y) ≅ Y := (hF Y).choose_spec.choose

omit [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] [F.Additive]
  [F.Linear R] [IsGradedSuperfunctor R F] [F.Full] [F.Faithful] in
/--
@isnad1 id=mem.1h5v.s9.70e2b1761578 from=translated src=- shape=28d71f16 vocab=0c8537fd
-/
theorem GradedEvenlyDense.iso_mem (Y : D) :
    (hF.iso F Y).hom ∈ parity (R := R) (F.obj (hF.obj F Y)) Y 0 :=
  (hF Y).choose_spec.choose_spec.1

omit [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] [F.Additive]
  [F.Linear R] [IsGradedSuperfunctor R F] [F.Full] [F.Faithful] in
/--
@isnad1 id=mem.1h5v.s9.45b73a769b24 from=translated src=- shape=c37025e6 vocab=21b67304
-/
theorem GradedEvenlyDense.iso_mem_degree (Y : D) :
    (hF.iso F Y).hom ∈ degree (R := R) (F.obj (hF.obj F Y)) Y 0 :=
  (hF Y).choose_spec.choose_spec.2

/-- The quasi-inverse of a full, faithful, gradedly evenly dense graded superfunctor.-/
@[simps]
def GradedEvenlyDense.inverse : D ⥤ C where
  obj := hF.obj F
  map {Y Y'} g := F.preimage ((hF.iso F Y).hom ≫ g ≫ (hF.iso F Y').inv)
  map_id Y := F.map_injective (by simp)
  map_comp f g := F.map_injective (by simp)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=additive.1h4v.s6.80140015568f from=translated src=- shape=85ed0d7c vocab=f7601cd8
-/
instance GradedEvenlyDense.inverse_additive : (hF.inverse F).Additive where
  map_add := F.map_injective (by simp)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=linear.1h4v.s7.d46b038c798c from=translated src=- shape=70e13f1f vocab=d3ba3a4f
-/
instance GradedEvenlyDense.inverse_linear : (hF.inverse F).Linear R where
  map_smul _ _ := F.map_injective (by simp [F.map_smul])

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=isgraded.1h4v.s7.f6882a79ecbf from=translated src=- shape=8197b9e8 vocab=be6111aa
-/
instance GradedEvenlyDense.inverse_isGraded : IsGradedSuperfunctor R (hF.inverse F) where
  map_mem {Y Y' p g} hg := by
    apply mem_of_map_mem F
    rw [GradedEvenlyDense.inverse_map, F.map_preimage]
    have := comp_mem (comp_mem (hF.iso_mem F Y) hg) (inv_mem _ (hF.iso_mem F Y'))
    rw [Category.assoc, zero_add, add_zero] at this
    exact this
  map_mem_degree {Y Y' n g} hg := by
    apply mem_degree_of_map_mem F
    rw [GradedEvenlyDense.inverse_map, F.map_preimage]
    have := comp_mem_degree (comp_mem_degree (hF.iso_mem_degree F Y) hg)
      (inv_mem_degree _ (hF.iso_mem_degree F Y'))
    rw [Category.assoc, zero_add, neg_zero, add_zero] at this
    exact this

set_option backward.isDefEq.respectTransparency false in
/-- A full, faithful graded superfunctor that is evenly dense in degree zero is a graded
superequivalence.-/
def GradedSuperequivalence.ofFullyFaithful : GradedSuperequivalence R F where
  inverse := hF.inverse F
  unitIso := NatIso.ofComponents (fun X => F.preimageIso (hF.iso F (F.obj X)).symm)
    (fun f => F.map_injective (by simp))
  counitIso := NatIso.ofComponents (fun Y => hF.iso F Y) (fun g => by simp)
  unitIso_mem X := by
    apply mem_of_map_mem F
    show F.map _ ∈ parity (R := R) (F.obj X) (F.obj (hF.obj F (F.obj X))) 0
    simpa using inv_mem _ (hF.iso_mem F (F.obj X))
  counitIso_mem Y := hF.iso_mem F Y
  unitIso_mem_degree X := by
    apply mem_degree_of_map_mem F
    show F.map _ ∈ degree (R := R) (F.obj X) (F.obj (hF.obj F (F.obj X))) 0
    simpa using inv_mem_degree _ (hF.iso_mem_degree F (F.obj X))
  counitIso_mem_degree Y := hF.iso_mem_degree F Y

end OfFullyFaithful

end Equivalence

/-! ## Morphisms of degree zero and the underlying category -/

section DegreeZero

/-- The supercategory with the objects of a graded supercategory and its morphisms of degree
zero.-/
@[ext]
structure DegreeZero (R : Type w) (C : Type w₁) where
  /-- The object of `C`.-/
  obj : C

namespace DegreeZero

instance : Category (DegreeZero R C) where
  Hom X Y := degree (R := R) X.obj Y.obj 0
  id X := ⟨𝟙 X.obj, id_mem_degree X.obj⟩
  comp f g := ⟨f.1 ≫ g.1, by simpa using comp_mem_degree f.2 g.2⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

/--
@isnad1 id=eq.1h6v.s9.2bcaaf3f3ce8 from=translated src=- shape=89e68acd vocab=f3db6519
-/
@[ext] theorem hom_ext {X Y : DegreeZero R C} {f g : X ⟶ Y} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

/--
@isnad1 id=eq.0h3v.s8.94a654e625ed from=translated src=- shape=391bd36c vocab=a823beb3
-/
@[simp] theorem id_val (X : DegreeZero R C) : (𝟙 X : X ⟶ X).1 = 𝟙 X.obj := rfl

/--
@isnad1 id=eq.0h7v.s10.15fccb69b081 from=translated src=- shape=b4e05003 vocab=c871f0a5
-/
@[simp] theorem comp_val {X Y Z : DegreeZero R C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

instance : Preadditive (DegreeZero R C) where
  homGroup X Y := inferInstanceAs (AddCommGroup (degree (R := R) X.obj Y.obj 0))
  add_comp _ _ _ f f' g := Subtype.ext (Preadditive.add_comp _ _ _ f.1 f'.1 g.1)
  comp_add _ _ _ f g g' := Subtype.ext (Preadditive.comp_add _ _ _ f.1 g.1 g'.1)

instance : Linear R (DegreeZero R C) where
  homModule X Y := inferInstanceAs (Module R (degree (R := R) X.obj Y.obj 0))
  smul_comp _ _ _ r f g := Subtype.ext (Linear.smul_comp _ _ _ r f.1 g.1)
  comp_smul _ _ _ f r g := Subtype.ext (Linear.comp_smul _ _ _ f.1 r g.1)

/--
@isnad1 id=eq.0h6v.s10.5f748d635350 from=translated src=- shape=380e9637 vocab=cddfd113
-/
@[simp] theorem add_val {X Y : DegreeZero R C} (f g : X ⟶ Y) : (f + g).1 = f.1 + g.1 := rfl

/--
@isnad1 id=eq.0h5v.s9.3de7cba2d91c from=translated src=- shape=76949877 vocab=67b3c174
-/
@[simp] theorem neg_val {X Y : DegreeZero R C} (f : X ⟶ Y) : (-f).1 = -f.1 := rfl

/--
@isnad1 id=eq.0h4v.s8.b1beb7260ac1 from=translated src=- shape=26afd2b5 vocab=f3db6519
-/
@[simp] theorem zero_val {X Y : DegreeZero R C} : (0 : X ⟶ Y).1 = 0 := rfl

/--
@isnad1 id=eq.0h6v.s10.bc56e789a158 from=translated src=- shape=380e9637 vocab=391a8d06
-/
@[simp] theorem sub_val {X Y : DegreeZero R C} (f g : X ⟶ Y) : (f - g).1 = f.1 - g.1 := rfl

/--
@isnad1 id=eq.0h6v.s10.9bfcacd1c123 from=translated src=- shape=b7311345 vocab=1f5bae73
-/
@[simp] theorem smul_val {X Y : DegreeZero R C} (r : R) (f : X ⟶ Y) : (r • f).1 = r • f.1 :=
  rfl

/-- The parities of morphisms of degree zero.-/
def parityZ (X Y : DegreeZero R C) (p : ZMod 2) : Submodule R (X ⟶ Y) :=
  (parity (R := R) X.obj Y.obj p).comap (degree (R := R) X.obj Y.obj 0).subtype

/--
@isnad1 id=iff.0h6v.s10.1ba5b7064e03 from=translated src=- shape=fc492ac2 vocab=84ea4bca
-/
theorem mem_parityZ {X Y : DegreeZero R C} {p : ZMod 2} {f : X ⟶ Y} :
    f ∈ parityZ X Y p ↔ f.1 ∈ parity (R := R) X.obj Y.obj p := Iff.rfl

/-- The morphisms of degree zero form a supercategory.-/
instance : Supercategory R (DegreeZero R C) where
  parity := parityZ
  isInternal X Y := by
    rw [DirectSum.isInternal_submodule_iff_isCompl _ (i := 0) (j := 1) (by decide)
      (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
    constructor
    · rw [Submodule.disjoint_def]
      intro f h0 h1
      have := proj_of_mem (R := R) (mem_parityZ.1 h0)
      rw [proj_of_mem_ne (mem_parityZ.1 h1) (by decide)] at this
      exact Subtype.ext this.symm
    · rw [codisjoint_iff, eq_top_iff]
      intro f _
      have e : f = ⟨proj R 0 f.1, proj_mem_degree 0 f.2⟩ + ⟨proj R 1 f.1, proj_mem_degree 1 f.2⟩ :=
        Subtype.ext (proj_add_proj (R := R) f.1).symm
      rw [e]
      exact Submodule.add_mem_sup (mem_parityZ.2 (proj_mem 0 _)) (mem_parityZ.2 (proj_mem 1 _))
  id_mem X := mem_parityZ.2 (id_mem X.obj)
  comp_mem hf hg := mem_parityZ.2 (comp_mem (mem_parityZ.1 hf) (mem_parityZ.1 hg))

variable (R C) in
/-- The inclusion of the morphisms of degree zero.-/
@[simps]
def ι : DegreeZero R C ⥤ C where
  obj X := X.obj
  map f := f.1

instance : (ι R C).Additive where
instance : (ι R C).Linear R where
instance : IsSuperfunctor R (ι R C) where
  map_mem hf := hf

/-- A homogeneous isomorphism of degree zero gives an isomorphism of `DegreeZero R C`.-/
@[simps]
def isoMk {X Y : C} (e : X ≅ Y) (he : e.hom ∈ degree (R := R) X Y 0) :
    (⟨X⟩ : DegreeZero R C) ≅ ⟨Y⟩ where
  hom := ⟨e.hom, he⟩
  inv := ⟨e.inv, by simpa using inv_mem_degree e he⟩
  hom_inv_id := Subtype.ext e.hom_inv_id
  inv_hom_id := Subtype.ext e.inv_hom_id

/-- The restriction of a graded superfunctor to morphisms of degree zero.-/
@[simps]
def map (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    DegreeZero R C ⥤ DegreeZero R D where
  obj X := ⟨F.obj X.obj⟩
  map f := ⟨F.map f.1, map_mem_degree F f.2⟩
  map_id X := Subtype.ext (F.map_id X.obj)
  map_comp f g := Subtype.ext (F.map_comp f.1 g.1)

instance (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    (map (R := R) F).Additive where
  map_add := Subtype.ext F.map_add

instance (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    (map (R := R) F).Linear R where
  map_smul f r := Subtype.ext (Functor.Linear.map_smul (F := F) f.1 r)

instance (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    IsSuperfunctor R (map (R := R) F) where
  map_mem hf := Supercategory.map_mem (R := R) F hf

end DegreeZero

variable (R C) in
/-- The underlying category of a graded supercategory (Brundan–Ellis, §6, after
Definition 6.1): the same objects, with only the even morphisms of degree zero.-/
abbrev GUnderlying := Underlying R (DegreeZero R C)

end DegreeZero

end GradedSupercategory

end StringDiagrams

end
