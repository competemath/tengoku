import Tengoku.StringDiagramsLean.StringDiagrams.Super.Presented
import Tengoku.StringDiagramsLean.StringDiagrams.Super.GradedTwo

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Graded presented 2-supercategories

For a presentation `P` whose relations are homogeneous both for the parity
(`Presentation.IsParityHomogeneous`) and for a `ℤ`-grading `deg : S.Gen → ℤ` of the generators
(`Presentation.IsHomogeneous deg`), the presented 2-supercategory `P.Bicat`
(`Presentation.twoSupercategory`) is a graded 2-supercategory in the sense of Brundan–Ellis,
*Monoidal supercategories*, arXiv:1603.05928v3, Definitions 6.1 and 6.2:

* each hom supercategory is a graded supercategory whose morphisms of degree `n` are the classes
  of linear combinations of diagrams of degree `n` (`Presentation.Bicat.gradedSupercategory`);
  the parity projections preserve degrees because the parity component of a linear combination
  of diagrams is a sub-sum of it (`Presentation.proj_eq_homogeneousComponent`);
* whiskerings preserve degrees and the coherence isomorphisms (equalities of words) have degree
  `0` (`Presentation.gradedTwoSupercategory`).

The monoidal case (a single region) is not treated here. The construction is used for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, where the Kac–Moody 2-supercategory is graded under the homogeneity
condition (1.31) and then passed to its `(Q, Π)`-envelope (Definition 1.6).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R] {P : Presentation.{w, v} S R}

namespace Presentation

/-- The homogeneous components for one grading preserve the homogeneous parts for another.
@isnad1 id=mem.2h12v.s11.918379fc4b5b from=translated src=- shape=8906c004 vocab=5735cc72
-/
theorem homogeneousComponent_mem_homDeg {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    {deg : S.Gen → A} {deg' : S.Gen → B} (hP : P.IsHomogeneous deg) {a b : Obj S} (d : A)
    {e : B} {x : P.obj a ⟶ P.obj b} (hx : x ∈ P.homDeg deg' a b e) :
    homogeneousComponent hP d x ∈ P.homDeg deg' a b e := by
  classical
  obtain ⟨f, hf, rfl⟩ := mem_homDeg_iff.mp hx
  rw [homogeneousComponent_lin]
  refine lin_mem_homDeg ?_
  rw [LinDiagram.mem_homDeg_iff] at hf ⊢
  intro g hg
  rw [LinDiagram.homogeneousComponent_apply] at hg
  have hmem := Finsupp.mem_support_iff.mpr hg
  rw [Finsupp.support_filter] at hmem
  exact hf g (Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hmem).1)

/-- The parity projections of the hom supercategories of `P.Bicat` are the homogeneous
components for the parity grading.
@isnad1 id=eq.1h9v.s11.54234eb80d11 from=translated src=- shape=22e4124f vocab=49fffcec
-/
theorem Bicat.proj_eq_homogeneousComponent (hP : P.IsParityHomogeneous) {l m : P.Bicat}
    {a b : l ⟶ m} (p : ZMod 2) (x : a ⟶ b) :
    letI := Bicat.supercategory hP l m
    proj R p x =
      homogeneousComponent hP p (show P.obj (Bicat.Hom.obj a) ⟶ P.obj (Bicat.Hom.obj b) from x) := by
  let _ := Bicat.supercategory hP l m
  refine Supercategory.induction_on (R := R) x ?_ ?_ ?_
  · exact (map_zero _).trans (map_zero (homogeneousComponent hP p)).symm
  · intro q g hg
    by_cases hq : q = p
    · subst hq
      exact (proj_of_mem hg).trans (homogeneousComponent_of_mem hP hg).symm
    · exact (proj_of_mem_ne hg hq).trans (homogeneousComponent_of_mem_of_ne hP hg hq).symm
  · intro g h hg hh
    exact ((map_add _ g h).trans (congrArg₂ (· + ·) hg hh)).trans
      (map_add (homogeneousComponent hP p) g h).symm

variable (deg : S.Gen → ℤ)

/-- The coherence isomorphisms of `P.Bicat` (equalities of words) have degree `0`.
@isnad1 id=mem.1h9v.s9.b1c39a522652 from=translated src=- shape=bc5e16e2 vocab=b894f79c
-/
theorem Bicat.isoOfEq_hom_mem_homDeg {A : Type*} [AddCommMonoid A] (deg : S.Gen → A)
    {l m : P.Bicat} {a b : l ⟶ m} (e : Bicat.Hom.obj a = Bicat.Hom.obj b) :
    ((Bicat.isoOfEq e).hom : a ⟶ b) ∈ P.homDeg deg (Bicat.Hom.obj a) (Bicat.Hom.obj b) 0 :=
  eqToHom_mem_homDeg (P := P) _ (congrArg P.obj e)

/-- The hom supercategories of `P.Bicat` are graded supercategories (Brundan–Ellis,
Definition 6.1) when the relations are homogeneous for the parity and for `deg`: the morphisms
of degree `n` are the classes of linear combinations of diagrams of degree `n`.-/
@[instance_reducible]
def Bicat.gradedSupercategory (hP : P.IsParityHomogeneous) (hd : P.IsHomogeneous deg)
    (l m : P.Bicat) :
    letI := Bicat.supercategory hP l m
    GradedSupercategory R (l ⟶ m) :=
  letI := Bicat.supercategory hP l m
  { degree := fun a b n => P.homDeg deg (Bicat.Hom.obj a) (Bicat.Hom.obj b) n
    isInternal_degree := fun a b => isInternal_homDeg hd (Bicat.Hom.obj a) (Bicat.Hom.obj b)
    proj_mem_degree := fun {a b} {n} {f} p hf => by
      rw [Bicat.proj_eq_homogeneousComponent hP p]
      exact homogeneousComponent_mem_homDeg hP p hf
    id_mem_degree := fun a => P.id_mem_homDeg deg (Bicat.Hom.obj a)
    comp_mem_degree := fun hf hg => comp_mem_homDeg hf hg }

end Presentation

end StringDiagrams
