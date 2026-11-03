import Tengoku.HodgeStructuresLean4.HodgePilot.SingularResolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# First-vertex partition endomorphisms of the singular cochain presheaf complex

For a topological space `X` and an arbitrary subset `A : Set X` this file
constructs, on the site `Opens X`:

1. the **chain-level weighting endomorphism** `keep S n P` of a term of the
   `ℚ`-coefficient chain complex of a simplicial set `S`, keeping exactly the
   simplex summands satisfying a predicate `P` (built by descending along the
   summand cofan `SSet.isColimitChainComplexXCofan`), together with its
   equivariance `keep_comm` under simplicial maps and the **finite-sum
   partition identities**: `keep_partition_pair` (two complementary
   predicates sum to the identity) and `keep_finpartition` (a Finset-indexed
   family of predicates, exactly one of which holds per simplex, sums to the
   identity — a finite sum of endomorphisms, with no infinite sum anywhere);
2. the **first-vertex partition endomorphism** `partitionEndo X A n` of a
   term of the singular cochain presheaf complex `singularPresheafComplex X`
   of `HodgePilot.SingularResolution`, weighting a singular simplex by
   whether the ambient point of its first vertex lies in `A`; restriction
   naturality holds because the first-vertex test only sees the ambient
   point (`keep_comm_opens`), and no continuity enters anywhere;
3. its vanishing `partApp_disjoint` over any open containing no point of `A`
   (the support mechanism), and the presheaf-level pair identity
   `partitionEndo_pair`;
4. the **sheafified partition endomorphism** `partitionEndoSheaf X A n`, an
   endomorphism of a term of the sheafified cochain complex
   `sheafifiedCochainComplex X` (a morphism of sheafified cochain sheaves),
   with its pair identity `partitionEndoSheaf_pair` by additivity of
   sheafification.

The entitled claim of this file, in full: *for every topological space `X`,
every subset `A`, and every degree `n`, the singular cochain presheaf complex
carries a restriction-natural first-vertex partition endomorphism which
vanishes over every `A`-disjoint open, and the weighting endomorphisms
satisfy finite-sum partition identities — complementary pairs, and
Finset-indexed exactly-one-per-simplex families, sum to the identity — at the
chain level, at the presheaf level, and (for pairs, by additivity of
sheafification) at the level of the sheafified cochain sheaves.*

**What remains open here**: the sheaf-level disjoint-vanishing statement
(vanishing of `partitionEndoSheaf` componentwise over `A`-disjoint opens),
locally-finite summation of sections of the sheafified cochain sheaves, the
`Γ`-surjectivity lemma for short exact sequences with sheafified-cochain
kernel, and the acyclicity engine are *not* approached in this file.  Every
statement below is a partition-endomorphism or finite-sum-identity
statement; no statement below is about the cohomology of anything, and no
acyclicity of anything is claimed anywhere.  The word "singular" below
refers exclusively to the genuine singular-cochain objects at the presheaf
level; the sheafified carriers are called sheafified cochain sheaves and are
never called singular.  **Nothing here identifies sheaf cohomology with
singular cohomology in any degree, and nothing here makes the Hodge
conjecture statable.**  Everything is at universe `0`, forced by the
`ModuleCat.{0} ℚ` coefficients of the house carrier.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology
  HodgePilot.SingularCohomology HodgePilot.ContractibleSingular HodgePilot.SingularResolution
open scoped Simplicial

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace HodgePilot.SingularFineness

/-! ## Chain-level weighting endomorphisms

Pure simplicial-set level: an endomorphism of each term of the `ℚ`-chain
complex of a simplicial set, keeping exactly the simplex summands satisfying
a predicate, with equivariance and the finite-sum partition identities. -/

/-- Chain-level weighting endomorphism: keep exactly the simplex summands
satisfying `P`.-/
def keep (S : SSet.{0}) (n : ℕ) (P : S _⦋n⦌ → Prop) :
    (S.chainComplex Qcoef).X n ⟶ (S.chainComplex Qcoef).X n :=
  (S.isColimitChainComplexXCofan Qcoef n).desc
    (Cofan.mk ((S.chainComplex Qcoef).X n)
      (fun σ => if P σ then S.ιChainComplex σ else 0))

set_option backward.isDefEq.respectTransparency false in
/-- The summand description of the weighting endomorphism.
@isnad1 id=eq.0h4v.s9.10b79e5b2d5a from=translated src=- shape=d194dcf2 vocab=1de122f5
-/
@[simp] lemma ι_keep (S : SSet.{0}) (n : ℕ) (P : S _⦋n⦌ → Prop) (σ : S _⦋n⦌) :
    S.ιChainComplex σ ≫ keep S n P = if P σ then S.ιChainComplex σ else 0 :=
  (S.isColimitChainComplexXCofan Qcoef n).fac _ ⟨σ⟩

set_option backward.isDefEq.respectTransparency false in
/-- Equivariance of the weighting endomorphisms under a simplicial map, for
compatible predicates.
@isnad1 id=eq.1h6v.s9.0eb6371441a0 from=translated src=- shape=a6bd8e25 vocab=9b8a613b
-/
lemma keep_comm {S T : SSet.{0}} (f : S ⟶ T) (n : ℕ)
    (P : T _⦋n⦌ → Prop) (Q : S _⦋n⦌ → Prop)
    (hPQ : ∀ σ, Q σ ↔ P (f.app (op ⦋n⦌) σ)) :
    (SSet.chainComplexMap f Qcoef).f n ≫ keep T n P
      = keep S n Q ≫ (SSet.chainComplexMap f Qcoef).f n := by
  refine SSet.chainComplex_hom_ext fun σ => ?_
  rw [SSet.ι_chainComplexMap_f_assoc, ι_keep, ← Category.assoc, ι_keep]
  by_cases h : Q σ
  · rw [ite_eq_left h, ite_eq_left ((hPQ σ).mp h), SSet.ι_chainComplexMap_f]
  · rw [ite_eq_right h, ite_eq_right (fun hP => h ((hPQ σ).mpr hP)), Limits.zero_comp]

/-- **Pair partition identity** (the minimal finite-sum organization): two
complementary predicates sum to the identity.
@isnad1 id=eq.1h4v.s9.df2e53cb33e2 from=translated src=- shape=d849aeed vocab=44fff4fc
-/
lemma keep_partition_pair (S : SSet.{0}) (n : ℕ) (P Q : S _⦋n⦌ → Prop)
    (hPQ : ∀ σ, Q σ ↔ ¬ P σ) :
    keep S n P + keep S n Q = 𝟙 ((S.chainComplex Qcoef).X n) := by
  refine SSet.chainComplex_hom_ext fun σ => ?_
  rw [Preadditive.comp_add, Category.comp_id, ι_keep, ι_keep]
  by_cases h : P σ
  · rw [ite_eq_left h, ite_eq_right (fun hQ => (hPQ σ).mp hQ h), add_zero]
  · rw [ite_eq_right h, ite_eq_left ((hPQ σ).mpr h), zero_add]

/-- **Finset partition identity**: for a finite family of predicates such
that each simplex satisfies exactly one, the weighting endomorphisms sum to
the identity — the finite-sum-per-simplex organization of the fineness
partition, with no infinite sum anywhere.
@isnad1 id=eq.1h5v.s9.e7a17efd9109 from=translated src=- shape=ceff972a vocab=c3e1e9a3
-/
lemma keep_finpartition (S : SSet.{0}) (n : ℕ) {ι' : Type} (s : Finset ι')
    (P : ι' → (S _⦋n⦌ → Prop)) (hcov : ∀ σ, ∃! i, i ∈ s ∧ P i σ) :
    ∑ i ∈ s, keep S n (P i) = 𝟙 ((S.chainComplex Qcoef).X n) := by
  refine SSet.chainComplex_hom_ext fun σ => ?_
  rw [Preadditive.comp_sum, Category.comp_id]
  obtain ⟨i₀, ⟨hi₀s, hPi₀⟩, huniq⟩ := hcov σ
  rw [Finset.sum_congr rfl (fun i _ => ι_keep S n (P i) σ),
    Finset.sum_eq_single i₀
      (fun b hb hne => ite_eq_right (fun hPb => hne (huniq b ⟨hb, hPb⟩)))
      (fun habs => absurd hi₀s habs),
    ite_eq_left hPi₀]

/-! ## The first-vertex predicate and the presheaf-level partition endomorphism

The first vertex of a singular simplex on an open subspace, its ambient
point, the membership predicate for a subset `A` of the base, and the
resulting presheaf endomorphism of a term of the singular cochain presheaf
complex. -/

/-- The chosen vertex (the `0`-th) of the topological `n`-simplex.-/
def vertexPt (n : ℕ) : ↑(SimplexCategory.toTop.{0}.obj ⦋n⦌) :=
  ULift.up ⟨Pi.single 0 1, single_mem_stdSimplex ℝ (0 : Fin (n + 1))⟩

set_option backward.isDefEq.respectTransparency false in
/-- The first vertex of a singular simplex.-/
def firstVertex {U : TopCat.{0}} {n : ℕ} (σ : (TopCat.toSSet.obj U) _⦋n⦌) : ↑U :=
  σ.down.hom (vertexPt n)

set_option backward.isDefEq.respectTransparency false in
/-- The first vertex is natural in the space.
@isnad1 id=eq.0h5v.s8.0238fe49fb2c from=translated src=- shape=8611bf9e vocab=b5cc9f25
-/
lemma firstVertex_map {V U : TopCat.{0}} (f : V ⟶ U) {n : ℕ}
    (σ : (TopCat.toSSet.obj V) _⦋n⦌) :
    firstVertex ((TopCat.toSSet.map f).app (op ⦋n⦌) σ) = f.hom (firstVertex σ) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The ambient point of a point of an open subspace.-/
def ambient {X : TopCat.{0}} {U : Opens X} (u : ↑((Opens.toTopCat X).obj U)) : ↑X :=
  u.1

/-- The first-vertex membership predicate over an open of the site.-/
def vertexPred (X : TopCat.{0}) (A : Set ↑X) (U : Opens X) (n : ℕ)
    (σ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)) _⦋n⦌) : Prop :=
  ambient (firstVertex σ) ∈ A

set_option backward.isDefEq.respectTransparency false in
/-- The ambient first vertex is invariant under restriction of opens.
@isnad1 id=eq.0h6v.s9.a6577e4ec056 from=translated src=- shape=a710c27f vocab=7a3d5376
-/
lemma ambient_firstVertex_map (X : TopCat.{0}) {V U : Opens X} (h : V ⟶ U) {n : ℕ}
    (σ : (TopCat.toSSet.obj ((Opens.toTopCat X).obj V)) _⦋n⦌) :
    ambient (firstVertex ((TopCat.toSSet.map ((Opens.toTopCat X).map h)).app (op ⦋n⦌) σ))
      = ambient (firstVertex σ) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Equivariance of the first-vertex weighting under restriction of opens
(the first-vertex test only sees the ambient point).
@isnad1 id=eq.0h6v.s10.cfebddf38d11 from=translated src=- shape=8ab615b0 vocab=eb229988
-/
lemma keep_comm_opens (X : TopCat.{0}) (A : Set ↑X) (n : ℕ) {V U : Opens X} (h : V ⟶ U) :
    (chainsFunctor.map ((Opens.toTopCat X).map h)).f n
        ≫ keep (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)) n (vertexPred X A U n)
      = keep (TopCat.toSSet.obj ((Opens.toTopCat X).obj V)) n (vertexPred X A V n)
        ≫ (chainsFunctor.map ((Opens.toTopCat X).map h)).f n :=
  keep_comm (TopCat.toSSet.map ((Opens.toTopCat X).map h)) n _ _
    (fun σ => Iff.of_eq ((congrArg (· ∈ A) (ambient_firstVertex_map X h σ)).symm))

set_option backward.isDefEq.respectTransparency false in
/-- The partition-endomorphism component at an open `U`: precomposition of a
singular cochain with the chain-level first-vertex weighting (the cochain
carrier is the hom-module, so the element *is* a morphism).-/
def partApp (X : TopCat.{0}) (A : Set ↑X) (n : ℕ) (U : Opens X) :
    ((singularPresheafComplex X).X n).obj (op U)
      ⟶ ((singularPresheafComplex X).X n).obj (op U) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun φ =>
      (keep (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)) n (vertexPred X A U n)
        ≫ (φ : (chainsFunctor.obj ((Opens.toTopCat X).obj U)).X n ⟶ Qcoef) :
        (chainsFunctor.obj ((Opens.toTopCat X).obj U)).X n ⟶ Qcoef))
    (fun _ _ => Preadditive.comp_add _ _ _ _ _ _))

set_option backward.isDefEq.respectTransparency false in
/-- **The partition endomorphism** of a term of the singular cochain presheaf
complex: a presheaf endomorphism (restriction naturality holds because the
first-vertex test is restriction-compatible).  No continuity enters anywhere.-/
def partitionEndo (X : TopCat.{0}) (A : Set ↑X) (n : ℕ) :
    (singularPresheafComplex X).X n ⟶ (singularPresheafComplex X).X n where
  app U := partApp X A n (unop U)
  naturality {U V} i := by
    ext φ
    show (keep (TopCat.toSSet.obj ((Opens.toTopCat X).obj (unop V))) n
          (vertexPred X A (unop V) n)
        ≫ ((chainsFunctor.map ((Opens.toTopCat X).map i.unop)).f n
          ≫ (φ : (chainsFunctor.obj ((Opens.toTopCat X).obj (unop U))).X n ⟶ Qcoef)) :
        (chainsFunctor.obj ((Opens.toTopCat X).obj (unop V))).X n ⟶ Qcoef)
      = ((chainsFunctor.map ((Opens.toTopCat X).map i.unop)).f n
        ≫ (keep (TopCat.toSSet.obj ((Opens.toTopCat X).obj (unop U))) n
            (vertexPred X A (unop U) n)
          ≫ (φ : (chainsFunctor.obj ((Opens.toTopCat X).obj (unop U))).X n ⟶ Qcoef)) :
        (chainsFunctor.obj ((Opens.toTopCat X).obj (unop V))).X n ⟶ Qcoef)
    rw [← Category.assoc, ← Category.assoc, keep_comm_opens]

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing on `A`-disjoint opens: over an open containing no point of `A`,
the partition endomorphism is the zero endomorphism (so its "support" is
contained in the closure of `A`).
@isnad1 id=eq.1h4v.s9.69a856f6b6c2 from=translated src=- shape=3ef223ec vocab=695eff89
-/
lemma partApp_disjoint (X : TopCat.{0}) (A : Set ↑X) (n : ℕ) (U : Opens X)
    (h : ∀ u : ↑((Opens.toTopCat X).obj U), ambient u ∉ A) :
    partApp X A n U = 0 := by
  have hk : keep (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)) n (vertexPred X A U n)
      = 0 := by
    refine SSet.chainComplex_hom_ext fun σ => ?_
    rw [ι_keep, ite_eq_right (show ¬ vertexPred X A U n σ from h (firstVertex σ)),
      Limits.comp_zero]
  ext φ
  show (keep (TopCat.toSSet.obj ((Opens.toTopCat X).obj U)) n (vertexPred X A U n)
      ≫ (φ : (chainsFunctor.obj ((Opens.toTopCat X).obj U)).X n ⟶ Qcoef) :
      (chainsFunctor.obj ((Opens.toTopCat X).obj U)).X n ⟶ Qcoef) = 0
  rw [hk, Limits.zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Pair partition identity at the presheaf level: the endomorphisms of a
complementary pair of sets sum to the identity endomorphism.
@isnad1 id=eq.0h3v.s10.de9977ae39ca from=translated src=- shape=7dc32eae vocab=253a5ccd
-/
lemma partitionEndo_pair (X : TopCat.{0}) (A : Set ↑X) (n : ℕ) :
    partitionEndo X A n + partitionEndo X Aᶜ n
      = 𝟙 ((singularPresheafComplex X).X n) := by
  refine NatTrans.ext (funext fun U => ?_)
  show (partitionEndo X A n).app U + (partitionEndo X Aᶜ n).app U
      = 𝟙 (((singularPresheafComplex X).X n).obj U)
  ext φ
  show (keep (TopCat.toSSet.obj ((Opens.toTopCat X).obj (unop U))) n
        (vertexPred X A (unop U) n)
      ≫ (φ : (chainsFunctor.obj ((Opens.toTopCat X).obj (unop U))).X n ⟶ Qcoef))
    + (keep (TopCat.toSSet.obj ((Opens.toTopCat X).obj (unop U))) n
        (vertexPred X Aᶜ (unop U) n)
      ≫ (φ : (chainsFunctor.obj ((Opens.toTopCat X).obj (unop U))).X n ⟶ Qcoef))
    = (φ : (chainsFunctor.obj ((Opens.toTopCat X).obj (unop U))).X n ⟶ Qcoef)
  rw [← Preadditive.add_comp,
    keep_partition_pair _ n (vertexPred X A (unop U) n) (vertexPred X Aᶜ (unop U) n)
      (fun σ => Set.mem_compl_iff A (ambient (firstVertex σ))),
    Category.id_comp]

/-! ## The sheafified partition endomorphism

The image of the partition endomorphism under sheafification: an endomorphism
of a term of the sheafified cochain complex, with the pair identity by
additivity of `presheafToSheaf`.  Nothing about cohomology is stated. -/

/-- The sheafified partition endomorphism of a term of the sheafified cochain
complex (a morphism of sheafified cochain sheaves; nothing about cohomology is
stated).-/
def partitionEndoSheaf (X : TopCat.{0}) (A : Set ↑X) (n : ℕ) :
    (sheafifiedCochainComplex X).X n ⟶ (sheafifiedCochainComplex X).X n :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map (partitionEndo X A n)

set_option backward.isDefEq.respectTransparency false in
/-- Pair partition identity at the sheaf level, by additivity of
sheafification (term-mode: the rewrite route trips the instance-key mismatch
between `TopCat.Presheaf` and the raw functor category).
@isnad1 id=eq.0h3v.s10.7dbc0b6cd1bc from=translated src=- shape=7dc32eae vocab=a686a739
-/
lemma partitionEndoSheaf_pair (X : TopCat.{0}) (A : Set ↑X) (n : ℕ) :
    partitionEndoSheaf X A n + partitionEndoSheaf X Aᶜ n
      = 𝟙 ((sheafifiedCochainComplex X).X n) :=
  ((Functor.map_add (presheafToSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat)).symm.trans
    ((congrArg (fun t => (presheafToSheaf (Opens.grothendieckTopology ↑X) AddCommGrpCat).map t)
      (partitionEndo_pair X A n)).trans
      (CategoryTheory.Functor.map_id _ _)) :
    partitionEndoSheaf X A n + partitionEndoSheaf X Aᶜ n
      = 𝟙 ((sheafifiedCochainComplex X).X n))

end HodgePilot.SingularFineness
