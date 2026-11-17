import Tengoku.StringDiagramsLean.StringDiagrams.Super.DrinfeldCenter
import Tengoku.StringDiagramsLean.StringDiagrams.Super.Graded
import Tengoku.Seed.Tactic.CategoryTheory.Bicategory.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Graded 2-supercategories and graded (Q, Π)-2-supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6,
Definitions 6.2, 6.3, 6.5 and Lemma 6.6.

* A *graded 2-supercategory* (`StringDiagrams.GradedTwoSupercategory`, Definition 6.2 and its
  weak version) is a 2-supercategory whose morphism supercategories are graded
  supercategories, such that horizontal composition preserves degrees and the coherence maps
  have degree `0`. In the unpacked form of `TwoSupercategory`: whiskering preserves degrees
  (`whiskerLeft_mem_degree`, `whiskerRight_mem_degree`) and the associator and unitors have
  degree `0`. A *strict graded 2-supercategory* (a category enriched in `GSCat`, Definition
  6.2) is a graded 2-supercategory with `BicategoryStruct.Strict`.
* A *graded 2-superfunctor* (`TwoSuperfunctor.IsGraded`, Definition 6.3): a 2-superfunctor
  whose superfunctors on morphism supercategories are graded and whose coherence maps `c`, `i`
  have degree `0`. The graded versions of 2-natural transformations and supermodifications,
  which the paper leaves to the reader, are `TwoNatTrans.IsGraded` (the `x_F` have degree
  `0`) and `Supermodification.IsHomogeneous` (homogeneous of a given parity and degree).
* A *graded `(Q, Π)`-2-supercategory* (`StringDiagrams.QPiTwoSupercategory`, Definition 6.5):
  a graded 2-supercategory with families of 1-morphisms `q_λ`, `q_λ⁻¹`, `π_λ` and
  2-isomorphisms `σ_λ : q_λ ⇒ 1_λ`, `σ̄_λ : q_λ⁻¹ ⇒ 1_λ`, `ζ_λ : π_λ ⇒ 1_λ`, which are even,
  even and odd of degrees `-1`, `1` and `0`. It extends `PiTwoSupercategory`
  (Definition 3.1).
* **Lemma 6.6**, stated (like Lemma 3.2 in `StringDiagrams.Super.PiTwo`) for not necessarily
  strict 2-supercategories, the unitors and associators being inserted:
  (i) `β` and `ξ` of Lemma 3.2 are even of degree zero (`β_hom_mem_degree`,
  `ξ_hom_mem_degree`); (ii) `γ_F := σ_μ F σ_λ⁻¹ : q_μ F ≅ F q_λ`
  (`QPiTwoSupercategory.γ`) is even of degree zero, supernatural (`γ_naturality`), and
  satisfies `γ_{GF} = G γ_F ∘ γ_G F` (`γ_comp`), `γ_{1_λ} = 1_{q_λ}` (`γ_id`),
  `γ_{q_λ} = 1_{q_λ²}` (`γ_q`) and `γ_{π_λ} = β_{q_λ}⁻¹` (`γ_pi`), so that `(q, γ)` is an
  object of the Drinfeld center of Definition 2.3 (`qCenterObj`), invertible since `σ` is an
  (even) isomorphism `(q, γ) ≅ 1` in the center (`centerσ`); (iii)
  `ii_λ := σ̄_λσ_λ : q_λ⁻¹ q_λ ≅ 1_λ` and `jj_λ := σ_λσ̄_λ : q_λ q_λ⁻¹ ≅ 1_λ` are even of
  degree zero with `q_λ ii_λ = jj_λ q_λ` (`q_ii`) and `ii_λ q_λ⁻¹ = q_λ⁻¹ jj_λ` (`ii_qinv`).

The identities of (ii)–(iii) involve only even 2-morphisms; they are proved in the underlying
bicategory `Underlying2 R B`, where Mathlib's bicategorical coherence applies, and transported
back.

Compositions of 1-morphisms are written in diagrammatic order: `f ≫ g` is the paper's `g f`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u w₁ w₂ v₂ u₂

/-! ## Isomorphisms `q ≅ 1` in a bicategory

Generic identities for a family of 2-isomorphisms `s_λ : q_λ ≅ 1_λ` in a (Mathlib) bicategory,
used for Lemma 6.6(ii)–(iii) through the underlying bicategory of even 2-morphisms. -/

namespace UnitIso

open Bicategory

variable {𝔅 : Type*} [Bicategory 𝔅] {a b c : 𝔅}

/-- For `s : q ≅ 1`, the two ways of contracting `q q` agree:
`s q = q s` up to unitors.
@isnad1 id=eq.0h4v.s8.792d62cb76f7 from=translated src=- shape=b7d4d62c vocab=b0619c32
-/
theorem swap (q : a ⟶ a) (s : q ≅ 𝟙 a) :
    s.hom ▷ q ≫ (λ_ q).hom = q ◁ s.hom ≫ (ρ_ q).hom := by
  rw [← cancel_mono s.hom]
  simp only [Category.assoc]
  rw [← leftUnitor_naturality, ← rightUnitor_naturality, unitors_equal]
  rw [← whisker_exchange_assoc]

variable (q : ∀ a : 𝔅, a ⟶ a) (s : ∀ a, q a ≅ 𝟙 a)

/-- The half-braiding `F q_μ ≅ q_λ F` (diagrammatic order) determined by `s`:
`F ◁ s_μ ≫ ρ_F ≫ λ_F⁻¹ ≫ s_λ⁻¹ ▷ F`.-/
def halfBraid (f : a ⟶ b) : f ≫ q b ≅ q a ≫ f :=
  whiskerLeftIso f (s b) ≪≫ ρ_ f ≪≫ (λ_ f).symm ≪≫ whiskerRightIso (s a).symm f

/--
@isnad1 id=eq.0h6v.s8.16b739f0ded0 from=translated src=- shape=e2d312d0 vocab=6d882ec4
-/
theorem halfBraid_hom (f : a ⟶ b) : (halfBraid q s f).hom =
    f ◁ (s b).hom ≫ (ρ_ f).hom ≫ (λ_ f).inv ≫ (s a).inv ▷ f := by
  simp [halfBraid]

/--
@isnad1 id=eq.0h4v.s7.5375a3dc69e2 from=translated src=- shape=12d03a65 vocab=2777880d
-/
theorem halfBraid_self (a : 𝔅) : (halfBraid q s (q a)).hom = 𝟙 _ := by
  rw [halfBraid_hom, ← reassoc_of% (swap (q a) (s a))]
  simp

/--
@isnad1 id=eq.0h4v.s8.226775422b1b from=translated src=- shape=152fb536 vocab=c0d63773
-/
theorem halfBraid_id (a : 𝔅) :
    (halfBraid q s (𝟙 a)).hom = (λ_ (q a)).hom ≫ (ρ_ (q a)).inv := by
  rw [halfBraid_hom, ← cancel_mono ((ρ_ (q a)).hom), ← cancel_mono (s a).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [rightUnitor_naturality_assoc, ← unitors_equal, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id, leftUnitor_naturality]

/--
@isnad1 id=eq.0h8v.s9.42e627b0372c from=translated src=- shape=e03c7b81 vocab=1d50152f
-/
theorem halfBraid_comp (f : a ⟶ b) (g : b ⟶ c) :
    (halfBraid q s (f ≫ g)).hom = (α_ f g (q c)).hom ≫ f ◁ (halfBraid q s g).hom ≫
      (α_ f (q b) g).inv ≫ (halfBraid q s f).hom ▷ g ≫ (α_ (q a) f g).hom := by
  rw [halfBraid_hom, halfBraid_hom, halfBraid_hom]
  simp only [Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight, Category.assoc]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, ← Bicategory.whiskerLeft_comp]
  simp only [Iso.inv_hom_id, Bicategory.whiskerLeft_id, Bicategory.id_whiskerRight, Category.id_comp]
  bicategory

variable {x : 𝔅} {q' qi : x ⟶ x} (s' : q' ≅ 𝟙 x) (t : qi ≅ 𝟙 x)

/-- `ii := s̄ s : q q⁻¹ ≅ 1` (diagrammatic order: `q` first).-/
def ii : q' ≫ qi ≅ 𝟙 x := whiskerRightIso s' qi ≪≫ λ_ qi ≪≫ t

/-- `jj := s s̄ : q⁻¹ q ≅ 1` (diagrammatic order: `q⁻¹` first).-/
def jj : qi ≫ q' ≅ 𝟙 x := whiskerRightIso t q' ≪≫ λ_ q' ≪≫ s'

/-- The paper's `q ii = jj q`.
@isnad1 id=eq.0h6v.s9.c38aaaeafc80 from=translated src=- shape=01678bde vocab=d4a042b1
-/
theorem q_ii : (ii s' t).hom ▷ q' ≫ (λ_ q').hom =
    (α_ q' qi q').hom ≫ q' ◁ (jj s' t).hom ≫ (ρ_ q').hom := by
  simp only [ii, jj, Iso.trans_hom, whiskerRightIso_hom, Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  rw [← swap q' s', whisker_exchange_assoc, whisker_exchange_assoc]
  bicategory

/-- The paper's `ii q⁻¹ = q⁻¹ jj`.
@isnad1 id=eq.0h6v.s9.b54aa4c4966b from=translated src=- shape=6ae52b56 vocab=b0ce19c7
-/
theorem ii_qinv : qi ◁ (ii s' t).hom ≫ (ρ_ qi).hom =
    (α_ qi q' qi).inv ≫ (jj s' t).hom ▷ qi ≫ (λ_ qi).hom := by
  simp only [ii, jj, Iso.trans_hom, whiskerRightIso_hom, Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  rw [← swap qi t, whisker_exchange_assoc, whisker_exchange_assoc]
  bicategory

end UnitIso

open Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

section Defs

variable (R : Type w₁) [CommRing R] (B : Type u) [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]

/-- A graded 2-supercategory (Brundan–Ellis, Definition 6.2 and the weak version after it):
a 2-supercategory whose morphism supercategories are graded, such that whiskering preserves
degrees and the coherence maps have degree `0`. It is strict if `BicategoryStruct.Strict B`
holds.-/
class GradedTwoSupercategory [TwoSupercategory R B] : Prop where
  whiskerLeft_mem_degree {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} {n : ℤ} {η : g ⟶ h} :
    η ∈ degree (R := R) g h n → f ◁ η ∈ degree (R := R) (f ≫ g) (f ≫ h) n
  whiskerRight_mem_degree {a b c : B} {f g : a ⟶ b} {n : ℤ} {η : f ⟶ g} (h : b ⟶ c) :
    η ∈ degree (R := R) f g n → η ▷ h ∈ degree (R := R) (f ≫ h) (g ≫ h) n
  associator_hom_mem_degree {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (associator f g h).hom ∈ degree (R := R) ((f ≫ g) ≫ h) (f ≫ g ≫ h) 0
  leftUnitor_hom_mem_degree {a b : B} (f : a ⟶ b) :
    (leftUnitor f).hom ∈ degree (R := R) (𝟙 a ≫ f) f 0
  rightUnitor_hom_mem_degree {a b : B} (f : a ⟶ b) :
    (rightUnitor f).hom ∈ degree (R := R) (f ≫ 𝟙 b) f 0

end Defs

namespace GradedTwoSupercategory

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B]

/-- Horizontal composition adds degrees.
@isnad1 id=mem.2h13v.s11.f7068a1b8a02 from=translated src=- shape=0f803cd6 vocab=4efa56ea
-/
theorem hcomp_mem_degree {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} {m n : ℤ} {x : f ⟶ g}
    {y : h ⟶ i} (hx : x ∈ degree (R := R) f g m) (hy : y ∈ degree (R := R) h i n) :
    hcomp x y ∈ degree (R := R) (f ≫ h) (g ≫ i) (m + n) :=
  comp_mem_degree (whiskerRight_mem_degree h hx) (whiskerLeft_mem_degree g hy)

/--
@isnad1 id=mem.0h9v.s10.13db33015d80 from=translated src=- shape=58aa47c8 vocab=a905bb60
-/
theorem associator_inv_mem_degree {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (associator f g h).inv ∈ degree (R := R) (f ≫ g ≫ h) ((f ≫ g) ≫ h) 0 := by
  simpa using inv_mem_degree _ (associator_hom_mem_degree (R := R) f g h)

/--
@isnad1 id=mem.0h5v.s9.d3285aa98657 from=translated src=- shape=727b4a94 vocab=6b435db4
-/
theorem leftUnitor_inv_mem_degree {a b : B} (f : a ⟶ b) :
    (leftUnitor f).inv ∈ degree (R := R) f (𝟙 a ≫ f) 0 := by
  simpa using inv_mem_degree _ (leftUnitor_hom_mem_degree (R := R) f)

/--
@isnad1 id=mem.0h5v.s9.205bd0b899b3 from=translated src=- shape=b2633113 vocab=579503d3
-/
theorem rightUnitor_inv_mem_degree {a b : B} (f : a ⟶ b) :
    (rightUnitor f).inv ∈ degree (R := R) f (f ≫ 𝟙 b) 0 := by
  simpa using inv_mem_degree _ (rightUnitor_hom_mem_degree (R := R) f)

end GradedTwoSupercategory

/-! ## Graded 2-superfunctors, 2-natural transformations and supermodifications -/

section Functors

variable {R : Type w} [CommRing R]
  {B : Type u} [BicategoryStruct.{w₁, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [∀ a b : C, GradedSupercategory R (a ⟶ b)]

/-- A graded 2-superfunctor (Brundan–Ellis, Definition 6.3): the superfunctors
`ℋom(λ, μ) → ℋom(ℝλ, ℝμ)` are graded, and the coherence isomorphisms `c` and `i` (which are
even) have degree `0`.-/
structure TwoSuperfunctor.IsGraded (F : TwoSuperfunctor R B C) : Prop where
  map₂_mem_degree {a b : B} {f g : a ⟶ b} {n : ℤ} {η : f ⟶ g} :
    η ∈ degree (R := R) f g n → F.map₂ η ∈ degree (R := R) (F.map f) (F.map g) n
  mapComp_hom_mem_degree {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (F.mapComp f g).hom ∈ degree (R := R) (F.map f ≫ F.map g) (F.map (f ≫ g)) 0
  mapId_hom_mem_degree (a : B) : (F.mapId a).hom ∈ degree (R := R) (𝟙 (F.obj a)) (F.map (𝟙 a)) 0

/-- The superfunctors on morphism supercategories of a graded 2-superfunctor are graded.
@isnad1 id=isgraded.1h6v.s9.a1b262829847 from=translated src=- shape=8806d4a0 vocab=0010b017
-/
theorem TwoSuperfunctor.IsGraded.isGradedSuperfunctor {F : TwoSuperfunctor R B C}
    (hF : F.IsGraded) (a b : B) : IsGradedSuperfunctor R (F.mapFunctor a b) where
  map_mem_degree := hF.map₂_mem_degree

/-- The identity 2-superfunctor is graded.
@isnad1 id=isgraded.0h2v.s7.00b4762cfac4 from=translated src=- shape=2fadfa14 vocab=4f4f78f4
-/
theorem TwoSuperfunctor.id_isGraded [TwoSupercategory R B] : (TwoSuperfunctor.id R B).IsGraded where
  map₂_mem_degree h := h
  mapComp_hom_mem_degree _ _ := id_mem_degree _
  mapId_hom_mem_degree _ := id_mem_degree _

/-- A graded 2-natural transformation: the even 2-morphisms `x_F` have degree `0` (the graded
version of Definition 2.2(iii), left to the reader in §6).-/
def TwoNatTrans.IsGraded {F G : TwoSuperfunctor R B C} (θ : TwoNatTrans F G) : Prop :=
  ∀ {a b : B} (f : a ⟶ b), θ.x f ∈ degree (R := R) (F.map f ≫ θ.X b) (θ.X a ≫ G.map f) 0

/-- A supermodification homogeneous of parity `p` and degree `n` (the graded version of
Definition 2.2(iv), left to the reader in §6).-/
def Supermodification.IsHomogeneous {F G : TwoSuperfunctor R B C} {θ θ' : TwoNatTrans F G}
    (α : Supermodification θ θ') (p : ZMod 2) (n : ℤ) : Prop :=
  ∀ a : B, α.app a ∈ parity (R := R) (θ.X a) (θ'.X a) p ∧
    α.app a ∈ degree (R := R) (θ.X a) (θ'.X a) n

end Functors

/-! ## Graded (Q, Π)-2-supercategories -/

section QPiDef

variable (R : Type w₁) [CommRing R] (B : Type u) [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B]

/-- A graded `(Q, Π)`-2-supercategory (Brundan–Ellis, Definition 6.5): a graded
2-supercategory with 1-morphisms `q_λ, q_λ⁻¹, π_λ : λ → λ` and 2-isomorphisms
`σ_λ : q_λ ⇒ 1_λ`, `σ̄_λ : q_λ⁻¹ ⇒ 1_λ`, `ζ_λ : π_λ ⇒ 1_λ` which are even, even and odd of
degrees `-1`, `1` and `0`.-/
class QPiTwoSupercategory [GradedTwoSupercategory R B] extends PiTwoSupercategory R B where
  ζ_hom_mem_degree : ∀ a : B, (ζ a).hom ∈ degree (R := R) (pi a) (𝟙 a) 0
  /-- The 1-morphisms `q_λ`.-/
  q : ∀ a : B, a ⟶ a
  /-- The 1-morphisms `q_λ⁻¹`.-/
  qinv : ∀ a : B, a ⟶ a
  /-- The 2-isomorphisms `σ_λ : q_λ ⇒ 1_λ`.-/
  σ : ∀ a : B, q a ≅ 𝟙 a
  /-- The 2-isomorphisms `σ̄_λ : q_λ⁻¹ ⇒ 1_λ`.-/
  σbar : ∀ a : B, qinv a ≅ 𝟙 a
  σ_hom_mem : ∀ a : B, (σ a).hom ∈ parity (R := R) (q a) (𝟙 a) 0
  σ_hom_mem_degree : ∀ a : B, (σ a).hom ∈ degree (R := R) (q a) (𝟙 a) (-1)
  σbar_hom_mem : ∀ a : B, (σbar a).hom ∈ parity (R := R) (qinv a) (𝟙 a) 0
  σbar_hom_mem_degree : ∀ a : B, (σbar a).hom ∈ degree (R := R) (qinv a) (𝟙 a) 1

end QPiDef

/-! ## Lemma 6.6 -/

namespace QPiTwoSupercategory

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B] [QPiTwoSupercategory R B]

open GradedTwoSupercategory PiTwoSupercategory

variable {a b c : B}

/--
@isnad1 id=mem.0h3v.s10.fbbfdddd2d14 from=translated src=- shape=b4209ea6 vocab=fcb037f3
-/
theorem σ_inv_mem (a : B) : (σ (R := R) a).inv ∈ parity (R := R) (𝟙 a) (q (R := R) a) 0 :=
  inv_mem _ (σ_hom_mem a)

/--
@isnad1 id=mem.0h3v.s9.21ef8c92f952 from=translated src=- shape=b394c6a1 vocab=5da5da56
-/
theorem σ_inv_mem_degree (a : B) :
    (σ (R := R) a).inv ∈ degree (R := R) (𝟙 a) (q (R := R) a) 1 := by
  simpa using inv_mem_degree _ (σ_hom_mem_degree (R := R) a)

/--
@isnad1 id=mem.0h3v.s10.c00b074b7ff1 from=translated src=- shape=b4209ea6 vocab=5593bec5
-/
theorem σbar_inv_mem (a : B) :
    (σbar (R := R) a).inv ∈ parity (R := R) (𝟙 a) (qinv (R := R) a) 0 :=
  inv_mem _ (σbar_hom_mem a)

/--
@isnad1 id=mem.0h3v.s9.10ae72b08c51 from=translated src=- shape=9427c2bb vocab=867d26c4
-/
theorem σbar_inv_mem_degree (a : B) :
    (σbar (R := R) a).inv ∈ degree (R := R) (𝟙 a) (qinv (R := R) a) (-1) :=
  inv_mem_degree _ (σbar_hom_mem_degree (R := R) a)

/--
@isnad1 id=mem.0h3v.s10.ace4314590dd from=translated src=- shape=ae7c872c vocab=7a93107c
-/
theorem ζ_inv_mem_degree' (a : B) :
    (ζ (R := R) a).inv ∈ degree (R := R) (𝟙 a) (pi (R := R) a) 0 := by
  simpa using inv_mem_degree _ (ζ_hom_mem_degree (R := R) a)

/-! ### (i) `β` and `ξ` have degree zero -/

/-- **Lemma 6.6(i).** `β_F` (Lemma 3.2) is even of degree zero.
@isnad1 id=mem.0h5v.s10.4b77c6198011 from=translated src=- shape=cbf1607a vocab=7b444440
-/
theorem β_hom_mem_degree (f : a ⟶ b) :
    (β (R := R) f).hom ∈ degree (R := R) (f ≫ pi (R := R) b) (pi (R := R) a ≫ f) 0 := by
  rw [β_hom]
  have h := comp_mem_degree (comp_mem_degree (comp_mem_degree
    (whiskerLeft_mem_degree f (ζ_hom_mem_degree (R := R) b))
    (rightUnitor_hom_mem_degree (R := R) f)) (leftUnitor_inv_mem_degree (R := R) f))
    (whiskerRight_mem_degree f (ζ_inv_mem_degree' (R := R) a))
  simpa [Category.assoc] using h

/-- **Lemma 6.6(i).** `ξ_λ` (Lemma 3.2(iv)) is even of degree zero.
@isnad1 id=mem.0h3v.s10.f2c78ccf1daf from=translated src=- shape=d3cca6c1 vocab=a5c872c1
-/
theorem ξ_hom_mem_degree (a : B) :
    (ξ (R := R) a).hom ∈ degree (R := R) (pi (R := R) a ≫ pi (R := R) a) (𝟙 a) 0 := by
  rw [ξ_hom]
  have h := comp_mem_degree (comp_mem_degree
    (whiskerRight_mem_degree (pi (R := R) a) (ζ_hom_mem_degree (R := R) a))
    (leftUnitor_hom_mem_degree (R := R) (pi (R := R) a))) (ζ_hom_mem_degree (R := R) a)
  simpa [Category.assoc] using h

/-! ### (ii) The half-braiding `γ` -/

/-- **Lemma 6.6(ii).** `γ_F := σ_μ F σ_λ⁻¹ : q_μ F ⇒ F q_λ` for `F : λ → μ`, in the
diagrammatic order: `F ◁ σ_μ ≫ ρ_F ≫ λ_F⁻¹ ≫ σ_λ⁻¹ ▷ F : F ≫ q_μ ≅ q_λ ≫ F`. (All maps being
even, this is the horizontal composite of `σ_λ⁻¹` and `F σ_μ` up to unitors, without sign.)-/
def γ (f : a ⟶ b) : f ≫ q (R := R) b ≅ q (R := R) a ≫ f :=
  whiskerLeftIso (R := R) f (σ (R := R) b) ≪≫ rightUnitor f ≪≫ (leftUnitor f).symm ≪≫
    whiskerRightIso (R := R) (σ (R := R) a).symm f

/--
@isnad1 id=eq.0h5v.s9.01ecc888704f from=translated src=- shape=6f071cbb vocab=f97d51e0
-/
theorem γ_hom (f : a ⟶ b) : (γ (R := R) f).hom =
    f ◁ (σ (R := R) b).hom ≫ (rightUnitor f).hom ≫ (leftUnitor f).inv ≫
      (σ (R := R) a).inv ▷ f := by
  simp [γ]

/-- **Lemma 6.6(ii).** `γ_F` is even.
@isnad1 id=mem.0h5v.s10.0b52139a1f65 from=translated src=- shape=d5362de8 vocab=4a3dc30a
-/
theorem γ_hom_mem (f : a ⟶ b) :
    (γ (R := R) f).hom ∈ parity (R := R) (f ≫ q (R := R) b) (q (R := R) a ≫ f) 0 := by
  rw [γ_hom]
  have h := comp_mem (comp_mem (comp_mem (whiskerLeft_mem f (σ_hom_mem (R := R) b))
    (rightUnitor_hom_mem (R := R) f)) (inv_mem _ (leftUnitor_hom_mem (R := R) f)))
    (whiskerRight_mem f (σ_inv_mem (R := R) a))
  simpa [Category.assoc] using h

/-- **Lemma 6.6(ii).** `γ_F` has degree zero.
@isnad1 id=mem.0h5v.s10.339493e358c9 from=translated src=- shape=16cb8ee1 vocab=68caeed5
-/
theorem γ_hom_mem_degree (f : a ⟶ b) :
    (γ (R := R) f).hom ∈ degree (R := R) (f ≫ q (R := R) b) (q (R := R) a ≫ f) 0 := by
  rw [γ_hom]
  have h := comp_mem_degree (comp_mem_degree (comp_mem_degree
    (whiskerLeft_mem_degree f (σ_hom_mem_degree (R := R) b))
    (rightUnitor_hom_mem_degree (R := R) f)) (leftUnitor_inv_mem_degree (R := R) f))
    (whiskerRight_mem_degree f (σ_inv_mem_degree (R := R) a))
  simpa [Category.assoc] using h

/-- **Lemma 6.6(ii).** `γ` is natural for all 2-morphisms `x : F ⇒ G` (of either parity):
`x q_λ ∘ γ_F = γ_G ∘ q_μ x`. Together with `γ_hom_mem`, `γ_{μ,λ}` is an even supernatural
isomorphism `q_μ - ⇒ - q_λ`.
@isnad1 id=eq.0h7v.s9.36645ad9765d from=translated src=- shape=0656bb87 vocab=1c5cffaf
-/
theorem γ_naturality {f g : a ⟶ b} (x : f ⟶ g) :
    (γ (R := R) f).hom ≫ q (R := R) a ◁ x = x ▷ q (R := R) b ≫ (γ (R := R) g).hom := by
  refine induction_on (R := R) x (by simp [zero_whiskerRight R, whiskerLeft_zero R])
    (fun p x hx => ?_) (fun x y hx hy => ?_)
  · rw [γ_hom, γ_hom]
    simp only [Category.assoc]
    have h1 := super_interchange (R := R) (σ_inv_mem (R := R) a) hx
    have h2 := super_interchange (R := R) hx (σ_hom_mem (R := R) b)
    rw [koszulSign_zero_left, one_smul] at h1
    rw [koszulSign_zero_right, one_smul] at h2
    rw [h1, ← leftUnitor_inv_naturality_assoc R, ← rightUnitor_naturality_assoc R,
      ← reassoc_of% h2]
  · rw [whiskerLeft_add (R := R), add_whiskerRight (R := R), Preadditive.comp_add,
      Preadditive.add_comp, hx, hy]

/-! #### Transport to the underlying bicategory -/

/-- `q_λ` as a 1-morphism of the underlying bicategory.-/
abbrev qU (a : Underlying2 R B) : a ⟶ a := Underlying2.hom1 (q (R := R) a.obj)

/-- `q_λ⁻¹` as a 1-morphism of the underlying bicategory.-/
abbrev qinvU (a : Underlying2 R B) : a ⟶ a := Underlying2.hom1 (qinv (R := R) a.obj)

/-- `σ_λ` as a 2-isomorphism of the underlying bicategory.-/
def σU (a : Underlying2 R B) : qU a ≅ 𝟙 a :=
  Underlying.isoMk (σ (R := R) a.obj) (σ_hom_mem a.obj)

/-- `σ̄_λ` as a 2-isomorphism of the underlying bicategory.-/
def σbarU (a : Underlying2 R B) : qinvU a ≅ 𝟙 a :=
  Underlying.isoMk (σbar (R := R) a.obj) (σbar_hom_mem a.obj)

/--
@isnad1 id=eq.0h3v.s11.657b8e4c251b from=translated src=- shape=25767e17 vocab=3f80c5a7
-/
@[simp] theorem σU_hom_val (a : Underlying2 R B) : (σU a).hom.1 = (σ (R := R) a.obj).hom := rfl

/--
@isnad1 id=eq.0h3v.s11.9c95e31badef from=translated src=- shape=60d0fb0f vocab=1da4f3a3
-/
@[simp] theorem σU_inv_val (a : Underlying2 R B) : (σU a).inv.1 = (σ (R := R) a.obj).inv := rfl

/--
@isnad1 id=eq.0h3v.s11.e127a97ee2c6 from=translated src=- shape=25767e17 vocab=f8499902
-/
@[simp] theorem σbarU_hom_val (a : Underlying2 R B) :
    (σbarU a).hom.1 = (σbar (R := R) a.obj).hom := rfl

/--
@isnad1 id=eq.0h5v.s12.14c3f85dd36b from=translated src=- shape=efe1837e vocab=060071d9
-/
theorem halfBraid_val (f : a ⟶ b) :
    (UnitIso.halfBraid (qU (R := R) (B := B)) σU (Underlying2.hom1 (a := a) (b := b) f)).hom.1 =
      (γ (R := R) f).hom := by
  rw [UnitIso.halfBraid_hom, γ_hom]
  rfl

/-- **Lemma 6.6(ii).** `γ_{GF} = G γ_F ∘ γ_G F` (with associators).
@isnad1 id=eq.0h7v.s10.4825153d8485 from=translated src=- shape=c9074a79 vocab=d324afad
-/
theorem γ_comp (f : a ⟶ b) (g : b ⟶ c) :
    (γ (R := R) (f ≫ g)).hom = (associator f g (q (R := R) c)).hom ≫ f ◁ (γ (R := R) g).hom ≫
      (associator f (q (R := R) b) g).inv ≫ (γ (R := R) f).hom ▷ g ≫
        (associator (q (R := R) a) f g).hom := by
  have h := congrArg Subtype.val (UnitIso.halfBraid_comp (qU (R := R) (B := B)) σU
    (Underlying2.hom1 (a := a) (b := b) f) (Underlying2.hom1 (a := b) (b := c) g))
  rw [← halfBraid_val, ← halfBraid_val, ← halfBraid_val]
  exact h

/-- **Lemma 6.6(ii).** `γ_{1_λ} = 1_{q_λ}` (up to unitors).
@isnad1 id=eq.0h3v.s9.a6c1aee0031f from=translated src=- shape=9ca9640f vocab=7e10c348
-/
theorem γ_id (a : B) :
    (γ (R := R) (𝟙 a)).hom = (leftUnitor (q (R := R) a)).hom ≫ (rightUnitor (q (R := R) a)).inv := by
  have h := congrArg Subtype.val (UnitIso.halfBraid_id (qU (R := R) (B := B)) σU ⟨a⟩)
  rw [← halfBraid_val]
  exact h

/-- **Lemma 6.6(ii).** `γ_{q_λ} = 1_{q_λ²}`.
@isnad1 id=eq.0h3v.s8.68248f413115 from=translated src=- shape=16d67bfc vocab=a1890612
-/
theorem γ_q (a : B) : (γ (R := R) (q (R := R) a)).hom = 𝟙 _ := by
  have h := congrArg Subtype.val (UnitIso.halfBraid_self (qU (R := R) (B := B)) σU ⟨a⟩)
  rw [← halfBraid_val]
  exact h

/-- **Lemma 6.6(ii).** `γ_{π_λ} = β_{q_λ}⁻¹`.
@isnad1 id=eq.0h3v.s9.95e0f5e042b7 from=translated src=- shape=7d0a519e vocab=d9f05611
-/
theorem γ_pi (a : B) : (γ (R := R) (pi (R := R) a)).hom = (β (R := R) (q (R := R) a)).inv := by
  rw [← cancel_mono (β (R := R) (q (R := R) a)).hom, Iso.inv_hom_id, γ_hom, β_hom]
  simp only [Category.assoc]
  have h1 := super_interchange (R := R) (σ_inv_mem (R := R) a) (ζ_hom_mem (R := R) a)
  rw [koszulSign_zero_left, one_smul] at h1
  have h2 := super_interchange (R := R) (ζ_hom_mem (R := R) a) (σ_hom_mem (R := R) a)
  rw [koszulSign_zero_right, one_smul] at h2
  rw [reassoc_of% h1, ← leftUnitor_inv_naturality_assoc R, rightUnitor_naturality_assoc R,
    ← unitors_equal R, Iso.inv_hom_id_assoc, ← rightUnitor_naturality_assoc R,
    ← reassoc_of% h2, ← unitors_equal R, leftUnitor_naturality_assoc R, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id_assoc, hom_inv_whiskerRight R]

/-! ### (iii) `ii` and `jj` -/

/-- **Lemma 6.6(iii).** `ii_λ := σ̄_λ σ_λ : q_λ⁻¹ q_λ ≅ 1_λ`, in the diagrammatic order
`q_λ ≫ q_λ⁻¹ ≅ 𝟙`: `σ_λ ▷ q_λ⁻¹ ≫ λ ≫ σ̄_λ`.-/
def ii (a : B) : q (R := R) a ≫ qinv (R := R) a ≅ 𝟙 a :=
  whiskerRightIso (R := R) (σ (R := R) a) (qinv (R := R) a) ≪≫ leftUnitor _ ≪≫ σbar (R := R) a

/-- **Lemma 6.6(iii).** `jj_λ := σ_λ σ̄_λ : q_λ q_λ⁻¹ ≅ 1_λ`, in the diagrammatic order
`q_λ⁻¹ ≫ q_λ ≅ 𝟙`: `σ̄_λ ▷ q_λ ≫ λ ≫ σ_λ`.-/
def jj (a : B) : qinv (R := R) a ≫ q (R := R) a ≅ 𝟙 a :=
  whiskerRightIso (R := R) (σbar (R := R) a) (q (R := R) a) ≪≫ leftUnitor _ ≪≫ σ (R := R) a

/--
@isnad1 id=eq.0h3v.s9.04d25e98e1db from=translated src=- shape=8567ae4b vocab=be30fbde
-/
theorem ii_hom (a : B) : (ii (R := R) a).hom = (σ (R := R) a).hom ▷ qinv (R := R) a ≫
    (leftUnitor (qinv (R := R) a)).hom ≫ (σbar (R := R) a).hom := by
  simp [ii]

/--
@isnad1 id=eq.0h3v.s9.40f53a5ed16c from=translated src=- shape=8567ae4b vocab=14a27d13
-/
theorem jj_hom (a : B) : (jj (R := R) a).hom = (σbar (R := R) a).hom ▷ q (R := R) a ≫
    (leftUnitor (q (R := R) a)).hom ≫ (σ (R := R) a).hom := by
  simp [jj]

/-- **Lemma 6.6(iii).** `ii_λ` is even.
@isnad1 id=mem.0h3v.s10.88e6036e30e5 from=translated src=- shape=cc13ef9e vocab=10ffc320
-/
theorem ii_hom_mem (a : B) : (ii (R := R) a).hom ∈ parity (R := R) _ (𝟙 a) 0 := by
  rw [ii_hom]
  simpa [Category.assoc] using comp_mem (comp_mem (whiskerRight_mem _ (σ_hom_mem (R := R) a))
    (leftUnitor_hom_mem (R := R) _)) (σbar_hom_mem (R := R) a)

/-- **Lemma 6.6(iii).** `ii_λ` has degree zero.
@isnad1 id=mem.0h3v.s10.186446629f3a from=translated src=- shape=7f853e3e vocab=8d45220a
-/
theorem ii_hom_mem_degree (a : B) : (ii (R := R) a).hom ∈ degree (R := R) _ (𝟙 a) 0 := by
  rw [ii_hom]
  have h := comp_mem_degree (comp_mem_degree
    (whiskerRight_mem_degree _ (σ_hom_mem_degree (R := R) a))
    (leftUnitor_hom_mem_degree (R := R) _)) (σbar_hom_mem_degree (R := R) a)
  simpa [Category.assoc] using h

/-- **Lemma 6.6(iii).** `jj_λ` is even.
@isnad1 id=mem.0h3v.s10.cbea9db3c01f from=translated src=- shape=cc13ef9e vocab=61c022dc
-/
theorem jj_hom_mem (a : B) : (jj (R := R) a).hom ∈ parity (R := R) _ (𝟙 a) 0 := by
  rw [jj_hom]
  simpa [Category.assoc] using comp_mem (comp_mem (whiskerRight_mem _ (σbar_hom_mem (R := R) a))
    (leftUnitor_hom_mem (R := R) _)) (σ_hom_mem (R := R) a)

/-- **Lemma 6.6(iii).** `jj_λ` has degree zero.
@isnad1 id=mem.0h3v.s10.88953856a859 from=translated src=- shape=7f853e3e vocab=e11eb1b5
-/
theorem jj_hom_mem_degree (a : B) : (jj (R := R) a).hom ∈ degree (R := R) _ (𝟙 a) 0 := by
  rw [jj_hom]
  have h := comp_mem_degree (comp_mem_degree
    (whiskerRight_mem_degree _ (σbar_hom_mem_degree (R := R) a))
    (leftUnitor_hom_mem_degree (R := R) _)) (σ_hom_mem_degree (R := R) a)
  simpa [Category.assoc] using h

/-- **Lemma 6.6(iii).** `q_λ ii_λ = jj_λ q_λ` in `Hom(q_λ q_λ⁻¹ q_λ, q_λ)` (with unitors and
the associator).
@isnad1 id=eq.0h3v.s10.2a841f53240b from=translated src=- shape=20e0a81a vocab=5131ecd3
-/
theorem q_ii (a : B) : (ii (R := R) a).hom ▷ q (R := R) a ≫ (leftUnitor (q (R := R) a)).hom =
    (associator (q (R := R) a) (qinv (R := R) a) (q (R := R) a)).hom ≫
      q (R := R) a ◁ (jj (R := R) a).hom ≫ (rightUnitor (q (R := R) a)).hom := by
  exact congrArg Subtype.val (UnitIso.q_ii (σU (R := R) (B := B) ⟨a⟩) (σbarU ⟨a⟩))

/-- **Lemma 6.6(iii).** `ii_λ q_λ⁻¹ = q_λ⁻¹ jj_λ` in `Hom(q_λ⁻¹ q_λ q_λ⁻¹, q_λ⁻¹)` (with
unitors and the associator).
@isnad1 id=eq.0h3v.s10.3951e3741fd2 from=translated src=- shape=66809cf5 vocab=fc8134bb
-/
theorem ii_qinv (a : B) : qinv (R := R) a ◁ (ii (R := R) a).hom ≫
    (rightUnitor (qinv (R := R) a)).hom =
      (associator (qinv (R := R) a) (q (R := R) a) (qinv (R := R) a)).inv ≫
        (jj (R := R) a).hom ▷ qinv (R := R) a ≫ (leftUnitor (qinv (R := R) a)).hom := by
  exact congrArg Subtype.val (UnitIso.ii_qinv (σU (R := R) (B := B) ⟨a⟩) (σbarU ⟨a⟩))

/-! ### (ii) `(q, γ)` in the Drinfeld center -/

/--
@isnad1 id=eq.0h5v.s9.85d1fb50861c from=translated src=- shape=ef3e4401 vocab=f97d51e0
-/
@[reassoc]
theorem γ_hom_comp_σ (f : a ⟶ b) :
    (γ (R := R) f).hom ≫ (σ (R := R) a).hom ▷ f =
      f ◁ (σ (R := R) b).hom ≫ (rightUnitor f).hom ≫ (leftUnitor f).inv := by
  rw [γ_hom]; simp only [Category.assoc, inv_hom_whiskerRight R, Category.comp_id]

open DrinfeldCenter MonoidalCategory

variable (R B) in
/-- **Lemma 6.6(ii).** `(q, γ)` is an object of the Drinfeld center (Definition 2.3):
`X_λ := q_λ`, `x_F := γ_F`.-/
def qCenterObj : DrinfeldCenter R B where
  toTwoNatTrans :=
    { X := q (R := R)
      x f := (γ (R := R) f).hom
      x_mem f := γ_hom_mem f
      naturality η := (γ_naturality η).symm
      x_comp f g := by
        simp only [Iso.refl_hom, TwoSuperfunctor.id_map]
        erw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.id_comp,
          Category.comp_id]
        exact γ_comp f g
      x_id a := by
        simp only [Iso.refl_hom, TwoSuperfunctor.id_obj]
        erw [id_whiskerRight (R := R), whiskerLeft_id (R := R), Category.id_comp]
        rw [γ_id]
        simp }
  isStrong f := (inferInstance : IsIso (γ (R := R) f).hom)

/--
@isnad1 id=eq.0h3v.s8.ad5aa077d632 from=translated src=- shape=ae5a2cd9 vocab=e1cf4e6c
-/
@[simp] theorem qCenterObj_X (a : B) : (qCenterObj R B).toTwoNatTrans.X a = q (R := R) a := rfl

/--
@isnad1 id=eq.0h5v.s9.cce156c50032 from=translated src=- shape=9894b04a vocab=62b012df
-/
@[simp] theorem qCenterObj_x {a b : B} (f : a ⟶ b) :
    (qCenterObj R B).toTwoNatTrans.x f = (γ (R := R) f).hom := rfl

variable (R B) in
/-- **Lemma 6.6(ii).** `σ` is an even isomorphism `(q, γ) ≅ 1` in the Drinfeld center; in
particular `(q, γ)` is an invertible object of the Drinfeld center.-/
def centerσ : qCenterObj R B ≅ 𝟙_ (DrinfeldCenter R B) where
  hom :=
    { app a := (σ (R := R) a).hom
      naturality f := by
        change (γ (R := R) f).hom ≫ (σ (R := R) _).hom ▷ f =
          f ◁ (σ (R := R) _).hom ≫ (rightUnitor f).hom ≫ (leftUnitor f).inv
        exact γ_hom_comp_σ f }
  inv :=
    { app a := (σ (R := R) a).inv
      naturality f := by
        change ((rightUnitor f).hom ≫ (leftUnitor f).inv) ≫ (σ (R := R) _).inv ▷ f =
          f ◁ (σ (R := R) _).inv ≫ (γ (R := R) f).hom
        rw [γ_hom, TwoSupercategory.whiskerLeft_inv_hom_assoc R, Category.assoc] }
  hom_inv_id := hom_ext fun a => (σ (R := R) a).hom_inv_id
  inv_hom_id := hom_ext fun a => (σ (R := R) a).inv_hom_id

/--
@isnad1 id=mem.0h2v.s10.f2ead94737fe from=translated src=- shape=ceb3a033 vocab=281d7859
-/
theorem centerσ_hom_mem :
    (centerσ R B).hom ∈ parity (R := R) (qCenterObj R B) (𝟙_ (DrinfeldCenter R B)) 0 :=
  fun a => σ_hom_mem (R := R) a

end QPiTwoSupercategory

end StringDiagrams

end
