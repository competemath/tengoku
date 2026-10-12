/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import Tengoku
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Foundations for the non-sofic group construction

This file develops the finite-permutation, property-T, Leavitt-algebra, and
prefix-action infrastructure used by the construction.
-/

noncomputable section

namespace SoficGroups

section

open Filter Topology

universe u v w

/-- Internal interface connecting the split non-sofic proof modules. -/
public
abbrev UnitaryRepresentation (G : Type u) (H : Type v) [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  G →* (H ≃ₗᵢ[ℂ] H)

open scoped Pointwise commutatorElement symmDiff

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure KazhdanPair (G : Type u) [Group G] where
  /-- Internal interface connecting the split non-sofic proof modules. -/
  generators : Finset G
  /-- Internal interface connecting the split non-sofic proof modules. -/
  kazhdanConstant : ℝ
  positive : 0 < kazhdanConstant
  invariant :
    ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (π : UnitaryRepresentation G H) (ξ : H),
      ‖ξ‖ = 1 →
      (∀ g ∈ generators, ‖π g ξ - ξ‖ < kazhdanConstant) →
      ∃ η : H, η ≠ 0 ∧ ∀ g : G, π g η = η

/-- Internal interface connecting the split non-sofic proof modules. -/
public
class HasPropertyT (G : Type u) [Group G] : Prop where
  exists_kazhdanPair : Nonempty (KazhdanPair.{u, v} G)

/-- The proportion of points on which two finite permutations differ. -/
public
def normalizedHamming {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) : ℝ :=
  (hammingDist (fun y => p y) (fun y => q y) : ℝ) / Fintype.card Y

@[simp]
public
theorem normalizedHamming_self {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p : Equiv.Perm Y) : normalizedHamming p p = 0 := by
  simp only [normalizedHamming, hammingDist_self, CharP.cast_eq_zero, zero_div]

/-- A finite permutation-valued approximation to a group action. -/
public
structure PermutationModel (G : Type*) [Group G] where
  /-- The cardinality of the finite model. -/
  size : ℕ
  /-- The model is nonempty. -/
  size_pos : 0 < size
  /-- The permutation assigned to each group element. -/
  action : G → Equiv.Perm (Fin size)
  /-- The identity is assigned the identity permutation. -/
  map_one : action 1 = 1

/-- Multiplication and separation hold on a prescribed finite set. -/
public
structure GoodOn {G : Type*} [Group G]
    (M : PermutationModel G) (F : Finset G) (ε : ℝ) : Prop where
  /-- The model is approximately multiplicative on the prescribed set. -/
  multiplicative : ∀ g ∈ F, ∀ h ∈ F,
    normalizedHamming (M.action (g * h)) (M.action g * M.action h) < ε
  /-- Nonidentity elements in the prescribed set stay far from the identity permutation. -/
  separated : ∀ g ∈ F, g ≠ 1 →
    1 - ε < normalizedHamming (M.action g) 1

/-- A group admitting arbitrarily accurate finite permutation models. -/
public
class Sofic (G : Type*) [Group G] : Prop where
  /-- Every finite set has a permutation model at every error strictly between zero and one. -/
  approximation : ∀ (F : Finset G) (ε : ℝ), 0 < ε → ε < 1 →
    ∃ M : PermutationModel G, GoodOn M F ε

private theorem normalizedHamming_permCongr
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (e : X ≃ Y) (p q : Equiv.Perm X) :
    normalizedHamming (e.permCongr p) (e.permCongr q) =
      normalizedHamming p q := by
  have hdist :
      hammingDist (fun y => e.permCongr p y) (fun y => e.permCongr q y) =
        hammingDist (fun x => p x) (fun x => q x) := by
    unfold hammingDist
    apply Finset.card_equiv e.symm
    intro y
    simp only [Equiv.permCongr_apply, ne_eq, e.injective.eq_iff, Finset.mem_filter, Finset.mem_univ,
      true_and]
  unfold normalizedHamming
  rw [hdist, ← Fintype.card_congr e]

private theorem hammingDist_prodCongr_refl_left
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (p q : Equiv.Perm Y) :
    hammingDist
      (fun z : X × Y => ((Equiv.refl X).prodCongr p) z)
      (fun z : X × Y => ((Equiv.refl X).prodCongr q) z) =
      Fintype.card X * hammingDist (fun y => p y) (fun y => q y) := by
  classical
  change
    (Finset.univ.filter fun z : X × Y =>
      (z.1, p z.2) ≠ (z.1, q z.2)).card =
      Fintype.card X *
        (Finset.univ.filter fun y : Y => p y ≠ q y).card
  have hfilter :
      (Finset.univ.filter fun z : X × Y =>
        (z.1, p z.2) ≠ (z.1, q z.2)) =
        (Finset.univ : Finset X) ×ˢ
          (Finset.univ.filter fun y : Y => p y ≠ q y) := by
    ext z
    simp only [ne_eq, Prod.mk.injEq, true_and, Finset.mem_filter, Finset.mem_univ,
      Finset.mem_product]
  rw [hfilter, Finset.card_product]
  rfl

private theorem normalizedHamming_prodCongr_refl_left
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (hX : Fintype.card X ≠ 0)
    (p q : Equiv.Perm Y) :
    normalizedHamming
      ((Equiv.refl X).prodCongr p) ((Equiv.refl X).prodCongr q) =
      normalizedHamming p q := by
  unfold normalizedHamming
  rw [hammingDist_prodCongr_refl_left, Fintype.card_prod, Nat.cast_mul,
    Nat.cast_mul]
  exact mul_div_mul_left _ _ (by exact_mod_cast hX)

private def amplifyModel {G : Type*} [Group G]
    (M : PermutationModel G) (k : ℕ) (hk : 0 < k) : PermutationModel G where
  size := k * M.size
  size_pos := Nat.mul_pos hk M.size_pos
  action g := finProdFinEquiv.permCongr
    ((Equiv.refl (Fin k)).prodCongr (M.action g))
  map_one := by
    ext x
    simp only [Equiv.prodCongr, Equiv.coe_refl, M.map_one, Equiv.Perm.coe_one, Prod.map_id,
      Equiv.refl_symm,
      Equiv.permCongr_apply, finProdFinEquiv_symm_apply, Equiv.coe_fn_mk, id_eq,
        finProdFinEquiv_apply_val,
      Fin.coe_modNat, Fin.coe_divNat, Nat.mod_add_div]

private theorem amplifyModel_normalizedHamming
    {G : Type*} [Group G] (M : PermutationModel G)
    (k : ℕ) (hk : 0 < k) (g h : G) :
    normalizedHamming ((amplifyModel M k hk).action g)
        ((amplifyModel M k hk).action h) =
      normalizedHamming (M.action g) (M.action h) := by
  change normalizedHamming
    (finProdFinEquiv.permCongr
      ((Equiv.refl (Fin k)).prodCongr (M.action g)))
    (finProdFinEquiv.permCongr
      ((Equiv.refl (Fin k)).prodCongr (M.action h))) = _
  rw [normalizedHamming_permCongr]
  apply normalizedHamming_prodCongr_refl_left
  simpa only [Fintype.card_fin, ne_eq] using hk.ne'

private theorem amplifyModel_multiplicative_distance
    {G : Type*} [Group G] (M : PermutationModel G)
    (k : ℕ) (hk : 0 < k) (g h : G) :
    normalizedHamming
      ((amplifyModel M k hk).action (g * h))
      ((amplifyModel M k hk).action g *
        (amplifyModel M k hk).action h) =
    normalizedHamming (M.action (g * h))
      (M.action g * M.action h) := by
  have hprod (p q : Equiv.Perm (Fin M.size)) :
      ((Equiv.refl (Fin k)).prodCongr p) *
        ((Equiv.refl (Fin k)).prodCongr q) =
      (Equiv.refl (Fin k)).prodCongr (p * q) := by
    apply Equiv.ext
    intro z
    exact Prod.ext rfl rfl
  change
    normalizedHamming
      (finProdFinEquiv.permCongr
        ((Equiv.refl (Fin k)).prodCongr (M.action (g * h))))
      (finProdFinEquiv.permCongr
        ((Equiv.refl (Fin k)).prodCongr (M.action g)) *
        finProdFinEquiv.permCongr
        ((Equiv.refl (Fin k)).prodCongr (M.action h))) = _
  rw [← Equiv.permCongr_mul, normalizedHamming_permCongr, hprod]
  apply normalizedHamming_prodCongr_refl_left
  simpa only [Fintype.card_fin, ne_eq] using hk.ne'

private theorem amplifyModel_separation_distance
    {G : Type*} [Group G] (M : PermutationModel G)
    (k : ℕ) (hk : 0 < k) (g : G) :
    normalizedHamming ((amplifyModel M k hk).action g) 1 =
      normalizedHamming (M.action g) 1 := by
  calc
    normalizedHamming ((amplifyModel M k hk).action g) 1 =
        normalizedHamming ((amplifyModel M k hk).action g)
          ((amplifyModel M k hk).action 1) := by
            rw [PermutationModel.map_one]
    _ = normalizedHamming (M.action g) (M.action 1) :=
      amplifyModel_normalizedHamming M k hk g 1
    _ = normalizedHamming (M.action g) 1 := by rw [M.map_one]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure SoficApproximation (G : Type*) [Group G] where
  /-- Internal interface connecting the split non-sofic proof modules. -/
  model : ℕ → PermutationModel G
  multiplicative : ∀ g h : G,
    Tendsto
      (fun n => normalizedHamming
        ((model n).action (g * h)) ((model n).action g * (model n).action h))
      atTop (𝓝 0)
  separated : ∀ g : G, g ≠ 1 →
    Tendsto
      (fun n => normalizedHamming ((model n).action g) 1)
      atTop (𝓝 1)

private def pullbackPermutationModel {G H : Type*} [Group G] [Group H]
    (f : H →* G) (M : PermutationModel G) : PermutationModel H where
  size := M.size
  size_pos := M.size_pos
  action h := M.action (f h)
  map_one := by simpa only [map_one] using M.map_one

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def pullbackSoficApproximation {G H : Type*} [Group G] [Group H]
    (f : H →* G) (hf : Function.Injective f)
    (A : SoficApproximation G) : SoficApproximation H where
  model n := pullbackPermutationModel f (A.model n)
  multiplicative g h := by
    convert A.multiplicative (f g) (f h) using 1
    funext n
    change
      normalizedHamming ((A.model n).action (f (g * h)))
        ((A.model n).action (f g) * (A.model n).action (f h)) =
      normalizedHamming ((A.model n).action (f g * f h))
        ((A.model n).action (f g) * (A.model n).action (f h))
    rw [map_mul]
  separated g hg := by
    have hfg : f g ≠ 1 := by
      intro he
      apply hg
      apply hf
      simpa only [map_one] using he
    convert A.separated (f g) hfg using 1
    funext n
    rfl

private def amplifyApproximation {G : Type*} [Group G]
    (A : SoficApproximation G) : SoficApproximation G where
  model n := amplifyModel (A.model n) (n + 1) (Nat.zero_lt_succ n)
  multiplicative g h := by
    simpa only [amplifyModel_multiplicative_distance] using
      A.multiplicative g h
  separated g hg := by
    simpa only [amplifyModel_separation_distance] using
      A.separated g hg

private noncomputable def multiplicationTable {G : Type*} [Group G]
    (F : Finset G) : Finset G := by
  classical
  exact F ∪ (F.product F).image (fun x : G × G => x.1 * x.2)

private theorem mem_multiplicationTable_of_mem {G : Type*} [Group G]
    {F : Finset G} {g : G} (hg : g ∈ F) : g ∈ multiplicationTable F := by
  classical
  simp only [multiplicationTable, Finset.product_eq_sprod, Finset.mem_union, hg, Finset.mem_image,
    Finset.mem_product, Prod.exists, true_or]

private theorem mul_mem_multiplicationTable {G : Type*} [Group G]
    {F : Finset G} {g h : G} (hg : g ∈ F) (hh : h ∈ F) :
    g * h ∈ multiplicationTable F := by
  classical
  change g * h ∈ F ∪ (F.product F).image (fun x : G × G => x.1 * x.2)
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr
    ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, rfl⟩

private noncomputable def tableRelators {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) :
    Finset (FreeGroup ↥(multiplicationTable F)) := by
  classical
  let oneGenerator : ↥(multiplicationTable F) :=
    ⟨1, mem_multiplicationTable_of_mem h₁⟩
  let word (x : ↥F × ↥F) : FreeGroup ↥(multiplicationTable F) :=
    FreeGroup.of ⟨x.1.1, mem_multiplicationTable_of_mem x.1.2⟩ *
      FreeGroup.of ⟨x.2.1, mem_multiplicationTable_of_mem x.2.2⟩ *
      (FreeGroup.of
        ⟨x.1.1 * x.2.1, mul_mem_multiplicationTable x.1.2 x.2.2⟩)⁻¹
  exact {FreeGroup.of oneGenerator} ∪ (F.attach.product F.attach).image word

private abbrev tableGroup {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) : Type _ :=
  PresentedGroup (tableRelators F h₁ : Set (FreeGroup ↥(multiplicationTable F)))

private noncomputable def tableGenerator {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) (g : ↥(multiplicationTable F)) :
    tableGroup F h₁ :=
  PresentedGroup.of g

private theorem tableGenerator_one {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) :
    tableGenerator F h₁ ⟨1, mem_multiplicationTable_of_mem h₁⟩ = 1 := by
  classical
  change PresentedGroup.mk _ (FreeGroup.of _) = 1
  apply PresentedGroup.one_of_mem
  change FreeGroup.of _ ∈ tableRelators F h₁
  simp only [tableRelators, Finset.product_eq_sprod, Finset.singleton_union, Finset.mem_insert,
    Finset.mem_image, Finset.mem_product, Finset.mem_attach, and_self, true_and, Prod.exists,
      Subtype.exists, true_or]

private noncomputable def tableEvaluation {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) : tableGroup F h₁ →* G := by
  classical
  apply PresentedGroup.toGroup (f := fun g : ↥(multiplicationTable F) => g.1)
  intro r hr
  change r ∈ tableRelators F h₁ at hr
  simp only [tableRelators, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_image] at hr
  rcases hr with rfl | ⟨⟨g, h⟩, _, rfl⟩
  · simp only [FreeGroup.lift_apply_of]
  · simp only [map_mul, FreeGroup.lift_apply_of, map_inv, mul_inv_rev, mul_mul_inv_mul_cancel,
    mul_inv_cancel]

@[simp]
private theorem tableEvaluation_generator {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) (g : ↥(multiplicationTable F)) :
    tableEvaluation F h₁ (tableGenerator F h₁ g) = g.1 := by
  change PresentedGroup.toGroup _ (PresentedGroup.of g) = g.1
  exact PresentedGroup.toGroup.of _

private noncomputable def tableTestSet {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F) : Finset (tableGroup F h₁) := by
  classical
  exact F.attach.image fun g =>
    tableGenerator F h₁ ⟨g.1, mem_multiplicationTable_of_mem g.2⟩

private noncomputable def pullbackTableModel {G : Type*} [Group G]
    (F : Finset G) (h₁ : 1 ∈ F)
    (M : PermutationModel (tableGroup F h₁)) : PermutationModel G := by
  classical
  refine
    { size := M.size
      size_pos := M.size_pos
      action := fun g => if hg : g ∈ multiplicationTable F then
        M.action (tableGenerator F h₁ ⟨g, hg⟩) else 1
      map_one := ?_ }
  simp only [mem_multiplicationTable_of_mem h₁, ↓reduceDIte, tableGenerator_one F h₁, M.map_one]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure LocalMultiplicativeOn {G : Type u} {H : Type v}
    [Group G] [Group H] (s : Finset G) (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ x ∈ s, ∀ y ∈ s, f (x * y) = f x * f y

/-- Internal interface connecting the split non-sofic proof modules. -/
public
class LEF (G : Type u) [Group G] : Prop where
  approximate : ∀ s : Finset G, ∃ (n : ℕ) (f : G → Equiv.Perm (Fin n)),
    Set.InjOn f (s : Set G) ∧ LocalMultiplicativeOn s f

namespace LocalMultiplicativeOn

variable {G : Type u} {H : Type v} [Group G] [Group H]

end LocalMultiplicativeOn

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def boundary {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (A : Finset V) : ℕ :=
  ∑ i : ι, (A.filter fun x => σ i x ∉ A).card

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def agreementSet {V : Type*} [Fintype V] [DecidableEq V]
    (c c' : Equiv.Perm V) : Finset V :=
  Finset.univ.filter (fun x => c x = c' x)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def permutationCommutationDefect {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (c : Equiv.Perm V) : ℕ :=
  ∑ i : ι, (Finset.univ.filter fun x => c (σ i x) ≠ σ i (c x)).card

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def inducedBoundary {V ι : Type*} [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (B E : Finset V) : ℕ :=
  ∑ i : ι, (E.filter fun x => σ i x ∉ B ∧ σ i x ∉ E).card

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def matchedRetainedSupport {V : Type*} [DecidableEq V]
    (R : Finset (Finset V)) : Finset V :=
  R.biUnion id

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def matchedCore {V : Type*} [DecidableEq V]
    (R : Finset (Finset V)) (D : Finset V → Finset V) : Finset V :=
  R.biUnion fun C => C ∩ D C

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def partitionWordCrossing {V : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U) (w : Equiv.Perm V) : Finset V :=
  U.filter (fun x => w x ∉ P.part x)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def matchedWordPreimageBad {V : Type*} [DecidableEq V]
    (U : Finset V) (R : Finset (Finset V))
    (D : Finset V → Finset V) (w : Equiv.Perm V) : Finset V :=
  U.filter (fun x => w x ∈ U \ matchedCore R D)

public
theorem exists_completion_of_internal_permutation {V : Type*}
    [Finite V]
    (p : Equiv.Perm V) (Z : Finset V) :
    ∃ q : Equiv.Perm {x : V // x ∈ Z},
      ∀ (x : V) (hx : x ∈ Z) (_hp : p x ∈ Z),
        (q ⟨x, hx⟩ : V) = p x := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let A := {x : V // x ∈ Z ∧ p x ∈ Z}
  let f : A → {x : V // x ∈ Z} := fun x => ⟨x.1, x.2.1⟩
  let g : A → {x : V // x ∈ Z} := fun x => ⟨p x.1, x.2.2⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {x : V // x ∈ Z} => (z : V)) h
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact p.injective
      (congrArg (fun z : {x : V // x ∈ Z} => (z : V)) h)
  obtain ⟨q, hq⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨q, ?_⟩
  intro x hx hp
  have h := hq (⟨x, hx, hp⟩ : A)
  exact congrArg (fun z : {x : V // x ∈ Z} => (z : V)) h

private def diagonalRadius (e : ℕ → ℕ → ℝ) (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun k => e n k < 1 / ((k : ℝ) + 1)) n

/-- Internal interface connecting the split non-sofic proof modules. -/
public
inductive LeavittGenerator where
  | s : Fin 2 → LeavittGenerator
  | t : Fin 2 → LeavittGenerator
  deriving Fintype

/-- Internal interface connecting the split non-sofic proof modules. -/
public
abbrev LeavittFree : Type := FreeAlgebra (ZMod 2) LeavittGenerator

/-- Internal interface connecting the split non-sofic proof modules. -/
public
inductive LeavittRelation : LeavittFree → LeavittFree → Prop where
  | inverse (i j : Fin 2) :
      LeavittRelation
        (FreeAlgebra.ι (ZMod 2) (.t i) * FreeAlgebra.ι (ZMod 2) (.s j))
        (if i = j then 1 else 0)
  | partition :
      LeavittRelation
        (FreeAlgebra.ι (ZMod 2) (.s 0) * FreeAlgebra.ι (ZMod 2) (.t 0) +
          FreeAlgebra.ι (ZMod 2) (.s 1) * FreeAlgebra.ι (ZMod 2) (.t 1))
        1

/-- Internal interface connecting the split non-sofic proof modules. -/
public
abbrev BinaryLeavitt : Type := RingQuot LeavittRelation

private def leavittQuotient : LeavittFree →ₐ[ZMod 2] BinaryLeavitt :=
  RingQuot.mkAlgHom (ZMod 2) LeavittRelation

private def leavittS (i : Fin 2) : BinaryLeavitt :=
  leavittQuotient (FreeAlgebra.ι (ZMod 2) (.s i))

private def leavittT (i : Fin 2) : BinaryLeavitt :=
  leavittQuotient (FreeAlgebra.ι (ZMod 2) (.t i))

private theorem leavittT_mul_S (i j : Fin 2) :
    leavittT i * leavittS j = if i = j then 1 else 0 := by
  simpa only [leavittT, leavittQuotient, leavittS, map_mul, MonoidWithZeroHom.map_ite_one_zero]
    using
    RingQuot.mkAlgHom_rel (ZMod 2) (LeavittRelation.inverse i j)

private theorem leavitt_partition :
    leavittS 0 * leavittT 0 + leavittS 1 * leavittT 1 = 1 := by
  simpa only [leavittS, leavittQuotient, Fin.isValue, leavittT, map_add, map_mul, map_one] using
    RingQuot.mkAlgHom_rel (ZMod 2) LeavittRelation.partition

private abbrev leavittSequence : Type := ℕ → ZMod 2

private def prefixOperator (i : Fin 2) : Module.End (ZMod 2) leavittSequence where
  toFun x n := if n % 2 = i.val then x (n / 2) else 0
  map_add' x y := by
    ext n
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' a x := by
    ext n
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

private def deletionOperator (i : Fin 2) : Module.End (ZMod 2) leavittSequence where
  toFun x n := x (2 * n + i.val)
  map_add' x y := by
    ext n
    rfl
  map_smul' a x := by
    ext n
    rfl

private theorem deletion_mul_prefix (i j : Fin 2) :
    deletionOperator i * prefixOperator j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> ext x n <;>
    simp [deletionOperator, prefixOperator, Module.End.mul_apply, Nat.add_mod]
  congr 1
  omega

private theorem prefix_deletion_partition :
    prefixOperator 0 * deletionOperator 0 +
      prefixOperator 1 * deletionOperator 1 = 1 := by
  ext x n
  simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply]
  change
    (if n % 2 = 0 then x (2 * (n / 2)) else 0) +
      (if n % 2 = 1 then x (2 * (n / 2) + 1) else 0) = x n
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> simp [h] <;> congr 1 <;> omega

private def leavittGeneratorAction :
    LeavittGenerator → Module.End (ZMod 2) leavittSequence
  | .s i => prefixOperator i
  | .t i => deletionOperator i

private def leavittFreeRepresentation :
    LeavittFree →ₐ[ZMod 2] Module.End (ZMod 2) leavittSequence :=
  FreeAlgebra.lift (ZMod 2) leavittGeneratorAction

private theorem leavittFreeRepresentation_respects {x y : LeavittFree}
    (h : LeavittRelation x y) :
    leavittFreeRepresentation x = leavittFreeRepresentation y := by
  cases h with
  | inverse i j =>
      simp only [leavittFreeRepresentation, map_mul, FreeAlgebra.lift_ι_apply,
        leavittGeneratorAction,
        deletion_mul_prefix, MonoidWithZeroHom.map_ite_one_zero]
  | partition =>
      simpa only [leavittFreeRepresentation, Fin.isValue, map_add, map_mul,
        FreeAlgebra.lift_ι_apply,
        leavittGeneratorAction, map_one] using prefix_deletion_partition

private def leavittRepresentation :
    BinaryLeavitt →ₐ[ZMod 2] Module.End (ZMod 2) leavittSequence :=
  RingQuot.liftAlgHom (ZMod 2)
    ⟨leavittFreeRepresentation, fun _ _ h => leavittFreeRepresentation_respects h⟩

@[simp] private theorem leavittRepresentation_S (i : Fin 2) :
    leavittRepresentation (leavittS i) = prefixOperator i := by
  simp only [leavittRepresentation, leavittFreeRepresentation, leavittS, leavittQuotient,
    RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply, leavittGeneratorAction]

@[simp] private theorem leavittRepresentation_T (i : Fin 2) :
    leavittRepresentation (leavittT i) = deletionOperator i := by
  simp only [leavittRepresentation, leavittFreeRepresentation, leavittT, leavittQuotient,
    RingQuot.liftAlgHom_mkAlgHom_apply, FreeAlgebra.lift_ι_apply, leavittGeneratorAction]

public
instance binaryLeavittNontrivial : Nontrivial BinaryLeavitt :=
  leavittRepresentation.toRingHom.domain_nontrivial

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def leavittWordS : List (Fin 2) → BinaryLeavitt
  | [] => 1
  | i :: a => leavittS i * leavittWordS a

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def leavittWordT : List (Fin 2) → BinaryLeavitt
  | [] => 1
  | i :: a => leavittWordT a * leavittT i

public
theorem leavittWordT_mul_wordS_self (a : List (Fin 2)) :
    leavittWordT a * leavittWordS a = 1 := by
  induction a with
  | nil => simp only [leavittWordT, leavittWordS, mul_one]
  | cons i a ih =>
      calc
        leavittWordT (i :: a) * leavittWordS (i :: a) =
            leavittWordT a *
              ((leavittT i * leavittS i) * leavittWordS a) := by
                simp only [leavittWordT, leavittWordS, mul_assoc]
        _ = 1 := by simp only [leavittT_mul_S, ↓reduceIte, one_mul, ih]

public
theorem leavittWordT_mul_wordS_of_incomparable
    (a b : List (Fin 2)) (hab : ¬a <+: b) (hba : ¬b <+: a) :
    leavittWordT a * leavittWordS b = 0 := by
  induction a generalizing b with
  | nil => exact (hab (by simp only [List.nil_prefix])).elim
  | cons i a ih =>
      cases b with
      | nil => exact (hba (by simp only [List.nil_prefix])).elim
      | cons j b =>
          by_cases hij : i = j
          · subst j
            have hab' : ¬a <+: b := by
              intro hp
              apply hab
              simpa only [List.cons_prefix_cons, true_and] using hp
            have hba' : ¬b <+: a := by
              intro hp
              apply hba
              simpa only [List.cons_prefix_cons, true_and] using hp
            calc
              leavittWordT (i :: a) * leavittWordS (i :: b) =
                  leavittWordT a *
                    ((leavittT i * leavittS i) * leavittWordS b) := by
                      simp only [leavittWordT, leavittWordS, mul_assoc]
              _ = leavittWordT a * leavittWordS b := by
                simp only [leavittT_mul_S, ↓reduceIte, one_mul]
              _ = 0 := ih b hab' hba'
          · calc
              leavittWordT (i :: a) * leavittWordS (j :: b) =
                  leavittWordT a *
                    ((leavittT i * leavittS j) * leavittWordS b) := by
                      simp only [leavittWordT, leavittWordS, mul_assoc]
              _ = 0 := by simp only [leavittT_mul_S, hij, ↓reduceIte, zero_mul, mul_zero]

public
theorem leavittWordS_append (a b : List (Fin 2)) :
    leavittWordS (a ++ b) = leavittWordS a * leavittWordS b := by
  induction a with
  | nil => simp only [List.nil_append, leavittWordS, one_mul]
  | cons i a ih => simp only [List.cons_append, leavittWordS, ih, mul_assoc]

public
theorem leavittWordT_append (a b : List (Fin 2)) :
    leavittWordT (a ++ b) = leavittWordT b * leavittWordT a := by
  induction a with
  | nil => simp only [List.nil_append, leavittWordT, mul_one]
  | cons i a ih => simp only [List.cons_append, leavittWordT, ih, mul_assoc]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def leavittCylinder (a : List (Fin 2)) : BinaryLeavitt :=
  leavittWordS a * leavittWordT a

private theorem leavittCylinder_split (a : List (Fin 2)) :
    leavittCylinder a =
      leavittCylinder (a ++ [0]) + leavittCylinder (a ++ [1]) := by
  calc
    leavittCylinder a =
        leavittWordS a *
          (leavittS 0 * leavittT 0 + leavittS 1 * leavittT 1) *
          leavittWordT a := by
            rw [leavitt_partition]
            simp only [leavittCylinder, mul_one]
    _ = leavittCylinder (a ++ [0]) + leavittCylinder (a ++ [1]) := by
      simp only [Fin.isValue, mul_add, add_mul, mul_assoc, leavittCylinder, leavittWordS_append,
        leavittWordS,
        mul_one, leavittWordT_append, leavittWordT, one_mul]

namespace MatrixCorner

variable {ι A : Type*} [Fintype ι] [Ring A]

private def codeIdempotent (s t : ι → A) : A := ∑ i, s i * t i

private def encode (s t : ι → A) (M : Matrix ι ι A) : A :=
  ∑ i, ∑ j, s i * M i j * t j

private def decode (s t : ι → A) (x : A) : Matrix ι ι A :=
  fun i j => t i * x * s j

private theorem decode_encode [DecidableEq ι] (s t : ι → A)
    (h : ∀ i j, t i * s j = if i = j then 1 else 0)
    (M : Matrix ι ι A) : decode s t (encode s t M) = M := by
  ext i j
  change t i * (∑ k, ∑ l, s k * M k l * t l) * s j = M i j
  calc
    t i * (∑ k, ∑ l, s k * M k l * t l) * s j =
        ∑ k, ∑ l, (t i * s k) * M k l * (t l * s j) := by
          simp only [mul_assoc, Finset.mul_sum, Finset.sum_mul]
    _ = M i j := by simp only [h, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ,
                      ↓reduceIte, Finset.sum_ite_eq]

private theorem encode_decode (s t : ι → A) (x : A) :
    encode s t (decode s t x) =
      codeIdempotent s t * x * codeIdempotent s t := by
  change
    (∑ i, ∑ j, s i * (t i * x * s j) * t j) =
      (∑ i, s i * t i) * x * (∑ j, s j * t j)
  calc
    (∑ i, ∑ j, s i * (t i * x * s j) * t j) =
        ∑ i, ∑ j, (s i * t i) * x * (s j * t j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          simp only [mul_assoc]
    _ = (∑ i, s i * t i) * x * (∑ j, s j * t j) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

private theorem codeIdempotent_isIdempotent [DecidableEq ι] (s t : ι → A)
    (h : ∀ i j, t i * s j = if i = j then 1 else 0) :
    IsIdempotentElem (codeIdempotent s t) := by
  change (∑ i, s i * t i) * (∑ i, s i * t i) = ∑ i, s i * t i
  calc
    (∑ i, s i * t i) * (∑ i, s i * t i) =
        ∑ i, ∑ j, s i * (t i * s j) * t j := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp only [mul_assoc]
    _ = ∑ i, s i * t i := by simp only [h, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

private theorem encode_one [DecidableEq ι] (s t : ι → A) :
    encode s t (1 : Matrix ι ι A) = codeIdempotent s t := by
  simp only [encode, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, codeIdempotent]

private theorem encode_mul [DecidableEq ι] (s t : ι → A)
    (h : ∀ i j, t i * s j = if i = j then 1 else 0)
    (M N : Matrix ι ι A) :
    encode s t (M * N) = encode s t M * encode s t N := by
  symm
  calc
    encode s t M * encode s t N =
        ∑ i, ∑ j, ∑ k, ∑ l,
          s i * M i j * (t j * s k) * N k l * t l := by
            change
              (∑ i, ∑ j, s i * M i j * t j) *
                (∑ k, ∑ l, s k * N k l * t l) = _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            simp only [mul_assoc]
    _ = ∑ i, ∑ j, ∑ l, s i * M i j * N j l * t l := by
      simp only [h, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_irrel,
        Finset.sum_const_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    _ = ∑ i, ∑ l, ∑ j, s i * M i j * N j l * t l := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = encode s t (M * N) := by
      simp only [encode, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simp only [mul_assoc]

private def ringEquiv [DecidableEq ι] (s t : ι → A)
    (h : ∀ i j, t i * s j = if i = j then 1 else 0) :
    Matrix ι ι A ≃+* (codeIdempotent_isIdempotent s t h).Corner where
  toFun M :=
    ⟨encode s t M, ⟨encode s t M, by
      change
        codeIdempotent s t * encode s t M * codeIdempotent s t =
          encode s t M
      rw [← encode_decode, decode_encode s t h]⟩⟩
  invFun x := decode s t x.1
  left_inv M := decode_encode s t h M
  right_inv x := Subtype.ext <| by
    change encode s t (decode s t x.1) = x.1
    rw [encode_decode]
    have hx :=
      (Subsemigroup.mem_corner_iff
        (codeIdempotent_isIdempotent s t h)).mp x.property
    rw [hx.1, hx.2]
  map_mul' M N := Subtype.ext (encode_mul s t h M N)
  map_add' M N := Subtype.ext <| by
    change encode s t (M + N) = encode s t M + encode s t N
    simp only [encode, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

end MatrixCorner

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure BinaryPrefixCode (ι : Type*) where
  /-- Internal interface connecting the split non-sofic proof modules. -/
  word : ι → List (Fin 2)
  prefix_free : ∀ ⦃i j⦄, i ≠ j → ¬word i <+: word j

private theorem binaryPrefixCode_orthogonal {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) (i j : ι) :
    leavittWordT (E.word i) * leavittWordS (E.word j) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [leavittWordT_mul_wordS_self, ↓reduceIte]
  · simp only [hij, ↓reduceIte]
    exact leavittWordT_mul_wordS_of_incomparable _ _
      (E.prefix_free hij) (E.prefix_free (Ne.symm hij))

private def binaryPrefixCornerEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    Matrix ι ι BinaryLeavitt ≃+*
      (MatrixCorner.codeIdempotent_isIdempotent
        (fun i => leavittWordS (E.word i))
        (fun i => leavittWordT (E.word i))
        (binaryPrefixCode_orthogonal E)).Corner :=
  MatrixCorner.ringEquiv
    (fun i => leavittWordS (E.word i))
    (fun i => leavittWordT (E.word i))
    (binaryPrefixCode_orthogonal E)

private def prefixTable {ι : Type*} [Fintype ι]
    (source target : BinaryPrefixCode ι) : BinaryLeavitt :=
  ∑ i, leavittWordS (target.word i) * leavittWordT (source.word i)

private theorem prefixTable_mul_reverse {ι : Type*} [Fintype ι]
    (source target : BinaryPrefixCode ι) :
    prefixTable source target * prefixTable target source =
      MatrixCorner.codeIdempotent
        (fun i => leavittWordS (target.word i))
        (fun i => leavittWordT (target.word i)) := by
  classical
  change
    (∑ i, leavittWordS (target.word i) * leavittWordT (source.word i)) *
        (∑ j, leavittWordS (source.word j) * leavittWordT (target.word j)) =
      ∑ i, leavittWordS (target.word i) * leavittWordT (target.word i)
  calc
    (∑ i, leavittWordS (target.word i) * leavittWordT (source.word i)) *
        (∑ j, leavittWordS (source.word j) * leavittWordT (target.word j)) =
        ∑ i, ∑ j,
          leavittWordS (target.word i) *
            (leavittWordT (source.word i) *
              leavittWordS (source.word j)) *
            leavittWordT (target.word j) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              simp only [mul_assoc]
    _ = ∑ i, leavittWordS (target.word i) *
          leavittWordT (target.word i) := by
      simp only [binaryPrefixCode_orthogonal, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]

private def prefixTableUnit {ι : Type*} [Fintype ι]
    (source target : BinaryPrefixCode ι)
    (hsource : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (source.word i))
      (fun i => leavittWordT (source.word i)) = 1)
    (htarget : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (target.word i))
      (fun i => leavittWordT (target.word i)) = 1) : BinaryLeavittˣ where
  val := prefixTable source target
  inv := prefixTable target source
  val_inv := (prefixTable_mul_reverse source target).trans htarget
  inv_val := (prefixTable_mul_reverse target source).trans hsource

private def alphaWord : Fin 3 → List (Fin 2)
  | 0 => [0, 0, 0]
  | 1 => [0, 0, 1]
  | _ => [0, 1]

private def betaWord : Fin 3 → List (Fin 2)
  | 0 => [1, 0, 0, 0]
  | 1 => [1, 0, 0, 1]
  | _ => [1, 0, 1]

private def nuWord : Fin 3 → List (Fin 2)
  | 0 => [1, 1, 0, 0]
  | 1 => [1, 1, 0, 1]
  | _ => [1, 1, 1]

private def etaWord : Fin 3 → List (Fin 2)
  | 0 => [1, 0, 0]
  | 1 => [1, 0, 1]
  | _ => [1, 1]

private def nineWord : Fin 9 → List (Fin 2)
  | 0 => alphaWord 0
  | 1 => betaWord 0
  | 2 => nuWord 0
  | 3 => alphaWord 1
  | 4 => betaWord 1
  | 5 => nuWord 1
  | 6 => alphaWord 2
  | 7 => betaWord 2
  | _ => nuWord 2

private def uWord : Fin 9 → List (Fin 2)
  | 0 => alphaWord 0 ++ [0]
  | 1 => alphaWord 0 ++ [1]
  | 2 => etaWord 0
  | 3 => alphaWord 1 ++ [0]
  | 4 => alphaWord 1 ++ [1]
  | 5 => etaWord 1
  | 6 => alphaWord 2 ++ [0]
  | 7 => alphaWord 2 ++ [1]
  | _ => etaWord 2

private def vWord : Fin 9 → List (Fin 2)
  | 0 => alphaWord 0 ++ [0]
  | 1 => etaWord 0
  | 2 => alphaWord 0 ++ [1]
  | 3 => alphaWord 1 ++ [0]
  | 4 => etaWord 1
  | 5 => alphaWord 1 ++ [1]
  | 6 => alphaWord 2 ++ [0]
  | 7 => etaWord 2
  | _ => alphaWord 2 ++ [1]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def alphaPrefixCode : BinaryPrefixCode (Fin 3) where
  word := alphaWord
  prefix_free := by decide

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def ninePrefixCode : BinaryPrefixCode (Fin 9) where
  word := nineWord
  prefix_free := by decide

private def uPrefixCode : BinaryPrefixCode (Fin 9) where
  word := uWord
  prefix_free := by decide

private def vPrefixCode : BinaryPrefixCode (Fin 9) where
  word := vWord
  prefix_free := by decide

private theorem alpha_cylinders :
    leavittCylinder (alphaWord 0) +
        leavittCylinder (alphaWord 1) +
        leavittCylinder (alphaWord 2) =
      leavittCylinder [0] := by
  have h₀₀ :
      leavittCylinder [0, 0, 0] + leavittCylinder [0, 0, 1] =
        leavittCylinder [0, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [0,
      0]).symm
  have h₀ :
      leavittCylinder [0, 0] + leavittCylinder [0, 1] =
        leavittCylinder [0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split
      [0]).symm
  change
    leavittCylinder [0, 0, 0] +
        leavittCylinder [0, 0, 1] +
        leavittCylinder [0, 1] = leavittCylinder [0]
  rw [h₀₀, h₀]

private theorem beta_cylinders :
    leavittCylinder (betaWord 0) +
        leavittCylinder (betaWord 1) +
        leavittCylinder (betaWord 2) =
      leavittCylinder [1, 0] := by
  have h₁₀₀ :
      leavittCylinder [1, 0, 0, 0] + leavittCylinder [1, 0, 0, 1] =
        leavittCylinder [1, 0, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 0,
      0]).symm
  have h₁₀ :
      leavittCylinder [1, 0, 0] + leavittCylinder [1, 0, 1] =
        leavittCylinder [1, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1,
      0]).symm
  change
    leavittCylinder [1, 0, 0, 0] +
        leavittCylinder [1, 0, 0, 1] +
        leavittCylinder [1, 0, 1] = leavittCylinder [1, 0]
  rw [h₁₀₀, h₁₀]

private theorem nu_cylinders :
    leavittCylinder (nuWord 0) +
        leavittCylinder (nuWord 1) +
        leavittCylinder (nuWord 2) =
      leavittCylinder [1, 1] := by
  have h₁₁₀ :
      leavittCylinder [1, 1, 0, 0] + leavittCylinder [1, 1, 0, 1] =
        leavittCylinder [1, 1, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 1,
      0]).symm
  have h₁₁ :
      leavittCylinder [1, 1, 0] + leavittCylinder [1, 1, 1] =
        leavittCylinder [1, 1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1,
      1]).symm
  change
    leavittCylinder [1, 1, 0, 0] +
        leavittCylinder [1, 1, 0, 1] +
        leavittCylinder [1, 1, 1] = leavittCylinder [1, 1]
  rw [h₁₁₀, h₁₁]

private theorem eta_cylinders :
    leavittCylinder (etaWord 0) +
        leavittCylinder (etaWord 1) +
        leavittCylinder (etaWord 2) =
      leavittCylinder [1] := by
  have h₁₀ :
      leavittCylinder [1, 0, 0] + leavittCylinder [1, 0, 1] =
        leavittCylinder [1, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1,
      0]).symm
  have h₁ :
      leavittCylinder [1, 0] + leavittCylinder [1, 1] =
        leavittCylinder [1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split
      [1]).symm
  change
    leavittCylinder [1, 0, 0] +
        leavittCylinder [1, 0, 1] +
        leavittCylinder [1, 1] = leavittCylinder [1]
  rw [h₁₀, h₁]

private theorem ninePrefixCode_complete :
    MatrixCorner.codeIdempotent
      (fun i => leavittWordS (ninePrefixCode.word i))
      (fun i => leavittWordT (ninePrefixCode.word i)) = 1 := by
  change (∑ i : Fin 9, leavittCylinder (nineWord i)) = 1
  have h₁ :
      leavittCylinder [1, 0] + leavittCylinder [1, 1] =
        leavittCylinder [1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split
      [1]).symm
  have hroot : leavittCylinder [0] + leavittCylinder [1] = 1 := by
    simpa only [leavittCylinder, leavittWordS, Fin.isValue, mul_one, leavittWordT, one_mul] using
      leavitt_partition
  calc
    (∑ i : Fin 9, leavittCylinder (nineWord i)) =
        (leavittCylinder (alphaWord 0) +
          leavittCylinder (alphaWord 1) +
          leavittCylinder (alphaWord 2)) +
        (leavittCylinder (betaWord 0) +
          leavittCylinder (betaWord 1) +
          leavittCylinder (betaWord 2)) +
        (leavittCylinder (nuWord 0) +
          leavittCylinder (nuWord 1) +
          leavittCylinder (nuWord 2)) := by
          simp only [nineWord, Fin.isValue, Fin.sum_univ_succ, Fin.succ_ne_zero, imp_self,
            Fin.succ_zero_eq_one,
            Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique, Fin.default_eq_zero,
              Finset.sum_singleton]
          ac_rfl
    _ = leavittCylinder [0] +
          leavittCylinder [1, 0] + leavittCylinder [1, 1] := by
      rw [alpha_cylinders, beta_cylinders, nu_cylinders]
    _ = leavittCylinder [0] + leavittCylinder [1] := by
      rw [add_assoc, h₁]
    _ = 1 := hroot

private theorem uPrefixCode_complete :
    MatrixCorner.codeIdempotent
      (fun i => leavittWordS (uPrefixCode.word i))
      (fun i => leavittWordT (uPrefixCode.word i)) = 1 := by
  change (∑ i : Fin 9, leavittCylinder (uWord i)) = 1
  have h₀ :
      leavittCylinder (alphaWord 0 ++ [0]) +
          leavittCylinder (alphaWord 0 ++ [1]) =
        leavittCylinder (alphaWord 0) :=
    (leavittCylinder_split (alphaWord 0)).symm
  have h₁ :
      leavittCylinder (alphaWord 1 ++ [0]) +
          leavittCylinder (alphaWord 1 ++ [1]) =
        leavittCylinder (alphaWord 1) :=
    (leavittCylinder_split (alphaWord 1)).symm
  have h₂ :
      leavittCylinder (alphaWord 2 ++ [0]) +
          leavittCylinder (alphaWord 2 ++ [1]) =
        leavittCylinder (alphaWord 2) :=
    (leavittCylinder_split (alphaWord 2)).symm
  have hroot : leavittCylinder [0] + leavittCylinder [1] = 1 := by
    simpa only [leavittCylinder, leavittWordS, Fin.isValue, mul_one, leavittWordT, one_mul] using
      leavitt_partition
  calc
    (∑ i : Fin 9, leavittCylinder (uWord i)) =
        ((leavittCylinder (alphaWord 0 ++ [0]) +
            leavittCylinder (alphaWord 0 ++ [1])) +
          (leavittCylinder (alphaWord 1 ++ [0]) +
            leavittCylinder (alphaWord 1 ++ [1])) +
          (leavittCylinder (alphaWord 2 ++ [0]) +
            leavittCylinder (alphaWord 2 ++ [1]))) +
        (leavittCylinder (etaWord 0) +
          leavittCylinder (etaWord 1) +
          leavittCylinder (etaWord 2)) := by
          simp only [uWord, Fin.isValue, Fin.sum_univ_succ, Fin.succ_ne_zero, imp_self,
            Fin.succ_zero_eq_one,
            Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique, Fin.default_eq_zero,
              Finset.sum_singleton]
          ac_rfl
    _ = (leavittCylinder (alphaWord 0) +
          leavittCylinder (alphaWord 1) +
          leavittCylinder (alphaWord 2)) + leavittCylinder [1] := by
      rw [h₀, h₁, h₂, eta_cylinders]
    _ = leavittCylinder [0] + leavittCylinder [1] := by
      rw [alpha_cylinders]
    _ = 1 := hroot

private theorem vPrefixCode_complete :
    MatrixCorner.codeIdempotent
      (fun i => leavittWordS (vPrefixCode.word i))
      (fun i => leavittWordT (vPrefixCode.word i)) = 1 := by
  change (∑ i : Fin 9, leavittCylinder (vWord i)) = 1
  calc
    (∑ i : Fin 9, leavittCylinder (vWord i)) =
        ∑ i : Fin 9, leavittCylinder (uWord i) := by
          simp only [vWord, Fin.isValue, Fin.sum_univ_succ, Fin.succ_ne_zero, imp_self,
            Fin.succ_zero_eq_one,
            Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique, Fin.default_eq_zero,
              Finset.sum_singleton, uWord,
            add_right_inj]
          ac_rfl
    _ = 1 := uPrefixCode_complete

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def compressionU : BinaryLeavittˣ :=
  prefixTableUnit ninePrefixCode uPrefixCode
    ninePrefixCode_complete uPrefixCode_complete

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def compressionV : BinaryLeavittˣ :=
  prefixTableUnit ninePrefixCode vPrefixCode
    ninePrefixCode_complete vPrefixCode_complete

private instance binaryLeavittCharP : CharP BinaryLeavitt 2 :=
  CharP.of_ringHom_of_ne_zero
    (algebraMap (ZMod 2) BinaryLeavitt) 2 (by decide)

private theorem matrixUnitTransport_root
    {A ι : Type*} [Ring A] [Fintype ι] [DecidableEq ι]
    (sSource tSource sTarget tTarget : ι → A)
    (hsource : ∀ i j, tSource i * sSource j = if i = j then 1 else 0)
    (i j : ι) (a : A) :
    (∑ k, sTarget k * tSource k) *
        (sSource i * a * tSource j) *
        (∑ k, sSource k * tTarget k) =
      sTarget i * a * tTarget j := by
  have hleft :
      (∑ k, sTarget k * tSource k) * sSource i = sTarget i := by
    calc
      (∑ k, sTarget k * tSource k) * sSource i =
          ∑ k, sTarget k * (tSource k * sSource i) := by
            simp only [Finset.sum_mul, mul_assoc]
      _ = sTarget i := by simp only [hsource, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
  have hright :
      tSource j * (∑ k, sSource k * tTarget k) = tTarget j := by
    calc
      tSource j * (∑ k, sSource k * tTarget k) =
          ∑ k, (tSource j * sSource k) * tTarget k := by
            simp only [Finset.mul_sum, mul_assoc]
      _ = tTarget j := by simp only [hsource, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
  calc
    (∑ k, sTarget k * tSource k) *
        (sSource i * a * tSource j) *
        (∑ k, sSource k * tTarget k) =
        ((∑ k, sTarget k * tSource k) * sSource i) * a *
          (tSource j * (∑ k, sSource k * tTarget k)) := by
            simp only [mul_assoc]
    _ = sTarget i * a * tTarget j := by rw [hleft, hright]

private theorem prefixTable_transport_root {ι : Type*}
    [Fintype ι]
    (source target : BinaryPrefixCode ι) (i j : ι)
    (a : BinaryLeavitt) :
    prefixTable source target *
        (leavittWordS (source.word i) * a *
          leavittWordT (source.word j)) *
        prefixTable target source =
      leavittWordS (target.word i) * a * leavittWordT (target.word j) := by
  classical
  exact matrixUnitTransport_root
    (fun k => leavittWordS (source.word k))
    (fun k => leavittWordT (source.word k))
    (fun k => leavittWordS (target.word k))
    (fun k => leavittWordT (target.word k))
    (binaryPrefixCode_orthogonal source) i j a

private theorem compressionU_conjugate_root (i j : Fin 9) (a : BinaryLeavitt) :
    (compressionU : BinaryLeavitt) *
        (leavittWordS (nineWord i) * a * leavittWordT (nineWord j)) *
        (↑(compressionU⁻¹) : BinaryLeavitt) =
      leavittWordS (uWord i) * a * leavittWordT (uWord j) := by
  exact prefixTable_transport_root ninePrefixCode uPrefixCode i j a

private theorem compressionV_conjugate_root (i j : Fin 9) (a : BinaryLeavitt) :
    (compressionV : BinaryLeavitt) *
        (leavittWordS (nineWord i) * a * leavittWordT (nineWord j)) *
        (↑(compressionV⁻¹) : BinaryLeavitt) =
      leavittWordS (vWord i) * a * leavittWordT (vWord j) := by
  exact prefixTable_transport_root ninePrefixCode vPrefixCode i j a

private def alphaNineIndex (i : Fin 3) : Fin 9 :=
  ⟨3 * i.val, by omega⟩

@[simp]
private theorem nineWord_alphaNineIndex (i : Fin 3) :
    nineWord (alphaNineIndex i) = alphaWord i := by
  fin_cases i <;> rfl

@[simp]
private theorem uWord_alphaNineIndex (i : Fin 3) :
    uWord (alphaNineIndex i) = alphaWord i ++ [0] := by
  fin_cases i <;> rfl

@[simp]
private theorem vWord_alphaNineIndex (i : Fin 3) :
    vWord (alphaNineIndex i) = alphaWord i ++ [0] := by
  fin_cases i <;> rfl

private theorem compressionU_conjugate_alpha_root
    (i j : Fin 3) (a : BinaryLeavitt) :
    (compressionU : BinaryLeavitt) *
        (leavittWordS (alphaWord i) * a * leavittWordT (alphaWord j)) *
        (↑(compressionU⁻¹) : BinaryLeavitt) =
      leavittWordS (alphaWord i ++ [0]) * a *
        leavittWordT (alphaWord j ++ [0]) := by
  simpa only [nineWord_alphaNineIndex, uWord_alphaNineIndex] using
    compressionU_conjugate_root (alphaNineIndex i) (alphaNineIndex j) a

private theorem compressionV_conjugate_alpha_root
    (i j : Fin 3) (a : BinaryLeavitt) :
    (compressionV : BinaryLeavitt) *
        (leavittWordS (alphaWord i) * a * leavittWordT (alphaWord j)) *
        (↑(compressionV⁻¹) : BinaryLeavitt) =
      leavittWordS (alphaWord i ++ [0]) * a *
        leavittWordT (alphaWord j ++ [0]) := by
  simpa only [nineWord_alphaNineIndex, vWord_alphaNineIndex] using
    compressionV_conjugate_root (alphaNineIndex i) (alphaNineIndex j) a

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def alphaZeroPrefixCode : BinaryPrefixCode (Fin 3) where
  word i := alphaWord i ++ [0]
  prefix_free := by decide

private def prefixElementaryUnit {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) (i j : ι) (hij : i ≠ j)
    (a : BinaryLeavitt) : BinaryLeavittˣ := by
  let x := leavittWordS (E.word i) * a * leavittWordT (E.word j)
  have hzero : leavittWordT (E.word j) * leavittWordS (E.word i) = 0 := by
    simpa only [hij.symm, ↓reduceIte] using binaryPrefixCode_orthogonal E j i
  have hx : x * x = 0 := by
    dsimp [x]
    calc
      (leavittWordS (E.word i) * a * leavittWordT (E.word j)) *
          (leavittWordS (E.word i) * a * leavittWordT (E.word j)) =
        leavittWordS (E.word i) * a *
          (leavittWordT (E.word j) * leavittWordS (E.word i)) *
          a * leavittWordT (E.word j) := by
            simp only [mul_assoc]
      _ = 0 := by rw [hzero]; simp only [mul_zero, zero_mul]
  exact
    { val := 1 + x
      inv := 1 - x
      val_inv := by noncomm_ring [hx]
      inv_val := by noncomm_ring [hx] }

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def prefixElementaryGroup {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) : Subgroup BinaryLeavittˣ :=
  Subgroup.closure
    {z | ∃ (i j : ι) (h : i ≠ j) (a : BinaryLeavitt),
      prefixElementaryUnit E i j h a = z}

private theorem compressionU_conjugate_alpha_elementaryUnit
    (i j : Fin 3) (hij : i ≠ j) (a : BinaryLeavitt) :
    MulAut.conj compressionU
        (prefixElementaryUnit alphaPrefixCode i j hij a) =
      prefixElementaryUnit alphaZeroPrefixCode i j hij a := by
  apply Units.ext
  change
    (compressionU : BinaryLeavitt) *
        (1 + leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionU⁻¹) : BinaryLeavitt) =
      1 + leavittWordS (alphaWord i ++ [0]) * a *
        leavittWordT (alphaWord j ++ [0])
  calc
    (compressionU : BinaryLeavitt) *
        (1 + leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionU⁻¹) : BinaryLeavitt) =
      1 + (compressionU : BinaryLeavitt) *
        (leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionU⁻¹) : BinaryLeavitt) := by
          simp only [mul_add, mul_one, add_mul, Units.mul_inv]
    _ = 1 + leavittWordS (alphaWord i ++ [0]) * a *
          leavittWordT (alphaWord j ++ [0]) := by
      rw [compressionU_conjugate_alpha_root]

private theorem compressionV_conjugate_alpha_elementaryUnit
    (i j : Fin 3) (hij : i ≠ j) (a : BinaryLeavitt) :
    MulAut.conj compressionV
        (prefixElementaryUnit alphaPrefixCode i j hij a) =
      prefixElementaryUnit alphaZeroPrefixCode i j hij a := by
  apply Units.ext
  change
    (compressionV : BinaryLeavitt) *
        (1 + leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionV⁻¹) : BinaryLeavitt) =
      1 + leavittWordS (alphaWord i ++ [0]) * a *
        leavittWordT (alphaWord j ++ [0])
  calc
    (compressionV : BinaryLeavitt) *
        (1 + leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionV⁻¹) : BinaryLeavitt) =
      1 + (compressionV : BinaryLeavitt) *
        (leavittWordS (alphaWord i) * a *
          leavittWordT (alphaWord j)) *
        (↑(compressionV⁻¹) : BinaryLeavitt) := by
          simp only [mul_add, mul_one, add_mul, Units.mul_inv]
    _ = 1 + leavittWordS (alphaWord i ++ [0]) * a *
          leavittWordT (alphaWord j ++ [0]) := by
      rw [compressionV_conjugate_alpha_root]

private theorem prefixElementaryGroup_map_conj
    {ι : Type*} [DecidableEq ι]
    (E E' : BinaryPrefixCode ι) (g : BinaryLeavittˣ)
    (hconj : ∀ (i j : ι) (hij : i ≠ j) (a : BinaryLeavitt),
      MulAut.conj g (prefixElementaryUnit E i j hij a) =
        prefixElementaryUnit E' i j hij a) :
    (prefixElementaryGroup E).map (MulAut.conj g).toMonoidHom =
      prefixElementaryGroup E' := by
  unfold prefixElementaryGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨i, j, hij, a, rfl⟩, hz⟩
    exact ⟨i, j, hij, a, (hconj i j hij a).symm.trans hz⟩
  · rintro ⟨i, j, hij, a, rfl⟩
    exact ⟨prefixElementaryUnit E i j hij a,
      ⟨i, j, hij, a, rfl⟩, hconj i j hij a⟩

public
theorem compressionU_map_alphaPrefixElementaryGroup :
    (prefixElementaryGroup alphaPrefixCode).map
        (MulAut.conj compressionU).toMonoidHom =
      prefixElementaryGroup alphaZeroPrefixCode :=
  prefixElementaryGroup_map_conj alphaPrefixCode alphaZeroPrefixCode
    compressionU compressionU_conjugate_alpha_elementaryUnit

public
theorem compressionV_map_alphaPrefixElementaryGroup :
    (prefixElementaryGroup alphaPrefixCode).map
        (MulAut.conj compressionV).toMonoidHom =
      prefixElementaryGroup alphaZeroPrefixCode :=
  prefixElementaryGroup_map_conj alphaPrefixCode alphaZeroPrefixCode
    compressionV compressionV_conjugate_alpha_elementaryUnit

private theorem alphaZero_prefixElementaryUnit_eq
    (i j : Fin 3) (hij : i ≠ j) (a : BinaryLeavitt) :
    prefixElementaryUnit alphaZeroPrefixCode i j hij a =
      prefixElementaryUnit alphaPrefixCode i j hij
        (leavittS 0 * a * leavittT 0) := by
  apply Units.ext
  change
    1 + leavittWordS (alphaWord i ++ [0]) * a *
      leavittWordT (alphaWord j ++ [0]) =
    1 + leavittWordS (alphaWord i) *
      (leavittS 0 * a * leavittT 0) * leavittWordT (alphaWord j)
  simp only [Fin.isValue, leavittWordS_append, leavittWordS, mul_one, mul_assoc,
    leavittWordT_append,
    leavittWordT, one_mul]

public
theorem alphaZero_prefixElementaryGroup_le :
    prefixElementaryGroup alphaZeroPrefixCode ≤
      prefixElementaryGroup alphaPrefixCode := by
  rw [prefixElementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  rw [alphaZero_prefixElementaryUnit_eq]
  exact Subgroup.subset_closure
    ⟨i, j, hij, leavittS 0 * a * leavittT 0, rfl⟩

section NoncommutativeElementaryGroup

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

private theorem single_mul_self_eq_zero (i j : ι) (h : i ≠ j) (a : R) :
    Matrix.single i j a * Matrix.single i j a = 0 :=
  Matrix.single_mul_single_of_ne (c := a) i j i h.symm a

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def elementaryUnit (i j : ι) (h : i ≠ j) (a : R) : (Matrix ι ι R)ˣ where
  val := 1 + Matrix.single i j a
  inv := 1 - Matrix.single i j a
  val_inv := by
    have hx := single_mul_self_eq_zero i j h a
    noncomm_ring [hx]
  inv_val := by
    have hx := single_mul_self_eq_zero i j h a
    noncomm_ring [hx]

@[simp] private theorem elementaryUnit_zero (i j : ι) (h : i ≠ j) :
    elementaryUnit (R := R) i j h 0 = 1 := by
  apply Units.ext
  simp only [elementaryUnit, Matrix.single_zero, add_zero, sub_zero, Units.val_one]

private theorem elementaryUnit_mul (i j : ι) (h : i ≠ j) (a b : R) :
    elementaryUnit i j h a * elementaryUnit i j h b =
      elementaryUnit i j h (a + b) := by
  apply Units.ext
  change
    (1 + Matrix.single i j a) * (1 + Matrix.single i j b) =
      1 + Matrix.single i j (a + b)
  have hab : Matrix.single i j a * Matrix.single i j b = 0 :=
    Matrix.single_mul_single_of_ne (c := a) i j i h.symm b
  rw [Matrix.single_add]
  noncomm_ring [hab]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def elementaryGroup (ι R : Type*) [Fintype ι] [DecidableEq ι] [Ring R] :
    Subgroup (Matrix ι ι R)ˣ :=
  Subgroup.closure
    {z | ∃ (i j : ι) (h : i ≠ j) (a : R), elementaryUnit i j h a = z}

public
theorem elementaryUnit_mem (i j : ι) (h : i ≠ j) (a : R) :
    elementaryUnit i j h a ∈ elementaryGroup ι R :=
  Subgroup.subset_closure ⟨i, j, h, a, rfl⟩

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def elementaryRootHom (i j : ι) (h : i ≠ j) :
    Multiplicative R →* elementaryGroup ι R where
  toFun a := ⟨elementaryUnit i j h a.toAdd, elementaryUnit_mem i j h a.toAdd⟩
  map_one' := by
    apply Subtype.ext
    exact elementaryUnit_zero i j h
  map_mul' a b := by
    apply Subtype.ext
    exact (elementaryUnit_mul i j h a.toAdd b.toAdd).symm

private theorem cylinder_transposition_factorization [CharP R 2] (P Q : R)
    (hPP : P * P = 0) (hPQP : P * Q * P = P) :
    (1 + P) * (1 + Q) * (1 + P) =
      1 - P * Q - Q * P + P + Q := by
  simp only [CharTwo.sub_eq_add]
  have hthree : (3 : ℤ) • P = P := by
    rw [zsmul_eq_mul, CharTwo.intCast_eq_mod]
    norm_num
  noncomm_ring [hPP, hPQP]
  simp only [hthree]

public
theorem elementaryUnit_commutator (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅elementaryUnit i j hij a, elementaryUnit j k hjk b⁆ =
      elementaryUnit i k hik (a * b) := by
  apply Units.ext
  change
    (1 + Matrix.single i j a) * (1 + Matrix.single j k b) *
      (1 - Matrix.single i j a) * (1 - Matrix.single j k b) =
      1 + Matrix.single i k (a * b)
  have hxx := single_mul_self_eq_zero i j hij a
  have hyy := single_mul_self_eq_zero j k hjk b
  have hyx : Matrix.single j k b * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne (c := b) j k i hik.symm a
  have hxy : Matrix.single i j a * Matrix.single j k b =
      Matrix.single i k (a * b) :=
    Matrix.single_mul_single_same (c := a) i j k b
  have hzx : Matrix.single i k (a * b) * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne (c := a * b) i k i hik.symm a
  have hzy : Matrix.single i k (a * b) * Matrix.single j k b = 0 :=
    Matrix.single_mul_single_of_ne (c := a * b) i k j hjk.symm b
  have hzz := single_mul_self_eq_zero i k hik (a * b)
  noncomm_ring [hxx, hyy, hyx, hxy, hzx, hzy, hzz]

public
theorem elementaryUnit_mem_of_two_step
    (H : Subgroup (Matrix ι ι R)ˣ) (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : R)
    (hleft : elementaryUnit i j hij a ∈ H)
    (hright : elementaryUnit j k hjk 1 ∈ H) :
    elementaryUnit i k hik a ∈ H := by
  have hc : ⁅elementaryUnit i j hij a, elementaryUnit j k hjk 1⁆ ∈ H := by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hleft hright) (H.inv_mem hleft))
      (H.inv_mem hright)
  rw [elementaryUnit_commutator i j k hij hjk hik a 1] at hc
  simpa only [mul_one] using hc

end NoncommutativeElementaryGroup

section FiniteGeneration

variable {R : Type*} [Ring R]

private noncomputable def finiteElementaryGenerators [DecidableEq R]
    (n : ℕ) (s : Finset R) : Finset (Matrix (Fin n) (Fin n) R)ˣ :=
  Finset.univ.biUnion (fun i : Fin n =>
    Finset.univ.biUnion (fun j : Fin n =>
      if h : i ≠ j then (insert 1 s).image (elementaryUnit i j h) else ∅))

variable [Algebra (ZMod 2) R]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def elementaryCoefficientSubalgebra (n : ℕ) (hn : 2 < n)
    (H : Subgroup (Matrix (Fin n) (Fin n) R)ˣ)
    (hunit : ∀ (i j : Fin n) (h : i ≠ j), elementaryUnit i j h (1 : R) ∈ H) :
    Subalgebra (ZMod 2) R where
  carrier :=
    {a | ∀ (i j : Fin n) (h : i ≠ j), elementaryUnit i j h a ∈ H}
  add_mem' := by
    intro a b ha hb i j hij
    rw [← elementaryUnit_mul]
    exact H.mul_mem (ha i j hij) (hb i j hij)
  mul_mem' := by
    intro a b ha hb i j hij
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
    have hik : i ≠ k := hki.symm
    have hleft := ha i k hik
    have hright := hb k j hkj
    have hc : ⁅elementaryUnit i k hik a, elementaryUnit k j hkj b⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem
        (H.mul_mem (H.mul_mem hleft hright) (H.inv_mem hleft))
        (H.inv_mem hright)
    rw [elementaryUnit_commutator i k j hik hkj hij a b] at hc
    exact hc
  algebraMap_mem' := by
    intro z
    have hz : z = 0 ∨ z = 1 := by
      fin_cases z
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hz with rfl | rfl
    · intro i j hij
      simpa only [map_zero, elementaryUnit_zero] using H.one_mem
    · intro i j hij
      simpa only [map_one] using hunit i j hij

end FiniteGeneration

/-- Internal interface connecting the split non-sofic proof modules. -/
public
abbrev binaryLeavittElementaryGroup (n : ℕ) : Type :=
  elementaryGroup (Fin n) BinaryLeavitt

private def completePrefixMatrixEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (hcomplete : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i)) = 1) :
    Matrix ι ι BinaryLeavitt ≃+* BinaryLeavitt where
  toFun := MatrixCorner.encode
    (fun i => leavittWordS (E.word i))
    (fun i => leavittWordT (E.word i))
  invFun := MatrixCorner.decode
    (fun i => leavittWordS (E.word i))
    (fun i => leavittWordT (E.word i))
  left_inv := MatrixCorner.decode_encode _ _ (binaryPrefixCode_orthogonal E)
  right_inv x := by
    rw [MatrixCorner.encode_decode, hcomplete]
    simp only [one_mul, mul_one]
  map_mul' := MatrixCorner.encode_mul _ _ (binaryPrefixCode_orthogonal E)
  map_add' M N := by
    simp only [MatrixCorner.encode, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

private def completePrefixUnitEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (hcomplete : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i)) = 1) :
    (Matrix ι ι BinaryLeavitt)ˣ ≃* BinaryLeavittˣ :=
  Units.mapEquiv (completePrefixMatrixEquiv E hcomplete).toMulEquiv

private theorem completePrefixUnitEquiv_elementaryUnit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (hcomplete : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i)) = 1)
    (i j : ι) (hij : i ≠ j) (a : BinaryLeavitt) :
    completePrefixUnitEquiv E hcomplete (elementaryUnit i j hij a) =
      prefixElementaryUnit E i j hij a := by
  apply Units.ext
  change
    MatrixCorner.encode
      (fun k => leavittWordS (E.word k))
      (fun k => leavittWordT (E.word k))
      (1 + Matrix.single i j a) =
        1 + leavittWordS (E.word i) * a * leavittWordT (E.word j)
  have h₁ :
      MatrixCorner.encode
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))
        (1 : Matrix ι ι BinaryLeavitt) = 1 := by
    rw [MatrixCorner.encode_one, hcomplete]
  calc
    MatrixCorner.encode
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))
        (1 + Matrix.single i j a) =
      MatrixCorner.encode
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))
        (1 : Matrix ι ι BinaryLeavitt) +
      MatrixCorner.encode
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))
        (Matrix.single i j a) := by
          simp only [MatrixCorner.encode, Matrix.add_apply, mul_add, add_mul,
            Finset.sum_add_distrib]
    _ = 1 + leavittWordS (E.word i) * a * leavittWordT (E.word j) := by
      rw [h₁]
      simp only [MatrixCorner.encode, Matrix.single_apply, ite_and, mul_ite, mul_zero, ite_mul,
        zero_mul,
        Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero]

private theorem completePrefixElementaryGroup_map
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (hcomplete : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i)) = 1) :
    (elementaryGroup ι BinaryLeavitt).map
        (completePrefixUnitEquiv E hcomplete).toMonoidHom =
      prefixElementaryGroup E := by
  unfold elementaryGroup prefixElementaryGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨i, j, hij, a, rfl⟩, hz⟩
    exact ⟨i, j, hij, a,
      (completePrefixUnitEquiv_elementaryUnit E hcomplete i j hij a).symm.trans hz⟩
  · rintro ⟨i, j, hij, a, rfl⟩
    exact ⟨elementaryUnit i j hij a, ⟨i, j, hij, a, rfl⟩,
      completePrefixUnitEquiv_elementaryUnit E hcomplete i j hij a⟩

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def ninePrefixElementaryGroupEquiv :
    binaryLeavittElementaryGroup 9 ≃* prefixElementaryGroup ninePrefixCode :=
  ((completePrefixUnitEquiv ninePrefixCode ninePrefixCode_complete).subgroupMap
      (elementaryGroup (Fin 9) BinaryLeavitt)).trans
    (MulEquiv.subgroupCongr
      (completePrefixElementaryGroup_map ninePrefixCode ninePrefixCode_complete))

private def idempotentCornerUnitExtension {A : Type*} [Ring A]
    {e : A} (he : IsIdempotentElem e) : he.Cornerˣ →* Aˣ where
  toFun u :=
    { val := u.val.val + (1 - e)
      inv := u.inv.val + (1 - e)
      val_inv := by
        have hu := (Subsemigroup.mem_corner_iff he).mp u.val.property
        have hv := (Subsemigroup.mem_corner_iff he).mp u.inv.property
        have huv : u.val.val * u.inv.val = e := by
          have h := congrArg (fun z : he.Corner => z.val) u.val_inv
          exact h
        noncomm_ring [he.eq, hu.1, hu.2, hv.1, hv.2, huv]
      inv_val := by
        have hu := (Subsemigroup.mem_corner_iff he).mp u.val.property
        have hv := (Subsemigroup.mem_corner_iff he).mp u.inv.property
        have hvu : u.inv.val * u.val.val = e := by
          have h := congrArg (fun z : he.Corner => z.val) u.inv_val
          exact h
        noncomm_ring [he.eq, hu.1, hu.2, hv.1, hv.2, hvu] }
  map_one' := by
    apply Units.ext
    change e + (1 - e) = 1
    noncomm_ring
  map_mul' u v := by
    apply Units.ext
    have hu := (Subsemigroup.mem_corner_iff he).mp u.val.property
    have hv := (Subsemigroup.mem_corner_iff he).mp v.val.property
    change
      u.val.val * v.val.val + (1 - e) =
        (u.val.val + (1 - e)) * (v.val.val + (1 - e))
    noncomm_ring [he.eq, hu.1, hu.2, hv.1, hv.2]

private theorem idempotentCornerUnitExtension_injective
    {A : Type*} [Ring A] {e : A} (he : IsIdempotentElem e) :
    Function.Injective (idempotentCornerUnitExtension he) := by
  intro u v huv
  apply Units.ext
  apply Subtype.ext
  have h := congrArg (fun z : Aˣ => (z : A)) huv
  change u.val.val + (1 - e) = v.val.val + (1 - e) at h
  exact add_right_cancel h

private def prefixCornerUnitHom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    (Matrix ι ι BinaryLeavitt)ˣ →* BinaryLeavittˣ :=
  (idempotentCornerUnitExtension
    (MatrixCorner.codeIdempotent_isIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i))
      (binaryPrefixCode_orthogonal E))).comp
    (Units.mapEquiv (binaryPrefixCornerEquiv E).toMulEquiv).toMonoidHom

private theorem prefixCornerUnitHom_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    Function.Injective (prefixCornerUnitHom E) := by
  exact (idempotentCornerUnitExtension_injective
    (MatrixCorner.codeIdempotent_isIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i))
      (binaryPrefixCode_orthogonal E))).comp
    (Units.mapEquiv (binaryPrefixCornerEquiv E).toMulEquiv).injective

private theorem prefixCornerUnitHom_elementaryUnit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a : BinaryLeavitt) :
    prefixCornerUnitHom E (elementaryUnit i j hij a) =
      prefixElementaryUnit E i j hij a := by
  apply Units.ext
  change
    MatrixCorner.encode
      (fun k => leavittWordS (E.word k))
      (fun k => leavittWordT (E.word k))
      (1 + Matrix.single i j a) +
      (1 - MatrixCorner.codeIdempotent
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))) =
      1 + leavittWordS (E.word i) * a * leavittWordT (E.word j)
  have henc :
      MatrixCorner.encode
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k))
        (1 + Matrix.single i j a) =
      MatrixCorner.codeIdempotent
        (fun k => leavittWordS (E.word k))
        (fun k => leavittWordT (E.word k)) +
        leavittWordS (E.word i) * a * leavittWordT (E.word j) := by
    calc
      MatrixCorner.encode
          (fun k => leavittWordS (E.word k))
          (fun k => leavittWordT (E.word k))
          (1 + Matrix.single i j a) =
        MatrixCorner.encode
          (fun k => leavittWordS (E.word k))
          (fun k => leavittWordT (E.word k))
          (1 : Matrix ι ι BinaryLeavitt) +
        MatrixCorner.encode
          (fun k => leavittWordS (E.word k))
          (fun k => leavittWordT (E.word k))
          (Matrix.single i j a) := by
            simp only [MatrixCorner.encode, Matrix.add_apply, mul_add, add_mul,
              Finset.sum_add_distrib]
      _ = MatrixCorner.codeIdempotent
          (fun k => leavittWordS (E.word k))
          (fun k => leavittWordT (E.word k)) +
          leavittWordS (E.word i) * a * leavittWordT (E.word j) := by
            rw [MatrixCorner.encode_one]
            simp only [MatrixCorner.encode, Matrix.single_apply, ite_and, mul_ite, mul_zero,
              ite_mul, zero_mul,
              Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
                Finset.sum_const_zero]
  rw [henc]
  noncomm_ring

private theorem prefixCornerElementaryGroup_map
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    (elementaryGroup ι BinaryLeavitt).map (prefixCornerUnitHom E) =
      prefixElementaryGroup E := by
  unfold elementaryGroup prefixElementaryGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨i, j, hij, a, rfl⟩, hz⟩
    exact ⟨i, j, hij, a,
      (prefixCornerUnitHom_elementaryUnit E i j hij a).symm.trans hz⟩
  · rintro ⟨i, j, hij, a, rfl⟩
    exact ⟨elementaryUnit i j hij a, ⟨i, j, hij, a, rfl⟩,
      prefixCornerUnitHom_elementaryUnit E i j hij a⟩

private def alphaPrefixElementaryGroupEquiv :
    binaryLeavittElementaryGroup 3 ≃* prefixElementaryGroup alphaPrefixCode :=
  ((elementaryGroup (Fin 3) BinaryLeavitt).equivMapOfInjective
      (prefixCornerUnitHom alphaPrefixCode)
      (prefixCornerUnitHom_injective alphaPrefixCode)).trans
    (MulEquiv.subgroupCongr
      (prefixCornerElementaryGroup_map alphaPrefixCode))

namespace SourceGeneration

open scoped commutatorElement

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def sourceGeneratedGroup : Subgroup BinaryLeavittˣ :=
  Subgroup.closure
    ((prefixElementaryGroup alphaPrefixCode : Set BinaryLeavittˣ) ∪
      {compressionU, compressionV})

private def betaNineIndex (i : Fin 3) : Fin 9 :=
  ⟨3 * i.val + 1, by omega⟩

private def nuNineIndex (i : Fin 3) : Fin 9 :=
  ⟨3 * i.val + 2, by omega⟩

@[simp] private theorem nineWord_betaNineIndex (i : Fin 3) :
    nineWord (betaNineIndex i) = betaWord i := by
  fin_cases i <;> rfl

@[simp] private theorem nineWord_nuNineIndex (i : Fin 3) :
    nineWord (nuNineIndex i) = nuWord i := by
  fin_cases i <;> rfl

@[simp] private theorem uWord_betaNineIndex (i : Fin 3) :
    uWord (betaNineIndex i) = alphaWord i ++ [1] := by
  fin_cases i <;> rfl

@[simp] private theorem vWord_nuNineIndex (i : Fin 3) :
    vWord (nuNineIndex i) = alphaWord i ++ [1] := by
  fin_cases i <;> rfl

private def alphaBetaNineIndex (p : Fin 2) (i : Fin 3) : Fin 9 :=
  ⟨3 * i.val + p.val, by omega⟩

@[simp] private theorem nineWord_alphaBetaNineIndex (p : Fin 2) (i : Fin 3) :
    nineWord (alphaBetaNineIndex p i) =
      if p = 0 then alphaWord i else betaWord i := by
  fin_cases p <;> fin_cases i <;> rfl

private def prefixElementaryEntry {ι : Type*} (E : BinaryPrefixCode ι)
    (i j : ι) (a : BinaryLeavitt) : BinaryLeavitt :=
  leavittWordS (E.word i) * a * leavittWordT (E.word j)

private def alphaNuNineIndex (p : Fin 2) (i : Fin 3) : Fin 9 :=
  ⟨3 * i.val + 2 * p.val, by omega⟩

@[simp] private theorem nineWord_alphaNuNineIndex (p : Fin 2) (i : Fin 3) :
    nineWord (alphaNuNineIndex p i) =
      if p = 0 then alphaWord i else nuWord i := by
  fin_cases p <;> fin_cases i <;> rfl

private theorem alphaNineIndex_ne {i j : Fin 3} (hij : i ≠ j) :
    alphaNineIndex i ≠ alphaNineIndex j := by
  intro h
  apply hij
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 3 * i.val = 3 * j.val at hv
  omega

private theorem alphaPrefixElementaryUnit_eq_nine
    (i j : Fin 3) (hij : i ≠ j) (a : BinaryLeavitt) :
    prefixElementaryUnit alphaPrefixCode i j hij a =
      prefixElementaryUnit ninePrefixCode
        (alphaNineIndex i) (alphaNineIndex j)
        (alphaNineIndex_ne hij) a := by
  apply Units.ext
  change
    1 + leavittWordS (alphaWord i) * a * leavittWordT (alphaWord j) =
      1 + leavittWordS (nineWord (alphaNineIndex i)) * a *
        leavittWordT (nineWord (alphaNineIndex j))
  rw [nineWord_alphaNineIndex, nineWord_alphaNineIndex]

public
theorem alphaPrefixElementaryGroup_le_nine :
    prefixElementaryGroup alphaPrefixCode ≤
      prefixElementaryGroup ninePrefixCode := by
  rw [prefixElementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  rw [alphaPrefixElementaryUnit_eq_nine]
  exact Subgroup.subset_closure
    ⟨alphaNineIndex i, alphaNineIndex j, alphaNineIndex_ne hij, a, rfl⟩

end SourceGeneration

private noncomputable def midrankFirstMoment (a : ℝ) : List ℝ → ℝ
  | [] => 0
  | p :: ps => p * (a + p / 2) + midrankFirstMoment (a + p) ps

private noncomputable def midrankSecondMoment (a : ℝ) : List ℝ → ℝ
  | [] => 0
  | p :: ps => p * (a + p / 2) ^ 2 + midrankSecondMoment (a + p) ps

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def midrankVariance (ps : List ℝ) : ℝ :=
  midrankSecondMoment 0 ps - (midrankFirstMoment 0 ps) ^ 2

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def componentRankMass {V : Type*}
    (C : Finset V) (b : V → ℤ) (j : ℤ) : ℝ :=
  ((C.filter fun x => b x = j).card : ℝ) / (C.card : ℝ)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def componentVertexMidrank {V : Type*}
    (C : Finset V) (b : V → ℤ) (x : V) : ℝ :=
  (((C.filter fun z => b z < b x).card : ℝ) +
      ((C.filter fun z => b z = b x).card : ℝ) / 2) /
    (C.card : ℝ)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def componentRankMassList {V : Type*}
    (C : Finset V) (b : V → ℤ) : List ℝ :=
  ((C.image b).sort (· ≤ ·)).map (componentRankMass C b)

private theorem exists_maximum_overlap_component
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V)
    (hC : C.Nonempty) (hCU : C ⊆ U) :
    ∃ D ∈ Q.parts,
      ∀ E ∈ Q.parts, (C ∩ E).card ≤ (C ∩ D).card := by
  classical
  have hU : U.Nonempty := hC.mono hCU
  exact Finset.exists_max_image Q.parts
    (fun D : Finset V => (C ∩ D).card)
    (Q.parts_nonempty hU.ne_empty)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def maximumOverlapPart
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V) : Finset V := by
  classical
  exact if h : C.Nonempty ∧ C ⊆ U then
    (exists_maximum_overlap_component Q C h.1 h.2).choose else ∅

namespace PrefixCompressionU

open scoped BigOperators

private def sourceCrossRoot (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) : BinaryLeavittˣ :=
  prefixElementaryUnit ninePrefixCode i j h
    (leavittWordS a * leavittWordT b)

private theorem sourceCrossRoot_mem (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) :
    sourceCrossRoot i j h a b ∈ prefixElementaryGroup ninePrefixCode :=
  Subgroup.subset_closure ⟨i, j, h,
    leavittWordS a * leavittWordT b, rfl⟩

@[simp] private theorem sourceCrossRoot_val (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) :
    (↑(sourceCrossRoot i j h a b) : BinaryLeavitt) =
      1 + leavittWordS (nineWord i ++ a) *
        leavittWordT (nineWord j ++ b) := by
  change
    1 + leavittWordS (nineWord i) *
      (leavittWordS a * leavittWordT b) * leavittWordT (nineWord j) = _
  rw [leavittWordS_append, leavittWordT_append]
  noncomm_ring

private def sourceCrossSwap (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) : BinaryLeavittˣ :=
  sourceCrossRoot i j h a b *
    sourceCrossRoot j i h.symm b a *
    sourceCrossRoot i j h a b

private theorem sourceCrossSwap_mem (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) :
    sourceCrossSwap i j h a b ∈ prefixElementaryGroup ninePrefixCode := by
  exact (prefixElementaryGroup ninePrefixCode).mul_mem
    ((prefixElementaryGroup ninePrefixCode).mul_mem
      (sourceCrossRoot_mem i j h a b)
      (sourceCrossRoot_mem j i h.symm b a))
    (sourceCrossRoot_mem i j h a b)

private theorem sourceRefinementOrthogonal (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) :
    leavittWordT (nineWord i ++ a) *
      leavittWordS (nineWord j ++ b) = 0 := by
  have hz : leavittWordT (nineWord i) * leavittWordS (nineWord j) = 0 := by
    simpa only [ninePrefixCode, h, ↓reduceIte] using binaryPrefixCode_orthogonal ninePrefixCode i j
  rw [leavittWordT_append, leavittWordS_append]
  calc
    (leavittWordT a * leavittWordT (nineWord i)) *
        (leavittWordS (nineWord j) * leavittWordS b) =
      leavittWordT a *
        (leavittWordT (nineWord i) * leavittWordS (nineWord j)) *
        leavittWordS b := by noncomm_ring
    _ = 0 := by rw [hz]; simp only [mul_zero, zero_mul]

private theorem sourceCrossSwap_val (i j : Fin 9) (h : i ≠ j)
    (a b : List (Fin 2)) :
    (↑(sourceCrossSwap i j h a b) : BinaryLeavitt) =
      1 - leavittWordS (nineWord i ++ a) *
          leavittWordT (nineWord i ++ a) -
        leavittWordS (nineWord j ++ b) *
          leavittWordT (nineWord j ++ b) +
        leavittWordS (nineWord i ++ a) *
          leavittWordT (nineWord j ++ b) +
        leavittWordS (nineWord j ++ b) *
          leavittWordT (nineWord i ++ a) := by
  let A : List (Fin 2) := nineWord i ++ a
  let B : List (Fin 2) := nineWord j ++ b
  let P : BinaryLeavitt := leavittWordS A * leavittWordT B
  let Q : BinaryLeavitt := leavittWordS B * leavittWordT A
  have hba : leavittWordT B * leavittWordS A = 0 :=
    sourceRefinementOrthogonal j i h.symm b a
  have hPP : P * P = 0 := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS A * leavittWordT B) = 0
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT B * leavittWordS A) * leavittWordT B := by
            noncomm_ring
      _ = 0 := by rw [hba]; simp only [mul_zero, zero_mul]
  have hPQ : P * Q = leavittWordS A * leavittWordT A := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS B * leavittWordT A) =
        leavittWordS A * leavittWordT A
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS B * leavittWordT A) =
        leavittWordS A *
          (leavittWordT B * leavittWordS B) * leavittWordT A := by
            noncomm_ring
      _ = leavittWordS A * leavittWordT A := by
        rw [leavittWordT_mul_wordS_self]
        simp only [mul_one]
  have hQP : Q * P = leavittWordS B * leavittWordT B := by
    change
      (leavittWordS B * leavittWordT A) *
        (leavittWordS A * leavittWordT B) =
        leavittWordS B * leavittWordT B
    calc
      (leavittWordS B * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS B *
          (leavittWordT A * leavittWordS A) * leavittWordT B := by
            noncomm_ring
      _ = leavittWordS B * leavittWordT B := by
        rw [leavittWordT_mul_wordS_self]
        simp only [mul_one]
  have hPQP : P * Q * P = P := by
    rw [hPQ]
    change
      (leavittWordS A * leavittWordT A) *
        (leavittWordS A * leavittWordT B) =
        leavittWordS A * leavittWordT B
    calc
      (leavittWordS A * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT A * leavittWordS A) * leavittWordT B := by
            noncomm_ring
      _ = leavittWordS A * leavittWordT B := by
        rw [leavittWordT_mul_wordS_self]
        simp only [mul_one]
  change
    (↑(sourceCrossSwap i j h a b) : BinaryLeavitt) =
      1 - leavittWordS A * leavittWordT A -
        leavittWordS B * leavittWordT B + P + Q
  calc
    (↑(sourceCrossSwap i j h a b) : BinaryLeavitt) =
        (1 + P) * (1 + Q) * (1 + P) := by
          simp only [sourceCrossSwap, Units.val_mul, sourceCrossRoot_val]
          rfl
    _ = 1 - P * Q - Q * P + P + Q :=
      cylinder_transposition_factorization P Q hPP hPQP
    _ = 1 - leavittWordS A * leavittWordT A -
        leavittWordS B * leavittWordT B + P + Q := by rw [hPQ, hQP]

private def refinedSourceWord : Fin 19 → List (Fin 2)
  | 0 => [0, 0, 0, 0]
  | 1 => [0, 0, 0, 1]
  | 2 => [1, 0, 0, 0, 0]
  | 3 => [1, 0, 0, 0, 1]
  | 4 => [1, 1, 0, 0, 0]
  | 5 => [1, 1, 0, 0, 1]
  | 6 => [0, 0, 1]
  | 7 => [1, 0, 0, 1, 0]
  | 8 => [1, 0, 0, 1, 1]
  | 9 => [1, 1, 0, 1]
  | 10 => [0, 1, 0, 0]
  | 11 => [0, 1, 0, 1]
  | 12 => [0, 1, 1]
  | 13 => [1, 0, 1, 0, 0]
  | 14 => [1, 0, 1, 0, 1]
  | 15 => [1, 0, 1, 1]
  | 16 => [1, 1, 1, 0, 0]
  | 17 => [1, 1, 1, 0, 1]
  | _ => [1, 1, 1, 1]

private def refinedSourcePrefixCode : BinaryPrefixCode (Fin 19) where
  word := refinedSourceWord
  prefix_free := by decide

private theorem refinedSourcePrefixCode_complete :
    MatrixCorner.codeIdempotent
      (fun i => leavittWordS (refinedSourcePrefixCode.word i))
      (fun i => leavittWordT (refinedSourcePrefixCode.word i)) = 1 := by
  have h000 :
      leavittCylinder [0, 0, 0, 0] +
          leavittCylinder [0, 0, 0, 1] =
        leavittCylinder [0, 0, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [0, 0,
      0]).symm
  have h1000 :
      leavittCylinder [1, 0, 0, 0, 0] +
          leavittCylinder [1, 0, 0, 0, 1] =
        leavittCylinder [1, 0, 0, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 0,
      0, 0]).symm
  have h1100 :
      leavittCylinder [1, 1, 0, 0, 0] +
          leavittCylinder [1, 1, 0, 0, 1] =
        leavittCylinder [1, 1, 0, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 1,
      0, 0]).symm
  have h1001 :
      leavittCylinder [1, 0, 0, 1, 0] +
          leavittCylinder [1, 0, 0, 1, 1] =
        leavittCylinder [1, 0, 0, 1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 0,
      0, 1]).symm
  have h010 :
      leavittCylinder [0, 1, 0, 0] +
          leavittCylinder [0, 1, 0, 1] =
        leavittCylinder [0, 1, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [0, 1,
      0]).symm
  have h01 :
      leavittCylinder [0, 1, 0] +
          leavittCylinder [0, 1, 1] =
        leavittCylinder [0, 1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [0,
      1]).symm
  have h1010 :
      leavittCylinder [1, 0, 1, 0, 0] +
          leavittCylinder [1, 0, 1, 0, 1] =
        leavittCylinder [1, 0, 1, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 0,
      1, 0]).symm
  have h101 :
      leavittCylinder [1, 0, 1, 0] +
          leavittCylinder [1, 0, 1, 1] =
        leavittCylinder [1, 0, 1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 0,
      1]).symm
  have h1110 :
      leavittCylinder [1, 1, 1, 0, 0] +
          leavittCylinder [1, 1, 1, 0, 1] =
        leavittCylinder [1, 1, 1, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 1,
      1, 0]).symm
  have h111 :
      leavittCylinder [1, 1, 1, 0] +
          leavittCylinder [1, 1, 1, 1] =
        leavittCylinder [1, 1, 1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split [1, 1,
      1]).symm
  change (∑ i : Fin 19, leavittCylinder (refinedSourceWord i)) = 1
  calc
    (∑ i : Fin 19, leavittCylinder (refinedSourceWord i)) =
        (leavittCylinder [0, 0, 0, 0] +
          leavittCylinder [0, 0, 0, 1]) +
        (leavittCylinder [1, 0, 0, 0, 0] +
          leavittCylinder [1, 0, 0, 0, 1]) +
        (leavittCylinder [1, 1, 0, 0, 0] +
          leavittCylinder [1, 1, 0, 0, 1]) +
        leavittCylinder [0, 0, 1] +
        (leavittCylinder [1, 0, 0, 1, 0] +
          leavittCylinder [1, 0, 0, 1, 1]) +
        leavittCylinder [1, 1, 0, 1] +
        ((leavittCylinder [0, 1, 0, 0] +
            leavittCylinder [0, 1, 0, 1]) +
          leavittCylinder [0, 1, 1]) +
        ((leavittCylinder [1, 0, 1, 0, 0] +
            leavittCylinder [1, 0, 1, 0, 1]) +
          leavittCylinder [1, 0, 1, 1]) +
        ((leavittCylinder [1, 1, 1, 0, 0] +
            leavittCylinder [1, 1, 1, 0, 1]) +
          leavittCylinder [1, 1, 1, 1]) := by
            simp only [refinedSourceWord, Fin.isValue, Fin.sum_univ_succ,
              Fin.succ_ne_zero, imp_self, Fin.succ_zero_eq_one,
              Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique,
              Fin.default_eq_zero, Finset.sum_singleton]
            ac_rfl
    _ = leavittCylinder [0, 0, 0] +
          leavittCylinder [1, 0, 0, 0] +
          leavittCylinder [1, 1, 0, 0] +
          leavittCylinder [0, 0, 1] +
          leavittCylinder [1, 0, 0, 1] +
          leavittCylinder [1, 1, 0, 1] +
          leavittCylinder [0, 1] +
          leavittCylinder [1, 0, 1] +
          leavittCylinder [1, 1, 1] := by
            rw [h000, h1000, h1100, h1001, h010, h01,
              h1010, h101, h1110, h111]
    _ = ∑ i : Fin 9, leavittCylinder (nineWord i) := by
      simp only [Fin.isValue, nineWord, alphaWord, betaWord, nuWord,
        Fin.sum_univ_succ, Fin.succ_ne_zero, imp_self, Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique,
        Fin.default_eq_zero, Finset.sum_singleton]
      ac_rfl
    _ = 1 := ninePrefixCode_complete

private theorem completePrefixWord_ext {ι : Type*} [Fintype ι]
    (E : BinaryPrefixCode ι)
    (hcomplete : MatrixCorner.codeIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i)) = 1)
    (x y : BinaryLeavitt)
    (haction : ∀ i : ι,
      x * leavittWordS (E.word i) =
        y * leavittWordS (E.word i)) :
    x = y := by
  calc
    x = x * 1 := (mul_one x).symm
    _ = x * MatrixCorner.codeIdempotent
        (fun i => leavittWordS (E.word i))
        (fun i => leavittWordT (E.word i)) := by rw [hcomplete]
    _ = ∑ i : ι,
        (x * leavittWordS (E.word i)) *
          leavittWordT (E.word i) := by
      rw [MatrixCorner.codeIdempotent, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (mul_assoc x _ _).symm
    _ = ∑ i : ι,
        (y * leavittWordS (E.word i)) *
          leavittWordT (E.word i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [haction i]
    _ = y * MatrixCorner.codeIdempotent
        (fun i => leavittWordS (E.word i))
        (fun i => leavittWordT (E.word i)) := by
      rw [MatrixCorner.codeIdempotent, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_assoc y _ _
    _ = y := by rw [hcomplete, mul_one]

private theorem prefixTable_mul_sourceWord {ι : Type*}
    [Fintype ι]
    (source target : BinaryPrefixCode ι) (i : ι) :
    prefixTable source target * leavittWordS (source.word i) =
      leavittWordS (target.word i) := by
  classical
  simp only [prefixTable, Finset.sum_mul, mul_assoc, binaryPrefixCode_orthogonal, mul_ite, mul_one,
    mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private theorem compressionU_mul_nine_refinement
    (i : Fin 9) (r : List (Fin 2)) :
    (compressionU : BinaryLeavitt) *
        leavittWordS (nineWord i ++ r) =
      leavittWordS (uWord i ++ r) := by
  rw [leavittWordS_append, leavittWordS_append]
  change
    prefixTable ninePrefixCode uPrefixCode *
        (leavittWordS (ninePrefixCode.word i) * leavittWordS r) =
      leavittWordS (uPrefixCode.word i) * leavittWordS r
  rw [← mul_assoc, prefixTable_mul_sourceWord]

private def refinedSourceParent : Fin 19 → Fin 9
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | 7 => 4
  | 8 => 4
  | 9 => 5
  | 10 => 6
  | 11 => 6
  | 12 => 6
  | 13 => 7
  | 14 => 7
  | 15 => 7
  | 16 => 8
  | 17 => 8
  | _ => 8

private def refinedSourceSuffix : Fin 19 → List (Fin 2)
  | 0 => [0]
  | 1 => [1]
  | 2 => [0]
  | 3 => [1]
  | 4 => [0]
  | 5 => [1]
  | 6 => []
  | 7 => [0]
  | 8 => [1]
  | 9 => []
  | 10 => [0, 0]
  | 11 => [0, 1]
  | 12 => [1]
  | 13 => [0, 0]
  | 14 => [0, 1]
  | 15 => [1]
  | 16 => [0, 0]
  | 17 => [0, 1]
  | _ => [1]

private def refinedTargetWord (i : Fin 19) : List (Fin 2) :=
  uWord (refinedSourceParent i) ++ refinedSourceSuffix i

private theorem refinedSourceWord_eq_parent_append (i : Fin 19) :
    refinedSourceWord i =
      nineWord (refinedSourceParent i) ++ refinedSourceSuffix i := by
  fin_cases i <;> decide

private theorem compressionU_mul_refinedSourceWord (i : Fin 19) :
    (compressionU : BinaryLeavitt) *
        leavittWordS (refinedSourceWord i) =
      leavittWordS (refinedTargetWord i) := by
  rw [refinedSourceWord_eq_parent_append]
  exact compressionU_mul_nine_refinement
    (refinedSourceParent i) (refinedSourceSuffix i)

private def binaryWordCancellation (a b : List (Fin 2)) : BinaryLeavitt :=
  match a, b with
  | [], b => leavittWordS b
  | a, [] => leavittWordT a
  | i :: a, j :: b =>
      if i = j then binaryWordCancellation a b else 0

private theorem leavittWordT_mul_wordS_cancel (a b : List (Fin 2)) :
    leavittWordT a * leavittWordS b =
      binaryWordCancellation a b := by
  induction a generalizing b with
  | nil => simp only [leavittWordT, one_mul, binaryWordCancellation]
  | cons i a ih =>
      cases b with
      | nil => simp only [leavittWordS, mul_one, binaryWordCancellation]
      | cons j b =>
          by_cases hij : i = j
          · subst j
            change
              (leavittWordT a * leavittT i) *
                  (leavittS i * leavittWordS b) =
                if i = i then binaryWordCancellation a b else 0
            rw [ite_eq_left rfl]
            calc
              (leavittWordT a * leavittT i) *
                  (leavittS i * leavittWordS b) =
                leavittWordT a *
                  ((leavittT i * leavittS i) * leavittWordS b) := by
                    noncomm_ring
              _ = binaryWordCancellation a b := by
                rw [leavittT_mul_S]
                simpa only [↓reduceIte, one_mul] using ih b
          · change
              (leavittWordT a * leavittT i) *
                  (leavittS j * leavittWordS b) =
                if i = j then binaryWordCancellation a b else 0
            rw [ite_eq_right hij]
            calc
              (leavittWordT a * leavittT i) *
                  (leavittS j * leavittWordS b) =
                leavittWordT a *
                  ((leavittT i * leavittS j) * leavittWordS b) := by
                    noncomm_ring
              _ = 0 := by rw [leavittT_mul_S]; simp only [hij, ↓reduceIte, zero_mul, mul_zero]

private theorem leavittWordS_mul_wordS (a b : List (Fin 2)) :
    leavittWordS a * leavittWordS b = leavittWordS (a ++ b) :=
  (leavittWordS_append a b).symm

private theorem sourceCrossSwap_mul_leavittWordS
    (i j : Fin 9) (h : i ≠ j)
    (a b x : List (Fin 2)) :
    (↑(sourceCrossSwap i j h a b) : BinaryLeavitt) * leavittWordS x =
      leavittWordS x -
        leavittWordS (nineWord i ++ a) *
          binaryWordCancellation (nineWord i ++ a) x -
        leavittWordS (nineWord j ++ b) *
          binaryWordCancellation (nineWord j ++ b) x +
        leavittWordS (nineWord i ++ a) *
          binaryWordCancellation (nineWord j ++ b) x +
        leavittWordS (nineWord j ++ b) *
          binaryWordCancellation (nineWord i ++ a) x := by
  rw [sourceCrossSwap_val]
  simp only [sub_mul, add_mul, one_mul, mul_assoc,
    leavittWordT_mul_wordS_cancel]

private def sourceUChronologicalSwaps : List BinaryLeavittˣ :=
  [sourceCrossSwap 0 1 (by decide) [0] [],
   sourceCrossSwap 0 4 (by decide) [1] [],
   sourceCrossSwap 3 7 (by decide) [] [],
   sourceCrossSwap 6 2 (by decide) [0, 0] [],
   sourceCrossSwap 6 5 (by decide) [0, 1] [],
   sourceCrossSwap 6 8 (by decide) [1] [],
   sourceCrossSwap 3 6 (by decide) [] [0],
   sourceCrossSwap 1 0 (by decide) [] [0, 0],
   sourceCrossSwap 4 0 (by decide) [] [0, 1],
   sourceCrossSwap 1 0 (by decide) [] [1, 0],
   sourceCrossSwap 4 0 (by decide) [] [1, 1],
   sourceCrossSwap 3 1 (by decide) [0, 0] [],
   sourceCrossSwap 3 4 (by decide) [0, 1] [],
   sourceCrossSwap 7 3 (by decide) [] [0],
   sourceCrossSwap 7 3 (by decide) [] [1],
   sourceCrossSwap 2 6 (by decide) [] [0, 0, 0],
   sourceCrossSwap 5 6 (by decide) [] [0, 0, 1],
   sourceCrossSwap 8 6 (by decide) [] [0, 1],
   sourceCrossSwap 2 6 (by decide) [] [1, 0, 0],
   sourceCrossSwap 5 6 (by decide) [] [1, 0, 1],
   sourceCrossSwap 8 6 (by decide) [] [1, 1]]

private def elementaryCompressionU : BinaryLeavittˣ :=
  sourceUChronologicalSwaps.reverse.prod

private theorem elementaryCompressionU_mem :
    elementaryCompressionU ∈ prefixElementaryGroup ninePrefixCode := by
  apply (prefixElementaryGroup ninePrefixCode).list_prod_mem
  intro x hx
  simp only [List.mem_reverse, sourceUChronologicalSwaps,
    List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h <;>
    subst x <;> exact sourceCrossSwap_mem _ _ _ _ _

private theorem elementaryCompressionU_mul_refinedSourceWord (i : Fin 19) :
    (elementaryCompressionU : BinaryLeavitt) *
        leavittWordS (refinedSourceWord i) =
      leavittWordS (refinedTargetWord i) := by
  fin_cases i <;>
    simp [elementaryCompressionU, sourceUChronologicalSwaps,
      sourceCrossSwap_mul_leavittWordS,
      refinedSourceWord, refinedTargetWord,
      refinedSourceParent, refinedSourceSuffix,
      nineWord, uWord, alphaWord, betaWord, nuWord, etaWord,
      binaryWordCancellation, leavittWordS_mul_wordS,
      List.prod_cons, mul_assoc]

private theorem elementaryCompressionU_eq_compressionU :
    elementaryCompressionU = compressionU := by
  apply Units.ext
  apply completePrefixWord_ext refinedSourcePrefixCode
    refinedSourcePrefixCode_complete
  intro i
  change
    (elementaryCompressionU : BinaryLeavitt) *
        leavittWordS (refinedSourceWord i) =
      (compressionU : BinaryLeavitt) *
        leavittWordS (refinedSourceWord i)
  rw [elementaryCompressionU_mul_refinedSourceWord,
    compressionU_mul_refinedSourceWord]

private theorem compressionU_mem_ninePrefixElementaryGroup :
    compressionU ∈ prefixElementaryGroup ninePrefixCode := by
  rw [← elementaryCompressionU_eq_compressionU]
  exact elementaryCompressionU_mem

end PrefixCompressionU

public
theorem compressionU_mem_ninePrefixElementaryGroup :
    compressionU ∈ prefixElementaryGroup ninePrefixCode :=
  PrefixCompressionU.compressionU_mem_ninePrefixElementaryGroup

namespace PrefixCompression

open scoped BigOperators

private theorem prefixTable_compose {ι : Type*} [Fintype ι]
    (source middle target : BinaryPrefixCode ι) :
    prefixTable middle target * prefixTable source middle =
      prefixTable source target := by
  classical
  change
    (∑ i, leavittWordS (target.word i) *
      leavittWordT (middle.word i)) *
      (∑ j, leavittWordS (middle.word j) *
        leavittWordT (source.word j)) =
      ∑ i, leavittWordS (target.word i) *
        leavittWordT (source.word i)
  calc
    (∑ i, leavittWordS (target.word i) *
        leavittWordT (middle.word i)) *
        (∑ j, leavittWordS (middle.word j) *
          leavittWordT (source.word j)) =
      ∑ i, ∑ j,
        leavittWordS (target.word i) *
          (leavittWordT (middle.word i) *
            leavittWordS (middle.word j)) *
          leavittWordT (source.word j) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            simp only [mul_assoc]
    _ = ∑ i, leavittWordS (target.word i) *
          leavittWordT (source.word i) := by
      simp only [binaryPrefixCode_orthogonal, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]

private def compressionTransition : BinaryLeavittˣ :=
  prefixTableUnit uPrefixCode vPrefixCode
    uPrefixCode_complete vPrefixCode_complete

private theorem compressionV_eq_transition_mul :
    compressionV = compressionTransition * compressionU := by
  apply Units.ext
  change
    prefixTable ninePrefixCode vPrefixCode =
      prefixTable uPrefixCode vPrefixCode *
        prefixTable ninePrefixCode uPrefixCode
  exact (prefixTable_compose ninePrefixCode uPrefixCode vPrefixCode).symm

private def nineCrossRoot (i j : Fin 9) (hij : i ≠ j)
    (a b : List (Fin 2)) : BinaryLeavittˣ :=
  prefixElementaryUnit ninePrefixCode i j hij
    (leavittWordS a * leavittWordT b)

private theorem nineCrossRoot_mem (i j : Fin 9) (hij : i ≠ j)
    (a b : List (Fin 2)) :
    nineCrossRoot i j hij a b ∈ prefixElementaryGroup ninePrefixCode := by
  exact Subgroup.subset_closure
    ⟨i, j, hij, leavittWordS a * leavittWordT b, rfl⟩

private def nineCrossSwap (i j : Fin 9) (hij : i ≠ j)
    (a b : List (Fin 2)) : BinaryLeavittˣ :=
  nineCrossRoot i j hij a b *
    nineCrossRoot j i hij.symm b a *
    nineCrossRoot i j hij a b

private theorem nineCrossSwap_mem (i j : Fin 9) (hij : i ≠ j)
    (a b : List (Fin 2)) :
    nineCrossSwap i j hij a b ∈ prefixElementaryGroup ninePrefixCode := by
  exact (prefixElementaryGroup ninePrefixCode).mul_mem
    ((prefixElementaryGroup ninePrefixCode).mul_mem
      (nineCrossRoot_mem i j hij a b)
      (nineCrossRoot_mem j i hij.symm b a))
    (nineCrossRoot_mem i j hij a b)

private def compressionTransitionCrossSwaps : List BinaryLeavittˣ :=
  [nineCrossSwap 0 1 (by decide) [1, 0] [],
   nineCrossSwap 0 4 (by decide) [1, 1] [],
   nineCrossSwap 3 7 (by decide) [1] [],
   nineCrossSwap 6 2 (by decide) [1, 0, 0] [],
   nineCrossSwap 6 5 (by decide) [1, 0, 1] [],
   nineCrossSwap 6 8 (by decide) [1, 1] []]

private theorem compressionTransitionCrossSwaps_prod_mem :
    compressionTransitionCrossSwaps.prod ∈
      prefixElementaryGroup ninePrefixCode := by
  apply (prefixElementaryGroup ninePrefixCode).list_prod_mem
  intro x hx
  simp only [compressionTransitionCrossSwaps, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h <;>
    subst x <;> exact nineCrossSwap_mem _ _ _ _ _

private def transpositionValue {A : Type*} [Ring A]
    (sa ta sb tb : A) : A :=
  1 - sa * ta - sb * tb + sa * tb + sb * ta

private theorem transpositionValue_refine {A : Type*} [Ring A]
    (sa ta sb tb p₀ q₀ p₁ q₁ : A)
    (haa : ta * sa = 1) (hbb : tb * sb = 1)
    (hab : ta * sb = 0) (hba : tb * sa = 0)
    (h₀₀ : q₀ * p₀ = 1) (h₁₁ : q₁ * p₁ = 1)
    (h₀₁ : q₀ * p₁ = 0) (h₁₀ : q₁ * p₀ = 0)
    (hpartition : p₀ * q₀ + p₁ * q₁ = 1) :
    transpositionValue (sa * p₀) (q₀ * ta) (sb * p₀) (q₀ * tb) *
        transpositionValue (sa * p₁) (q₁ * ta) (sb * p₁) (q₁ * tb) =
      transpositionValue sa ta sb tb := by
  have haa' (x : A) : ta * (sa * x) = x := by
    rw [← mul_assoc, haa, one_mul]
  have hbb' (x : A) : tb * (sb * x) = x := by
    rw [← mul_assoc, hbb, one_mul]
  have hab' (x : A) : ta * (sb * x) = 0 := by
    rw [← mul_assoc, hab, zero_mul]
  have hba' (x : A) : tb * (sa * x) = 0 := by
    rw [← mul_assoc, hba, zero_mul]
  have h₀₀' (x : A) : q₀ * (p₀ * x) = x := by
    rw [← mul_assoc, h₀₀, one_mul]
  have h₁₁' (x : A) : q₁ * (p₁ * x) = x := by
    rw [← mul_assoc, h₁₁, one_mul]
  have h₀₁' (x : A) : q₀ * (p₁ * x) = 0 := by
    rw [← mul_assoc, h₀₁, zero_mul]
  have h₁₀' (x : A) : q₁ * (p₀ * x) = 0 := by
    rw [← mul_assoc, h₁₀, zero_mul]
  have hpartition' (x : A) :
      p₀ * (q₀ * x) + p₁ * (q₁ * x) = x := by
    rw [← mul_assoc, ← mul_assoc, ← add_mul, hpartition, one_mul]
  have hpartition_left (z x : A) :
      z * (p₀ * (q₀ * x)) + z * (p₁ * (q₁ * x)) = z * x := by
    rw [← mul_add, hpartition']
  unfold transpositionValue
  calc
    _ = 1 -
          (sa * (p₀ * (q₀ * ta)) + sa * (p₁ * (q₁ * ta))) -
          (sb * (p₀ * (q₀ * tb)) + sb * (p₁ * (q₁ * tb))) +
          (sa * (p₀ * (q₀ * tb)) + sa * (p₁ * (q₁ * tb))) +
          (sb * (p₀ * (q₀ * ta)) + sb * (p₁ * (q₁ * ta))) := by
            noncomm_ring [haa, hbb, hab, hba, h₀₀, h₁₁, h₀₁, h₁₀,
              haa', hbb', hab', hba', h₀₀', h₁₁', h₀₁', h₁₀']
    _ = _ := by
      rw [hpartition_left sa ta, hpartition_left sb tb,
        hpartition_left sa tb, hpartition_left sb ta]

private theorem nineRefinement_orthogonal
    (i j : Fin 9) (hij : i ≠ j) (a b : List (Fin 2)) :
    leavittWordT (nineWord i ++ a) *
      leavittWordS (nineWord j ++ b) = 0 := by
  have hzero :
      leavittWordT (nineWord i) * leavittWordS (nineWord j) = 0 := by
    simpa only [ninePrefixCode, hij, ↓reduceIte] using binaryPrefixCode_orthogonal ninePrefixCode i
      j
  rw [leavittWordT_append, leavittWordS_append]
  calc
    (leavittWordT a * leavittWordT (nineWord i)) *
        (leavittWordS (nineWord j) * leavittWordS b) =
      leavittWordT a *
        (leavittWordT (nineWord i) * leavittWordS (nineWord j)) *
        leavittWordS b := by noncomm_ring
    _ = 0 := by rw [hzero]; simp only [mul_zero, zero_mul]

private theorem nineCrossSwap_val (i j : Fin 9) (hij : i ≠ j)
    (a b : List (Fin 2)) :
    (↑(nineCrossSwap i j hij a b) : BinaryLeavitt) =
      transpositionValue
        (leavittWordS (nineWord i ++ a))
        (leavittWordT (nineWord i ++ a))
        (leavittWordS (nineWord j ++ b))
        (leavittWordT (nineWord j ++ b)) := by
  let A : List (Fin 2) := nineWord i ++ a
  let B : List (Fin 2) := nineWord j ++ b
  let P : BinaryLeavitt := leavittWordS A * leavittWordT B
  let Q : BinaryLeavitt := leavittWordS B * leavittWordT A
  have hBA : leavittWordT B * leavittWordS A = 0 :=
    nineRefinement_orthogonal j i hij.symm b a
  have hPP : P * P = 0 := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS A * leavittWordT B) = 0
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT B * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = 0 := by rw [hBA]; simp only [mul_zero, zero_mul]
  have hPQP : P * Q * P = P := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS B * leavittWordT A) *
        (leavittWordS A * leavittWordT B) =
        leavittWordS A * leavittWordT B
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS B * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT B * leavittWordS B) *
          (leavittWordT A * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = leavittWordS A * leavittWordT B := by
        rw [leavittWordT_mul_wordS_self,
          leavittWordT_mul_wordS_self]
        simp only [mul_one]
  have hPQ : P * Q = leavittWordS A * leavittWordT A := by
    dsimp [P, Q]
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS B * leavittWordT A) =
        leavittWordS A *
          (leavittWordT B * leavittWordS B) *
          leavittWordT A := by noncomm_ring
      _ = _ := by rw [leavittWordT_mul_wordS_self]; simp only [mul_one]
  have hQP : Q * P = leavittWordS B * leavittWordT B := by
    dsimp [P, Q]
    calc
      (leavittWordS B * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS B *
          (leavittWordT A * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = _ := by rw [leavittWordT_mul_wordS_self]; simp only [mul_one]
  change
    (1 + leavittWordS (nineWord i) *
      (leavittWordS a * leavittWordT b) * leavittWordT (nineWord j)) *
      (1 + leavittWordS (nineWord j) *
        (leavittWordS b * leavittWordT a) * leavittWordT (nineWord i)) *
      (1 + leavittWordS (nineWord i) *
        (leavittWordS a * leavittWordT b) * leavittWordT (nineWord j)) = _
  have hleft :
      leavittWordS (nineWord i) *
          (leavittWordS a * leavittWordT b) * leavittWordT (nineWord j) =
        P := by
    dsimp [P, A, B]
    rw [leavittWordS_append, leavittWordT_append]
    noncomm_ring
  have hright :
      leavittWordS (nineWord j) *
          (leavittWordS b * leavittWordT a) * leavittWordT (nineWord i) =
        Q := by
    dsimp [Q, A, B]
    rw [leavittWordS_append, leavittWordT_append]
    noncomm_ring
  rw [hleft, hright,
    cylinder_transposition_factorization P Q hPP hPQP,
    hPQ, hQP]
  rfl

private def wordSwapValue (a b : List (Fin 2)) : BinaryLeavitt :=
  transpositionValue (leavittWordS a) (leavittWordT a)
    (leavittWordS b) (leavittWordT b)

private theorem wordSwapValue_refine (a b : List (Fin 2))
    (hab : leavittWordT a * leavittWordS b = 0)
    (hba : leavittWordT b * leavittWordS a = 0) :
    wordSwapValue (a ++ [0]) (b ++ [0]) *
        wordSwapValue (a ++ [1]) (b ++ [1]) =
      wordSwapValue a b := by
  unfold wordSwapValue
  simpa only [leavittWordS_append, leavittWordT_append,
    leavittWordS, leavittWordT, mul_one, one_mul] using
    transpositionValue_refine
      (leavittWordS a) (leavittWordT a)
      (leavittWordS b) (leavittWordT b)
      (leavittS 0) (leavittT 0)
      (leavittS 1) (leavittT 1)
      (leavittWordT_mul_wordS_self a)
      (leavittWordT_mul_wordS_self b)
      hab hba
      (by simpa only [Fin.isValue, ↓reduceIte] using leavittT_mul_S 0 0)
      (by simpa only [Fin.isValue, ↓reduceIte] using leavittT_mul_S 1 1)
      (by simpa only [Fin.isValue, zero_ne_one, ↓reduceIte] using leavittT_mul_S 0 1)
      (by simpa only [Fin.isValue, one_ne_zero, ↓reduceIte] using leavittT_mul_S 1 0)
      leavitt_partition

private theorem compressionTransitionCrossSwaps_prod_val :
    (↑compressionTransitionCrossSwaps.prod : BinaryLeavitt) =
      wordSwapValue (uWord 1) (uWord 2) *
        wordSwapValue (uWord 4) (uWord 5) *
        wordSwapValue (uWord 7) (uWord 8) := by
  have h₀ :
      wordSwapValue [0, 0, 0, 1, 0] [1, 0, 0, 0] *
        wordSwapValue [0, 0, 0, 1, 1] [1, 0, 0, 1] =
        wordSwapValue [0, 0, 0, 1] [1, 0, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using
      wordSwapValue_refine [0, 0, 0, 1] [1, 0, 0] (leavittWordT_mul_wordS_of_incomparable _ _ (by
        decide) (by decide))
        (leavittWordT_mul_wordS_of_incomparable _ _ (by decide) (by decide))
  have h₂₀ :
      wordSwapValue [0, 1, 1, 0, 0] [1, 1, 0, 0] *
        wordSwapValue [0, 1, 1, 0, 1] [1, 1, 0, 1] =
        wordSwapValue [0, 1, 1, 0] [1, 1, 0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using
      wordSwapValue_refine [0, 1, 1, 0] [1, 1, 0] (leavittWordT_mul_wordS_of_incomparable _ _ (by
        decide) (by decide))
        (leavittWordT_mul_wordS_of_incomparable _ _ (by decide) (by decide))
  have h₂ :
      wordSwapValue [0, 1, 1, 0] [1, 1, 0] *
        wordSwapValue [0, 1, 1, 1] [1, 1, 1] =
        wordSwapValue [0, 1, 1] [1, 1] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using
      wordSwapValue_refine [0, 1, 1] [1, 1] (leavittWordT_mul_wordS_of_incomparable _ _ (by decide)
        (by decide))
        (leavittWordT_mul_wordS_of_incomparable _ _ (by decide) (by decide))
  simp only [compressionTransitionCrossSwaps, List.prod_cons, List.prod_nil,
    Units.val_mul, nineCrossSwap_val, mul_one]
  change
    wordSwapValue [0, 0, 0, 1, 0] [1, 0, 0, 0] *
      (wordSwapValue [0, 0, 0, 1, 1] [1, 0, 0, 1] *
      (wordSwapValue [0, 0, 1, 1] [1, 0, 1] *
      (wordSwapValue [0, 1, 1, 0, 0] [1, 1, 0, 0] *
      (wordSwapValue [0, 1, 1, 0, 1] [1, 1, 0, 1] *
       wordSwapValue [0, 1, 1, 1] [1, 1, 1])))) =
    wordSwapValue [0, 0, 0, 1] [1, 0, 0] *
      wordSwapValue [0, 0, 1, 1] [1, 0, 1] *
      wordSwapValue [0, 1, 1] [1, 1]
  calc
    _ =
      (wordSwapValue [0, 0, 0, 1, 0] [1, 0, 0, 0] *
        wordSwapValue [0, 0, 0, 1, 1] [1, 0, 0, 1]) *
      wordSwapValue [0, 0, 1, 1] [1, 0, 1] *
      ((wordSwapValue [0, 1, 1, 0, 0] [1, 1, 0, 0] *
        wordSwapValue [0, 1, 1, 0, 1] [1, 1, 0, 1]) *
        wordSwapValue [0, 1, 1, 1] [1, 1, 1]) := by
          noncomm_ring
    _ = _ := by rw [h₀, h₂₀, h₂]

private theorem transpositionValue_mul_codeWord {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι) (i j : ι) (hij : i ≠ j) (k : ι) :
    transpositionValue
        (leavittWordS (E.word i)) (leavittWordT (E.word i))
        (leavittWordS (E.word j)) (leavittWordT (E.word j)) *
        leavittWordS (E.word k) =
      if k = i then leavittWordS (E.word j)
      else if k = j then leavittWordS (E.word i)
      else leavittWordS (E.word k) := by
  by_cases hki : k = i
  · subst k
    simp only [transpositionValue, add_mul, sub_mul, one_mul, mul_assoc,
      binaryPrefixCode_orthogonal, ↓reduceIte,
      mul_one, sub_self, hij.symm, mul_zero, add_zero, zero_add]
  · by_cases hkj : k = j
    · subst k
      simp only [transpositionValue, add_mul, sub_mul, one_mul, mul_assoc,
        binaryPrefixCode_orthogonal, hij,
        ↓reduceIte, mul_zero, sub_zero, mul_one, sub_self, zero_add, add_zero, hij.symm]
    · simp only [transpositionValue, add_mul, sub_mul, one_mul, mul_assoc,
      binaryPrefixCode_orthogonal, Ne.symm hki,
        ↓reduceIte, mul_zero, sub_zero, Ne.symm hkj, add_zero, hki, hkj]

private theorem uSwap12_mul (k : Fin 9) :
    wordSwapValue (uWord 1) (uWord 2) * leavittWordS (uWord k) =
      if k = 1 then leavittWordS (uWord 2)
      else if k = 2 then leavittWordS (uWord 1)
      else leavittWordS (uWord k) :=
  transpositionValue_mul_codeWord uPrefixCode 1 2 (by decide) k

private theorem uSwap45_mul (k : Fin 9) :
    wordSwapValue (uWord 4) (uWord 5) * leavittWordS (uWord k) =
      if k = 4 then leavittWordS (uWord 5)
      else if k = 5 then leavittWordS (uWord 4)
      else leavittWordS (uWord k) :=
  transpositionValue_mul_codeWord uPrefixCode 4 5 (by decide) k

private theorem uSwap78_mul (k : Fin 9) :
    wordSwapValue (uWord 7) (uWord 8) * leavittWordS (uWord k) =
      if k = 7 then leavittWordS (uWord 8)
      else if k = 8 then leavittWordS (uWord 7)
      else leavittWordS (uWord k) :=
  transpositionValue_mul_codeWord uPrefixCode 7 8 (by decide) k

private theorem compressionTransitionParentSwaps_mul_word (k : Fin 9) :
    (wordSwapValue (uWord 1) (uWord 2) *
      wordSwapValue (uWord 4) (uWord 5) *
      wordSwapValue (uWord 7) (uWord 8)) *
        leavittWordS (uWord k) = leavittWordS (vWord k) := by
  fin_cases k <;>
    simp [mul_assoc, uSwap12_mul, uSwap45_mul, uSwap78_mul] <;>
    rfl

private theorem compressionTransitionParentSwaps_eq_table :
    wordSwapValue (uWord 1) (uWord 2) *
        wordSwapValue (uWord 4) (uWord 5) *
        wordSwapValue (uWord 7) (uWord 8) =
      prefixTable uPrefixCode vPrefixCode := by
  let x : BinaryLeavitt :=
    wordSwapValue (uWord 1) (uWord 2) *
      wordSwapValue (uWord 4) (uWord 5) *
      wordSwapValue (uWord 7) (uWord 8)
  change x = prefixTable uPrefixCode vPrefixCode
  calc
    x = x * 1 := (mul_one x).symm
    _ = x * MatrixCorner.codeIdempotent
          (fun i => leavittWordS (uPrefixCode.word i))
          (fun i => leavittWordT (uPrefixCode.word i)) := by
            rw [uPrefixCode_complete]
    _ = ∑ i : Fin 9,
          (x * leavittWordS (uWord i)) * leavittWordT (uWord i) := by
            simp only [MatrixCorner.codeIdempotent, uPrefixCode, Finset.mul_sum, mul_assoc]
    _ = ∑ i : Fin 9,
          leavittWordS (vWord i) * leavittWordT (uWord i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [show x * leavittWordS (uWord i) =
              leavittWordS (vWord i) from
              compressionTransitionParentSwaps_mul_word i]
    _ = prefixTable uPrefixCode vPrefixCode := rfl

private theorem compressionTransitionCrossSwaps_prod_eq :
    compressionTransitionCrossSwaps.prod = compressionTransition := by
  apply Units.ext
  exact compressionTransitionCrossSwaps_prod_val.trans
    compressionTransitionParentSwaps_eq_table

private theorem compressionTransition_mem :
    compressionTransition ∈ prefixElementaryGroup ninePrefixCode := by
  rw [← compressionTransitionCrossSwaps_prod_eq]
  exact compressionTransitionCrossSwaps_prod_mem

private theorem compressionV_mem_of_compressionU
    (hU : compressionU ∈ prefixElementaryGroup ninePrefixCode) :
    compressionV ∈ prefixElementaryGroup ninePrefixCode := by
  rw [compressionV_eq_transition_mul]
  exact (prefixElementaryGroup ninePrefixCode).mul_mem
    compressionTransition_mem hU

end PrefixCompression

public
theorem compressionV_mem_ninePrefixElementaryGroup :
    compressionV ∈ prefixElementaryGroup ninePrefixCode :=
  PrefixCompression.compressionV_mem_of_compressionU
    compressionU_mem_ninePrefixElementaryGroup

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def rankDropCount {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (H r : ℝ) : ℝ :=
  Finset.univ.sum (fun i : ι =>
    if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋ then (1 : ℝ) else 0)

namespace CheegerPoincare

open scoped BigOperators

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def positiveSupport {V : Type*} [Fintype V]
    (f : V → ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun x => 0 < f x

@[simp] public theorem mem_positiveSupport {V : Type*} [Fintype V]
    (f : V → ℝ) (x : V) :
    x ∈ positiveSupport f ↔ 0 < f x := by
  classical
  simp only [positiveSupport, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def finiteMean {V : Type*} [Fintype V] (f : V → ℝ) : ℝ :=
  (∑ x : V, f x) / (Fintype.card V : ℝ)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def lowerLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun x => f x < a

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def upperLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter fun x => a < f x

@[simp] public theorem mem_lowerLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) (x : V) :
    x ∈ lowerLevel f a ↔ f x < a := by
  classical
  simp only [lowerLevel, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] public theorem mem_upperLevel {V : Type*} [Fintype V]
    (f : V → ℝ) (a : ℝ) (x : V) :
    x ∈ upperLevel f a ↔ a < f x := by
  classical
  simp only [upperLevel, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def finiteVariance {V : Type*} [Fintype V] (f : V → ℝ) : ℝ :=
  (∑ x : V, (f x - finiteMean f) ^ 2) / (Fintype.card V : ℝ)

end CheegerPoincare

namespace ThompsonPrefixLocal

open scoped BigOperators

private theorem idempotentCornerUnitExtensions_commute
    {A : Type*} [Ring A] {e f : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0)
    (u : he.Cornerˣ) (v : hf.Cornerˣ) :
    Commute
      (idempotentCornerUnitExtension he u)
      (idempotentCornerUnitExtension hf v) := by
  apply Units.ext
  have hu := (Subsemigroup.mem_corner_iff he).mp u.val.property
  have hv := (Subsemigroup.mem_corner_iff hf).mp v.val.property
  have huv : u.val.val * v.val.val = 0 := by
    calc
      u.val.val * v.val.val =
          (u.val.val * e) * (f * v.val.val) := by rw [hu.2, hv.1]
      _ = u.val.val * (e * f) * v.val.val := by noncomm_ring
      _ = 0 := by rw [hef]; simp only [mul_zero, zero_mul]
  have hvu : v.val.val * u.val.val = 0 := by
    calc
      v.val.val * u.val.val =
          (v.val.val * f) * (e * u.val.val) := by rw [hv.2, hu.1]
      _ = v.val.val * (f * e) * u.val.val := by noncomm_ring
      _ = 0 := by rw [hfe]; simp only [mul_zero, zero_mul]
  have hev : e * v.val.val = 0 := by
    calc
      e * v.val.val = e * (f * v.val.val) := by rw [hv.1]
      _ = (e * f) * v.val.val := by rw [mul_assoc]
      _ = 0 := by rw [hef]; simp only [zero_mul]
  have hve : v.val.val * e = 0 := by
    calc
      v.val.val * e = (v.val.val * f) * e := by rw [hv.2]
      _ = v.val.val * (f * e) := by rw [mul_assoc]
      _ = 0 := by rw [hfe]; simp only [mul_zero]
  have huf : u.val.val * f = 0 := by
    calc
      u.val.val * f = (u.val.val * e) * f := by rw [hu.2]
      _ = u.val.val * (e * f) := by rw [mul_assoc]
      _ = 0 := by rw [hef]; simp only [mul_zero]
  have hfu : f * u.val.val = 0 := by
    calc
      f * u.val.val = f * (e * u.val.val) := by rw [hu.1]
      _ = (f * e) * u.val.val := by rw [mul_assoc]
      _ = 0 := by rw [hfe]; simp only [zero_mul]
  change
    (u.val.val + (1 - e)) * (v.val.val + (1 - f)) =
      (v.val.val + (1 - f)) * (u.val.val + (1 - e))
  noncomm_ring [he.eq, hf.eq, hu.1, hu.2, hv.1, hv.2,
    hef, hfe, huv, hvu, hev, hve, huf, hfu]

private def idempotentCornerGroup {A : Type*} [Ring A]
    {e : A} (he : IsIdempotentElem e) : Subgroup Aˣ :=
  (idempotentCornerUnitExtension he).range

private theorem idempotentCornerGroup_le_centralizer
    {A : Type*} [Ring A] {e f : A}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0) :
    idempotentCornerGroup hf ≤
      Subgroup.centralizer (idempotentCornerGroup he : Set Aˣ) := by
  intro z hz
  obtain ⟨v, rfl⟩ := hz
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  obtain ⟨u, rfl⟩ := hx
  exact (idempotentCornerUnitExtensions_commute he hf hef hfe u v).eq

private theorem leavittCylinder_isIdempotent (a : List (Fin 2)) :
    IsIdempotentElem (leavittCylinder a) := by
  change
    (leavittWordS a * leavittWordT a) *
        (leavittWordS a * leavittWordT a) =
      leavittWordS a * leavittWordT a
  calc
    (leavittWordS a * leavittWordT a) *
        (leavittWordS a * leavittWordT a) =
      leavittWordS a *
        (leavittWordT a * leavittWordS a) * leavittWordT a := by
          noncomm_ring
    _ = leavittWordS a * leavittWordT a := by
      rw [leavittWordT_mul_wordS_self]
      simp only [mul_one]

private theorem leavittCylinder_mul_eq_zero_of_incomparable
    (a b : List (Fin 2)) (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    leavittCylinder a * leavittCylinder b = 0 := by
  change
    (leavittWordS a * leavittWordT a) *
      (leavittWordS b * leavittWordT b) = 0
  calc
    (leavittWordS a * leavittWordT a) *
        (leavittWordS b * leavittWordT b) =
      leavittWordS a *
        (leavittWordT a * leavittWordS b) * leavittWordT b := by
          noncomm_ring
    _ = 0 := by
      rw [leavittWordT_mul_wordS_of_incomparable a b hab hba]
      simp only [mul_zero, zero_mul]

private def cylinderCornerGroup (a : List (Fin 2)) : Subgroup BinaryLeavittˣ :=
  idempotentCornerGroup (leavittCylinder_isIdempotent a)

private def prefixCodeIdempotent {ι : Type*} [Fintype ι]
    (E : BinaryPrefixCode ι) : BinaryLeavitt :=
  MatrixCorner.codeIdempotent
    (fun i => leavittWordS (E.word i))
    (fun i => leavittWordT (E.word i))

private def prefixCodeCornerGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) : Subgroup BinaryLeavittˣ :=
  idempotentCornerGroup
    (MatrixCorner.codeIdempotent_isIdempotent
      (fun i => leavittWordS (E.word i))
      (fun i => leavittWordT (E.word i))
      (binaryPrefixCode_orthogonal E))

private theorem prefixElementaryGroup_le_corner
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    prefixElementaryGroup E ≤ prefixCodeCornerGroup E := by
  rw [← prefixCornerElementaryGroup_map E]
  rintro _ ⟨u, _, rfl⟩
  exact ⟨(Units.mapEquiv (binaryPrefixCornerEquiv E).toMulEquiv) u, rfl⟩

private theorem alphaZeroWord_incomparable_local (i : Fin 3) :
    ¬ alphaZeroPrefixCode.word i <+: [0, 0, 0, 1] := by
  fin_cases i <;> decide

private theorem localWord_incomparable_alphaZero (i : Fin 3) :
    ¬ [0, 0, 0, 1] <+: alphaZeroPrefixCode.word i := by
  fin_cases i <;> decide

private theorem alphaZeroCode_mul_localCylinder :
    prefixCodeIdempotent alphaZeroPrefixCode *
        leavittCylinder [0, 0, 0, 1] = 0 := by
  change
    (∑ i : Fin 3, leavittCylinder (alphaZeroPrefixCode.word i)) *
        leavittCylinder [0, 0, 0, 1] = 0
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  exact leavittCylinder_mul_eq_zero_of_incomparable
    (alphaZeroPrefixCode.word i) [0, 0, 0, 1]
    (alphaZeroWord_incomparable_local i)
    (localWord_incomparable_alphaZero i)

private theorem localCylinder_mul_alphaZeroCode :
    leavittCylinder [0, 0, 0, 1] *
        prefixCodeIdempotent alphaZeroPrefixCode = 0 := by
  change
    leavittCylinder [0, 0, 0, 1] *
        (∑ i : Fin 3, leavittCylinder (alphaZeroPrefixCode.word i)) = 0
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i hi
  exact leavittCylinder_mul_eq_zero_of_incomparable
    [0, 0, 0, 1] (alphaZeroPrefixCode.word i)
    (localWord_incomparable_alphaZero i)
    (alphaZeroWord_incomparable_local i)

private theorem localCylinderCorner_le_centralizer_alphaZero :
    cylinderCornerGroup [0, 0, 0, 1] ≤
      Subgroup.centralizer
        (prefixElementaryGroup alphaZeroPrefixCode : Set BinaryLeavittˣ) := by
  let he := MatrixCorner.codeIdempotent_isIdempotent
    (fun i => leavittWordS (alphaZeroPrefixCode.word i))
    (fun i => leavittWordT (alphaZeroPrefixCode.word i))
    (binaryPrefixCode_orthogonal alphaZeroPrefixCode)
  let hf := leavittCylinder_isIdempotent [0, 0, 0, 1]
  have hef : prefixCodeIdempotent alphaZeroPrefixCode *
      leavittCylinder [0, 0, 0, 1] = 0 :=
    alphaZeroCode_mul_localCylinder
  have hfe : leavittCylinder [0, 0, 0, 1] *
      prefixCodeIdempotent alphaZeroPrefixCode = 0 :=
    localCylinder_mul_alphaZeroCode
  intro z hz
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  have hx' := prefixElementaryGroup_le_corner alphaZeroPrefixCode hx
  have hz' : z ∈ idempotentCornerGroup hf := hz
  have hc := idempotentCornerGroup_le_centralizer he hf hef hfe hz'
  exact Subgroup.mem_centralizer_iff.mp hc x hx'

end ThompsonPrefixLocal

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def matchedRetainedFinpartition
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) : Finpartition (matchedRetainedSupport R) :=
  P.ofSubset hR (Finset.sup_eq_biUnion R id)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def matchedRadiusBad {V ι : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (I : Finset ι) (w : ι → Equiv.Perm V)
    (B : Finset V) : Finset V :=
  B ∪ I.biUnion fun i => partitionWordCrossing P (w i)

namespace ComponentMidrankVariance

open scoped BigOperators

private def lowerRankWeight (s : Finset ℤ) (w : ℤ → ℝ) (j : ℤ) : ℝ :=
  (s.filter (fun i => i < j)).sum w

end ComponentMidrankVariance

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def insufficientOverlapComponents
    {V : Type u} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (eta : ℝ) : Finset (Finset V) := by
  classical
  exact P.parts.filter fun C =>
    ((C ∩ maximumOverlapPart Q C).card : ℝ) <
      (1 - eta) * (C.card : ℝ)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
noncomputable def partitionComponentSize
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (x : V) : ℕ :=
  (Q.part x).card

namespace ThompsonPrefixInsertion

open scoped BigOperators

private def singletonPrefixCode (a : List (Fin 2)) : BinaryPrefixCode (Fin 1) where
  word _ := a
  prefix_free := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

private theorem singletonPrefixCode_codeIdempotent (a : List (Fin 2)) :
    MatrixCorner.codeIdempotent
        (fun i => leavittWordS ((singletonPrefixCode a).word i))
        (fun i => leavittWordT ((singletonPrefixCode a).word i)) =
      leavittCylinder a := by
  simp only [MatrixCorner.codeIdempotent, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    singletonPrefixCode, Finset.sum_const, Finset.card_singleton, one_smul, leavittCylinder]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def prefixInsertionHom (a : List (Fin 2)) :
    BinaryLeavittˣ →* BinaryLeavittˣ :=
  (prefixCornerUnitHom (singletonPrefixCode a)).comp
    (Units.mapEquiv
      (Matrix.uniqueRingEquiv (m := Fin 1)
        (A := BinaryLeavitt)).symm.toMulEquiv).toMonoidHom

private def cylinderCornerGroup (a : List (Fin 2)) : Subgroup BinaryLeavittˣ :=
  (idempotentCornerUnitExtension (ThompsonPrefixLocal.leavittCylinder_isIdempotent a)).range

private theorem cylinderCornerGroup_eq_source (a : List (Fin 2)) :
    cylinderCornerGroup a = ThompsonPrefixLocal.cylinderCornerGroup a := by
  rfl

private theorem prefixInsertionHom_mem_cylinderCorner
    (a : List (Fin 2)) (u : BinaryLeavittˣ) :
    prefixInsertionHom a u ∈ cylinderCornerGroup a := by
  unfold cylinderCornerGroup
  let he := MatrixCorner.codeIdempotent_isIdempotent
    (fun i => leavittWordS ((singletonPrefixCode a).word i))
    (fun i => leavittWordT ((singletonPrefixCode a).word i))
    (binaryPrefixCode_orthogonal (singletonPrefixCode a))
  have hidem :
      (⟨MatrixCorner.codeIdempotent
        (fun i => leavittWordS ((singletonPrefixCode a).word i))
        (fun i => leavittWordT ((singletonPrefixCode a).word i)), he⟩ :
          {e : BinaryLeavitt // IsIdempotentElem e}) =
        ⟨leavittCylinder a, ThompsonPrefixLocal.leavittCylinder_isIdempotent a⟩ :=
    Subtype.ext (singletonPrefixCode_codeIdempotent a)
  have hcorner := congrArg
    (fun p : {e : BinaryLeavitt // IsIdempotentElem e} =>
      (idempotentCornerUnitExtension p.property).range)
    hidem
  rw [← hcorner]
  refine ⟨(Units.mapEquiv
      (binaryPrefixCornerEquiv (singletonPrefixCode a)).toMulEquiv)
    ((Units.mapEquiv
      (Matrix.uniqueRingEquiv (m := Fin 1)
        (A := BinaryLeavitt)).symm.toMulEquiv) u), ?_⟩
  rfl

public
theorem prefixInsertionHom_val (a : List (Fin 2)) (u : BinaryLeavittˣ) :
    (↑(prefixInsertionHom a u) : BinaryLeavitt) =
      leavittWordS a * (u : BinaryLeavitt) * leavittWordT a +
        (1 - leavittCylinder a) := by
  change
    MatrixCorner.encode
        (fun i => leavittWordS ((singletonPrefixCode a).word i))
        (fun i => leavittWordT ((singletonPrefixCode a).word i))
        ((Matrix.uniqueRingEquiv (m := Fin 1)
          (A := BinaryLeavitt)).symm (u : BinaryLeavitt)) +
      (1 - MatrixCorner.codeIdempotent
        (fun i => leavittWordS ((singletonPrefixCode a).word i))
        (fun i => leavittWordT ((singletonPrefixCode a).word i))) = _
  simp only [MatrixCorner.encode, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    singletonPrefixCode,
    Matrix.uniqueRingEquiv_symm_apply, Matrix.of_apply, Finset.sum_const, Finset.card_singleton,
      one_smul,
    MatrixCorner.codeIdempotent, leavittCylinder]

private theorem transpositionValue_mul_self {A : Type*} [Ring A]
    (sa ta sb tb : A)
    (haa : ta * sa = 1) (hbb : tb * sb = 1)
    (hab : ta * sb = 0) (hba : tb * sa = 0) :
    PrefixCompression.transpositionValue sa ta sb tb *
      PrefixCompression.transpositionValue sa ta sb tb = 1 := by
  have haa' (x : A) : ta * (sa * x) = x := by
    rw [← mul_assoc, haa, one_mul]
  have hbb' (x : A) : tb * (sb * x) = x := by
    rw [← mul_assoc, hbb, one_mul]
  have hab' (x : A) : ta * (sb * x) = 0 := by
    rw [← mul_assoc, hab, zero_mul]
  have hba' (x : A) : tb * (sa * x) = 0 := by
    rw [← mul_assoc, hba, zero_mul]
  unfold PrefixCompression.transpositionValue
  noncomm_ring [haa, hbb, hab, hba, haa', hbb', hab', hba']

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def cylinderSwap (a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) : BinaryLeavittˣ where
  val := PrefixCompression.wordSwapValue a b
  inv := PrefixCompression.wordSwapValue a b
  val_inv := transpositionValue_mul_self
    (leavittWordS a) (leavittWordT a)
    (leavittWordS b) (leavittWordT b)
    (leavittWordT_mul_wordS_self a)
    (leavittWordT_mul_wordS_self b)
    (leavittWordT_mul_wordS_of_incomparable a b hab hba)
    (leavittWordT_mul_wordS_of_incomparable b a hba hab)
  inv_val := transpositionValue_mul_self
    (leavittWordS a) (leavittWordT a)
    (leavittWordS b) (leavittWordT b)
    (leavittWordT_mul_wordS_self a)
    (leavittWordT_mul_wordS_self b)
    (leavittWordT_mul_wordS_of_incomparable a b hab hba)
    (leavittWordT_mul_wordS_of_incomparable b a hba hab)

private theorem append_not_prefix_append (a b x y : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    ¬ a ++ x <+: b ++ y := by
  intro h
  have ha : a <+: b ++ y := (List.prefix_append a x).trans h
  by_cases hle : a.length ≤ b.length
  · exact hab ((List.isPrefix_append_of_length hle).mp ha)
  · apply hba
    rw [List.prefix_iff_eq_take]
    have hea := List.prefix_iff_eq_take.mp ha
    rw [hea, List.take_take, Nat.min_eq_left (Nat.le_of_not_ge hle)]
    simp only [List.take_left']

private theorem prepend_not_prefix_prepend (l a b : List (Fin 2))
    (hab : ¬ a <+: b) :
    ¬ l ++ a <+: l ++ b := by
  intro h
  apply hab
  simpa only [List.prefix_append_right_inj] using h

private theorem prefixInsertionHom_cylinderSwap
    (l a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    prefixInsertionHom l (cylinderSwap a b hab hba) =
      cylinderSwap (l ++ a) (l ++ b)
        (prepend_not_prefix_prepend l a b hab)
        (prepend_not_prefix_prepend l b a hba) := by
  apply Units.ext
  rw [prefixInsertionHom_val]
  change
    leavittWordS l *
        (1 - leavittWordS a * leavittWordT a -
          leavittWordS b * leavittWordT b +
          leavittWordS a * leavittWordT b +
          leavittWordS b * leavittWordT a) * leavittWordT l +
        (1 - leavittWordS l * leavittWordT l) =
      1 - leavittWordS (l ++ a) * leavittWordT (l ++ a) -
        leavittWordS (l ++ b) * leavittWordT (l ++ b) +
        leavittWordS (l ++ a) * leavittWordT (l ++ b) +
        leavittWordS (l ++ b) * leavittWordT (l ++ a)
  rw [leavittWordS_append, leavittWordT_append,
    leavittWordS_append, leavittWordT_append]
  simp only [CharTwo.sub_eq_add]
  noncomm_ring
  simp only [zsmul_eq_mul, Int.cast_ofNat, CharTwo.two_eq_zero, zero_mul, zero_add]

private theorem transpositionValue_braid {A : Type*} [Ring A]
    (sa ta sb tb sc tc : A)
    (haa : ta * sa = 1) (hbb : tb * sb = 1) (hcc : tc * sc = 1)
    (hab : ta * sb = 0) (hba : tb * sa = 0)
    (hac : ta * sc = 0) (hca : tc * sa = 0)
    (hbc : tb * sc = 0) (hcb : tc * sb = 0) :
    PrefixCompression.transpositionValue sa ta sc tc *
        PrefixCompression.transpositionValue sb tb sc tc *
        PrefixCompression.transpositionValue sa ta sc tc =
      PrefixCompression.transpositionValue sa ta sb tb := by
  have haa' (x : A) : ta * (sa * x) = x := by
    rw [← mul_assoc, haa, one_mul]
  have hbb' (x : A) : tb * (sb * x) = x := by
    rw [← mul_assoc, hbb, one_mul]
  have hcc' (x : A) : tc * (sc * x) = x := by
    rw [← mul_assoc, hcc, one_mul]
  have hab' (x : A) : ta * (sb * x) = 0 := by
    rw [← mul_assoc, hab, zero_mul]
  have hba' (x : A) : tb * (sa * x) = 0 := by
    rw [← mul_assoc, hba, zero_mul]
  have hac' (x : A) : ta * (sc * x) = 0 := by
    rw [← mul_assoc, hac, zero_mul]
  have hca' (x : A) : tc * (sa * x) = 0 := by
    rw [← mul_assoc, hca, zero_mul]
  have hbc' (x : A) : tb * (sc * x) = 0 := by
    rw [← mul_assoc, hbc, zero_mul]
  have hcb' (x : A) : tc * (sb * x) = 0 := by
    rw [← mul_assoc, hcb, zero_mul]
  unfold PrefixCompression.transpositionValue
  noncomm_ring [haa, hbb, hcc, hab, hba, hac, hca, hbc, hcb,
    haa', hbb', hcc', hab', hba', hac', hca', hbc', hcb']

private def prefixCrossRoot {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a b : List (Fin 2)) : BinaryLeavittˣ :=
  prefixElementaryUnit E i j hij
    (leavittWordS a * leavittWordT b)

private theorem prefixCrossRoot_mem {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a b : List (Fin 2)) :
    prefixCrossRoot E i j hij a b ∈ prefixElementaryGroup E :=
  Subgroup.subset_closure
    ⟨i, j, hij, leavittWordS a * leavittWordT b, rfl⟩

private def prefixCrossSwap {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a b : List (Fin 2)) : BinaryLeavittˣ :=
  prefixCrossRoot E i j hij a b *
    prefixCrossRoot E j i hij.symm b a *
    prefixCrossRoot E i j hij a b

private theorem prefixCrossSwap_mem {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a b : List (Fin 2)) :
    prefixCrossSwap E i j hij a b ∈ prefixElementaryGroup E :=
  (prefixElementaryGroup E).mul_mem
    ((prefixElementaryGroup E).mul_mem
      (prefixCrossRoot_mem E i j hij a b)
      (prefixCrossRoot_mem E j i hij.symm b a))
    (prefixCrossRoot_mem E i j hij a b)

private theorem prefixCrossSwap_val {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j) (a b : List (Fin 2)) :
    (↑(prefixCrossSwap E i j hij a b) : BinaryLeavitt) =
      PrefixCompression.wordSwapValue
        (E.word i ++ a) (E.word j ++ b) := by
  let A : List (Fin 2) := E.word i ++ a
  let B : List (Fin 2) := E.word j ++ b
  let P : BinaryLeavitt := leavittWordS A * leavittWordT B
  let Q : BinaryLeavitt := leavittWordS B * leavittWordT A
  have hBA : leavittWordT B * leavittWordS A = 0 := by
    apply leavittWordT_mul_wordS_of_incomparable B A
    · exact append_not_prefix_append (E.word j) (E.word i)
        b a (E.prefix_free hij.symm) (E.prefix_free hij)
    · exact append_not_prefix_append (E.word i) (E.word j)
        a b (E.prefix_free hij) (E.prefix_free hij.symm)
  have hPP : P * P = 0 := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS A * leavittWordT B) = 0
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT B * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = 0 := by rw [hBA]; simp only [mul_zero, zero_mul]
  have hPQP : P * Q * P = P := by
    change
      (leavittWordS A * leavittWordT B) *
        (leavittWordS B * leavittWordT A) *
        (leavittWordS A * leavittWordT B) =
        leavittWordS A * leavittWordT B
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS B * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS A *
          (leavittWordT B * leavittWordS B) *
          (leavittWordT A * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = leavittWordS A * leavittWordT B := by
        rw [leavittWordT_mul_wordS_self,
          leavittWordT_mul_wordS_self]
        simp only [mul_one]
  have hPQ : P * Q = leavittWordS A * leavittWordT A := by
    dsimp [P, Q]
    calc
      (leavittWordS A * leavittWordT B) *
          (leavittWordS B * leavittWordT A) =
        leavittWordS A *
          (leavittWordT B * leavittWordS B) *
          leavittWordT A := by noncomm_ring
      _ = _ := by rw [leavittWordT_mul_wordS_self]; simp only [mul_one]
  have hQP : Q * P = leavittWordS B * leavittWordT B := by
    dsimp [P, Q]
    calc
      (leavittWordS B * leavittWordT A) *
          (leavittWordS A * leavittWordT B) =
        leavittWordS B *
          (leavittWordT A * leavittWordS A) *
          leavittWordT B := by noncomm_ring
      _ = _ := by rw [leavittWordT_mul_wordS_self]; simp only [mul_one]
  change
    (1 + leavittWordS (E.word i) *
      (leavittWordS a * leavittWordT b) * leavittWordT (E.word j)) *
      (1 + leavittWordS (E.word j) *
        (leavittWordS b * leavittWordT a) * leavittWordT (E.word i)) *
      (1 + leavittWordS (E.word i) *
        (leavittWordS a * leavittWordT b) * leavittWordT (E.word j)) = _
  have hleft :
      leavittWordS (E.word i) *
          (leavittWordS a * leavittWordT b) * leavittWordT (E.word j) =
        P := by
    dsimp [P, A, B]
    rw [leavittWordS_append, leavittWordT_append]
    noncomm_ring
  have hright :
      leavittWordS (E.word j) *
          (leavittWordS b * leavittWordT a) * leavittWordT (E.word i) =
        Q := by
    dsimp [Q, A, B]
    rw [leavittWordS_append, leavittWordT_append]
    noncomm_ring
  rw [hleft, hright,
    cylinder_transposition_factorization P Q hPP hPQP,
    hPQ, hQP]
  rfl

private theorem samePrefixCylinderSwap_mem {ι : Type*} [DecidableEq ι]
    (E : BinaryPrefixCode ι)
    (i j : ι) (hij : i ≠ j)
    (a b c : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    cylinderSwap (E.word i ++ a) (E.word i ++ b)
        (prepend_not_prefix_prepend (E.word i) a b hab)
        (prepend_not_prefix_prepend (E.word i) b a hba) ∈
      prefixElementaryGroup E := by
  let x := prefixCrossSwap E i j hij a c
  let y := prefixCrossSwap E i j hij b c
  have hx : x ∈ prefixElementaryGroup E :=
    prefixCrossSwap_mem E i j hij a c
  have hy : y ∈ prefixElementaryGroup E :=
    prefixCrossSwap_mem E i j hij b c
  have hfactor : x * y * x =
      cylinderSwap (E.word i ++ a) (E.word i ++ b)
        (prepend_not_prefix_prepend (E.word i) a b hab)
        (prepend_not_prefix_prepend (E.word i) b a hba) := by
    apply Units.ext
    change
      (↑(prefixCrossSwap E i j hij a c) : BinaryLeavitt) *
          (↑(prefixCrossSwap E i j hij b c) : BinaryLeavitt) *
          (↑(prefixCrossSwap E i j hij a c) : BinaryLeavitt) =
        PrefixCompression.wordSwapValue (E.word i ++ a) (E.word i ++ b)
    rw [prefixCrossSwap_val, prefixCrossSwap_val]
    exact transpositionValue_braid
      (leavittWordS (E.word i ++ a))
      (leavittWordT (E.word i ++ a))
      (leavittWordS (E.word i ++ b))
      (leavittWordT (E.word i ++ b))
      (leavittWordS (E.word j ++ c))
      (leavittWordT (E.word j ++ c))
      (leavittWordT_mul_wordS_self (E.word i ++ a))
      (leavittWordT_mul_wordS_self (E.word i ++ b))
      (leavittWordT_mul_wordS_self (E.word j ++ c))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word i ++ a) (E.word i ++ b)
        (prepend_not_prefix_prepend (E.word i) a b hab)
        (prepend_not_prefix_prepend (E.word i) b a hba))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word i ++ b) (E.word i ++ a)
        (prepend_not_prefix_prepend (E.word i) b a hba)
        (prepend_not_prefix_prepend (E.word i) a b hab))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word i ++ a) (E.word j ++ c)
        (append_not_prefix_append (E.word i) (E.word j) a c
          (E.prefix_free hij) (E.prefix_free hij.symm))
        (append_not_prefix_append (E.word j) (E.word i) c a
          (E.prefix_free hij.symm) (E.prefix_free hij)))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word j ++ c) (E.word i ++ a)
        (append_not_prefix_append (E.word j) (E.word i) c a
          (E.prefix_free hij.symm) (E.prefix_free hij))
        (append_not_prefix_append (E.word i) (E.word j) a c
          (E.prefix_free hij) (E.prefix_free hij.symm)))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word i ++ b) (E.word j ++ c)
        (append_not_prefix_append (E.word i) (E.word j) b c
          (E.prefix_free hij) (E.prefix_free hij.symm))
        (append_not_prefix_append (E.word j) (E.word i) c b
          (E.prefix_free hij.symm) (E.prefix_free hij)))
      (leavittWordT_mul_wordS_of_incomparable
        (E.word j ++ c) (E.word i ++ b)
        (append_not_prefix_append (E.word j) (E.word i) c b
          (E.prefix_free hij.symm) (E.prefix_free hij))
        (append_not_prefix_append (E.word i) (E.word j) b c
          (E.prefix_free hij) (E.prefix_free hij.symm)))
  rw [← hfactor]
  exact (prefixElementaryGroup E).mul_mem
    ((prefixElementaryGroup E).mul_mem hx hy) hx

private theorem sourceLocal_cylinderSwap_mem_alpha
    (a b : List (Fin 2))
    (hab : ¬ a <+: b) (hba : ¬ b <+: a) :
    prefixInsertionHom [0, 0, 0, 1] (cylinderSwap a b hab hba) ∈
      prefixElementaryGroup alphaPrefixCode := by
  rw [prefixInsertionHom_cylinderSwap]
  have h := samePrefixCylinderSwap_mem alphaPrefixCode
    (0 : Fin 3) (1 : Fin 3) (by decide)
    ([1] ++ a) ([1] ++ b) []
    (prepend_not_prefix_prepend [1] a b hab)
    (prepend_not_prefix_prepend [1] b a hba)
  simpa only [alphaPrefixCode, Fin.isValue, List.cons_append, List.nil_append, alphaWord] using h

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def binaryPrefixTranspositionGroup : Subgroup BinaryLeavittˣ :=
  Subgroup.closure
    {z | ∃ (a b : List (Fin 2))
      (hab : ¬ a <+: b) (hba : ¬ b <+: a),
      cylinderSwap a b hab hba = z}

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def localPrefixTranspositionGroup
    (l : List (Fin 2)) : Subgroup BinaryLeavittˣ :=
  binaryPrefixTranspositionGroup.map (prefixInsertionHom l)

private theorem localPrefixTranspositionGroup_le_cylinderCorner
    (l : List (Fin 2)) :
    localPrefixTranspositionGroup l ≤ cylinderCornerGroup l := by
  rintro _ ⟨u, _, rfl⟩
  exact prefixInsertionHom_mem_cylinderCorner l u

private theorem localPrefixTranspositionGroup_le_sourceCylinderCorner
    (l : List (Fin 2)) :
    localPrefixTranspositionGroup l ≤
      ThompsonPrefixLocal.cylinderCornerGroup l := by
  rw [← cylinderCornerGroup_eq_source]
  exact localPrefixTranspositionGroup_le_cylinderCorner l

private theorem sourceLocalPrefixTranspositionGroup_le_alpha :
    localPrefixTranspositionGroup [0, 0, 0, 1] ≤
      prefixElementaryGroup alphaPrefixCode := by
  apply (Subgroup.map_le_iff_le_comap).2
  apply (Subgroup.closure_le _).2
  rintro _ ⟨a, b, hab, hba, rfl⟩
  exact sourceLocal_cylinderSwap_mem_alpha a b hab hba

public
theorem sourceLocalPrefixTranspositionGroup_le_alpha_sourceWord :
    localPrefixTranspositionGroup [0, 0, 0, 1] ≤
      prefixElementaryGroup alphaPrefixCode := by
  exact sourceLocalPrefixTranspositionGroup_le_alpha

private theorem sourceLocalPrefixTranspositionGroup_le_nine :
    localPrefixTranspositionGroup [0, 0, 0, 1] ≤
      prefixElementaryGroup ninePrefixCode :=
  sourceLocalPrefixTranspositionGroup_le_alpha_sourceWord.trans
    SourceGeneration.alphaPrefixElementaryGroup_le_nine

private theorem sourceLocalPrefixTranspositionGroup_le_centralizer_alphaZero :
    localPrefixTranspositionGroup [0, 0, 0, 1] ≤
      Subgroup.centralizer
        (prefixElementaryGroup alphaZeroPrefixCode : Set BinaryLeavittˣ) :=
  (localPrefixTranspositionGroup_le_sourceCylinderCorner
    [0, 0, 0, 1]).trans
    ThompsonPrefixLocal.localCylinderCorner_le_centralizer_alphaZero

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def sourceCompressedLocalProductHom :
    (prefixElementaryGroup alphaZeroPrefixCode ×
      localPrefixTranspositionGroup [0, 0, 0, 1]) →*
        BinaryLeavittˣ where
  toFun x := (x.1 : BinaryLeavittˣ) * (x.2 : BinaryLeavittˣ)
  map_one' := by simp only [Prod.fst_one, OneMemClass.coe_one, Prod.snd_one, mul_one]
  map_mul' p q := by
    have hcomm :
        (q.1 : BinaryLeavittˣ) * (p.2 : BinaryLeavittˣ) =
          (p.2 : BinaryLeavittˣ) * (q.1 : BinaryLeavittˣ) :=
      Subgroup.mem_centralizer_iff.mp
        (sourceLocalPrefixTranspositionGroup_le_centralizer_alphaZero
          p.2.property)
        (q.1 : BinaryLeavittˣ) q.1.property
    change
      ((p.1 : BinaryLeavittˣ) * (q.1 : BinaryLeavittˣ)) *
          ((p.2 : BinaryLeavittˣ) * (q.2 : BinaryLeavittˣ)) =
        ((p.1 : BinaryLeavittˣ) * (p.2 : BinaryLeavittˣ)) *
          ((q.1 : BinaryLeavittˣ) * (q.2 : BinaryLeavittˣ))
    calc
      ((p.1 : BinaryLeavittˣ) * (q.1 : BinaryLeavittˣ)) *
          ((p.2 : BinaryLeavittˣ) * (q.2 : BinaryLeavittˣ)) =
        (p.1 : BinaryLeavittˣ) *
          (((q.1 : BinaryLeavittˣ) * (p.2 : BinaryLeavittˣ)) *
            (q.2 : BinaryLeavittˣ)) := by simp only [mul_assoc]
      _ = (p.1 : BinaryLeavittˣ) *
          (((p.2 : BinaryLeavittˣ) * (q.1 : BinaryLeavittˣ)) *
            (q.2 : BinaryLeavittˣ)) := by rw [hcomm]
      _ = ((p.1 : BinaryLeavittˣ) * (p.2 : BinaryLeavittˣ)) *
          ((q.1 : BinaryLeavittˣ) * (q.2 : BinaryLeavittˣ)) := by
            simp only [mul_assoc]

private theorem sourceCompressedLocalProductHom_range_le_nine :
    sourceCompressedLocalProductHom.range ≤
      prefixElementaryGroup ninePrefixCode := by
  rintro _ ⟨⟨k, j⟩, rfl⟩
  exact (prefixElementaryGroup ninePrefixCode).mul_mem
    (SourceGeneration.alphaPrefixElementaryGroup_le_nine
      (alphaZero_prefixElementaryGroup_le k.property))
    (sourceLocalPrefixTranspositionGroup_le_nine j.property)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def sourceCompressedLocalProductEmbedding :
    (prefixElementaryGroup alphaZeroPrefixCode ×
      localPrefixTranspositionGroup [0, 0, 0, 1]) →*
        prefixElementaryGroup ninePrefixCode :=
  sourceCompressedLocalProductHom.codRestrict
    (prefixElementaryGroup ninePrefixCode)
    (fun x => sourceCompressedLocalProductHom_range_le_nine ⟨x, rfl⟩)

end ThompsonPrefixInsertion

namespace MidrankPermutationEnergy

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def partitionVertexMidrank {V : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U) (b : V → ℤ) (x : V) : ℝ :=
  componentVertexMidrank (P.part x) b x

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def rankDecreasingVertices {V : Type*}
    (U : Finset V) (b : V → ℤ) (p : Equiv.Perm V) : Finset V :=
  U.filter (fun x => b (p x) < b x)

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def offsetFloorRank {V : Type*} (u : V → ℝ) (H r : ℝ) : V → ℤ :=
  fun x => ⌊(u x + r) / H⌋

private def midpointDecreasingVertices {V : Type*} [DecidableEq V]
    {U : Finset V} (P : Finpartition U) (b : V → ℤ)
    (p : Equiv.Perm V) : Finset V :=
  U.filter (fun x => partitionVertexMidrank P b (p x) <
    partitionVertexMidrank P b x)

end MidrankPermutationEnergy

namespace RankArcCharging

open scoped BigOperators

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def selectedRankSupport
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ) : Finset V :=
  P.parts.biUnion (fun C => C.filter (fun x => b x = j C))

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def rankChangingArc
    {V : Type*}
    (U : Finset V) (b : V → ℤ) (w : Equiv.Perm V) : Finset V :=
  U.filter (fun x => b (w x) ≠ b x)

private def rankSupportPreimageBad
    {V : Type*} [DecidableEq V]
    (U S : Finset V) (w : Equiv.Perm V) : Finset V :=
  U.filter (fun x => w x ∈ U \ S)

end RankArcCharging

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def permutationDistance {V : Type*} [Fintype V] [DecidableEq V]
    (p q : Equiv.Perm V) : ℕ :=
  hammingDist (fun x => p x) (fun x => q x)

@[simp]
public
theorem permutationDistance_self {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) : permutationDistance p p = 0 := by
  simp only [permutationDistance, hammingDist_self]

private theorem permutationDistance_comm {V : Type*} [Fintype V] [DecidableEq V]
    (p q : Equiv.Perm V) : permutationDistance p q = permutationDistance q p := by
  exact hammingDist_comm _ _

private theorem permutationDistance_triangle {V : Type*}
    [Fintype V] [DecidableEq V] (p q r : Equiv.Perm V) :
    permutationDistance p r ≤ permutationDistance p q + permutationDistance q r :=
  hammingDist_triangle _ _ _

private theorem permutationDistance_mul_left {V : Type*}
    [Fintype V] [DecidableEq V] (s p q : Equiv.Perm V) :
    permutationDistance (s * p) (s * q) = permutationDistance p q := by
  have h := hammingDist_comp (fun (_ : V) (x : V) => s x)
    (x := fun x => p x) (y := fun x => q x) (fun _ => s.injective)
  simpa only [permutationDistance, Equiv.Perm.mul_apply] using h

private theorem permutationDistance_mul_right {V : Type*}
    [Fintype V] [DecidableEq V] (s p q : Equiv.Perm V) :
    permutationDistance (p * s) (q * s) = permutationDistance p q := by
  unfold permutationDistance hammingDist
  apply Finset.card_bij (fun x _ => s x)
  · intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [Equiv.Perm.mul_apply] using (Finset.mem_filter.mp hx).2
  · intro x hx y hy h
    exact s.injective h
  · intro y hy
    refine ⟨s.symm y, ?_, by simp only [Equiv.apply_symm_apply]⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using
      (Finset.mem_filter.mp hy).2

private theorem permutationDistance_mul_le {V : Type*}
    [Fintype V] [DecidableEq V] (p p' q q' : Equiv.Perm V) :
    permutationDistance (p * q) (p' * q') ≤
      permutationDistance p p' + permutationDistance q q' := by
  calc
    permutationDistance (p * q) (p' * q') ≤
        permutationDistance (p * q) (p' * q) +
          permutationDistance (p' * q) (p' * q') :=
      permutationDistance_triangle _ _ _
    _ = permutationDistance p p' + permutationDistance q q' := by
      rw [permutationDistance_mul_right, permutationDistance_mul_left]

private theorem permutationDistance_inv {V : Type*}
    [Fintype V] [DecidableEq V] (p q : Equiv.Perm V) :
    permutationDistance p⁻¹ q⁻¹ = permutationDistance p q := by
  calc
    permutationDistance p⁻¹ q⁻¹ =
        permutationDistance (q * p⁻¹) (q * q⁻¹) :=
      (permutationDistance_mul_left q p⁻¹ q⁻¹).symm
    _ = permutationDistance (q * p⁻¹) 1 := by simp only [mul_inv_cancel]
    _ = permutationDistance ((q * p⁻¹) * p) (1 * p) :=
      (permutationDistance_mul_right p (q * p⁻¹) 1).symm
    _ = permutationDistance q p := by simp only [inv_mul_cancel_right, one_mul]
    _ = permutationDistance p q := permutationDistance_comm q p

@[simp]
public
theorem permutationCommutationDefect_one {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) :
    permutationCommutationDefect σ 1 = 0 := by
  simp only [permutationCommutationDefect, Equiv.Perm.coe_one, id_eq, ne_eq, not_true_eq_false,
    Finset.filter_false, Finset.card_empty, Finset.sum_const_zero]

private theorem permutationCommutationDefect_inv {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (c : Equiv.Perm V) :
    permutationCommutationDefect σ c⁻¹ = permutationCommutationDefect σ c := by
  classical
  unfold permutationCommutationDefect
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.card_bij (fun x _ => c⁻¹ x)
  · intro x hx
    have hbad := (Finset.mem_filter.mp hx).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro heq
    apply hbad
    apply c.injective
    simpa only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using heq.symm
  · intro x hx y hy heq
    exact (c⁻¹).injective heq
  · intro y hy
    have hbad := (Finset.mem_filter.mp hy).2
    refine ⟨c y, ?_, by simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro heq
    apply hbad
    have heq' := congrArg c heq
    simpa only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, Equiv.apply_symm_apply] using heq'.symm

private theorem permutationCommutationDefect_mul_le {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (p q : Equiv.Perm V) :
    permutationCommutationDefect σ (p * q) ≤
      permutationCommutationDefect σ p + permutationCommutationDefect σ q := by
  classical
  unfold permutationCommutationDefect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  let Bp : Finset V :=
    Finset.univ.filter fun x => p (σ i x) ≠ σ i (p x)
  let Bq : Finset V :=
    Finset.univ.filter fun x => q (σ i x) ≠ σ i (q x)
  let C : Finset V :=
    Finset.univ.filter fun x => q x ∈ Bp
  have hC : C.card = Bp.card := by
    apply Finset.card_bij (fun x _ => q x)
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro x hx y hy hxy
      exact q.injective hxy
    · intro y hy
      refine ⟨q.symm y, ?_, by simp only [Equiv.apply_symm_apply]⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by simpa only [Equiv.apply_symm_apply] using hy⟩
  have hsub :
      (Finset.univ.filter fun x =>
        (p * q) (σ i x) ≠ σ i ((p * q) x)) ⊆ Bq ∪ C := by
    intro x hx
    have hbad := (Finset.mem_filter.mp hx).2
    by_cases hq : q (σ i x) = σ i (q x)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hp
      apply hbad
      simpa only [Equiv.Perm.mul_apply, hq] using hp
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
  calc
    (Finset.univ.filter fun x =>
      (p * q) (σ i x) ≠ σ i ((p * q) x)).card ≤
        (Bq ∪ C).card := Finset.card_le_card hsub
    _ ≤ Bq.card + C.card := Finset.card_union_le Bq C
    _ = Bp.card + Bq.card := by rw [hC, Nat.add_comm]

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure AlmostCentralizerElement {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) where
  /-- Internal interface connecting the split non-sofic proof modules. -/
  permutation : Equiv.Perm V
  defect_le : permutationCommutationDefect σ permutation ≤ tolerance

@[ext (iff := false)]
private theorem AlmostCentralizerElement.ext {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (p q : AlmostCentralizerElement σ tolerance)
    (h : p.permutation = q.permutation) : p = q := by
  cases p with
  | mk p hp =>
    cases q with
    | mk q hq =>
      cases h
      rfl

private structure AlmostCentralizerGap {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) : Prop where
  dichotomy : ∀ p q : AlmostCentralizerElement σ tolerance,
    5 * permutationDistance p.permutation q.permutation ≤ Fintype.card V ∨
      4 * Fintype.card V <
        5 * permutationDistance p.permutation q.permutation

private def almostCentralizerSetoid {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ)
    (hgap : AlmostCentralizerGap σ tolerance) :
    Setoid (AlmostCentralizerElement σ tolerance) where
  r p q := 5 * permutationDistance p.permutation q.permutation ≤ Fintype.card V
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      simp only [permutationDistance_self, mul_zero, zero_le]
    · intro p q hpq
      simpa only [permutationDistance_comm q.permutation p.permutation] using hpq
    · intro p q r hpq hqr
      rcases hgap.dichotomy p r with hclose | hfar
      · exact hclose
      · have htri := permutationDistance_triangle
          p.permutation q.permutation r.permutation
        omega

private abbrev AlmostCentralizerClusters {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ)
    (hgap : AlmostCentralizerGap σ tolerance) :=
  Quotient (almostCentralizerSetoid σ tolerance hgap)

private def almostCentralizerCluster {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (p : AlmostCentralizerElement σ tolerance) :
    AlmostCentralizerClusters σ tolerance hgap :=
  Quotient.mk (almostCentralizerSetoid σ tolerance hgap) p

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure AlmostCentralizerRepair {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) where
  /-- Internal interface connecting the split non-sofic proof modules. -/
  correct : Equiv.Perm V → Equiv.Perm V
  corrected_defect : ∀ p q : AlmostCentralizerElement σ tolerance,
    permutationCommutationDefect σ
      (correct (p.permutation * q.permutation)) ≤ tolerance
  corrected_distance : ∀ p q : AlmostCentralizerElement σ tolerance,
    5 * permutationDistance
      (correct (p.permutation * q.permutation))
      (p.permutation * q.permutation) ≤ Fintype.card V

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure HasAlmostCentralizerImprovement {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) : Prop where
  improve : ∀ p : Equiv.Perm V,
    permutationCommutationDefect σ p ≤ 2 * tolerance →
      ∃ q : Equiv.Perm V,
        permutationCommutationDefect σ q ≤ tolerance ∧
          5 * permutationDistance q p ≤ Fintype.card V

private def almostCentralizerRepairOfImprovement {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (h : HasAlmostCentralizerImprovement σ tolerance) :
    AlmostCentralizerRepair σ tolerance := by
  classical
  let correction : Equiv.Perm V → Equiv.Perm V := fun p =>
    if hp : permutationCommutationDefect σ p ≤ 2 * tolerance then
      (h.improve p hp).choose
    else p
  refine ⟨correction, ?_, ?_⟩
  · intro p q
    have hprod := permutationCommutationDefect_mul_le σ
      p.permutation q.permutation
    have hp := p.defect_le
    have hq := q.defect_le
    have hgood : permutationCommutationDefect σ
        (p.permutation * q.permutation) ≤ 2 * tolerance := by
      omega
    change permutationCommutationDefect σ
      (correction (p.permutation * q.permutation)) ≤ tolerance
    simpa [correction, hgood] using
      (h.improve (p.permutation * q.permutation) hgood).choose_spec.1
  · intro p q
    have hprod := permutationCommutationDefect_mul_le σ
      p.permutation q.permutation
    have hp := p.defect_le
    have hq := q.defect_le
    have hgood : permutationCommutationDefect σ
        (p.permutation * q.permutation) ≤ 2 * tolerance := by
      omega
    change 5 * permutationDistance
      (correction (p.permutation * q.permutation))
      (p.permutation * q.permutation) ≤ Fintype.card V
    simpa [correction, hgood] using
      (h.improve (p.permutation * q.permutation) hgood).choose_spec.2

private def correctedAlmostCentralizerProduct {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (R : AlmostCentralizerRepair σ tolerance)
    (p q : AlmostCentralizerElement σ tolerance) :
    AlmostCentralizerElement σ tolerance :=
  ⟨R.correct (p.permutation * q.permutation), R.corrected_defect p q⟩

private theorem correctedAlmostCentralizerProduct_congr {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (R : AlmostCentralizerRepair σ tolerance)
    {p p' q q' : AlmostCentralizerElement σ tolerance}
    (hp : 5 * permutationDistance p.permutation p'.permutation ≤
      Fintype.card V)
    (hq : 5 * permutationDistance q.permutation q'.permutation ≤
      Fintype.card V) :
    5 * permutationDistance
      (correctedAlmostCentralizerProduct R p q).permutation
      (correctedAlmostCentralizerProduct R p' q').permutation ≤
        Fintype.card V := by
  let a := correctedAlmostCentralizerProduct R p q
  let b := correctedAlmostCentralizerProduct R p' q'
  have ha := R.corrected_distance p q
  have hb := R.corrected_distance p' q'
  have hmul := permutationDistance_mul_le
    p.permutation p'.permutation q.permutation q'.permutation
  have htri₁ := permutationDistance_triangle a.permutation
    (p.permutation * q.permutation) b.permutation
  have htri₂ := permutationDistance_triangle
    (p.permutation * q.permutation)
    (p'.permutation * q'.permutation) b.permutation
  have hsym :
      permutationDistance (p'.permutation * q'.permutation) b.permutation =
        permutationDistance b.permutation
          (p'.permutation * q'.permutation) :=
    permutationDistance_comm _ _
  change 5 * permutationDistance a.permutation b.permutation ≤
    Fintype.card V
  rcases hgap.dichotomy a b with hclose | hfar
  · exact hclose
  · change 4 * Fintype.card V <
      5 * permutationDistance a.permutation b.permutation at hfar
    change 5 * permutationDistance a.permutation
      (p.permutation * q.permutation) ≤ Fintype.card V at ha
    change 5 * permutationDistance b.permutation
      (p'.permutation * q'.permutation) ≤ Fintype.card V at hb
    omega

private def almostCentralizerClusterMul {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (R : AlmostCentralizerRepair σ tolerance) :
    AlmostCentralizerClusters σ tolerance hgap →
      AlmostCentralizerClusters σ tolerance hgap →
        AlmostCentralizerClusters σ tolerance hgap :=
  Quotient.map₂ (correctedAlmostCentralizerProduct R)
    (fun _ _ hp _ _ hq =>
      correctedAlmostCentralizerProduct_congr hgap R hp hq)

private def almostCentralizerOne {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) :
    AlmostCentralizerElement σ tolerance :=
  ⟨1, by simp only [permutationCommutationDefect_one, zero_le]⟩

private def almostCentralizerInverse {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (p : AlmostCentralizerElement σ tolerance) :
    AlmostCentralizerElement σ tolerance :=
  ⟨p.permutation⁻¹, by
    rw [permutationCommutationDefect_inv]
    exact p.defect_le⟩

private def almostCentralizerClusterInv {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance) :
    AlmostCentralizerClusters σ tolerance hgap →
      AlmostCentralizerClusters σ tolerance hgap :=
  Quotient.map almostCentralizerInverse (by
    intro p q hpq
    change 5 * permutationDistance p.permutation⁻¹ q.permutation⁻¹ ≤
      Fintype.card V
    rwa [permutationDistance_inv])

private theorem correctedAlmostCentralizerProduct_assoc {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (R : AlmostCentralizerRepair σ tolerance)
    (p q r : AlmostCentralizerElement σ tolerance) :
    5 * permutationDistance
      (correctedAlmostCentralizerProduct R
        (correctedAlmostCentralizerProduct R p q) r).permutation
      (correctedAlmostCentralizerProduct R p
        (correctedAlmostCentralizerProduct R q r)).permutation ≤
        Fintype.card V := by
  let a := correctedAlmostCentralizerProduct R p q
  let b := correctedAlmostCentralizerProduct R q r
  let l := correctedAlmostCentralizerProduct R a r
  let t := correctedAlmostCentralizerProduct R p b
  have hl := R.corrected_distance a r
  have ht := R.corrected_distance p b
  have ha := R.corrected_distance p q
  have hb := R.corrected_distance q r
  have ha' :
      5 * permutationDistance
        (a.permutation * r.permutation)
        ((p.permutation * q.permutation) * r.permutation) ≤
          Fintype.card V := by
    rw [permutationDistance_mul_right]
    exact ha
  have hb' :
      5 * permutationDistance
        ((p.permutation * q.permutation) * r.permutation)
        (p.permutation * b.permutation) ≤ Fintype.card V := by
    rw [mul_assoc, permutationDistance_mul_left,
      permutationDistance_comm]
    exact hb
  have ht' :
      5 * permutationDistance
        (p.permutation * b.permutation) t.permutation ≤
          Fintype.card V := by
    rw [permutationDistance_comm]
    exact ht
  have htri₁ := permutationDistance_triangle l.permutation
    (a.permutation * r.permutation) t.permutation
  have htri₂ := permutationDistance_triangle
    (a.permutation * r.permutation)
    ((p.permutation * q.permutation) * r.permutation) t.permutation
  have htri₃ := permutationDistance_triangle
    ((p.permutation * q.permutation) * r.permutation)
    (p.permutation * b.permutation) t.permutation
  change 5 * permutationDistance l.permutation t.permutation ≤
    Fintype.card V
  rcases hgap.dichotomy l t with hclose | hfar
  · exact hclose
  · change 4 * Fintype.card V <
      5 * permutationDistance l.permutation t.permutation at hfar
    change 5 * permutationDistance l.permutation
      (a.permutation * r.permutation) ≤ Fintype.card V at hl
    omega

@[instance_reducible]
private def almostCentralizerClusterGroup {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    {σ : ι → Equiv.Perm V} {tolerance : ℕ}
    (hgap : AlmostCentralizerGap σ tolerance)
    (R : AlmostCentralizerRepair σ tolerance) :
    Group (AlmostCentralizerClusters σ tolerance hgap) := by
  letI : One (AlmostCentralizerClusters σ tolerance hgap) :=
    ⟨almostCentralizerCluster hgap (almostCentralizerOne σ tolerance)⟩
  letI : Mul (AlmostCentralizerClusters σ tolerance hgap) :=
    ⟨almostCentralizerClusterMul hgap R⟩
  letI : Inv (AlmostCentralizerClusters σ tolerance hgap) :=
    ⟨almostCentralizerClusterInv hgap⟩
  apply Group.ofLeftAxioms
  · intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ p q r =>
      apply Quotient.sound
      exact correctedAlmostCentralizerProduct_assoc hgap R p q r
  · intro x
    induction x using Quotient.inductionOn with
    | _ p =>
      apply Quotient.sound
      change 5 * permutationDistance
        (R.correct (1 * p.permutation)) p.permutation ≤ Fintype.card V
      simpa only [one_mul, almostCentralizerOne] using R.corrected_distance (almostCentralizerOne σ
        tolerance) p
  · intro x
    induction x using Quotient.inductionOn with
    | _ p =>
      apply Quotient.sound
      change 5 * permutationDistance
        (R.correct (p.permutation⁻¹ * p.permutation)) 1 ≤ Fintype.card V
      simpa only [inv_mul_cancel, almostCentralizerInverse] using
        R.corrected_distance (almostCentralizerInverse p) p

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure ExpandingCentralizerFiniteModel (G : Type*) [Group G]
    (F : Finset G) where
  /-- Internal interface connecting the split non-sofic proof modules. -/
  vertices : Type
  /-- Internal interface connecting the split non-sofic proof modules. -/
  [verticesFintype : Fintype vertices]
  /-- Internal interface connecting the split non-sofic proof modules. -/
  [verticesDecidableEq : DecidableEq vertices]
  /-- Internal interface connecting the split non-sofic proof modules. -/
  generatorIndex : Type
  /-- Internal interface connecting the split non-sofic proof modules. -/
  [generatorFintype : Fintype generatorIndex]
  /-- Internal interface connecting the split non-sofic proof modules. -/
  generators : generatorIndex → Equiv.Perm vertices
  /-- Internal interface connecting the split non-sofic proof modules. -/
  tolerance : ℕ
  /-- Internal interface connecting the split non-sofic proof modules. -/
  cheeger : ℝ
  cheeger_positive : 0 < cheeger
  expansion : ∀ A : Finset vertices,
    cheeger * min (A.card : ℝ)
        ((Fintype.card vertices : ℝ) - A.card) ≤
      (boundary generators A : ℝ)
  small : (10 : ℝ) * tolerance < cheeger * Fintype.card vertices
  /-- Internal interface connecting the split non-sofic proof modules. -/
  repair : AlmostCentralizerRepair generators tolerance
  /-- Internal interface connecting the split non-sofic proof modules. -/
  approximation : G → AlmostCentralizerElement generators tolerance
  map_one : (approximation 1).permutation = 1
  multiplicative : ∀ x ∈ F, ∀ y ∈ F,
    5 * permutationDistance (approximation (x * y)).permutation
      ((approximation x).permutation * (approximation y).permutation) ≤
        Fintype.card vertices
  separated : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
    Fintype.card vertices <
      5 * permutationDistance
        (approximation x).permutation (approximation y).permutation

private instance expandingCentralizerFiniteModelVerticesFintype
    {G : Type*} [Group G] {F : Finset G}
    (M : ExpandingCentralizerFiniteModel G F) : Fintype M.vertices :=
  M.verticesFintype

private instance expandingCentralizerFiniteModelVerticesDecidableEq
    {G : Type*} [Group G] {F : Finset G}
    (M : ExpandingCentralizerFiniteModel G F) : DecidableEq M.vertices :=
  M.verticesDecidableEq

private instance expandingCentralizerFiniteModelGeneratorFintype
    {G : Type*} [Group G] {F : Finset G}
    (M : ExpandingCentralizerFiniteModel G F) : Fintype M.generatorIndex :=
  M.generatorFintype

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def expandingCentralizerFiniteModelOfImprovement
    {G : Type*} [Group G] (F : Finset G)
    {V ι : Type} [Fintype V] [DecidableEq V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ) (h : ℝ)
    (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤ (boundary σ A : ℝ))
    (hsmall : (10 : ℝ) * tolerance < h * Fintype.card V)
    (himprove : HasAlmostCentralizerImprovement σ tolerance)
    (f : G → AlmostCentralizerElement σ tolerance)
    (hone : (f 1).permutation = 1)
    (hmul : ∀ x ∈ F, ∀ y ∈ F,
      5 * permutationDistance (f (x * y)).permutation
        ((f x).permutation * (f y).permutation) ≤ Fintype.card V)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
      Fintype.card V < 5 * permutationDistance
        (f x).permutation (f y).permutation) :
    ExpandingCentralizerFiniteModel G F where
  vertices := V
  verticesFintype := inferInstance
  verticesDecidableEq := inferInstance
  generatorIndex := ι
  generatorFintype := inferInstance
  generators := σ
  tolerance := tolerance
  cheeger := h
  cheeger_positive := hpositive
  expansion := hexp
  small := hsmall
  repair := almostCentralizerRepairOfImprovement himprove
  approximation := f
  map_one := hone
  multiplicative := hmul
  separated := hsep

namespace ExceptionalRankOffset

open Filter Topology
open scoped BigOperators

end ExceptionalRankOffset

namespace ThompsonPrefixInsertion

end ThompsonPrefixInsertion

universe u₁ u₂ u₃

section ElementaryRingQuotient

variable {ι : Type u₁} {R : Type u₂} {S : Type u₃}
  [Fintype ι] [DecidableEq ι]
  [Ring R] [Ring S]

private def elementaryMatrixUnitMap (f : R →+* S) :
    (Matrix ι ι R)ˣ →* (Matrix ι ι S)ˣ :=
  Units.map f.mapMatrix.toMonoidHom

private theorem elementaryMatrixUnitMap_elementaryUnit
    (f : R →+* S) (i j : ι) (hij : i ≠ j) (a : R) :
    elementaryMatrixUnitMap f (elementaryUnit i j hij a) =
      elementaryUnit i j hij (f a) := by
  apply Units.ext
  change f.mapMatrix (1 + Matrix.single i j a) =
    1 + Matrix.single i j (f a)
  rw [map_add, map_one]
  congr 1
  ext k l
  change f (if i = k ∧ j = l then a else 0) =
    if i = k ∧ j = l then f a else 0
  split_ifs <;> simp

private theorem elementaryGroup_map_le (f : R →+* S) :
    (elementaryGroup ι R).map (elementaryMatrixUnitMap f) ≤
      elementaryGroup ι S := by
  rw [Subgroup.map_le_iff_le_comap, elementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  change elementaryMatrixUnitMap f (elementaryUnit i j hij a) ∈
    elementaryGroup ι S
  rw [elementaryMatrixUnitMap_elementaryUnit]
  exact elementaryUnit_mem i j hij (f a)

private theorem elementaryGroup_map_eq_of_surjective
    (f : R →+* S) (hf : Function.Surjective f) :
    (elementaryGroup ι R).map (elementaryMatrixUnitMap f) =
      elementaryGroup ι S := by
  apply le_antisymm (elementaryGroup_map_le f)
  rw [elementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, b, rfl⟩
  obtain ⟨a, rfl⟩ := hf b
  refine ⟨elementaryUnit i j hij a,
    elementaryUnit_mem i j hij a, ?_⟩
  exact elementaryMatrixUnitMap_elementaryUnit f i j hij a

end ElementaryRingQuotient

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def binaryPrefixElementaryGroupEquiv
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) :
    elementaryGroup ι BinaryLeavitt ≃* prefixElementaryGroup E :=
  ((elementaryGroup ι BinaryLeavitt).equivMapOfInjective
      (prefixCornerUnitHom E) (prefixCornerUnitHom_injective E)).trans
    (MulEquiv.subgroupCongr (prefixCornerElementaryGroup_map E))

namespace CompressionCriterion

open Filter Topology

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def productTrackedTable {J : Type*} [Group J]
    (F : Finset J) : Finset J := by
  classical
  exact multiplicationTable (insert 1 F)

end CompressionCriterion

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def permutationGraph {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) : Finset (V × V) :=
  Finset.univ.image fun x => (x, p x)

namespace ThompsonPrefixInsertion

open scoped commutatorElement

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure PrefixWordAction (g : BinaryLeavittˣ)
    (a b : List (Fin 2)) : Prop where
  prefixing : (↑g : BinaryLeavitt) * leavittWordS a = leavittWordS b
  deletion :
    leavittWordT a * (↑(g⁻¹) : BinaryLeavitt) = leavittWordT b

end ThompsonPrefixInsertion

namespace LeavittElementaryMorita

open scoped BigOperators commutatorElement

section ElementaryBlockFlattening

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Ring R]

private def elementaryBlockMatrixEquiv :
    Matrix ι ι (Matrix κ κ R) ≃+*
      Matrix (ι × κ) (ι × κ) R :=
  Matrix.compRingEquiv ι κ R

private def elementaryBlockUnitEquiv :
    (Matrix ι ι (Matrix κ κ R))ˣ ≃*
      (Matrix (ι × κ) (ι × κ) R)ˣ :=
  Units.mapEquiv (elementaryBlockMatrixEquiv (ι := ι)
    (κ := κ) (R := R)).toMulEquiv

private theorem elementaryBlockUnitEquiv_elementaryUnit_single
    (i j : ι) (hij : i ≠ j) (k l : κ) (a : R) :
    elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := R)
        (elementaryUnit i j hij (Matrix.single k l a)) =
      elementaryUnit (i, k) (j, l)
        (fun h => hij (congrArg Prod.fst h)) a := by
  apply Units.ext
  change
    elementaryBlockMatrixEquiv (ι := ι) (κ := κ) (R := R)
        (1 + Matrix.single i j (Matrix.single k l a)) =
      1 + Matrix.single (i, k) (j, l) a
  rw [map_add, map_one]
  congr 1
  exact Matrix.comp_single_single i j k l a

private theorem elementaryBlockUnitEquiv_elementaryUnit_mem
    (i j : ι) (hij : i ≠ j) (A : Matrix κ κ R) :
    elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := R)
        (elementaryUnit i j hij A) ∈
      elementaryGroup (ι × κ) R := by
  induction A using Matrix.induction_on' with
  | h_zero =>
      simp only [elementaryUnit_zero, map_one, one_mem]
  | h_add A B hA hB =>
      rw [← elementaryUnit_mul, map_mul]
      exact (elementaryGroup (ι × κ) R).mul_mem hA hB
  | h_std_basis k l a =>
      rw [elementaryBlockUnitEquiv_elementaryUnit_single i j hij k l a]
      exact elementaryUnit_mem (i, k) (j, l)
        (fun h => hij (congrArg Prod.fst h)) a

private theorem elementaryBlockGroup_map [Nontrivial ι] :
    (elementaryGroup ι (Matrix κ κ R)).map
        (elementaryBlockUnitEquiv
          (ι := ι) (κ := κ) (R := R)).toMonoidHom =
      elementaryGroup (ι × κ) R := by
  let B : Subgroup (Matrix (ι × κ) (ι × κ) R)ˣ :=
    (elementaryGroup ι (Matrix κ κ R)).map
      (elementaryBlockUnitEquiv
        (ι := ι) (κ := κ) (R := R)).toMonoidHom
  have hcross (i j : ι) (hij : i ≠ j) (k l : κ) (a : R) :
      elementaryUnit (i, k) (j, l)
          (fun h => hij (congrArg Prod.fst h)) a ∈ B := by
    refine ⟨elementaryUnit i j hij (Matrix.single k l a),
      elementaryUnit_mem i j hij (Matrix.single k l a), ?_⟩
    exact elementaryBlockUnitEquiv_elementaryUnit_single
      i j hij k l a
  change B = elementaryGroup (ι × κ) R
  apply le_antisymm
  · change
      (elementaryGroup ι (Matrix κ κ R)).map
          (elementaryBlockUnitEquiv
            (ι := ι) (κ := κ) (R := R)).toMonoidHom ≤
        elementaryGroup (ι × κ) R
    rw [elementaryGroup, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, j, hij, A, rfl⟩, rfl⟩
    change
      elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := R)
          (elementaryUnit i j hij A) ∈
        elementaryGroup (ι × κ) R
    exact elementaryBlockUnitEquiv_elementaryUnit_mem
      i j hij A
  · rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, k⟩, ⟨j, l⟩, hne, a, rfl⟩
    by_cases hij : i = j
    · subst j
      obtain ⟨j, hji⟩ := exists_ne i
      exact elementaryUnit_mem_of_two_step B
        (i, k) (j, k) (i, l)
        (fun h => hji (congrArg Prod.fst h).symm)
        (fun h => hji (congrArg Prod.fst h))
        hne a
        (hcross i j hji.symm k k a)
        (hcross j i hji k l 1)
    · exact hcross i j hij k l a

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def elementaryBlockGroupEquiv [Nontrivial ι] :
    elementaryGroup ι (Matrix κ κ R) ≃*
      elementaryGroup (ι × κ) R :=
  ((elementaryBlockUnitEquiv
      (ι := ι) (κ := κ) (R := R)).subgroupMap
    (elementaryGroup ι (Matrix κ κ R))).trans
    (MulEquiv.subgroupCongr
      (elementaryBlockGroup_map (ι := ι) (κ := κ) (R := R)))

end ElementaryBlockFlattening

section ElementaryReindexing

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Ring R]

private def elementaryReindexUnitEquiv (e : ι ≃ κ) :
    (Matrix ι ι R)ˣ ≃* (Matrix κ κ R)ˣ :=
  Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv

private theorem elementaryReindexUnitEquiv_elementaryUnit
    (e : ι ≃ κ) (i j : ι) (hij : i ≠ j) (a : R) :
    elementaryReindexUnitEquiv (R := R) e
        (elementaryUnit i j hij a) =
      elementaryUnit (e i) (e j) (e.injective.ne hij) a := by
  apply Units.ext
  change
    (Matrix.reindexRingEquiv R e)
        (1 + Matrix.single i j a) =
      1 + Matrix.single (e i) (e j) a
  rw [map_add, map_one]
  congr 1
  change
    Matrix.reindex e e (Matrix.single i j a) =
      Matrix.single (e i) (e j) a
  simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
    (Matrix.submatrix_single_equiv e.symm e.symm i j a)

private theorem elementaryReindexGroup_map (e : ι ≃ κ) :
    (elementaryGroup ι R).map
        (elementaryReindexUnitEquiv (R := R) e).toMonoidHom =
      elementaryGroup κ R := by
  apply le_antisymm
  · rw [elementaryGroup, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, j, hij, a, rfl⟩, rfl⟩
    change
      elementaryReindexUnitEquiv (R := R) e
          (elementaryUnit i j hij a) ∈ elementaryGroup κ R
    rw [elementaryReindexUnitEquiv_elementaryUnit]
    exact elementaryUnit_mem (e i) (e j) (e.injective.ne hij) a
  · rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨k, l, hkl, a, rfl⟩
    have hij : e.symm k ≠ e.symm l := e.symm.injective.ne hkl
    refine ⟨elementaryUnit (e.symm k) (e.symm l) hij a,
      elementaryUnit_mem (e.symm k) (e.symm l) hij a, ?_⟩
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, Equiv.apply_symm_apply] using
      elementaryReindexUnitEquiv_elementaryUnit e (e.symm k) (e.symm l) hij a

/-- Internal interface connecting the split non-sofic proof modules. -/
public
def elementaryReindexGroupEquiv (e : ι ≃ κ) :
    elementaryGroup ι R ≃* elementaryGroup κ R :=
  ((elementaryReindexUnitEquiv (R := R) e).subgroupMap
    (elementaryGroup ι R)).trans
    (MulEquiv.subgroupCongr (elementaryReindexGroup_map e))

end ElementaryReindexing

section ElementaryCoefficientEquivalence

variable {ι R S : Type*} [Fintype ι] [DecidableEq ι]
  [Ring R] [Ring S]

private def elementaryCoefficientGroupEquiv (f : R ≃+* S) :
    elementaryGroup ι R ≃* elementaryGroup ι S :=
  ((Units.mapEquiv f.mapMatrix.toMulEquiv).subgroupMap
    (elementaryGroup ι R)).trans
    (MulEquiv.subgroupCongr (by
      change
        (elementaryGroup ι R).map
          (elementaryMatrixUnitMap f.toRingHom) =
            elementaryGroup ι S
      exact elementaryGroup_map_eq_of_surjective
        f.toRingHom f.surjective))

end ElementaryCoefficientEquivalence

private def ternaryLeavittWord : Fin 3 → List (Fin 2)
  | 0 => [0, 0]
  | 1 => [0, 1]
  | _ => [1]

private def ternaryLeavittPrefixCode : BinaryPrefixCode (Fin 3) where
  word := ternaryLeavittWord
  prefix_free := by decide

private theorem ternaryLeavittPrefixCode_complete :
    MatrixCorner.codeIdempotent
        (fun i => leavittWordS (ternaryLeavittPrefixCode.word i))
        (fun i => leavittWordT (ternaryLeavittPrefixCode.word i)) =
      1 := by
  have hzero :
      leavittCylinder [0, 0] + leavittCylinder [0, 1] =
        leavittCylinder [0] := by
    simpa only [Fin.isValue, List.cons_append, List.nil_append] using (leavittCylinder_split
      [0]).symm
  have hroot :
      leavittCylinder [0] + leavittCylinder [1] = 1 := by
    simpa only [leavittCylinder, leavittWordS, Fin.isValue, mul_one, leavittWordT, one_mul,
      List.nil_append] using
      (leavittCylinder_split ([] : List (Fin 2))).symm
  have hsum :
      leavittCylinder [0, 0] + leavittCylinder [0, 1] +
          leavittCylinder [1] = 1 := by
    rw [hzero]
    exact hroot
  simpa only [MatrixCorner.codeIdempotent, ternaryLeavittPrefixCode, ternaryLeavittWord,
    Fin.isValue,
    Fin.sum_univ_succ, Fin.succ_ne_zero, imp_self, Fin.succ_zero_eq_one, Finset.univ_unique,
      Fin.default_eq_zero,
    Finset.sum_singleton, Fin.succ_one_eq_two, leavittCylinder, add_assoc] using hsum

private def binaryLeavittMatrixThreeEquiv :
    BinaryLeavitt ≃+* Matrix (Fin 3) (Fin 3) BinaryLeavitt :=
  (completePrefixMatrixEquiv ternaryLeavittPrefixCode
    ternaryLeavittPrefixCode_complete).symm

private def binaryLeavittElementaryThreeEquivNine :
    binaryLeavittElementaryGroup 3 ≃*
      binaryLeavittElementaryGroup 9 :=
  (elementaryCoefficientGroupEquiv
    (ι := Fin 3) binaryLeavittMatrixThreeEquiv).trans
    ((elementaryBlockGroupEquiv
      (ι := Fin 3) (κ := Fin 3) (R := BinaryLeavitt)).trans
      (elementaryReindexGroupEquiv
        (R := BinaryLeavitt) (finProdFinEquiv :
          Fin 3 × Fin 3 ≃ Fin 9)))

end LeavittElementaryMorita

namespace ThompsonFiniteGeneration

open ThompsonPrefixInsertion

end ThompsonFiniteGeneration

end

end SoficGroups

end
