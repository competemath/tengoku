import Tengoku.Ulmstheorem.Lib.Ulm.Pure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extension lemmas for Ulm's theorem

This file contains the one-generator extension interface used in the hard
direction of Ulm's theorem, formulated against the classical invariants
`dim_{ℤ/pℤ}(P_α / P_{α+1})`.
-/
namespace Tengoku.Ulmstheorem end Tengoku.Ulmstheorem open Tengoku.Ulmstheorem
open Ordinal

universe u

variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]

/-! ## Kaplansky's finite-stage data -/

-- `IsProper` now lives in `Lib.Ulm.Pure`, next to `ulmHeight`, so that the
-- Section 1 definitions layer can use it without importing this file.

/-- `S_α = S ∩ G_α`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.stageAt (S : AddSubgroup G) (α : Ordinal) : AddSubgroup G :=
  S ⊓ ulmSubgroup p α

/-- Kaplansky's `S_α* = S_α ∩ p⁻¹G_{α+2}`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.kaplanskyStar (S : AddSubgroup G) (α : Ordinal) : AddSubgroup G where
  carrier := {x | x ∈ S ∧ x ∈ ulmSubgroup p α ∧
    p • x ∈ ulmSubgroup p (Order.succ (Order.succ α))}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hxS, hxα, hpx⟩ ⟨hyS, hyα, hpy⟩
    exact ⟨S.add_mem hxS hyS, (ulmSubgroup p α).add_mem hxα hyα, by
      rw [smul_add]
      exact (ulmSubgroup p (Order.succ (Order.succ α))).add_mem hpx hpy⟩
  neg_mem' := by
    rintro x ⟨hxS, hxα, hpx⟩
    exact ⟨S.neg_mem hxS, (ulmSubgroup p α).neg_mem hxα, by
      rw [smul_neg]
      exact (ulmSubgroup p (Order.succ (Order.succ α))).neg_mem hpx⟩

/-- `S_{α+1}` viewed as a subgroup of `S_α*`.-/
noncomputable def _root_.Tengoku.Ulmstheorem.stageAtSuccInStar (S : AddSubgroup G) (α : Ordinal) :
    AddSubgroup (kaplanskyStar p S α) :=
  (stageAt p S (Order.succ α)).comap (kaplanskyStar p S α).subtype

/-- The source quotient in Kaplansky's relative-Ulm map.-/
noncomputable def _root_.Tengoku.Ulmstheorem.kaplanskyDomainQuotient (S : AddSubgroup G) (α : Ordinal) : Type u :=
  kaplanskyStar p S α ⧸ stageAtSuccInStar p S α

noncomputable instance (S : AddSubgroup G) (α : Ordinal) :
    AddCommGroup (kaplanskyDomainQuotient p S α) := by
  unfold kaplanskyDomainQuotient
  infer_instance

/-- A finite height-preserving partial isomorphism, as used in Kaplansky's proof.

The stages are deliberately finite, not finitely generated pure subgroups.  Requiring
purity would make it impossible to cover a nonzero element of `G_ω`.-/
structure _root_.Tengoku.Ulmstheorem.UlmStage where
  A : AddSubgroup G
  B : AddSubgroup H
  hAfinite : Set.Finite (A : Set G)
  hBfinite : Set.Finite (B : Set H)
  e : A ≃+ B
  hφ : IsHeightPresOn p e.toAddMonoidHom

/-- The exact local interface used by Kaplansky target selection at height
`α`.  Only filtration preservation at `α`, `α+1`, and `α+2` enters the
range argument.  Keeping this separate from `UlmStage` lets cutoff-preserving
ACM stages use the same construction below their cutoff.-/
structure _root_.Tengoku.Ulmstheorem.UlmStageAt (α : Ordinal.{0}) where
  A : AddSubgroup G
  B : AddSubgroup H
  hAfinite : Set.Finite (A : Set G)
  hBfinite : Set.Finite (B : Set H)
  e : A ≃+ B
  hφ_at : ∀ x : A,
    ((x : G) ∈ ulmSubgroup p α (G := G) ↔
      (e x : H) ∈ ulmSubgroup p α (G := H))
  hφ_succ : ∀ x : A,
    ((x : G) ∈ ulmSubgroup p (Order.succ α) (G := G) ↔
      (e x : H) ∈ ulmSubgroup p (Order.succ α) (G := H))
  hφ_succSucc : ∀ x : A,
    ((x : G) ∈ ulmSubgroup p (Order.succ (Order.succ α)) (G := G) ↔
      (e x : H) ∈ ulmSubgroup p (Order.succ (Order.succ α)) (G := H))

/-- A globally height-preserving stage supplies the local three-level
interface at every height.-/
def Tengoku.Ulmstheorem.UlmStage.at (s : UlmStage p (G := G) (H := H)) (α : Ordinal.{0}) :
    UlmStageAt p (G := G) (H := H) α where
  A := s.A
  B := s.B
  hAfinite := s.hAfinite
  hBfinite := s.hBfinite
  e := s.e
  hφ_at := fun x ↦ s.hφ x α
  hφ_succ := fun x ↦ s.hφ x (Order.succ α)
  hφ_succSucc := fun x ↦ s.hφ x (Order.succ (Order.succ α))

/-- Reverse a finite partial isomorphism.-/
noncomputable def Tengoku.Ulmstheorem.UlmStage.symm (s : UlmStage p (G := G) (H := H)) :
    UlmStage p (G := H) (H := G) where
  A := s.B
  B := s.A
  hAfinite := s.hBfinite
  hBfinite := s.hAfinite
  e := s.e.symm
  hφ := by
    intro b α
    simpa using (s.hφ (s.e.symm b) α).symm

/-- A height-preserving stage isomorphism identifies Kaplansky's starred
subgroups on the two sides.-/
noncomputable def _root_.Tengoku.Ulmstheorem.kaplanskyStarEquiv
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α) :
    kaplanskyStar p s.A α ≃+ kaplanskyStar p s.B α where
  toFun x := by
    refine ⟨(s.e ⟨(x : G), x.property.1⟩ : H), ?_⟩
    refine ⟨(s.e ⟨(x : G), x.property.1⟩).prop,
      (s.hφ_at ⟨(x : G), x.property.1⟩).mp x.property.2.1, ?_⟩
    have hpxA : p • (x : G) ∈ s.A := s.A.nsmul_mem x.property.1 p
    have hmap :
        p • (s.e ⟨(x : G), x.property.1⟩ : H) =
          (s.e ⟨p • (x : G), hpxA⟩ : H) := by
      exact
        (congrArg Subtype.val
          (map_nsmul s.e p ⟨(x : G), x.property.1⟩)).symm
    rw [hmap]
    exact
      (s.hφ_succSucc ⟨p • (x : G), hpxA⟩).mp x.property.2.2
  invFun y := by
    refine ⟨(s.e.symm ⟨(y : H), y.property.1⟩ : G), ?_⟩
    have heinv :
        s.e (s.e.symm ⟨(y : H), y.property.1⟩) =
          ⟨(y : H), y.property.1⟩ := s.e.apply_symm_apply _
    refine ⟨(s.e.symm ⟨(y : H), y.property.1⟩).prop, ?_, ?_⟩
    · apply (s.hφ_at (s.e.symm ⟨(y : H), y.property.1⟩)).mpr
      simpa [heinv] using y.property.2.1
    ·
      have hpxA :
          p • (s.e.symm ⟨(y : H), y.property.1⟩ : G) ∈ s.A :=
        s.A.nsmul_mem (s.e.symm ⟨(y : H), y.property.1⟩).prop p
      apply
        (s.hφ_succSucc
          ⟨p • (s.e.symm ⟨(y : H), y.property.1⟩ : G), hpxA⟩).mpr
      have hmap :
          (s.e
            ⟨p • (s.e.symm ⟨(y : H), y.property.1⟩ : G), hpxA⟩ : H) =
            p • (y : H) := by
        calc
          (s.e
              ⟨p • (s.e.symm ⟨(y : H), y.property.1⟩ : G), hpxA⟩ : H) =
              p • (s.e (s.e.symm ⟨(y : H), y.property.1⟩) : H) := by
                exact congrArg Subtype.val
                  (map_nsmul s.e
                    p (s.e.symm ⟨(y : H), y.property.1⟩))
          _ = p • (y : H) := by
                rw [congrArg Subtype.val heinv]
      simpa [hmap] using y.property.2.2
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_add' x y := by
    ext
    simpa using congrArg Subtype.val
      (s.e.map_add ⟨(x : G), x.property.1⟩ ⟨(y : G), y.property.1⟩)

omit hp in
lemma _root_.Tengoku.Ulmstheorem.kaplanskyStarEquiv_map_stageAtSucc
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α) :
    (stageAtSuccInStar p s.A α).map
        (kaplanskyStarEquiv p s).toAddMonoidHom =
      stageAtSuccInStar p s.B α := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change
      ((kaplanskyStarEquiv p s x : kaplanskyStar p s.B α) : H) ∈
        stageAt p s.B (Order.succ α)
    change (x : G) ∈ stageAt p s.A (Order.succ α) at hx
    refine ⟨(kaplanskyStarEquiv p s x).property.1, ?_⟩
    change
      (s.e ⟨(x : G), x.property.1⟩ : H) ∈
        ulmSubgroup p (Order.succ α)
    exact (s.hφ_succ ⟨(x : G), x.property.1⟩).mp hx.2
  · intro hy
    let x : kaplanskyStar p s.A α :=
      (kaplanskyStarEquiv p s).symm y
    refine ⟨x, ?_, (kaplanskyStarEquiv p s).apply_symm_apply y⟩
    change (x : G) ∈ stageAt p s.A (Order.succ α)
    change (y : H) ∈ stageAt p s.B (Order.succ α) at hy
    refine ⟨x.property.1, ?_⟩
    apply (s.hφ_succ ⟨(x : G), x.property.1⟩).mpr
    have heq :
        (s.e ⟨(x : G), x.property.1⟩ : H) = (y : H) := by
      simp [x, kaplanskyStarEquiv]
    change
      (s.e ⟨(x : G), x.property.1⟩ : H) ∈
        ulmSubgroup p (Order.succ α)
    rw [heq]
    exact hy.2

/-- The stage isomorphism induces an additive equivalence between the finite
source quotients in Kaplansky's range maps.-/
noncomputable def _root_.Tengoku.Ulmstheorem.kaplanskyDomainEquiv
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α) :
    kaplanskyDomainQuotient p s.A α ≃+
      kaplanskyDomainQuotient p s.B α :=
  QuotientAddGroup.congr
    (stageAtSuccInStar p s.A α)
    (stageAtSuccInStar p s.B α)
    (kaplanskyStarEquiv p s)
    (kaplanskyStarEquiv_map_stageAtSucc p s)

omit hp in
 /-- Trivial extension when the prescribed generator is already in the domain subgroup.-/
lemma _root_.Tengoku.Ulmstheorem.extend_by_one_of_mem
    {A : AddSubgroup G}
    {B : AddSubgroup H} (hB : IsPure p B)
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    {g : G} (hg : g ∈ A) :
    ∃ (A' : AddSubgroup G) (hAA' : A ≤ A') (_ : g ∈ A')
      (B' : AddSubgroup H) (_ : IsPure p B') (_ : B ≤ B')
      (φ' : A' →+ B'),
        IsHeightPresOn p φ' ∧
        ∀ a : A, (φ' ⟨a, hAA' a.prop⟩ : H) = φ a := by
  refine ⟨A, le_rfl, hg, B, hB, le_rfl, φ, hφ, ?_⟩
  intro a
  rfl

omit hp in
/-- Trivial finite-stage extension when the prescribed generator is already in
the domain subgroup.-/
lemma _root_.Tengoku.Ulmstheorem.extend_by_one_fg_of_mem
    {A : AddSubgroup G} (hA : IsPure p A) (hAfg : A.FG)
    {B : AddSubgroup H} (hB : IsPure p B) (hBfg : B.FG)
    (φ : A →+ B) (hφ : IsHeightPresOn p φ)
    {g : G} (hg : g ∈ A) :
    ∃ (A' : AddSubgroup G) (_ : IsPure p A') (_ : A'.FG) (hAA' : A ≤ A') (_ : g ∈ A')
      (B' : AddSubgroup H) (_ : IsPure p B') (_ : B'.FG) (_ : B ≤ B')
      (φ' : A' →+ B'),
        IsHeightPresOn p φ' ∧
        ∀ a : A, (φ' ⟨a, hAA' a.prop⟩ : H) = φ a := by
  refine ⟨A, hA, hAfg, le_rfl, hg, B, hB, hBfg, le_rfl, φ, hφ, ?_⟩
  intro a
  rfl

/-- Adjoin one element to a subgroup by taking the supremum with its cyclic closure.-/
def _root_.Tengoku.Ulmstheorem.adjoinElem (A : AddSubgroup G) (g : G) : AddSubgroup G :=
  A ⊔ AddSubgroup.closure ({g} : Set G)

lemma _root_.Tengoku.Ulmstheorem.le_adjoinElem (A : AddSubgroup G) (g : G) : A ≤ adjoinElem A g := by
  exact le_sup_left

lemma _root_.Tengoku.Ulmstheorem.mem_adjoinElem_right (A : AddSubgroup G) (g : G) :
    g ∈ adjoinElem A g := by
  exact
    (show AddSubgroup.closure ({g} : Set G) ≤ adjoinElem A g from le_sup_right)
      (AddSubgroup.subset_closure (by simp))

lemma _root_.Tengoku.Ulmstheorem.adjoinElem_fg {A : AddSubgroup G} (hAfg : A.FG) (g : G) :
    (adjoinElem A g).FG := by
  classical
  unfold adjoinElem
  refine hAfg.sup ?_
  exact (AddSubgroup.fg_iff _).2 ⟨{g}, rfl, Set.finite_singleton g⟩

lemma _root_.Tengoku.Ulmstheorem.adjoinElem_eq_sup_zmultiples (A : AddSubgroup G) (g : G) :
    adjoinElem A g = A ⊔ AddSubgroup.zmultiples g := by
  unfold adjoinElem
  rw [AddSubgroup.zmultiples_eq_closure]
-- Tengoku: root names of this library moved to Tengoku.Ulmstheorem so they do not collide with other libraries (generated)
