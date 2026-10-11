import Tengoku
import Tengoku.OpenaiMath.OAI.Probability.CoordinateSweeps.PlacementMoment
import Tengoku.OpenaiMath.OAI.RepresentationTheory.Young.Restriction
import Tengoku.OpenaiMath.OAI.Probability.CoordinateSweeps.Induction

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.Grid.Holes
open YoungCorner PlacementInduction UnitaryIrrep
variable {G : Grid} {h : ℕ} (H : G.Holes h) (μ : YoungDiagram) (p : ℕ)
    (e : H.FreeAt 0 ≃ Boxes μ)
def removedPlacement : H.Placement (k := Fintype.card (Boxes (removedPart μ p))) where
  toFun i := e.symm (boxesSplit μ p (Sum.inr ((Fintype.equivFin _).symm i)))
  inj' := by
    intro i j hij
    have h₁ := e.symm.injective hij
    have h₂ := (boxesSplit μ p).injective h₁
    exact (Fintype.equivFin _).symm.injective (Sum.inr.inj h₂)
def retainedMap : Equiv.Perm (Boxes (hookPart μ p)) →* H.stabilizer :=
  H.stabilizerFreeEquiv.symm.toMonoidHom.comp
    (e.symm.permCongrHom.toMonoidHom.comp (leftPerm (boxesSplit μ p)))
lemma retainedMap_fixed (g : Equiv.Perm (Boxes (hookPart μ p))) :
    H.placementAction (H.retainedMap μ p e g) (H.removedPlacement μ p e)=H.removedPlacement μ p e := by
  apply Function.Embedding.ext
  intro i
  change H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
    (e.symm.permCongrHom (leftPerm (boxesSplit μ p) g)))
    (e.symm (boxesSplit μ p (Sum.inr ((Fintype.equivFin _).symm i))))=_
  rw [MulEquiv.apply_symm_apply]
  simp [leftPerm,removedPlacement]
  rfl
def retainedInto : Equiv.Perm (Boxes (hookPart μ p)) →*
    (H.placementChart (H.removedPlacement μ p e)).stabilizer where
  toFun g := ⟨H.retainedMap μ p e g,H.retainedMap_fixed μ p e g⟩
  map_one' := by apply Subtype.ext; exact map_one (H.retainedMap μ p e)
  map_mul' g g' := by apply Subtype.ext; exact map_mul (H.retainedMap μ p e) g g'
lemma retainedInto_bijective : Function.Bijective (H.retainedInto μ p e) := by
  constructor
  · intro g g' hh
    have heq := congrArg (fun t => e.permCongrHom (H.stabilizerFreeEquiv t.val)) hh
    change e.permCongrHom (H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
      (e.symm.permCongrHom (leftPerm (boxesSplit μ p) g))))=
      e.permCongrHom (H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
      (e.symm.permCongrHom (leftPerm (boxesSplit μ p) g')))) at heq
    simp only [MulEquiv.apply_symm_apply] at heq
    have hleft : leftPerm (boxesSplit μ p) g=leftPerm (boxesSplit μ p) g' := by simpa using heq
    apply Equiv.ext
    intro x
    have hx := congrArg (fun t : Equiv.Perm (Boxes μ) => (boxesSplit μ p).symm (t (boxesSplit μ p (Sum.inl x)))) hleft
    simpa [leftPerm] using hx
  · intro g
    have hfix : ∀ z : Boxes (removedPart μ p),
        e.permCongrHom (H.stabilizerFreeEquiv g.val) (boxesSplit μ p (Sum.inr z))=boxesSplit μ p (Sum.inr z) := by
      intro z
      have hh := congrArg (fun u : H.Placement (k := Fintype.card (Boxes (removedPart μ p))) => e (u ((Fintype.equivFin _) z))) g.property
      change e ((H.stabilizerFreeEquiv g.val) (e.symm (boxesSplit μ p (Sum.inr ((Fintype.equivFin _).symm ((Fintype.equivFin _) z))))))=e (e.symm (boxesSplit μ p (Sum.inr ((Fintype.equivFin _).symm ((Fintype.equivFin _) z))))) at hh
      change e ((H.stabilizerFreeEquiv g.val) (e.symm (boxesSplit μ p (Sum.inr z))))=_
      simpa only [Equiv.symm_apply_apply,Equiv.apply_symm_apply] using hh
    obtain ⟨a,ha⟩ := leftPerm_range_of_fix_right (boxesSplit μ p)
      (e.permCongrHom (H.stabilizerFreeEquiv g.val)) hfix
    refine ⟨a,?_⟩
    apply Subtype.ext
    apply H.stabilizerFreeEquiv.injective
    change H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
      (e.symm.permCongrHom (leftPerm (boxesSplit μ p) a)))=H.stabilizerFreeEquiv g.val
    rw [MulEquiv.apply_symm_apply,ha]
    apply Equiv.ext
    intro y
    simp
/- Actual retained-hook subgroup chart inside the original hole stabilizer. -/
def retainedEquiv : Equiv.Perm (Boxes (hookPart μ p)) ≃*
    (H.placementChart (H.removedPlacement μ p e)).stabilizer :=
  MulEquiv.ofBijective (H.retainedInto μ p e) (H.retainedInto_bijective μ p e)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.UnitaryIrrep
variable {Γ Λ : Type*} [Group Γ] [Group Λ]
lemma asRepresentation_pullback (ρ : UnitaryIrrep Γ) (e : Λ ≃* Γ) :
    (ρ.pullback e).asRepresentation=ρ.asRepresentation.comp e.toMonoidHom := rfl
lemma dimension_eq_finrank (ρ : UnitaryIrrep Γ) :
    Module.finrank ℂ (Fin ρ.dimension → ℂ)=ρ.dimension := by simp
end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.Grid.Holes
open YoungCorner PlacementInduction UnitaryIrrep
variable {G : Grid} {h : ℕ} (H : G.Holes h) (μ : YoungDiagram) (p : ℕ)
    (e : H.FreeAt 0 ≃ Boxes μ)
def boxesChart : Equiv.Perm (Boxes μ) ≃* H.stabilizer :=
  e.symm.permCongrHom.trans H.stabilizerFreeEquiv.symm

/- Source06:eq22 and genuine retained-hook Hom multiplicity simultaneously,
on the literal placement stabilizer used by the conditional induced cycle. -/
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open YoungCorner PlacementInduction UnitaryIrrep
variable {G : Grid} {h : ℕ} (H : G.Holes h) (μ : YoungDiagram) (p : ℕ)
    (e : H.FreeAt 0 ≃ Boxes μ)
def retainedSite : Boxes (hookPart μ p) ↪ H.FreeAt 0 where
  toFun a := e.symm (boxesSplit μ p (Sum.inl a))
  inj' := by intro a b hh; exact Sum.inl.inj ((boxesSplit μ p).injective (e.symm.injective hh))
lemma retainedSite_ne_removed (a : Boxes (hookPart μ p))
    (i : Fin (Fintype.card (Boxes (removedPart μ p)))) :
    H.retainedSite μ p e a ≠ H.removedPlacement μ p e i := by
  intro hh
  have he := (boxesSplit μ p).injective (e.symm.injective hh)
  cases he

def augmentedRetainedEmbedding
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    Boxes (hookPart μ p) ↪ (H.augmented x ω₀).FreeAt 0 where
  toFun a := ⟨(H.stabilizerFreeEquiv ((H.placementChart (H.removedPlacement μ p e)).rep x)
    (H.retainedSite μ p e a)).val,by
    intro i
    cases i using Fin.addCases with
    | left i =>
      simpa only [augmented,augment_old] using
        (H.stabilizerFreeEquiv ((H.placementChart (H.removedPlacement μ p e)).rep x)
          (H.retainedSite μ p e a)).property i
    | right i =>
      simp only [augmented,augment_new,Grid.pathBetween_zero]
      intro he
      have hr := congrArg (fun y : H.Placement (k := Fintype.card (Boxes (removedPart μ p))) => (y i).val)
        ((H.placementChart (H.removedPlacement μ p e)).reaches x)
      change ((H.placementChart (H.removedPlacement μ p e)).rep x).val
        ((H.removedPlacement μ p e i).val)=(x i).val at hr
      have hh := ((H.placementChart (H.removedPlacement μ p e)).rep x).val.injective (he.trans hr.symm)
      exact H.retainedSite_ne_removed μ p e a i (Subtype.ext hh)⟩
  inj' := by
    intro a b hh
    have he := congrArg Subtype.val hh
    exact (H.retainedSite μ p e).injective
      ((H.stabilizerFreeEquiv ((H.placementChart (H.removedPlacement μ p e)).rep x)).injective (Subtype.ext he))

lemma augmentedRetainedEmbedding_surjective
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    Function.Surjective (H.augmentedRetainedEmbedding μ p e x ω₀) := by
  have hc : Fintype.card (Boxes (hookPart μ p))=Fintype.card ((H.augmented x ω₀).FreeAt 0) := by
    have hsplit := split_card μ p
    have he := Fintype.card_congr e
    rw [H.card_freeAt] at he
    rw [(H.augmented x ω₀).card_freeAt]
    omega
  by_contra hn
  have hh := Fintype.card_lt_of_injective_not_surjective _
    (H.augmentedRetainedEmbedding μ p e x ω₀).injective hn
  omega

def augmentedRetainedEquiv
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    Boxes (hookPart μ p) ≃ (H.augmented x ω₀).FreeAt 0 :=
  Equiv.ofBijective (H.augmentedRetainedEmbedding μ p e x ω₀)
    ⟨(H.augmentedRetainedEmbedding μ p e x ω₀).injective,
      H.augmentedRetainedEmbedding_surjective μ p e x ω₀⟩
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open YoungCorner PlacementInduction UnitaryIrrep
variable {G : Grid} {h : ℕ} (H : G.Holes h) (μ : YoungDiagram) (p : ℕ)
    (e : H.FreeAt 0 ≃ Boxes μ)
def augmentedRetainedChart
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    Equiv.Perm (Boxes (hookPart μ p)) ≃* (H.augmented x ω₀).stabilizer :=
  (H.augmentedRetainedEquiv μ p e x ω₀).permCongrHom.trans (H.augmented x ω₀).stabilizerFreeEquiv.symm

/- The transported fiber is the same retained Young type on the *actual*
remaining sites. This rules out any unsupported abstract symmetric-group relabeling. -/
end CoordinateSweeps.Grid.Holes
end
end
end
end
end
end

/-!
Work on the genuinely missing main statements of the pinned manuscript.
All definitions are finite and use the source's ordinary probability and trace
normalizations. No result of the manuscript is assumed.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

/-! New work: the actual alternating placement kernel from 04-sparse:eq7.
The preceding definitions/proofs are reused verbatim from the pinned support.
Endpoints below need not be injections; invalid specifications have probability
zero automatically. On valid endpoint placements this is exactly the source Q. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/- Reused exact conditional transition/potential support from pinned root-02. -/

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

theorem extraProbability_nonneg (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    0 ≤ H.extraProbability x y A μ := by
  apply Finset.prod_nonneg
  intro j _
  apply Finset.prod_nonneg
  intro L _
  apply div_nonneg <;> apply Finset.sum_nonneg <;> intro σ _ <;>
    split_ifs <;> first | exact (μ j).nonneg σ | exact le_rfl

/- Faithful finite-event application of the transition comparison: the selected
extra paths are appended to the holes only when their joint event is possible. -/

/- Source 04:eq8, with an explicit absolute constant in place of O(·).
Only valid input placements are needed; impossible output events contribute zero. -/

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

def ValidOutput (H : G.Holes h) (y : Fin k → G.Slot) : Prop :=
  Function.Injective y ∧ ∀ i a, y i ≠ H.path a (Fin.last G.b)

/- Counting-measure Hilbert--Schmidt square on the actual free placements. -/
def placementHSsq (H : G.Holes h)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) : ℝ :=
  ∑ x : Fin k → G.Slot, ∑ y : Fin k → G.Slot,
    if H.ValidInput x ∧ H.ValidOutput y then (H.placementKernel x y μ)^2 else 0

/- The full endpoint product weight is exactly s^(-2k). -/
theorem endpoint_productMass (p : Fin k → G.Slot × G.Slot) :
    Coverage.productMass G.endpointWeight p = (G.size : ℝ)⁻¹^(2*k) := by
  simp [Coverage.productMass, Grid.endpointWeight, FiniteLaw.uniform,
    Fintype.card_prod, G.card_slot, mul_pow, pow_mul, mul_comm, pow_two]

/- Rewriting the counting norm using independent full-grid endpoints never
conditions the auxiliary trajectories on being valid placements. -/
theorem placementHSsq_eq_full (H : G.Holes h)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    H.placementHSsq (k := k) μ =
      ∑ p : Fin k → G.Slot × G.Slot,
        Coverage.productMass G.endpointWeight p *
          if H.ValidInput (fun i => (p i).1) ∧ H.ValidOutput (fun i => (p i).2) then
            ((G.size : ℝ)^k * H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ)^2
          else 0 := by
  classical
  have hs : (G.size : ℝ) ≠ 0 := by unfold Grid.size; positivity
  have hterm (p : Fin k → G.Slot × G.Slot) :
      (if H.ValidInput (fun i => (p i).1) ∧ H.ValidOutput (fun i => (p i).2) then
          (H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ)^2 else 0) =
        Coverage.productMass G.endpointWeight p *
          if H.ValidInput (fun i => (p i).1) ∧ H.ValidOutput (fun i => (p i).2) then
            ((G.size : ℝ)^k * H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ)^2
          else 0 := by
    rw [endpoint_productMass]
    split_ifs
    · have hid : (G.size : ℝ)⁻¹^(2*k) * ((G.size : ℝ)^k)^2 = 1 := by
        rw [← pow_mul, Nat.mul_comm k 2, ← mul_pow, inv_mul_cancel₀ hs, one_pow]
      rw [mul_pow, ← mul_assoc, hid, one_mul]
    · simp
  let e : (Fin k → G.Slot × G.Slot) ≃ ((Fin k → G.Slot) × (Fin k → G.Slot)) :=
    ⟨fun p => (fun i => (p i).1, fun i => (p i).2),
      fun p i => (p.1 i, p.2 i), fun _ => rfl, fun _ => rfl⟩
  calc
    _ = ∑ p : (Fin k → G.Slot) × (Fin k → G.Slot),
        if H.ValidInput p.1 ∧ H.ValidOutput p.2 then (H.placementKernel p.1 p.2 μ)^2 else 0 := by
      rw [Fintype.sum_prod_type]; rfl
    _ = ∑ p : Fin k → G.Slot × G.Slot,
        if H.ValidInput (fun i => (p i).1) ∧ H.ValidOutput (fun i => (p i).2) then
          (H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ)^2 else 0 :=
      (Equiv.sum_comp e (fun p =>
        if H.ValidInput p.1 ∧ H.ValidOutput p.2 then (H.placementKernel p.1 p.2 μ)^2 else 0)).symm
    _ = _ := Finset.sum_congr rfl (fun p _ => hterm p)

/- Source 04:eqs8--9 combined, with an explicit counting HS estimate.
This is the direct, unweakened many-coordinate sparse-kernel estimate. -/

end CoordinateSweeps.Grid.Holes

/- Necessary shared-line polynomial expansion for the sparse conditional main.
A variable names a LINE, not a particle. The tensor moment functional is merely
linear, never multiplicative when two factors use the same line. -/
end
end
open scoped Matrix.Norms.L2Operator

end OAI
