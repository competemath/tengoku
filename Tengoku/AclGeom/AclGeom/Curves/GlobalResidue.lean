/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Curves.TateResidue
import Tengoku.AclGeom.AclGeom.Curves.Differentials

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Toward the residue theorem: global adelic operators

The bounded adele spaces viewed inside the adele module are pairwise
commensurable — enlarging the divisor adds one line per point — and
the adelic multiplication operators almost-stabilize each of them, so
the global residue commutator against any projection onto a bounded
adele space is trace-class. These are the global inputs to Tate's
residue theorem `Σ_P res_P (f dg) = 0`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P6 via Tate residues).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- The bounded adele space `A(D)` as a subspace of the adele
module.-/
noncomputable def adeleSpaceIn (D : Divisor k F) :
    Submodule k ↥(adeleSubmodule k F) :=
  (adeleSpace D).comap (adeleSubmodule k F).subtype

/-- The diagonal copy of the function field inside the adele
module.-/
noncomputable def adeleDiagonalIn : Submodule k ↥(adeleSubmodule k F) :=
  (LinearMap.range (adeleDiagonal k F)).comap
    (adeleSubmodule k F).subtype

/-- The Riemann–Roch space maps to the adele module diagonally.-/
noncomputable def riemannToAdele (D : Divisor k F) :
    ↥(RiemannSpace D) →ₗ[k] ↥(adeleSubmodule k F) :=
  LinearMap.codRestrict _
    ((adeleDiagonal k F).comp (RiemannSpace D).subtype)
    fun _ ↦ adeleDiagonal_mem_adeleSubmodule _

/-- The componentwise projection onto local filtration stages, at the
ambient level: each coordinate is projected onto
`π_P^{−D(P)} O_P`.-/
noncomputable def adeleProjPi (D : Divisor k F) :
    ((P : Place k F) → F) →ₗ[k] ((P : Place k F) → F) :=
  LinearMap.pi fun P ↦
    (P.filtrationProj (D P).toNat).comp (LinearMap.proj P)

/--
@isnad1 id=eq.0h5v.s9.9dfe748d7c5e from=translated src=- shape=4c9f54e9 vocab=8caf95dd
-/
theorem adeleProjPi_apply (D : Divisor k F)
    (α : (P : Place k F) → F) (P : Place k F) :
    adeleProjPi D α P = P.filtrationProj (D P).toNat (α P) := rfl

/-- The componentwise projection preserves the adeles: the image
coordinate at `P` has order at least `−D(P)`, so the exceptional set
is inside the support of `D`.
@isnad1 id=mem.0h4v.s9.19f884545333 from=translated src=- shape=e8200244 vocab=93bc4ace
-/
theorem adeleProjPi_mem_adeleSubmodule (D : Divisor k F)
    (α : (P : Place k F) → F) :
    adeleProjPi D α ∈ adeleSubmodule k F := by
  refine Set.Finite.subset D.support.finite_toSet fun P hP ↦ ?_
  simp only [Set.mem_ofPred_eq, adeleProjPi_apply] at hP
  obtain ⟨hne, hlt⟩ := hP
  have h1 := P.filtrationProj_mem (D P).toNat (α P)
  rw [Place.mem_filtration_iff_ord] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 hne
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h0
  omega

/-- The componentwise projection as an endomorphism of the adele
module.-/
noncomputable def adeleProj (D : Divisor k F) :
    Module.End k ↥(adeleSubmodule k F) :=
  LinearMap.codRestrict _
    ((adeleProjPi D).comp (adeleSubmodule k F).subtype)
    fun α ↦ adeleProjPi_mem_adeleSubmodule D ↑α

open Classical in
/-- The single-place inclusion at the ambient level: the value `x`
concentrated at the place `P`.-/
noncomputable def adeleSinglePi (P : Place k F) :
    F →ₗ[k] ((Q : Place k F) → F) where
  toFun x := fun Q ↦ if Q = P then x else 0
  map_add' x y := by
    funext Q
    by_cases h : Q = P <;> simp [h]
  map_smul' c x := by
    funext Q
    by_cases h : Q = P <;> simp [h]

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/--
@isnad1 id=eq.1h5v.s8.1945833d5add from=translated src=- shape=d552e8b8 vocab=8faad419
-/
theorem adeleSinglePi_apply_ne (P : Place k F) {Q : Place k F}
    (hQ : Q ≠ P) (x : F) : adeleSinglePi (k := k) P x Q = 0 :=
  ite_eq_right hQ

/--
@isnad1 id=mem.0h4v.s9.701754307b95 from=translated src=- shape=3c77cc6f vocab=6322b27b
-/
theorem adeleSinglePi_mem_adeleSubmodule (P : Place k F) (x : F) :
    adeleSinglePi (k := k) P x ∈ adeleSubmodule k F := by
  refine Set.Finite.subset (Set.finite_singleton P) fun Q hQ ↦ ?_
  simp only [Set.mem_ofPred_eq] at hQ
  rw [Set.mem_singleton_iff]
  by_contra hne
  rw [adeleSinglePi_apply_ne P hne] at hQ
  exact hQ.1 rfl

/-- The single-place inclusion into the adele module.-/
noncomputable def adeleSingle (P : Place k F) :
    F →ₗ[k] ↥(adeleSubmodule k F) :=
  LinearMap.codRestrict _ (adeleSinglePi P)
    fun x ↦ adeleSinglePi_mem_adeleSubmodule P x

/-- Evaluation of an adele at a place.-/
noncomputable def adeleEval (P : Place k F) :
    ↥(adeleSubmodule k F) →ₗ[k] F :=
  (LinearMap.proj P).comp (adeleSubmodule k F).subtype

/-- The single-place block of the global residue commutator: evaluate
at `P`, apply the local commutator, include back at `P`.-/
noncomputable def blockOp (D : Divisor k F) (f g : F)
    (P : Place k F) : Module.End k ↥(adeleSubmodule k F) :=
  adeleSingle P ∘ₗ
    ((P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f) ∘ₗ
        LinearMap.mulLeft k g -
      LinearMap.mulLeft k g ∘ₗ
        (P.filtrationProj (D P).toNat ∘ₗ LinearMap.mulLeft k f)) ∘ₗ
    adeleEval P

/-- The residue of `α_P dg` vanishes at almost every place: outside
the exceptional set of `α` and the poles of `g`, both entries are
integral.
@isnad1 id=finite.0h4v.s9.4676494330f4 from=translated src=- shape=0b263a74 vocab=483e2dd5
-/
theorem residue_support_finite (g : F) (α : ↥(adeleSubmodule k F)) :
    {P : Place k F |
      P.residue ((α : (Q : Place k F) → F) P) g ≠ 0}.Finite := by
  rcases eq_or_ne g 0 with rfl | hg
  · refine Set.Finite.subset Set.finite_empty fun P hP ↦ ?_
    exact absurd (P.residue_zero_right _) hP
  refine Set.Finite.subset
    ((show Set.Finite _ from α.2).union
      (finite_setOf_one_lt_valuation hg)) fun P hP ↦ ?_
  rw [Set.mem_ofPred_eq] at hP
  rw [Set.mem_union]
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [Set.mem_ofPred_eq] at h1 h2
  push Not at h1 h2
  refine hP (P.residue_eq_zero_of_mem ?_ ?_)
  · rw [Place.mem_toSubmodule_iff]
    rcases eq_or_ne ((α : (Q : Place k F) → F) P) 0 with h3 | h3
    · rw [h3, Valuation.map_zero]
      exact zero_le
    · have h4 := h1 h3
      rw [← P.ord_nonneg_iff h3]
      omega
  · rw [Place.mem_toSubmodule_iff]
    exact h2

/-- **The residue functional of `dg`**: the finite sum of the local
residues `res_P(α_P dg)`, as a linear functional on the adele
module.-/
noncomputable def residueFunctional (g : F) :
    Module.Dual k ↥(adeleSubmodule k F) where
  toFun α := ∑ᶠ P : Place k F,
    P.residue ((α : (Q : Place k F) → F) P) g
  map_add' α β := by
    have h1 : ∀ P : Place k F,
        P.residue (((α + β : ↥(adeleSubmodule k F)) :
          (Q : Place k F) → F) P) g =
        P.residue ((α : (Q : Place k F) → F) P) g +
          P.residue ((β : (Q : Place k F) → F) P) g := by
      intro P
      have h2 : ((α + β : ↥(adeleSubmodule k F)) :
          (Q : Place k F) → F) P =
          (α : (Q : Place k F) → F) P +
            (β : (Q : Place k F) → F) P := rfl
      rw [h2, Place.residue_add_left]
    rw [finsum_congr h1]
    exact finsum_add_distrib (residue_support_finite g α)
      (residue_support_finite g β)
  map_smul' c α := by
    have h1 : ∀ P : Place k F,
        P.residue (((c • α : ↥(adeleSubmodule k F)) :
          (Q : Place k F) → F) P) g =
        c • P.residue ((α : (Q : Place k F) → F) P) g := by
      intro P
      have h2 : ((c • α : ↥(adeleSubmodule k F)) :
          (Q : Place k F) → F) P =
          c • (α : (Q : Place k F) → F) P := rfl
      rw [h2, Place.residue_smul_left]
      rfl
    rw [finsum_congr h1, ← smul_finsum]
    rfl

/--
@isnad1 id=eq.0h4v.s11.89a426a68a31 from=translated src=- shape=2656daad vocab=40d25043
-/
theorem residueFunctional_apply (g : F) (α : ↥(adeleSubmodule k F)) :
    residueFunctional g α = ∑ᶠ P : Place k F,
      P.residue ((α : (Q : Place k F) → F) P) g := rfl

/-- The residue functional is additive in its differential
parameter.
@isnad1 id=eq.0h4v.s11.5f1e839d2f95 from=translated src=- shape=d6c01d32 vocab=df8a5c26
-/
theorem residueFunctional_add (g h : F) :
    residueFunctional (k := k) (F := F) (g + h) =
      residueFunctional g + residueFunctional h := by
  ext α
  rw [LinearMap.add_apply, residueFunctional_apply,
    residueFunctional_apply, residueFunctional_apply]
  have hpoint : ∀ P : Place k F,
      P.residue ((α : (Q : Place k F) → F) P) (g + h) =
        P.residue ((α : (Q : Place k F) → F) P) g +
          P.residue ((α : (Q : Place k F) → F) P) h :=
    fun P ↦ P.residue_add_right _ _ _
  rw [finsum_congr hpoint]
  exact finsum_add_distrib (residue_support_finite g α)
    (residue_support_finite h α)

/-- The residue functional scales in its differential parameter.
@isnad1 id=eq.0h4v.s11.40da9be11913 from=translated src=- shape=86a7b02c vocab=b5e2556b
-/
theorem residueFunctional_smul (c : k) (g : F) :
    residueFunctional (k := k) (F := F) (c • g) =
      c • residueFunctional g := by
  ext α
  rw [LinearMap.smul_apply, residueFunctional_apply,
    residueFunctional_apply]
  have hpoint : ∀ P : Place k F,
      P.residue ((α : (Q : Place k F) → F) P) (c • g) =
        c • P.residue ((α : (Q : Place k F) → F) P) g := by
    intro P
    rw [P.residue_smul_right]
    rfl
  rw [finsum_congr hpoint, ← smul_finsum]

/-- The linear map sending a function to the residue differential of
its formal differential.-/
noncomputable def residueFunctionalLinearMap :
    F →ₗ[k] Module.Dual k ↥(adeleSubmodule k F) where
  toFun := residueFunctional
  map_add' := residueFunctional_add
  map_smul' := residueFunctional_smul

/--
@isnad1 id=eq.0h3v.s12.9b19df102f05 from=translated src=- shape=8d55f539 vocab=3c9e6711
-/
@[simp]
theorem residueFunctionalLinearMap_apply (g : F) :
    residueFunctionalLinearMap (k := k) (F := F) g =
      residueFunctional g := rfl

end

end AclGeom
