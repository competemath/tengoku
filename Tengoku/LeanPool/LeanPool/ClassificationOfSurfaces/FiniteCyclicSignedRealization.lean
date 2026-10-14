/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.FiniteCyclicRealization
public import Tengoku

/-!
# Polygonal realization under signed presentation isomorphism

A signed presentation isomorphism may rename and independently reverse edge names, relabel faces,
and cyclically rotate each stored face word. This file realizes those operations geometrically.
The selected cyclic rotation acts on the circular polygon carrier by an exact complex rotation,
so every labelled source side is sent to the target side carrying its relabelled dart.

The resulting homeomorphism of polygonal pre-realizations transports both the elementary gluing
generators and their equivalence closures. It therefore descends to a homeomorphism of the faithful
polygonal quotients.
-/

@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

open Complex

namespace PolygonCell

/-- The `rotationUnit` declaration. -/
noncomputable def rotationUnit (n k : ℕ) : Circle :=
  Circle.exp (2 * Real.pi * k / n)

/-- The `rotateHomeomorph` declaration. -/
noncomputable def rotateHomeomorph {n m : ℕ} (h : n = m) (k : ℕ) :
    PolygonCell n ≃ₜ PolygonCell m := by
  subst m
  exact
    { toFun := fun z => ⟨(rotationUnit n k : ℂ) * z.val, by
        rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero, norm_mul,
          Circle.norm_coe, one_mul]
        simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using z.property⟩
      invFun := fun z => ⟨((rotationUnit n k)⁻¹ : Circle) * z.val, by
        rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero, norm_mul,
          Circle.norm_coe, one_mul]
        simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using z.property⟩
      left_inv := by
        intro z
        apply PolygonCell.ext
        dsimp
        rw [← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero (rotationUnit n k)), one_mul]
      right_inv := by
        intro z
        apply PolygonCell.ext
        dsimp
        rw [← mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero (rotationUnit n k)), one_mul]
      continuous_toFun := by
        apply continuous_induced_rng.2
        fun_prop
      continuous_invFun := by
        apply continuous_induced_rng.2
        fun_prop }

/--
@isnad1 id=eq.1h4v.s7.e0b3a9c82976 from=translated src=- shape=5fd2484d vocab=3956888a
-/
@[simp]
theorem rotateHomeomorph_apply_val {n m : ℕ} (h : n = m) (k : ℕ)
    (z : PolygonCell n) :
    (rotateHomeomorph h k z).val = (rotationUnit n k : ℂ) * z.val :=
  by
    subst m
    rfl

/-- The `rotateIndex` declaration. -/
def rotateIndex {n : ℕ} (hn : 0 < n) (k : ℕ) (i : Fin n) : Fin n :=
  ⟨(i.val + k) % n, Nat.mod_lt _ hn⟩

/--
@isnad1 id=eq.1h3v.s5.ab1dd342bb17 from=translated src=- shape=e4d922bf vocab=66a0b8b0
-/
@[simp]
theorem rotateIndex_val {n : ℕ} (hn : 0 < n) (k : ℕ) (i : Fin n) :
    (rotateIndex hn k i).val = (i.val + k) % n :=
  rfl

/--
@isnad1 id=eq.1h4v.s7.7138be24e87f from=translated src=- shape=2ccf4c95 vocab=e8cf2ecc
-/
theorem rotateHomeomorph_side {n : ℕ} (hn : 0 < n) (k : ℕ)
    (i : Fin n) (t : unitInterval) :
    rotateHomeomorph (Eq.refl n) k (side i t) =
      side (rotateIndex hn k i) t := by
  apply PolygonCell.ext
  change ((Circle.exp (2 * Real.pi * k / n) : Circle) : ℂ) *
      ((Circle.exp (sideAngle i t) : Circle) : ℂ) =
    ((Circle.exp (sideAngle (rotateIndex hn k i) t) : Circle) : ℂ)
  rw [← Circle.coe_mul, ← Circle.exp_add]
  apply congrArg (fun z : Circle => (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  refine ⟨Int.ofNat ((i.val + k) / n), ?_⟩
  simp only [sideAngle, rotateIndex_val]
  have hdecomp : (i.val + k) % n + n * ((i.val + k) / n) = i.val + k :=
    Nat.mod_add_div (i.val + k) n
  have hdecompR := congrArg (fun q : ℕ => (q : ℝ)) hdecomp
  push_cast at hdecompR
  have hquot :
      ((Int.ofNat ((i.val + k) / n) : ℤ) : ℝ) =
        (((i.val + k) / n : ℕ) : ℝ) := by
    rfl
  rw [hquot]
  field_simp [hn.ne']
  nlinarith [hdecompR]

/-- Rotation sends a side to the correspondingly shifted side after changing only the phantom
side-count index.
@isnad1 id=eq.2h5v.s7.29633fcddf19 from=translated src=- shape=9fa19f0f vocab=34ef9020
-/
theorem rotateHomeomorph_side_of_eq {n m : ℕ} (h : n = m) (hm : 0 < m) (k : ℕ)
    (i : Fin n) (t : unitInterval) :
    rotateHomeomorph h k (side i t) =
      side
        (⟨(i.val + k) % m, Nat.mod_lt _ hm⟩ : Fin m) t := by
  subst m
  exact rotateHomeomorph_side hm k i t

end PolygonCell

namespace FiniteCyclicPresentation.SignedPresentationIso

open SurfaceCellComplex

variable {P Q : FiniteCyclicPresentation}

/-- The target-boundary rotation selected for a signed presentation isomorphism. -/
noncomputable def faceRotation (e : SignedPresentationIso P Q) (f : P.Face) : ℕ :=
  Classical.choose (e.boundary_rotated f).symm

/--
@isnad1 id=eq.0h4v.s6.41475b3c7cc7 from=translated src=- shape=816d61e6 vocab=47917b39
-/
theorem rotate_target_boundary (e : SignedPresentationIso P Q) (f : P.Face) :
    (Q.boundary (e.faceEquiv f)).rotate (e.faceRotation f) =
      (P.boundary f).map e.edgeRelabeling.mapDart :=
  Classical.choose_spec (e.boundary_rotated f).symm

/-- The target side occupied by a source side after the selected face rotation. -/
noncomputable def sideIndex (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    Fin (Q.boundary (e.faceEquiv f)).length := by
  have hpos : 0 < (Q.boundary (e.faceEquiv f)).length :=
    List.length_pos_of_ne_nil (validQ.2.1 (e.faceEquiv f))
  exact ⟨(i.val + e.faceRotation f) %
    (Q.boundary (e.faceEquiv f)).length, Nat.mod_lt _ hpos⟩

/--
@isnad1 id=eq.1h5v.s7.f0257be9da03 from=translated src=- shape=7ebe6ee9 vocab=67268f9e
-/
@[simp]
theorem sideIndex_val (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    (e.sideIndex validQ f i).val =
      (i.val + e.faceRotation f) %
        (Q.boundary (e.faceEquiv f)).length :=
  rfl

/-- The rotated target side carries exactly the relabeled source dart.
@isnad1 id=eq.1h5v.s6.fe0978266acd from=translated src=- shape=66c1bfb0 vocab=2f125374
-/
theorem boundary_get_sideIndex (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length) :
    (Q.boundary (e.faceEquiv f)).get (e.sideIndex validQ f i) =
      e.edgeRelabeling.mapDart ((P.boundary f).get i) := by
  let target := Q.boundary (e.faceEquiv f)
  let mapped := (P.boundary f).map e.edgeRelabeling.mapDart
  have hrot : target.rotate (e.faceRotation f) = mapped :=
    e.rotate_target_boundary f
  have hlen : target.length = mapped.length := by
    rw [← hrot, List.length_rotate]
  have hiTarget : i.val < target.length := by
    rw [hlen]
    simpa only [mapped, List.length_map] using i.isLt
  have hpoint :
      (target.rotate (e.faceRotation f))[i.val]? = mapped[i.val]? :=
    congrArg (fun word => word[i.val]?) hrot
  rw [List.getElem?_rotate hiTarget] at hpoint
  have hmapped :
      mapped[i.val]? =
        some (e.edgeRelabeling.mapDart ((P.boundary f).get i)) := by
    simp [mapped, i.isLt]
  rw [hmapped] at hpoint
  have htarget :
      target.get
          ⟨(i.val + e.faceRotation f) % target.length,
            Nat.mod_lt _ (List.length_pos_of_ne_nil
              (validQ.2.1 (e.faceEquiv f)))⟩ =
        e.edgeRelabeling.mapDart ((P.boundary f).get i) := by
    rw [← Option.some_inj, ← hpoint]
    simp
  exact htarget

/-- The disk homeomorphism on a face selected by the cyclic boundary rotation. -/
noncomputable def faceHomeomorph (e : SignedPresentationIso P Q) (f : P.Face) :
    PolygonCell (P.boundary f).length ≃ₜ
      PolygonCell (Q.boundary (e.faceEquiv f)).length :=
  PolygonCell.rotateHomeomorph (e.boundary_length_eq f) (e.faceRotation f)

/-- A signed presentation isomorphism gives a facewise homeomorphism of polygonal
pre-realizations. -/
noncomputable def preHomeomorph (e : SignedPresentationIso P Q) :
    P.PolygonalPreRealization ≃ₜ Q.PolygonalPreRealization :=
  (IsHomeomorph.sigmaMap e.faceEquiv.bijective
      (fun f => (e.faceHomeomorph f).isHomeomorph)).homeomorph
    (Sigma.map e.faceEquiv fun f => e.faceHomeomorph f)

/--
@isnad1 id=eq.0h4v.s8.fa373bcf5088 from=translated src=- shape=5d37b520 vocab=d1ffe1f3
-/
@[simp]
theorem preHomeomorph_apply_fst (e : SignedPresentationIso P Q)
    (x : P.PolygonalPreRealization) :
    (e.preHomeomorph x).1 = e.faceEquiv x.1 :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.af920617ba55 from=translated src=- shape=615e0455 vocab=0421bbea
-/
@[simp]
theorem preHomeomorph_apply_snd (e : SignedPresentationIso P Q)
    (x : P.PolygonalPreRealization) :
    (e.preHomeomorph x).2 = e.faceHomeomorph x.1 x.2 :=
  rfl

/-- On a labelled side, the pre-realization homeomorphism is exactly the selected cyclic shift.
@isnad1 id=eq.1h6v.s9.539595fe4cc6 from=translated src=- shape=1609b086 vocab=c9a729bd
-/
theorem preHomeomorph_side (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (f : P.Face)
    (i : Fin (P.boundary f).length) (t : unitInterval) :
    e.preHomeomorph ⟨f, PolygonCell.side i t⟩ =
      ⟨e.faceEquiv f, PolygonCell.side (e.sideIndex validQ f i) t⟩ := by
  apply Sigma.ext
  · rfl
  · simp only [preHomeomorph_apply_snd, faceHomeomorph]
    apply heq_of_eq
    exact PolygonCell.rotateHomeomorph_side_of_eq
        (e.boundary_length_eq f)
        (List.length_pos_of_ne_nil (validQ.2.1 (e.faceEquiv f)))
        (e.faceRotation f) i t

/-- Transport a boundary occurrence through the selected cyclic shift. -/
noncomputable def mapOccurrence (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) :
    P.BoundaryOccurrence → Q.BoundaryOccurrence
  | ⟨f, i⟩ => ⟨e.faceEquiv f, e.sideIndex validQ f i⟩

/--
@isnad1 id=eq.1h4v.s6.4a97ba365671 from=translated src=- shape=dbbf7090 vocab=f3c92b92
-/
@[simp]
theorem mapOccurrence_fst (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).1 = e.faceEquiv o.1 := by
  cases o
  rfl

/--
@isnad1 id=eq.1h4v.s7.83145e51c3d0 from=translated src=- shape=ee9aeb1f vocab=c2bf95ef
-/
@[simp]
theorem mapOccurrence_snd_val (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).2.val =
      (o.2.val + e.faceRotation o.1) %
        (Q.boundary (e.faceEquiv o.1)).length := by
  cases o
  rfl

/-- The transported occurrence carries the signed relabeling of the source dart.
@isnad1 id=eq.1h4v.s5.4e410f6330cf from=translated src=- shape=af7b753c vocab=8cdf8c73
-/
theorem mapOccurrence_dart (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).dart =
      e.edgeRelabeling.mapDart o.dart := by
  rcases o with ⟨f, i⟩
  exact e.boundary_get_sideIndex validQ f i

/-- Cyclic shifting is injective on the finite side-index type. -/
private theorem sideIndex_injective (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (f : P.Face) :
    Function.Injective (e.sideIndex validQ f) := by
  intro i j hij
  have hlen := e.boundary_length_eq f
  have hmod :
      i.val + e.faceRotation f ≡ j.val + e.faceRotation f
        [MOD (Q.boundary (e.faceEquiv f)).length] := by
    exact congrArg Fin.val hij
  have hcancel :
      i.val ≡ j.val [MOD (Q.boundary (e.faceEquiv f)).length] :=
    Nat.ModEq.add_right_cancel' (e.faceRotation f) hmod
  apply Fin.ext
  unfold Nat.ModEq at hcancel
  rw [← hlen, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hcancel
  exact hcancel

/-- Transport of boundary occurrences is injective.
@isnad1 id=injectiv.1h3v.s4.b8ca21794510 from=translated src=- shape=c7d7d62f vocab=62affc37
-/
theorem mapOccurrence_injective (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) :
    Function.Injective (e.mapOccurrence validQ) := by
  rintro ⟨f, i⟩ ⟨g, j⟩ h
  have hface : f = g := by
    apply e.faceEquiv.injective
    exact congrArg Sigma.fst h
  subst g
  have hindex : i = j := by
    apply e.sideIndex_injective validQ f
    exact eq_of_heq ((Sigma.ext_iff.mp h).2)
  subst j
  rfl

/--
@isnad1 id=eq.1h4v.s5.06444620efd2 from=translated src=- shape=c1a853b6 vocab=849da1d1
-/
@[simp]
theorem mapOccurrence_edge (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    (e.mapOccurrence validQ o).edge = e.edgeEquiv o.edge := by
  rw [BoundaryOccurrence.edge, e.mapOccurrence_dart,
    EdgeRelabeling.edgeOfDart_mapDart]
  rfl

/-- A compatible source pairing transports to a compatible target pairing. -/
noncomputable def mapPairing (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing) :
    Q.BoundaryPairing where
  source := e.mapOccurrence validQ pairing.source
  target := e.mapOccurrence validQ pairing.target
  source_ne_target :=
    (e.mapOccurrence_injective validQ).ne pairing.source_ne_target
  source_not_boundary := by
    rw [e.mapOccurrence_edge]
    exact (e.isBoundaryEdge_iff pairing.source.edge).not.mp
      pairing.source_not_boundary
  target_not_boundary := by
    rw [e.mapOccurrence_edge]
    exact (e.isBoundaryEdge_iff pairing.target.edge).not.mp
      pairing.target_not_boundary
  direction := pairing.direction
  compatible := by
    cases hdirection : pairing.direction
    · have hcompatible : pairing.target.dart = pairing.source.dart := by
        simpa only [hdirection] using pairing.compatible
      rw [e.mapOccurrence_dart, e.mapOccurrence_dart, hcompatible]
    · have hcompatible : pairing.target.dart = pairing.source.dart.flip := by
        simpa only [hdirection] using pairing.compatible
      rw [e.mapOccurrence_dart, e.mapOccurrence_dart, hcompatible,
        EdgeRelabeling.mapDart_flip]

/--
@isnad1 id=eq.1h4v.s4.b808af92b01c from=translated src=- shape=ed806b78 vocab=e59ef7e3
-/
@[simp]
theorem mapPairing_direction (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing) :
    (e.mapPairing validQ pairing).direction = pairing.direction :=
  rfl

/--
@isnad1 id=eq.1h4v.s5.2397ad5cd7c1 from=translated src=- shape=79244f45 vocab=93ea1a1d
-/
@[simp]
theorem mapPairing_source (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing) :
    (e.mapPairing validQ pairing).source =
      e.mapOccurrence validQ pairing.source :=
  rfl

/--
@isnad1 id=eq.1h4v.s5.c885e6f5bc33 from=translated src=- shape=79244f45 vocab=c124f04d
-/
@[simp]
theorem mapPairing_target (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing) :
    (e.mapPairing validQ pairing).target =
      e.mapOccurrence validQ pairing.target :=
  rfl

/-- The pre-realization homeomorphism maps an occurrence-side point to its transported side.
@isnad1 id=eq.1h5v.s8.ffdaeeb3fff8 from=translated src=- shape=55e72094 vocab=5375527c
-/
theorem preHomeomorph_occurrenceSide_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : P.BoundaryOccurrence) (t : unitInterval) :
    e.preHomeomorph ((P.occurrenceSide o).point t) =
      (Q.occurrenceSide (e.mapOccurrence validQ o)).point t := by
  rcases o with ⟨f, i⟩
  exact e.preHomeomorph_side validQ f i t

/-- Ignoring cyclic shifts, corresponding boundary-occurrence types have the same cardinality. -/
noncomputable def rawOccurrenceEquiv (e : SignedPresentationIso P Q) :
    P.BoundaryOccurrence ≃ Q.BoundaryOccurrence :=
  Equiv.sigmaCongr e.faceEquiv fun f =>
    (Fin.castOrderIso (e.boundary_length_eq f)).toEquiv

/-- The cyclic occurrence transport bundled as an equivalence. -/
noncomputable def occurrenceEquiv (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) :
    P.BoundaryOccurrence ≃ Q.BoundaryOccurrence :=
  Equiv.ofBijective (e.mapOccurrence validQ)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨e.mapOccurrence_injective validQ,
        Fintype.card_congr e.rawOccurrenceEquiv⟩)

/--
@isnad1 id=eq.1h4v.s5.48d6fde70e43 from=translated src=- shape=2f6968ac vocab=6670469f
-/
@[simp]
theorem occurrenceEquiv_apply (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (o : P.BoundaryOccurrence) :
    e.occurrenceEquiv validQ o = e.mapOccurrence validQ o :=
  rfl

/--
@isnad1 id=eq.1h4v.s5.f03de2a58cd9 from=translated src=- shape=e5ca91f0 vocab=f5a12a2d
-/
@[simp]
theorem mapOccurrence_occurrenceEquiv_symm
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    e.mapOccurrence validQ ((e.occurrenceEquiv validQ).symm o) = o :=
  (e.occurrenceEquiv validQ).apply_symm_apply o

/--
@isnad1 id=eq.1h5v.s8.a15e8ea4fd26 from=translated src=- shape=b7ad2206 vocab=7c3d74ac
-/
theorem preHomeomorph_symm_occurrenceSide_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) (t : unitInterval) :
    e.preHomeomorph.symm ((Q.occurrenceSide o).point t) =
      (P.occurrenceSide ((e.occurrenceEquiv validQ).symm o)).point t := by
  apply e.preHomeomorph.injective
  rw [e.preHomeomorph.apply_symm_apply]
  rw [e.preHomeomorph_occurrenceSide_point validQ]
  rw [e.mapOccurrence_occurrenceEquiv_symm validQ]

/--
@isnad1 id=eq.1h4v.s6.9aa53bf3d90f from=translated src=- shape=5112459f vocab=50860b86
-/
theorem occurrenceEquiv_symm_dart
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    e.edgeRelabeling.mapDart ((e.occurrenceEquiv validQ).symm o).dart =
      o.dart := by
  rw [← e.mapOccurrence_dart validQ]
  rw [e.mapOccurrence_occurrenceEquiv_symm validQ]

/--
@isnad1 id=eq.1h4v.s6.d5a4bd81cd1c from=translated src=- shape=5e680689 vocab=aa73b7ff
-/
theorem occurrenceEquiv_symm_edge
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (o : Q.BoundaryOccurrence) :
    e.edgeEquiv ((e.occurrenceEquiv validQ).symm o).edge = o.edge := by
  rw [← e.mapOccurrence_edge validQ]
  rw [e.mapOccurrence_occurrenceEquiv_symm validQ]

/-- Pull a compatible target pairing back through the occurrence equivalence. -/
noncomputable def comapPairing (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : Q.BoundaryPairing) :
    P.BoundaryPairing where
  source := (e.occurrenceEquiv validQ).symm pairing.source
  target := (e.occurrenceEquiv validQ).symm pairing.target
  source_ne_target :=
    (e.occurrenceEquiv validQ).symm.injective.ne pairing.source_ne_target
  source_not_boundary := by
    apply (e.isBoundaryEdge_iff
      ((e.occurrenceEquiv validQ).symm pairing.source).edge).not.mpr
    rw [e.occurrenceEquiv_symm_edge validQ]
    exact pairing.source_not_boundary
  target_not_boundary := by
    apply (e.isBoundaryEdge_iff
      ((e.occurrenceEquiv validQ).symm pairing.target).edge).not.mpr
    rw [e.occurrenceEquiv_symm_edge validQ]
    exact pairing.target_not_boundary
  direction := pairing.direction
  compatible := by
    cases hdirection : pairing.direction
    · have hcompatible : pairing.target.dart = pairing.source.dart := by
        simpa only [hdirection] using pairing.compatible
      apply e.edgeRelabeling.dartEquiv.injective
      simpa only [EdgeRelabeling.dartEquiv_apply,
        e.occurrenceEquiv_symm_dart validQ] using hcompatible
    · have hcompatible : pairing.target.dart = pairing.source.dart.flip := by
        simpa only [hdirection] using pairing.compatible
      apply e.edgeRelabeling.dartEquiv.injective
      rw [EdgeRelabeling.dartEquiv_apply, EdgeRelabeling.dartEquiv_apply,
        EdgeRelabeling.mapDart_flip, e.occurrenceEquiv_symm_dart,
        e.occurrenceEquiv_symm_dart]
      exact hcompatible

/--
@isnad1 id=eq.1h4v.s4.1fa8126458e4 from=translated src=- shape=33bbe75b vocab=41cd4fbe
-/
@[simp]
theorem comapPairing_direction (e : SignedPresentationIso P Q)
    (validQ : Q.IsSurfaceValid) (pairing : Q.BoundaryPairing) :
    (e.comapPairing validQ pairing).direction = pairing.direction :=
  rfl

/--
@isnad1 id=eq.1h5v.s8.09c6aa228530 from=translated src=- shape=ca5cbb35 vocab=2bff6848
-/
theorem preHomeomorph_pairing_source_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph (pairing.identification.source.point t) =
      ((e.mapPairing validQ pairing).identification.source.point t) := by
  exact e.preHomeomorph_occurrenceSide_point validQ pairing.source t

/--
@isnad1 id=eq.1h5v.s8.fbe086a8f40e from=translated src=- shape=ca5cbb35 vocab=d1cbcf86
-/
theorem preHomeomorph_pairing_target_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph (pairing.identification.target.point t) =
      ((e.mapPairing validQ pairing).identification.target.point t) := by
  exact e.preHomeomorph_occurrenceSide_point validQ pairing.target t

/--
@isnad1 id=eq.1h5v.s9.5696aa91357f from=translated src=- shape=c349a10c vocab=b4993e0d
-/
theorem preHomeomorph_pairing_parameter_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : P.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph
        (pairing.identification.target.point
          (pairing.identification.parameter t)) =
      (e.mapPairing validQ pairing).identification.target.point
        ((e.mapPairing validQ pairing).identification.parameter t) := by
  rw [e.preHomeomorph_pairing_target_point]
  rfl

/-- The facewise homeomorphism sends every source gluing generator into the target generated
relation.
@isnad1 id=r.2h5v.s9.c08b3b4f32b5 from=translated src=- shape=b3a9b09c vocab=1a57af4a
-/
theorem preHomeomorph_generator_related
    (e : SignedPresentationIso P Q) (_validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) (pairing : P.BoundaryPairing)
    (t : unitInterval) :
    Q.PolygonalGluingRel validQ
      (e.preHomeomorph (pairing.identification.source.point t))
      (e.preHomeomorph
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rw [e.preHomeomorph_pairing_source_point,
    e.preHomeomorph_pairing_parameter_point]
  exact PolygonGluing.related_of_mem
    (e.mapPairing validQ pairing).identification
    (pairing_identification_mem validQ (e.mapPairing validQ pairing)) t

/-- The facewise homeomorphism preserves the complete generated gluing relation.
@isnad1 id=r.3h5v.s8.58a1ebd565c0 from=translated src=- shape=120ddb97 vocab=108effbc
-/
theorem preHomeomorph_related
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) {x y : P.PolygonalPreRealization}
    (hxy : P.PolygonalGluingRel validP x y) :
    Q.PolygonalGluingRel validQ (e.preHomeomorph x) (e.preHomeomorph y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator (P.polygonalIdentifications validP)) x y at hxy
  induction hxy with
  | rel x y hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact e.preHomeomorph_generator_related validP validQ pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/--
@isnad1 id=eq.1h5v.s8.2bf2ee7ea502 from=translated src=- shape=1bee184e vocab=717617f5
-/
theorem preHomeomorph_symm_pairing_source_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph.symm (pairing.identification.source.point t) =
      ((e.comapPairing validQ pairing).identification.source.point t) := by
  exact e.preHomeomorph_symm_occurrenceSide_point validQ pairing.source t

/--
@isnad1 id=eq.1h5v.s8.0726b4f21b97 from=translated src=- shape=1bee184e vocab=6b9bce2a
-/
theorem preHomeomorph_symm_pairing_target_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph.symm (pairing.identification.target.point t) =
      ((e.comapPairing validQ pairing).identification.target.point t) := by
  exact e.preHomeomorph_symm_occurrenceSide_point validQ pairing.target t

/--
@isnad1 id=eq.1h5v.s9.2c3501f60957 from=translated src=- shape=ea627bb9 vocab=af07cccc
-/
theorem preHomeomorph_symm_pairing_parameter_point
    (e : SignedPresentationIso P Q) (validQ : Q.IsSurfaceValid)
    (pairing : Q.BoundaryPairing) (t : unitInterval) :
    e.preHomeomorph.symm
        (pairing.identification.target.point
          (pairing.identification.parameter t)) =
      (e.comapPairing validQ pairing).identification.target.point
        ((e.comapPairing validQ pairing).identification.parameter t) := by
  rw [e.preHomeomorph_symm_pairing_target_point]
  rfl

/-- The inverse facewise homeomorphism sends every target generator into the source relation.
@isnad1 id=r.2h5v.s9.5b32e5c5ca00 from=translated src=- shape=998e8862 vocab=841723bd
-/
theorem preHomeomorph_symm_generator_related
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) (pairing : Q.BoundaryPairing)
    (t : unitInterval) :
    P.PolygonalGluingRel validP
      (e.preHomeomorph.symm (pairing.identification.source.point t))
      (e.preHomeomorph.symm
        (pairing.identification.target.point
          (pairing.identification.parameter t))) := by
  rw [e.preHomeomorph_symm_pairing_source_point,
    e.preHomeomorph_symm_pairing_parameter_point]
  exact PolygonGluing.related_of_mem
    (e.comapPairing validQ pairing).identification
    (pairing_identification_mem validP (e.comapPairing validQ pairing)) t

/-- The inverse facewise homeomorphism preserves the complete generated relation.
@isnad1 id=r.3h5v.s9.7f51d6c6bd83 from=translated src=- shape=e1628ed6 vocab=0c30d528
-/
theorem preHomeomorph_symm_related
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) {x y : Q.PolygonalPreRealization}
    (hxy : Q.PolygonalGluingRel validQ x y) :
    P.PolygonalGluingRel validP (e.preHomeomorph.symm x)
      (e.preHomeomorph.symm y) := by
  change Relation.EqvGen
    (PolygonGluing.Generator (Q.polygonalIdentifications validQ)) x y at hxy
  induction hxy with
  | rel x y hgenerator =>
      cases hgenerator with
      | glue identification hmem t =>
          rcases hmem with ⟨pairing, rfl⟩
          exact e.preHomeomorph_symm_generator_related validP validQ pairing t
  | refl =>
      exact Relation.EqvGen.refl _
  | symm _ _ _ ih =>
      exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ =>
      exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The selected pre-realization homeomorphism identifies the two generated gluing relations.
@isnad1 id=iff.2h5v.s8.5a0781a65377 from=translated src=- shape=d4595119 vocab=108effbc
-/
theorem preHomeomorph_related_iff
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) (x y : P.PolygonalPreRealization) :
    P.PolygonalGluingRel validP x y ↔
      Q.PolygonalGluingRel validQ (e.preHomeomorph x) (e.preHomeomorph y) := by
  constructor
  · exact e.preHomeomorph_related validP validQ
  · intro hxy
    simpa only [e.preHomeomorph.symm_apply_apply] using
      e.preHomeomorph_symm_related validP validQ hxy

/-- Signed edge relabeling, face relabeling, and cyclic boundary rotation preserve the faithful
polygonal realization. -/
noncomputable def realizationHomeomorph
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    P.PolygonalRealization validP ≃ₜ Q.PolygonalRealization validQ :=
  PolygonGluing.realizationCongr e.preHomeomorph
    (e.preHomeomorph_related_iff validP validQ)

/-- Propositional realization-invariance form used by elementary-move closures.
@isnad1 id=polygona.2h3v.s4.0cabf15043c4 from=translated src=- shape=5ee3f51a vocab=b0c230dd
-/
theorem polygonallyEquivalent
    (e : SignedPresentationIso P Q) (validP : P.IsSurfaceValid)
    (validQ : Q.IsSurfaceValid) :
    P.PolygonallyEquivalent Q validP validQ :=
  ⟨e.realizationHomeomorph validP validQ⟩

end FiniteCyclicPresentation.SignedPresentationIso

end LeanEval.Topology.ClassificationOfSurfaces
