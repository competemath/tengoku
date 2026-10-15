import Tengoku.NavierStokesEuler.Euler.PacketMatchingFamily
import Tengoku.NavierStokesEuler.Euler.PacketShiftedTimeGluing

/-!
# Joining an actual history with a forward elapsed-time path

The two continuous paths have matching traces. This wrapper uses the fixed
linear gluing map, proves the true time derivative through the junction,
and preserves the original ordered-word Sobolev radius.
-/

noncomputable section

namespace EulerElapsedTimePathGluing

open Set ContinuousLinearMap EulerTimeIntervalGlue EulerPacketTimePathGluing
  EulerVolterraConvolution EulerParameterWordGevrey
open scoped ContDiff

attribute [local instance] EulerPacketTimePathGluing.compactInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (S τ : ℝ) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S)
  (u : C(Icc (0 : ℝ) τ,E)) (v : C(Icc (0 : ℝ) (S-τ),E))
  (hmatch : u ⟨τ,hτ0,le_rfl⟩ = v ⟨0,le_rfl,sub_nonneg.mpr hτS⟩)

def pair : Matching (E := E) S τ hτ0 hτS :=
  ⟨(u,shiftPath S τ v),by
    change u ⟨τ,hτ0,le_rfl⟩-shiftPath S τ v ⟨τ,le_rfl,hτS⟩ = 0
    rw [shiftPath_initial S τ hτS,hmatch,sub_self]⟩

def join : C(Icc (0 : ℝ) S,E) := gluePath S τ hτ0 hτS (pair S τ hτ0 hτS u v hmatch)

/--
@isnad1 id=eq.3h5v.s13.e1187c1f9233 from=translated src=- shape=00d4acb1 vocab=935b6232
-/
theorem join_eq_projection : join S τ hτ0 hτS u v hmatch =
    gluePath S τ hτ0 hτS (matchingProjection S τ hτ0 hτS (u,shiftPath S τ v)) := by
  apply congrArg (gluePath S τ hτ0 hτS)
  apply Subtype.ext
  exact (matchingProjection_value S τ hτ0 hτS (u,shiftPath S τ v) (by
    change u ⟨τ,hτ0,le_rfl⟩ = shiftPath S τ v ⟨τ,le_rfl,hτS⟩
    rw [shiftPath_initial S τ hτS]
    exact hmatch)).symm

/--
@isnad1 id=eq.4h6v.s9.e64a5a2d6f72 from=translated src=- shape=a57a63a4 vocab=67f08f3c
-/
theorem join_extend (t : ℝ) (ht : t ∈ Icc (0 : ℝ) S) :
    extendPath S (hτ0.trans hτS) (join S τ hτ0 hτS u v hmatch) t =
      glue τ (extendPath τ hτ0 u) (fun r => extendPath (S-τ) (sub_nonneg.mpr hτS) v (r-τ)) t := by
  change glue τ (fun r => u (projIcc 0 τ hτ0 r))
      (fun r => shiftPath S τ v (projIcc τ S hτS r)) (projIcc 0 S (hτ0.trans hτS) t) = _
  rw [projIcc_of_mem (hτ0.trans hτS) ht]
  by_cases h : t ≤ τ
  · simp only [glue,h,ite_true]
    rfl
  · have hr : t ∈ Icc τ S := ⟨(not_le.mp h).le,ht.2⟩
    have he : t-τ ∈ Icc (0 : ℝ) (S-τ) :=
      ⟨sub_nonneg.mpr hr.1,sub_le_sub_right hr.2 τ⟩
    simp only [glue,h,ite_false,projIcc_of_mem hτS hr,shiftPath_apply,
      extendPath,projIcc_of_mem (sub_nonneg.mpr hτS) he]

/--
@isnad1 id=eq.3h6v.s9.f7d850583039 from=translated src=- shape=7aa0a5e5 vocab=8476cd28
-/
theorem join_left (t : Icc (0 : ℝ) τ) :
    join S τ hτ0 hτS u v hmatch ⟨t,t.property.1,t.property.2.trans hτS⟩ = u t := by
  have he := join_extend S τ hτ0 hτS u v hmatch t ⟨t.property.1,t.property.2.trans hτS⟩
  simpa only [extendPath,projIcc_of_mem (hτ0.trans hτS) ⟨t.property.1,t.property.2.trans hτS⟩,
    glue,t.property.2,ite_true,projIcc_of_mem hτ0 t.property] using he

/--
@isnad1 id=eq.3h6v.s10.1a04618e6a2b from=translated src=- shape=5fe09af8 vocab=6978c81e
-/
theorem join_right (t : Icc τ S) :
    join S τ hτ0 hτS u v hmatch ⟨t,hτ0.trans t.property.1,t.property.2⟩ =
      v ⟨(t : ℝ)-τ,sub_nonneg.mpr t.property.1,sub_le_sub_right t.property.2 τ⟩ := by
  have hreal : extendPath τ hτ0 u τ = extendPath (S-τ) (sub_nonneg.mpr hτS) v (τ-τ) := by
    simpa only [extendPath,sub_self,projIcc_of_mem hτ0 ⟨hτ0,le_rfl⟩,
      projIcc_of_mem (sub_nonneg.mpr hτS) ⟨le_rfl,sub_nonneg.mpr hτS⟩] using hmatch
  have he := join_extend S τ hτ0 hτS u v hmatch t ⟨hτ0.trans t.property.1,t.property.2⟩
  rw [glue_right τ _ _ hreal t t.property.1] at he
  simpa only [extendPath,projIcc_of_mem (hτ0.trans hτS) ⟨hτ0.trans t.property.1,t.property.2⟩,
    projIcc_of_mem (sub_nonneg.mpr hτS) ⟨sub_nonneg.mpr t.property.1,sub_le_sub_right t.property.2 τ⟩] using he

/-- Genuine within-time differentiation holds even at the joining time.
@isnad1 id=hasderiv.6h8v.s10.f08632e13a51 from=translated src=- shape=bf252e3e vocab=c62249ad
-/
theorem join_hasDerivWithinAt
    (u' : C(Icc (0 : ℝ) τ,E)) (v' : C(Icc (0 : ℝ) (S-τ),E))
    (hmatch' : u' ⟨τ,hτ0,le_rfl⟩ = v' ⟨0,le_rfl,sub_nonneg.mpr hτS⟩)
    (hu : ∀ t : Icc (0 : ℝ) τ,
      HasDerivWithinAt (extendPath τ hτ0 u) (u' t) (Icc (0 : ℝ) τ) t)
    (hv : ∀ t : Icc (0 : ℝ) (S-τ),
      HasDerivWithinAt (extendPath (S-τ) (sub_nonneg.mpr hτS) v) (v' t) (Icc (0 : ℝ) (S-τ)) t)
    (t : Icc (0 : ℝ) S) :
    HasDerivWithinAt (extendPath S (hτ0.trans hτS) (join S τ hτ0 hτS u v hmatch))
      (join S τ hτ0 hτS u' v' hmatch' t) (Icc (0 : ℝ) S) t := by
  have hr : MapsTo (fun s : ℝ => s-τ) (Icc τ S) (Icc (0 : ℝ) (S-τ)) :=
    fun s hs => ⟨sub_nonneg.mpr hs.1,sub_le_sub_right hs.2 τ⟩
  have hm : extendPath τ hτ0 u τ = extendPath (S-τ) (sub_nonneg.mpr hτS) v (τ-τ) := by
    simpa only [extendPath,sub_self,projIcc_of_mem hτ0 ⟨hτ0,le_rfl⟩,
      projIcc_of_mem (sub_nonneg.mpr hτS) ⟨le_rfl,sub_nonneg.mpr hτS⟩] using hmatch
  have hm' : extendPath τ hτ0 u' τ = extendPath (S-τ) (sub_nonneg.mpr hτS) v' (τ-τ) := by
    simpa only [extendPath,sub_self,projIcc_of_mem hτ0 ⟨hτ0,le_rfl⟩,
      projIcc_of_mem (sub_nonneg.mpr hτS) ⟨le_rfl,sub_nonneg.mpr hτS⟩] using hmatch'
  have hu' (s : ℝ) (hs : s ∈ Icc (0 : ℝ) τ) :
      HasDerivWithinAt (extendPath τ hτ0 u) (extendPath τ hτ0 u' s) (Icc (0 : ℝ) τ) s := by
    simpa only [extendPath,projIcc_of_mem hτ0 hs] using hu ⟨s,hs⟩
  have hv' (s : ℝ) (hs : s ∈ Icc τ S) :
      HasDerivWithinAt (fun r => extendPath (S-τ) (sub_nonneg.mpr hτS) v (r-τ))
        (extendPath (S-τ) (sub_nonneg.mpr hτS) v' (s-τ)) (Icc τ S) s := by
    have hd := (hv ⟨s-τ,hr hs⟩).scomp s ((hasDerivAt_id s).sub_const τ).hasDerivWithinAt hr
    simpa only [one_smul,Function.comp_def,id_eq,extendPath,
      projIcc_of_mem (sub_nonneg.mpr hτS) (hr hs)] using hd
  have hd := glue_hasDerivWithinAt S τ hτ0 hτS (extendPath τ hτ0 u)
    (fun r => extendPath (S-τ) (sub_nonneg.mpr hτS) v (r-τ))
    (extendPath τ hτ0 u') (fun r => extendPath (S-τ) (sub_nonneg.mpr hτS) v' (r-τ))
    hm hm' hu' hv' t t.property
  rw [← join_extend S τ hτ0 hτS u' v' hmatch' t t.property] at hd
  simpa only [extendPath,projIcc_of_mem (hτ0.trans hτS) t.property] using
    hd.congr_of_mem (fun s hs => join_extend S τ hτ0 hτS u v hmatch s hs) t.property

section Parameter

variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype ι]
  (p : X → C(Icc (0 : ℝ) τ,E)) (q : X → C(Icc (0 : ℝ) (S-τ),E))
  (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
  (hm : ∀ x, p x ⟨τ,hτ0,le_rfl⟩ = q x ⟨0,le_rfl,sub_nonneg.mpr hτS⟩)

include hp hq hm in
/--
@isnad1 id=contdiff.5h6v.s10.cf9ac6c8b008 from=translated src=- shape=2c0dee30 vocab=54ba3054
-/
theorem join_contDiff : ContDiff ℝ ∞ (fun x => join S τ hτ0 hτS (p x) (q x) (hm x)) := by
  simp_rw [join_eq_projection]
  exact (glueOperator (E := E) S τ hτ0 hτS).contDiff.comp
    (matchingFamily_contDiff S τ hτ0 hτS p (fun x => shiftPath S τ (q x))
      hp ((shiftPath (E := E) S τ).contDiff.comp hq))

include hp hq hm in
/-- The fixed Sobolev block is bounded by the sum of the input blocks, with
no new radius or derivative factor from the time junction.
@isnad1 id=le.5h11v.s10.72c486cc9396 from=translated src=- shape=aa4659af vocab=cc94168b
-/
theorem join_block_bound (directions : ι → X) (k n : ℕ) (x : X) :
    block directions k (fun y => join S τ hτ0 hτS (p y) (q y) (hm y)) n x ≤
      block directions k p n x+block directions k q n x := by
  simp_rw [join_eq_projection]
  have hm' (y) : p y ⟨τ,hτ0,le_rfl⟩ = shiftPath S τ (q y) ⟨τ,le_rfl,hτS⟩ := by
    rw [shiftPath_initial S τ hτS]
    exact hm y
  have hb := matchingFamily_glue_block S τ hτ0 hτS directions k p (fun y => shiftPath S τ (q y))
    hp ((shiftPath (E := E) S τ).contDiff.comp hq) hm' n x
  exact hb.trans (by
    gcongr
    exact shiftPath_block_bound S τ directions k q hq n x)

end Parameter
end EulerElapsedTimePathGluing
