import Tengoku.AbelFormalization.AbelFormalization.CountableSardAvoidance
import Tengoku.Seed.Analysis.Calculus.FDeriv.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Linear algebra for parametric submersions

For a surjective derivative on a product, surjectivity in the first variable
is equivalent to surjectivity of the second projection on its kernel.  This
is the algebraic bridge between regularity of a fixed-parameter system and
regularity of the parameter projection on the joint zero locus.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {X Y Z V : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def fstPartial (L : (X × Y) →L[ℝ] Z) : X →L[ℝ] Z :=
  L.comp (ContinuousLinearMap.inl ℝ X Y)

def sndOnKernel (L : (X × Y) →L[ℝ] Z) : L.ker →L[ℝ] Y :=
  (ContinuousLinearMap.snd ℝ X Y).comp L.ker.subtypeL

/--
@isnad1 id=eq.0h5v.s8.68b6061400ab from=translated src=- shape=a6d9e083 vocab=8aba0126
-/
@[simp]
theorem fstPartial_apply (L : (X × Y) →L[ℝ] Z) (x : X) :
    fstPartial L x = L (x, 0) := by
  rfl

/--
@isnad1 id=eq.0h5v.s11.f161517400e9 from=translated src=- shape=8c1e6859 vocab=04eb5472
-/
@[simp]
theorem sndOnKernel_apply (L : (X × Y) →L[ℝ] Z) (p : L.ker) :
    sndOnKernel L p = (p : X × Y).2 := by
  rfl

/--
@isnad1 id=eq.1h4v.s11.e2541d601461 from=translated src=- shape=e02737ab vocab=72ff93cb
-/
theorem sndOnKernel_range_eq_top_of_fstPartial_range_eq_top
    (L : (X × Y) →L[ℝ] Z)
    (hfst : (fstPartial L).range = ⊤) :
    (sndOnKernel L).range = ⊤ := by
  rw [LinearMap.range_eq_top] at hfst ⊢
  intro y
  obtain ⟨x, hx⟩ := hfst (-L (0, y))
  let p : L.ker := ⟨(x, y), by
    change L (x, y) = 0
    rw [show (x, y) = (x, 0) + (0, y) by ext <;> simp, map_add]
    rw [show L (x, 0) = -L (0, y) by
      simpa [fstPartial] using hx]
    simp⟩
  exact ⟨p, rfl⟩

/--
@isnad1 id=eq.2h4v.s11.ce8c9e7524aa from=translated src=- shape=2344d0aa vocab=72ff93cb
-/
theorem fstPartial_range_eq_top_of_sndOnKernel_range_eq_top
    (L : (X × Y) →L[ℝ] Z) (hL : L.range = ⊤)
    (hsnd : (sndOnKernel L).range = ⊤) :
    (fstPartial L).range = ⊤ := by
  rw [LinearMap.range_eq_top] at hL hsnd ⊢
  intro z
  obtain ⟨p, hp⟩ := hL z
  obtain ⟨k, hk⟩ := hsnd p.2
  refine ⟨p.1 - (k : X × Y).1, ?_⟩
  have hksnd : (k : X × Y).2 = p.2 := by
    simpa [sndOnKernel] using hk
  have hpair : (p.1 - (k : X × Y).1, 0) = p - (k : X × Y) := by
    ext <;> simp [hksnd]
  change L (p.1 - (k : X × Y).1, 0) = z
  rw [hpair, map_sub]
  change L.toLinearMap p - L.toLinearMap (k : X × Y) = z
  have hkzero : L.toLinearMap (k : X × Y) = 0 := k.property
  rw [hkzero, sub_zero]
  exact hp

/--
@isnad1 id=iff.1h4v.s11.cbd99f769cad from=translated src=- shape=3c9ee1bf vocab=72ff93cb
-/
theorem fstPartial_range_eq_top_iff_sndOnKernel_range_eq_top
    (L : (X × Y) →L[ℝ] Z) (hL : L.range = ⊤) :
    (fstPartial L).range = ⊤ ↔
      (sndOnKernel L).range = ⊤ :=
  ⟨sndOnKernel_range_eq_top_of_fstPartial_range_eq_top L,
    fstPartial_range_eq_top_of_sndOnKernel_range_eq_top L hL⟩

/--
@isnad1 id=eq.1h6v.s11.4124131a91de from=translated src=- shape=2f45a9a1 vocab=f87367de
-/
theorem range_eq_top_comp_of_range_eq_ker
    (L : (X × Y) →L[ℝ] Z) (d : V →L[ℝ] (X × Y))
    (hd : d.range = L.ker) :
    ((ContinuousLinearMap.snd ℝ X Y).comp d).range =
      (sndOnKernel L).range := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    have hdv : d v ∈ L.ker := by
      rw [← hd]
      exact ⟨v, rfl⟩
    exact ⟨⟨d v, hdv⟩, rfl⟩
  · rintro ⟨p, rfl⟩
    have hp : (p : X × Y) ∈ d.range := by
      rw [hd]
      exact p.property
    obtain ⟨v, hv⟩ := hp
    exact ⟨v, by simpa [sndOnKernel] using congrArg Prod.snd hv⟩

end AbelFormalization
