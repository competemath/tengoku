import Tengoku.Seed.LinearAlgebra.Projectivization.Basic
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Analysis.Normed.Module.RCLike.Basic
import Tengoku.Seed.Topology.MetricSpace.ProperSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The Hopf map and its circle fibers

The direction map in `pshd-vibe`, Lemma 1.3, uses mathlib's projectivization.
-/

open Set Metric

namespace PshLines.PSHD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Hopf map sends a unit vector to the complex line it spans.-/
noncomputable def hopf (e : sphere (0 : E) 1) : Projectivization ℂ E :=
  Projectivization.mk ℂ (e : E) (by
    have he : ‖(e : E)‖ = 1 := by simp
    intro h
    simp [h] at he)

/-- Equality of Hopf directions is precisely multiplication by a unit phase.
@isnad1 id=iff.0h3v.s8.5d57780ce870 from=translated src=- shape=2c89a074 vocab=2dd47252
-/
theorem hopf_eq_iff (e f : sphere (0 : E) 1) :
    hopf e = hopf f ↔ ∃ a : ℂ, ‖a‖ = 1 ∧ a • (f : E) = (e : E) := by
  rw [hopf, hopf, Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_, ha⟩
    have he : ‖(e : E)‖ = 1 := by simp
    have hf : ‖(f : E)‖ = 1 := by simp
    have := congrArg norm ha
    simpa [norm_smul, he, hf] using this
  · rintro ⟨a, _, ha⟩
    exact ⟨a, ha⟩

/-- Multiplication by a unit complex number on the unit sphere.-/
def phaseOrbit (e : sphere (0 : E) 1) (a : sphere (0 : ℂ) 1) :
    sphere (0 : E) 1 :=
  ⟨(a : ℂ) • (e : E), by
    have he : ‖(e : E)‖ = 1 := by simp
    have ha : ‖(a : ℂ)‖ = 1 := by simp
    simp [norm_smul, he, ha]⟩

/--
@isnad1 id=continuo.0h2v.s7.06b3bf5a1bad from=translated src=- shape=6314d96c vocab=a3deac52
-/
theorem continuous_phaseOrbit (e : sphere (0 : E) 1) :
    Continuous (phaseOrbit e) :=
  (continuous_subtype_val.smul continuous_const).subtype_mk _

/-- A Hopf fiber is exactly the image of the unit circle under its phase action.
@isnad1 id=eq.0h2v.s7.89b78e9c5b66 from=translated src=- shape=306d3043 vocab=a1b134cc
-/
theorem hopf_fiber_eq_range (e : sphere (0 : E) 1) :
    {f | hopf f = hopf e} = range (phaseOrbit e) := by
  ext f
  constructor
  · intro h
    obtain ⟨a, ha, heq⟩ := (hopf_eq_iff f e).mp h
    exact ⟨⟨a, by simpa using ha⟩, Subtype.ext heq⟩
  · rintro ⟨a, rfl⟩
    exact (hopf_eq_iff _ _).mpr
      ⟨a, by simp, rfl⟩

/-- Hopf fibers are compact, even without finite dimensionality of the ambient space.
@isnad1 id=iscompac.0h2v.s7.3c72adb04bb5 from=translated src=- shape=1699f3c1 vocab=1e3e1529
-/
theorem isCompact_hopf_fiber (e : sphere (0 : E) 1) :
    IsCompact {f | hopf f = hopf e} := by
  rw [hopf_fiber_eq_range]
  exact isCompact_range (continuous_phaseOrbit e)

/-- Every complex projective direction admits a unit representative.
@isnad1 id=surjecti.0h1v.s6.d137a906d8d9 from=translated src=- shape=95f7acf7 vocab=aab0afe2
-/
theorem hopf_surjective : Function.Surjective (hopf (E := E)) := by
  intro p
  let e : sphere (0 : E) 1 :=
    ⟨(‖p.rep‖⁻¹ : ℂ) • p.rep, by
      simp [norm_smul, norm_inv, Complex.norm_real, norm_ne_zero_iff.mpr p.rep_nonzero]⟩
  refine ⟨e, ?_⟩
  rw [← p.mk_rep]
  exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨(‖p.rep‖⁻¹ : ℂ), rfl⟩

end PshLines.PSHD
