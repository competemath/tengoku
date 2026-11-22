import Tengoku.Seed.Algebra.Module.LinearMap.Basic
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Module

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Differential recovery of the EMD coupling

For the convention-fixed EMD system, set `v = dφ` and
`𝓕 = exp(aφ/2) F`.  The Bianchi and Maxwell equations become

`d𝓕 = (a/2) v ∧ 𝓕`,
`d(*𝓕) = -(a/2) v ∧ (*𝓕)`.

After multiplying by two, both equations have the abstract linear form
encoded by `CouplingCompatible`.  This file proves three facts needed by the
curvature-reconstruction program:

1. a nonzero wedge channel determines the coupling uniquely once the global
   orientation of `v` is fixed;
2. reversing `v` reverses `a`, leaving the equations unchanged;
3. a linear probe of any nonzero channel gives an explicit recovery formula.

The exterior derivative, Hodge star, wedge product, and their reconstruction
from curvature are not formalized here.  Their evaluated values are the four
module elements supplied to `CouplingCompatible`.
-/

namespace RainichKaluza

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- Compatibility of a candidate EMD coupling with the rescaled Bianchi and
Maxwell differential channels.

The arguments represent, in order, `d𝓕`, `d(*𝓕)`, `v∧𝓕`, and
`v∧(*𝓕)`.-/
def CouplingCompatible
    (a : ℝ) (dF dStarF vWedgeF vWedgeStarF : W) : Prop :=
  (2 : ℝ) • dF = a • vWedgeF ∧
  (2 : ℝ) • dStarF = (-a) • vWedgeStarF

/-- Reversing the reconstructed scalar orientation `v ↦ -v` reverses the
signed coupling while preserving both differential equations.
@isnad1 id=coupling.1h6v.s6.1e3e942c0303 from=translated src=- shape=c78a3dd9 vocab=59f30c8c
-/
theorem couplingCompatible_neg_orientation
    (a : ℝ) (dF dStarF vWedgeF vWedgeStarF : W)
    (h : CouplingCompatible a dF dStarF vWedgeF vWedgeStarF) :
    CouplingCompatible (-a) dF dStarF (-vWedgeF) (-vWedgeStarF) := by
  rcases h with ⟨hF, hStarF⟩
  constructor
  · rw [hF]
    module
  · rw [hStarF]
    module

/-- A nonzero primal wedge channel uniquely determines the signed coupling
after the scalar orientation has been fixed.
@isnad1 id=eq.3h7v.s6.ec23ba37196c from=translated src=- shape=5c9df614 vocab=4a343fb9
-/
theorem couplingCompatible_unique_of_primal_ne_zero
    (a b : ℝ) (dF dStarF vWedgeF vWedgeStarF : W)
    (ha : CouplingCompatible a dF dStarF vWedgeF vWedgeStarF)
    (hb : CouplingCompatible b dF dStarF vWedgeF vWedgeStarF)
    (hsource : vWedgeF ≠ 0) :
    a = b := by
  have hsmul : (a - b) • vWedgeF = 0 := by
    calc
      (a - b) • vWedgeF = a • vWedgeF - b • vWedgeF := by module
      _ = (2 : ℝ) • dF - (2 : ℝ) • dF := by rw [← ha.1, ← hb.1]
      _ = 0 := sub_self _
  have hab : a - b = 0 :=
    (smul_eq_zero.mp hsmul).resolve_right hsource
  linarith

/-- A nonzero dual wedge channel also uniquely determines the signed
coupling.
@isnad1 id=eq.3h7v.s6.5dfd1a354ef2 from=translated src=- shape=198ae6b4 vocab=4a343fb9
-/
theorem couplingCompatible_unique_of_dual_ne_zero
    (a b : ℝ) (dF dStarF vWedgeF vWedgeStarF : W)
    (ha : CouplingCompatible a dF dStarF vWedgeF vWedgeStarF)
    (hb : CouplingCompatible b dF dStarF vWedgeF vWedgeStarF)
    (hsource : vWedgeStarF ≠ 0) :
    a = b := by
  have hsmul : ((-a) - (-b)) • vWedgeStarF = 0 := by
    calc
      ((-a) - (-b)) • vWedgeStarF =
          (-a) • vWedgeStarF - (-b) • vWedgeStarF := by module
      _ = (2 : ℝ) • dStarF - (2 : ℝ) • dStarF := by
        rw [← ha.2, ← hb.2]
      _ = 0 := sub_self _
  have hab : (-a) - (-b) = 0 :=
    (smul_eq_zero.mp hsmul).resolve_right hsource
  linarith

/-- Either nonzero differential wedge channel suffices for uniqueness.
@isnad1 id=eq.3h7v.s6.0951a8f59fe1 from=translated src=- shape=86e037dc vocab=4a343fb9
-/
theorem couplingCompatible_unique_of_nondegenerate
    (a b : ℝ) (dF dStarF vWedgeF vWedgeStarF : W)
    (ha : CouplingCompatible a dF dStarF vWedgeF vWedgeStarF)
    (hb : CouplingCompatible b dF dStarF vWedgeF vWedgeStarF)
    (hnondegenerate : vWedgeF ≠ 0 ∨ vWedgeStarF ≠ 0) :
    a = b := by
  rcases hnondegenerate with hprimal | hdual
  · exact couplingCompatible_unique_of_primal_ne_zero
      a b dF dStarF vWedgeF vWedgeStarF ha hb hprimal
  · exact couplingCompatible_unique_of_dual_ne_zero
      a b dF dStarF vWedgeF vWedgeStarF ha hb hdual

/-- Coupling recovered by applying a real-linear probe to the primal channel.
Different probes give the same result whenever the compatibility equation
holds and their denominator is nonzero.-/
noncomputable def couplingFromProbe
    (probe : W →ₗ[ℝ] ℝ) (dF vWedgeF : W) : ℝ :=
  2 * probe dF / probe vWedgeF

/--
@isnad1 id=eq.2h7v.s6.49e6a70e7aae from=translated src=- shape=d1e7f75f vocab=ab8aefb0
-/
theorem couplingFromProbe_eq_of_compatible
    (probe : W →ₗ[ℝ] ℝ)
    (a : ℝ) (dF dStarF vWedgeF vWedgeStarF : W)
    (h : CouplingCompatible a dF dStarF vWedgeF vWedgeStarF)
    (hprobe : probe vWedgeF ≠ 0) :
    couplingFromProbe probe dF vWedgeF = a := by
  have hscalar := congrArg probe h.1
  simp at hscalar
  unfold couplingFromProbe
  exact (div_eq_iff hprobe).2 hscalar

/-- Coupling recovered from a linear probe of the dual Maxwell channel.-/
noncomputable def couplingFromDualProbe
    (probe : W →ₗ[ℝ] ℝ) (dStarF vWedgeStarF : W) : ℝ :=
  -(2 * probe dStarF / probe vWedgeStarF)

/--
@isnad1 id=eq.2h7v.s6.eae7ce700360 from=translated src=- shape=0970efba vocab=6f3ccb0a
-/
theorem couplingFromDualProbe_eq_of_compatible
    (probe : W →ₗ[ℝ] ℝ)
    (a : ℝ) (dF dStarF vWedgeF vWedgeStarF : W)
    (h : CouplingCompatible a dF dStarF vWedgeF vWedgeStarF)
    (hprobe : probe vWedgeStarF ≠ 0) :
    couplingFromDualProbe probe dStarF vWedgeStarF = a := by
  have hscalar := congrArg probe h.2
  simp at hscalar
  have hscalar' : 2 * probe dStarF = (-a) * probe vWedgeStarF := by
    calc
      2 * probe dStarF = -(a * probe vWedgeStarF) := hscalar
      _ = (-a) * probe vWedgeStarF := by ring
  have hquot : 2 * probe dStarF / probe vWedgeStarF = -a :=
    (div_eq_iff hprobe).2 hscalar'
  unfold couplingFromDualProbe
  linarith

/-- Any two nonvanishing primal probes recover the same coupling.
@isnad1 id=eq.3h8v.s7.67b7a98d17d0 from=translated src=- shape=c738966e vocab=ab8aefb0
-/
theorem couplingFromProbe_independent_of_compatible
    (probe₁ probe₂ : W →ₗ[ℝ] ℝ)
    (a : ℝ) (dF dStarF vWedgeF vWedgeStarF : W)
    (h : CouplingCompatible a dF dStarF vWedgeF vWedgeStarF)
    (hprobe₁ : probe₁ vWedgeF ≠ 0)
    (hprobe₂ : probe₂ vWedgeF ≠ 0) :
    couplingFromProbe probe₁ dF vWedgeF =
      couplingFromProbe probe₂ dF vWedgeF := by
  rw [couplingFromProbe_eq_of_compatible probe₁ a dF dStarF
    vWedgeF vWedgeStarF h hprobe₁]
  rw [couplingFromProbe_eq_of_compatible probe₂ a dF dStarF
    vWedgeF vWedgeStarF h hprobe₂]

/-- Nonvanishing primal and dual probes recover the same coupling.
@isnad1 id=eq.3h8v.s7.8175ce88663b from=translated src=- shape=8515793c vocab=1c2f3096
-/
theorem couplingFrom_primal_dual_probes_agree
    (primalProbe dualProbe : W →ₗ[ℝ] ℝ)
    (a : ℝ) (dF dStarF vWedgeF vWedgeStarF : W)
    (h : CouplingCompatible a dF dStarF vWedgeF vWedgeStarF)
    (hprimal : primalProbe vWedgeF ≠ 0)
    (hdual : dualProbe vWedgeStarF ≠ 0) :
    couplingFromProbe primalProbe dF vWedgeF =
      couplingFromDualProbe dualProbe dStarF vWedgeStarF := by
  rw [couplingFromProbe_eq_of_compatible primalProbe a dF dStarF
    vWedgeF vWedgeStarF h hprimal]
  rw [couplingFromDualProbe_eq_of_compatible dualProbe a dF dStarF
    vWedgeF vWedgeStarF h hdual]

/-- The probe formula changes sign when the reconstructed scalar orientation,
and hence the wedge source, is reversed.
@isnad1 id=eq.0h4v.s6.01d4eddd93bb from=translated src=- shape=bcefb312 vocab=0eab9a27
-/
theorem couplingFromProbe_neg_source
    (probe : W →ₗ[ℝ] ℝ) (dF vWedgeF : W) :
    couplingFromProbe probe dF (-vWedgeF) =
      -couplingFromProbe probe dF vWedgeF := by
  simp only [couplingFromProbe, map_neg]
  exact div_neg _

/-- Orientation-independent coupling magnitude reconstructed from a probe.-/
noncomputable def couplingSqFromProbe
    (probe : W →ₗ[ℝ] ℝ) (dF vWedgeF : W) : ℝ :=
  couplingFromProbe probe dF vWedgeF ^ 2

/--
@isnad1 id=eq.2h7v.s7.daf5949c77aa from=translated src=- shape=0c68e9a1 vocab=b3e39125
-/
theorem couplingSqFromProbe_eq_of_compatible
    (probe : W →ₗ[ℝ] ℝ)
    (a : ℝ) (dF dStarF vWedgeF vWedgeStarF : W)
    (h : CouplingCompatible a dF dStarF vWedgeF vWedgeStarF)
    (hprobe : probe vWedgeF ≠ 0) :
    couplingSqFromProbe probe dF vWedgeF = a ^ 2 := by
  rw [couplingSqFromProbe, couplingFromProbe_eq_of_compatible
    probe a dF dStarF vWedgeF vWedgeStarF h hprobe]

/--
@isnad1 id=eq.3h8v.s7.76c627e397a9 from=translated src=- shape=c738966e vocab=76f71e3b
-/
theorem couplingSqFromProbe_independent_of_compatible
    (probe₁ probe₂ : W →ₗ[ℝ] ℝ)
    (a : ℝ) (dF dStarF vWedgeF vWedgeStarF : W)
    (h : CouplingCompatible a dF dStarF vWedgeF vWedgeStarF)
    (hprobe₁ : probe₁ vWedgeF ≠ 0)
    (hprobe₂ : probe₂ vWedgeF ≠ 0) :
    couplingSqFromProbe probe₁ dF vWedgeF =
      couplingSqFromProbe probe₂ dF vWedgeF := by
  rw [couplingSqFromProbe_eq_of_compatible probe₁ a dF dStarF
    vWedgeF vWedgeStarF h hprobe₁]
  rw [couplingSqFromProbe_eq_of_compatible probe₂ a dF dStarF
    vWedgeF vWedgeStarF h hprobe₂]

/--
@isnad1 id=eq.0h4v.s6.ffa5b439fc4f from=translated src=- shape=ef3b7d52 vocab=0c8970ac
-/
theorem couplingSqFromProbe_neg_source
    (probe : W →ₗ[ℝ] ℝ) (dF vWedgeF : W) :
    couplingSqFromProbe probe dF (-vWedgeF) =
      couplingSqFromProbe probe dF vWedgeF := by
  rw [couplingSqFromProbe, couplingSqFromProbe]
  rw [couplingFromProbe_neg_source]
  ring

/-- The convention-independent coupling magnitude is unchanged by reversing
the scalar orientation.
@isnad1 id=eq.0h1v.s5.4b765521950c from=translated src=- shape=9c8b14aa vocab=873040dc
-/
theorem couplingSq_neg_orientation (a : ℝ) :
    (-a) ^ 2 = a ^ 2 := by
  ring

end RainichKaluza
