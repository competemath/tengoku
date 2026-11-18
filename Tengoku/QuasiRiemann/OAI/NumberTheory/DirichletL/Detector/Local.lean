import Tengoku.Seed.Analysis.Complex.Norm
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

namespace SevenEighths.ProbeLocal
noncomputable section

def localFactor (V W Pstar : ℂ) : ℂ := 1 / (1 - V) + W / (1 - W) + Pstar

def localCorrection (V W D Pstar : ℂ) : ℂ :=
  localFactor V W Pstar * ((1 - V) * (1 - W)) / (1 - D)

def continuedCorrection (V W D Pstar : ℂ) : ℂ :=
  (1 - V * W + (1 - V) * (1 - W) * Pstar) / (1 - D)

/--
@isnad1 id=eq.3h4v.s6.bd39e240d24e from=translated src=- shape=deb7c41b vocab=21a57b76
-/
theorem continuedCorrection_eq_raw (V W D Pstar : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0) :
    continuedCorrection V W D Pstar = localCorrection V W D Pstar := by
  unfold continuedCorrection localCorrection localFactor
  field_simp
  ring

def compensatedReplacement (V W D Pstar B q : ℂ) : ℂ :=
  ((B - q) * (1 - V) * (1 - W) * Pstar - q * (1 - V * W)) / (1 - D)

/--
@isnad1 id=eq.3h4v.s7.1f30054064f5 from=translated src=- shape=0b1cd95b vocab=be913555
-/
theorem correction_defect (V W D Pstar : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0) :
    localCorrection V W D Pstar - 1 =
      (D * (V + W - V * W) - V * W +
        (1 - V) * (1 - W) * (Pstar + D)) / (1 - D) := by
  unfold localCorrection localFactor
  field_simp
  ring

/--
@isnad1 id=eq.4h6v.s7.ca35ed8eef9a from=translated src=- shape=fb8a9acf vocab=85541668
-/
theorem compensatedReplacement_eq_raw (V W D Pstar B q : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0)
    (hP : localFactor V W Pstar ≠ 0) :
    compensatedReplacement V W D Pstar B q =
      localCorrection V W D Pstar * (B * Pstar / localFactor V W Pstar - q) := by
  unfold localCorrection compensatedReplacement
  field_simp
  unfold localFactor
  field_simp
  ring

/--
@isnad1 id=eq.1h4v.s6.3d958266c3a8 from=translated src=- shape=6f2ed1ea vocab=34a0a88c
-/
theorem compensatedReplacement_ramified (V Pstar B q : ℂ) (hV : 1 - V ≠ 0) :
    compensatedReplacement V 0 0 Pstar B q =
      B * (1 - V) * Pstar - q * localCorrection V 0 0 Pstar := by
  unfold compensatedReplacement localCorrection localFactor
  field_simp
  ring

/--
@isnad1 id=eq.5h7v.s8.c64c15bf1522 from=translated src=- shape=cc705277 vocab=fd5be421
-/
theorem normalized_cancellation (V W D Pstar B q vInv : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0)
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    compensatedReplacement V W D Pstar B q +
        localCorrection V W D Pstar * vInv =
      (1 - V) * (1 - W) / (1 - D) *
        ((vInv - q) * (V / (1 - V) - D) +
          (B + vInv - q) * (Pstar + D)) := by
  unfold compensatedReplacement localCorrection localFactor
  field_simp
  linear_combination -(1 - V) * (1 - W) * hBD + (1 - V) * hvW

/--
@isnad1 id=eq.1h4v.s7.609847e5528d from=translated src=- shape=a1d59ece vocab=c09d6ac8
-/
theorem continuedCorrection_defect (V W D Pstar : ℂ) (hD : 1 - D ≠ 0) :
    continuedCorrection V W D Pstar - 1 =
      (D * (V + W - V * W) - V * W +
        (1 - V) * (1 - W) * (Pstar + D)) / (1 - D) := by
  unfold continuedCorrection
  field_simp
  ring

/--
@isnad1 id=eq.4h7v.s8.fdf44a8c6435 from=translated src=- shape=3f652db4 vocab=e96d70fe
-/
theorem continued_normalized_cancellation (V W D Pstar B q vInv : ℂ)
    (hV : 1 - V ≠ 0) (hD : 1 - D ≠ 0)
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    compensatedReplacement V W D Pstar B q +
        continuedCorrection V W D Pstar * vInv =
      (1 - V) * (1 - W) / (1 - D) *
        ((vInv - q) * (V / (1 - V) - D) +
          (B + vInv - q) * (Pstar + D)) := by
  unfold compensatedReplacement continuedCorrection
  field_simp
  linear_combination -(1 - V) * (1 - W) * hBD + (1 - V) * hvW

/--
@isnad1 id=eq.0h4v.s6.30e3b0a4ae03 from=translated src=- shape=a2d151d8 vocab=b15af2b9
-/
theorem continued_ramified_compensation (V Pstar B q : ℂ) :
    compensatedReplacement V 0 0 Pstar B q =
      B * (1 - V) * Pstar - q * continuedCorrection V 0 0 Pstar := by
  simp only [compensatedReplacement, continuedCorrection, mul_zero, sub_zero,
    mul_one, div_one]
  ring

end
end SevenEighths.ProbeLocal

end OAI
