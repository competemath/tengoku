import Tengoku
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.QuasiRiemann end Tengoku.QuasiRiemann open Tengoku.QuasiRiemann
namespace OAI

namespace SevenEighths.InverseMoment

def MarkedMargins (m r z c : ℝ) : Prop :=
  r + 2 * z ≤ m - c ∧ 2 * r + 8 * z ≤ 3 * m - c

def CanonicalMargins (F M Q z c : ℝ) : Prop :=
  c ≤ F - M - Q - z ∧ c ≤ 4 * F - 3 * M - 6 * z

/--
@isnad1 id=ex.2h3v.s6.7497dcf03ccd from=translated src=- shape=48aa4aff vocab=1f6c8398
-/
theorem markedMargins_of_strict {m r z : ℝ}
    (h₁ : r + 2 * z < m) (h₂ : 2 * r + 8 * z < 3 * m) :
    ∃ c > 0, MarkedMargins m r z c := by
  refine ⟨min (m - r - 2 * z) (3 * m - 2 * r - 8 * z), ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · constructor
    · have := min_le_left (m - r - 2 * z) (3 * m - 2 * r - 8 * z)
      linarith
    · have := min_le_right (m - r - 2 * z) (3 * m - 2 * r - 8 * z)
      linarith

/--
@isnad1 id=markedma.2h5v.s4.8216efa02b05 from=translated src=- shape=d656a051 vocab=e6d579bb
-/
theorem markedMargins_subcollection {m r z z' c : ℝ}
    (h : MarkedMargins m r z c) (hz : z' ≤ z) :
    MarkedMargins m r z' c := by
  obtain ⟨h₁, h₂⟩ := h
  constructor <;> linarith

/--
@isnad1 id=canonica.2h6v.s4.b23b36461093 from=translated src=- shape=75e17d71 vocab=ee61e14f
-/
theorem canonicalMargins_subcollection {F M Q z z' c : ℝ}
    (h : CanonicalMargins F M Q z c) (hz : z' ≤ z) :
    CanonicalMargins F M Q z' c := by
  obtain ⟨h₁, h₂⟩ := h
  constructor <;> linarith

/--
@isnad1 id=canonica.2h6v.s4.1dc506252766 from=translated src=- shape=fb49d4fc vocab=ee61e14f
-/
theorem canonicalMargins_weaken {F M Q z c c' : ℝ}
    (h : CanonicalMargins F M Q z c) (hc : c' ≤ c) :
    CanonicalMargins F M Q z c' := by
  exact ⟨hc.trans h.1, hc.trans h.2⟩

def decrease (ell A t g theta V : ℝ) : ℝ := ell + A + t + g - theta + V

def childF (F ell A t g theta V j delta : ℝ) : ℝ :=
  F - decrease ell A t g theta V - 2 * ell + j + delta

def childM (M ell A t g theta V j eta : ℝ) : ℝ :=
  M - 2 * decrease ell A t g theta V - 2 * ell + j + eta

/--
@isnad1 id=and.0h9v.s7.94e884f64a85 from=translated src=- shape=398f7697 vocab=fd45730d
-/
theorem canonical_transition (F M ell A t g theta V j : ℝ) :
    childF F ell A t g theta V j 0 - childM M ell A t g theta V j 0 =
      F - M + decrease ell A t g theta V ∧
    4 * childF F ell A t g theta V j 0 -
      3 * childM M ell A t g theta V j 0 =
      4 * F - 3 * M + 2 * (A + t + g - theta + V) + j := by
  constructor <;> unfold childF childM decrease <;> ring

/--
@isnad1 id=and.7h15v.s8.28fc61d261c9 from=translated src=- shape=a04e7182 vocab=45224bc7
-/
theorem child_margins_sharp {F M Q Q' z c ell A t g theta V j delta eta : ℝ}
    (h : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hgt : -2 * eta ≤ g - theta)
    (hQ : Q' ≤ Q + decrease ell A t g theta V + 4 * eta) :
    c + delta - 5 * eta ≤
      childF F ell A t g theta V j delta -
      childM M ell A t g theta V j eta - Q' - z ∧
    c + 4 * delta - 7 * eta ≤
      4 * childF F ell A t g theta V j delta -
      3 * childM M ell A t g theta V j eta - 6 * z := by
  obtain ⟨h₁, h₂⟩ := h
  unfold childF childM decrease at *
  constructor <;> linarith

/--
@isnad1 id=canonica.9h15v.s7.75c4075ce3e5 from=translated src=- shape=9d1a820e vocab=45224bc7
-/
theorem child_margins {F M Q Q' z c ell A t g theta V j delta eta : ℝ}
    (h : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hgt : -2 * eta ≤ g - theta) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : Q' ≤ Q + decrease ell A t g theta V + 4 * eta) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta) Q' z (c - 7 * eta) := by
  obtain ⟨h₁, h₂⟩ := child_margins_sharp (delta := delta) h hA ht hV hj hgt hQ
  constructor <;> linarith

/--
@isnad1 id=le.6h10v.s7.dfdda05b8351 from=translated src=- shape=07080d3e vocab=fdc5360a
-/
theorem child_row_decrease {M ell A t g theta V j eta d : ℝ}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hgt : -2 * eta ≤ g - theta)
    (hj : j ≤ 2 * ell + 3 * eta) (hterminal : d ≤ ell + V)
    (heta : eta ≤ d / 16) :
    3 * d / 2 ≤ M - childM M ell A t g theta V j eta := by
  unfold childM decrease
  linarith

/--
@isnad1 id=le.7h10v.s7.a0d39c834dcb from=translated src=- shape=b153b8be vocab=7ae88cb3
-/
theorem childF_upper {F ell A t g theta V j delta eta : ℝ}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hell : 0 ≤ ell) (hV : 0 ≤ V)
    (hgt : -2 * eta ≤ g - theta) (hj : j ≤ 2 * ell + 3 * eta)
    (hdelta : delta ≤ 6 * eta) :
    childF F ell A t g theta V j delta ≤ F + 11 * eta := by
  unfold childF decrease
  linarith

/--
@isnad1 id=and.2h2v.s6.357272645894 from=translated src=- shape=a834be2b vocab=268f85b0
-/
theorem clipping_bounds {N eta : ℝ} (heta : 0 ≤ eta) (hN : -6 * eta ≤ N) :
    0 ≤ max 0 N - N ∧ max 0 N - N ≤ 6 * eta := by
  constructor
  · exact sub_nonneg.mpr (le_max_right 0 N)
  · rcases le_total 0 N with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith

/--
@isnad1 id=le.2h10v.s8.347d70a9bea3 from=translated src=- shape=c12bff03 vocab=a31a7c56
-/
theorem step_energy_exponent {F Fc kappa lambda count delta eta tau pi eps : ℝ}
    (hid : kappa + lambda + count + 2 * Fc = F)
    (hdelta : delta ≤ 6 * eta) :
    kappa + lambda + count + 2 * (Fc + delta) +
      (9 / 2 + 18 + 11 / 2) * eta + tau + pi + eps ≤
      F + 40 * eta + tau + pi + eps := by
  linarith

def initialF (r z G P delta : ℝ) : ℝ := r + z - 2 * G - P + delta

def initialM (m r z G P eta tau : ℝ) : ℝ :=
  2 * (r + z - 2 * G) - m - 2 * P + 6 * eta + tau

/--
@isnad1 id=and.5h11v.s8.b19983d0c0e1 from=translated src=- shape=bb487d19 vocab=b804c2fc
-/
theorem initial_margins_sharp {m r z G P delta eta tau Q c₁ c₂ : ℝ}
    (h₁ : r + 2 * z ≤ m - c₁) (h₂ : 2 * r + 8 * z ≤ 3 * m - c₂)
    (hG : 0 ≤ G) (hP : -2 * eta ≤ P) (hQ : Q ≤ P + G + 3 * eta) :
    c₁ + delta - 9 * eta - tau ≤
      initialF r z G P delta - initialM m r z G P eta tau - Q - (z - G) ∧
    c₂ + 4 * delta - 22 * eta - 3 * tau ≤
      4 * initialF r z G P delta - 3 * initialM m r z G P eta tau -
        6 * (z - G) := by
  unfold initialF initialM
  constructor <;> linarith

/--
@isnad1 id=canonica.9h11v.s8.3bdcf3d676f6 from=translated src=- shape=d255d02d vocab=6ecce90f
-/
theorem initial_margins {m r z G P delta eta tau Q c₁ c₂ : ℝ}
    (h₁ : r + 2 * z ≤ m - c₁) (h₂ : 2 * r + 8 * z ≤ 3 * m - c₂)
    (hG : 0 ≤ G) (hP : -2 * eta ≤ P) (hQ : Q ≤ P + G + 3 * eta)
    (hc : 0 ≤ min c₁ c₂) (hdelta : 0 ≤ delta) (heta : eta ≤ min c₁ c₂ / 100)
    (htau : tau ≤ min c₁ c₂ / 100) :
    CanonicalMargins (initialF r z G P delta)
      (initialM m r z G P eta tau) Q (z - G) (3 * min c₁ c₂ / 4) := by
  obtain ⟨ha, hb⟩ := initial_margins_sharp (delta := delta) (tau := tau) h₁ h₂ hG hP hQ
  have hc₁ := min_le_left c₁ c₂
  have hc₂ := min_le_right c₁ c₂
  constructor <;> linarith

/--
@isnad1 id=eq.0h5v.s6.d79e8a2cd5bd from=translated src=- shape=e2830ab7 vocab=30133c62
-/
theorem initial_prefactor_identity (m r z G P : ℝ) :
    (m - 2 * (r + z - 2 * G) + P) + P +
      2 * initialF r z G P 0 = m := by
  unfold initialF
  ring

/--
@isnad1 id=le.1h5v.s7.a09cddd0f1e9 from=translated src=- shape=b6db8f55 vocab=805e4ba8
-/
theorem initial_energy_exponent {m delta eta pi eps : ℝ}
    (hdelta : delta ≤ 3 * eta) :
    m + 3 * eta + 2 * eta + 2 * delta + pi + eps ≤
      m + 11 * eta + pi + eps := by
  linarith

/--
@isnad1 id=le.3h5v.s7.8a2a7e7cd5a0 from=translated src=- shape=172e4d69 vocab=a31a7c56
-/
theorem total_step_loss {D eta tau pi eps : ℝ}
    (h₁ : D * eta ≤ eps / 160) (h₂ : D * tau ≤ eps / 4)
    (h₃ : D * pi ≤ eps / 4) :
    D * (40 * eta + tau + pi) ≤ 3 * eps / 4 := by
  nlinarith

/--
@isnad1 id=le.3h4v.s6.938e56839014 from=translated src=- shape=b6a684cc vocab=00cae1bd
-/
theorem depth_margin {c D h eta : ℝ} (heta : 0 ≤ eta) (hh : h ≤ D)
    (hbudget : D * eta ≤ c / 14) : c / 2 ≤ c - 7 * h * eta := by
  have := mul_le_mul_of_nonneg_right hh heta
  nlinarith

end SevenEighths.InverseMoment

end OAI
-- Tengoku: root names of this library moved to Tengoku.QuasiRiemann so they do not collide with other libraries (generated)
