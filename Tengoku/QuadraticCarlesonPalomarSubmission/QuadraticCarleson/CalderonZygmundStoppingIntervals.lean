/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.CalderonZygmundDyadicStopping

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Converting canonical dyadic stopping cells to centered intervals

The analytic atom estimates use a center and a length, while the canonical
stopping construction uses half-open dyadic cells.  The project's centered
interval convention is also half-open, so this file supplies an exact set
identity and transfers literal pairwise disjointness without a boundary loss.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace QuadraticCarleson
namespace CalderonZygmundStoppingIntervals

open CalderonZygmundDyadicStopping

set_option autoImplicit false

noncomputable section

/-- Center of the canonical half-open stopping interval.-/
def stoppingCenter {f : ℝ → ℂ} (c : stoppingCell f) : ℝ :=
  ((c.1.index : ℝ) + 1 / 2) * dyadicLength (rootLength f) c.1.depth

/-- Length of the canonical half-open stopping interval.-/
def stoppingLength {f : ℝ → ℂ} (c : stoppingCell f) : ℝ :=
  dyadicLength (rootLength f) c.1.depth

/--
@isnad1 id=lt.0h2v.s4.f63cdf7092f4 from=translated src=- shape=5fcc27e0 vocab=0127bad6
-/
theorem stoppingLength_pos {f : ℝ → ℂ} (c : stoppingCell f) :
    0 < stoppingLength c :=
  dyadicLength_pos rootLength_pos c.1.depth

/-- The centered representative has the same half-open endpoints as the
stopping cell.
@isnad1 id=eq.0h2v.s6.1e1aca915dad from=translated src=- shape=c037c5fd vocab=b9dc32fa
-/
theorem centeredInterval_stopping_eq_Ico {f : ℝ → ℂ} (c : stoppingCell f) :
    centeredInterval (stoppingCenter c) (stoppingLength c) =
      Ico ((c.1.index : ℝ) * stoppingLength c)
        (((c.1.index : ℝ) + 1) * stoppingLength c) := by
  unfold centeredInterval stoppingCenter stoppingLength
  congr 1 <;> ring

/--
@isnad1 id=eq.0h2v.s6.b0ac26936604 from=translated src=- shape=afd4e0f8 vocab=4e83d150
-/
theorem stoppingInterval_eq_Ico {f : ℝ → ℂ} (c : stoppingCell f) :
    c.1.interval (rootLength f) =
      Ico ((c.1.index : ℝ) * stoppingLength c)
        (((c.1.index : ℝ) + 1) * stoppingLength c) := by
  rfl

/-- Exact conversion from a canonical cell to its center/length form.
@isnad1 id=eq.0h2v.s4.dfaedf6704b0 from=translated src=- shape=576c80d7 vocab=54dbc8cb
-/
theorem centeredInterval_eq_stoppingInterval {f : ℝ → ℂ}
    (c : stoppingCell f) :
    centeredInterval (stoppingCenter c) (stoppingLength c) =
      c.1.interval (rootLength f) := by
  rw [centeredInterval_stopping_eq_Ico, stoppingInterval_eq_Ico]

/--
@isnad1 id=eventual.0h2v.s5.6bc773f9bd4c from=translated src=- shape=7d8f270e vocab=c07def61
-/
theorem centeredInterval_ae_eq_stoppingInterval {f : ℝ → ℂ}
    (c : stoppingCell f) :
    centeredInterval (stoppingCenter c) (stoppingLength c) =ᵐ[volume]
      c.1.interval (rootLength f) :=
  Filter.Eventually.of_forall fun x ↦ Set.ext_iff.mp
    (centeredInterval_eq_stoppingInterval c) x |> propext

/-- Center/length representatives of distinct stopping cells are literally
pairwise disjoint.
@isnad1 id=pairwise.0h1v.s5.3c0cb74776bb from=translated src=- shape=178b3d61 vocab=abf6dff5
-/
theorem centeredStoppingIntervals_pairwiseDisjoint {f : ℝ → ℂ} :
    Pairwise (Function.onFun Disjoint fun c : stoppingCell f ↦
      centeredInterval (stoppingCenter c) (stoppingLength c)) := by
  intro c d hcd
  simpa only [centeredInterval_eq_stoppingInterval] using
    stoppingCell_pairwiseDisjoint hcd

/-- The corresponding almost-everywhere disjointness statement.
@isnad1 id=pairwise.0h1v.s4.ec239e9d84a7 from=translated src=- shape=e9ef50ef vocab=e48c6156
-/
theorem centeredStoppingIntervals_pairwiseAEDisjoint {f : ℝ → ℂ} :
    Pairwise (Function.onFun (AEDisjoint volume) fun c : stoppingCell f ↦
      centeredInterval (stoppingCenter c) (stoppingLength c)) := by
  exact centeredStoppingIntervals_pairwiseDisjoint.aedisjoint

/-- Set integrals over the centered representative and the canonical stopping
cell agree.
@isnad1 id=eq.0h4v.s6.f0492937c97a from=translated src=- shape=a86a1ae3 vocab=991459a8
-/
theorem setIntegral_centeredStopping_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → ℂ} (c : stoppingCell f) (g : ℝ → E) :
    (∫ x in centeredInterval (stoppingCenter c) (stoppingLength c), g x) =
      ∫ x in c.1.interval (rootLength f), g x := by
  rw [centeredInterval_eq_stoppingInterval]

/-- The centered interval has exactly the stopping-cell length.
@isnad1 id=eq.0h2v.s5.50e944d2fa12 from=translated src=- shape=9a9e0a2d vocab=03faf0a4
-/
theorem volume_centeredStoppingInterval {f : ℝ → ℂ} (c : stoppingCell f) :
    volume (centeredInterval (stoppingCenter c) (stoppingLength c)) =
      ENNReal.ofReal (stoppingLength c) := by
  rw [centeredInterval_stopping_eq_Ico, Real.volume_Ico]
  congr 1
  ring

end
end CalderonZygmundStoppingIntervals
end QuadraticCarleson
