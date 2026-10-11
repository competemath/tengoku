module

public import Tengoku

public section

-- Upstreaming status: This file is ready for upstreaming, but would need significant polish.

namespace NNReal

-- MR wonders: is this lemma actually used? could or should it be golfed away?
/--
@isnad1 id=eq.0h1v.s5.50d588f1baef from=translated src=- shape=14107493 vocab=85fa19c5
-/
lemma div_self_eq_ite {x : ℝ≥0} : x / x = if 0 < x then 1 else 0 := by
  split_ifs with h
  · exact div_self h.ne'
  · simp_all

end NNReal

-- MR wonders: should one study the corresponding `ENorm` inequality instead?
/-- Transfer an inequality over `ℝ` to one of `NNNorm`s over `ℝ≥0`.
@isnad1 id=le.2h2v.s5.e9971893a794 from=translated src=- shape=dbe6a4da vocab=f860a90a
-/
lemma Real.nnnorm_le_nnnorm {x y : ℝ} (hx : 0 ≤ x) (hy : x ≤ y) : ‖x‖₊ ≤ ‖y‖₊ := by
  rwa [Real.nnnorm_of_nonneg hx, Real.nnnorm_of_nonneg (hx.trans hy)]
