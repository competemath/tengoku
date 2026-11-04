import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.Assembly

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős Problem 996 (JSP-000829): the answer is **no**

Main result: `Erdos996.erdos_996 : ¬ Erdos996Statement` (statement in `Statement.lean`).
The proof formalizes the counterexample of B. S. Ho, *Counterexamples for lacunary dilates via
dyadic spike blocks*, arXiv:2604.18535, Corollary 1.4.

The construction follows Ho (§§2–5), simplified for #996:

* only `f ∈ L²` is needed (no `Lᵖ` / Rosenthal);
* the signal height is a fixed constant `B₀` (no `B_k → ∞`), since it suffices that the averages
  exceed `B₀ - μ > 0` infinitely often on a set of positive measure;
* stage failure probabilities are made summable with total `< 1`, so a union bound replaces the
  second Borel–Cantelli lemma and no cross-stage independence is needed;
* for each fixed `C` we build a separate example, so the Fourier tail only has to beat
  `(log log log N)^{-C}` rather than the endpoint `(log log N)^{-1/2}`.

File layout: `Defs` (spikes, digit windows, blocks), `Parts/*` (G1–G3: spike bounds, Fourier support
and tail, independence of disjoint binary-digit windows, block floor, trial signal),
`Parts/Asm/*` (global construction, parameters, L² and Fourier-tail bounds, positive-measure
assembly), and this file (reduction to the literal statement).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real

namespace Erdos996

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

/-! ### Reduction to the literal statement -/

theorem not_lacunaryAveragesConverge {f : Lp ℂ 2 μ𝕋} {n : ℕ → ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hint : ∫ t, f t ∂μ𝕋 = 0)
    (hpos : 0 < μ𝕋 {x | ∃ᶠ N in atTop, δ ≤ ‖(∑ k ∈ range N, f (n k • x)) / (N : ℂ)‖}) :
    ¬ LacunaryAveragesConverge f n := by
  intro hconv
  have h0 := ae_iff.1 hconv
  refine (ne_of_gt hpos) (measure_mono_null (fun x hx => ?_) h0)
  simp only [Set.mem_ofPred_eq] at hx ⊢
  intro hlim
  rw [hint] at hlim
  have hev : ∀ᶠ N in atTop, ‖(∑ k ∈ range N, f (n k • x)) / (N : ℂ)‖ < δ := by
    have := hlim.norm
    simp only [norm_zero] at this
    exact this.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN1, hN2⟩ := (hx.and_eventually hev).exists
  exact lt_irrefl _ (hN1.trans_lt hN2)

end Erdos996
