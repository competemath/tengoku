/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.FiniteApproximation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# compatible Hensel prefixes

This file turns the finite Hensel-prefix construction into a recursive family
of compatible prefixes.  The completion/limit argument is kept for the next
layer.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- the data carried by a finite Hensel prefix at stage `N`.
The fields are exactly the invariants needed to extend the prefix one more
step and later pass to the complete limit.-/
structure HenselFactorizationFinitePrefixState
    {R : Type*} [CommRing R] [IsLocalRing R] (π : R)
    (f g0 h0 : R[X]) (m d N : ℕ) where
  /-- The polynomial corrections for the first factor at each stage.-/
  pCorr : ℕ → R[X]
  /-- The polynomial corrections for the second factor at each stage.-/
  qCorr : ℕ → R[X]
  /-- The residual error polynomial at the current stage.-/
  fErr : R[X]
  /-- Every prefix through the current stage factors the error by the corresponding power of `π`.-/
  prefixFactor :
    ∀ r : ℕ, r ≤ N →
      ∃ fr : R[X],
        f - henselFactorization_henselIterate π g0 pCorr r *
            henselFactorization_henselIterate π h0 qCorr r =
          Polynomial.C (π ^ (r + 1)) * fr
  /-- Each correction for the first factor has degree at most `m`.-/
  pCorrDeg : ∀ r : ℕ, (pCorr r).natDegree ≤ m
  /-- Each correction for the second factor has degree at most `d - m`.-/
  qCorrDeg : ∀ r : ℕ, (qCorr r).natDegree ≤ d - m
  /-- At stage `N`, the factorization error is `π ^ (N + 1)` times `fErr`.-/
  factor :
    f - henselFactorization_henselIterate π g0 pCorr N *
        henselFactorization_henselIterate π h0 qCorr N =
      Polynomial.C (π ^ (N + 1)) * fErr
  /-- The first approximate factor at stage `N` has degree at most `m`.-/
  gDeg : (henselFactorization_henselIterate π g0 pCorr N).natDegree ≤ m
  /-- The second approximate factor at stage `N` has degree at most `d - m`.-/
  hDeg : (henselFactorization_henselIterate π h0 qCorr N).natDegree ≤ d - m
  /-- The first approximate factor remains congruent to `g0` modulo the maximal ideal.-/
  gRed :
    ∀ i : ℕ,
      (henselFactorization_henselIterate π g0 pCorr N - g0).coeff i ∈
        IsLocalRing.maximalIdeal R
  /-- The second approximate factor remains congruent to `h0` modulo the maximal ideal.-/
  hRed :
    ∀ i : ℕ,
      (henselFactorization_henselIterate π h0 qCorr N - h0).coeff i ∈
        IsLocalRing.maximalIdeal R

/-- the stage `0` prefix state from a displayed
finite-minimum factor of the initial error.-/
def henselFactorization_initialPrefixState_of_factor
    {R : Type*} [CommRing R] [IsLocalRing R]
    {π : R} {f g0 h0 f1 : R[X]} {m d : ℕ}
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hg0nat : g0.natDegree = m)
    (hh0deg : h0.natDegree ≤ d - m) :
    HenselFactorizationFinitePrefixState π f g0 h0 m d 0 := by
  refine
    { pCorr := fun _ => 0
      qCorr := fun _ => 0
      fErr := f1
      prefixFactor := ?_
      pCorrDeg := ?_
      qCorrDeg := ?_
      factor := ?_
      gDeg := ?_
      hDeg := ?_
      gRed := ?_
      hRed := ?_ }
  · intro r hr
    have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
    subst r
    exact ⟨f1, by
      simpa only [henselFactorization_henselIterate_zero, zero_add, pow_one] using hfactor0⟩
  · intro r
    exact Nat.zero_le m
  · intro r
    exact Nat.zero_le (d - m)
  · simpa only [henselFactorization_henselIterate_zero, zero_add, pow_one] using hfactor0
  · rw [henselFactorization_henselIterate_zero, hg0nat]
  · exact hh0deg
  · intro i
    rw [henselFactorization_henselIterate_zero, sub_self, Polynomial.coeff_zero]
    exact (IsLocalRing.maximalIdeal R).zero_mem
  · intro i
    rw [henselFactorization_henselIterate_zero, sub_self, Polynomial.coeff_zero]
    exact (IsLocalRing.maximalIdeal R).zero_mem

/-- Choose an extension of a prefix state by one Hensel correction in the
displayed-factor form.-/
def henselFactorization_chosenNextPrefixState_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d N : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d)
    (s : HenselFactorizationFinitePrefixState π f g0 h0 m d N) :
    HenselFactorizationFinitePrefixState π f g0 h0 m d (N + 1) := by
  classical
  let hstep := henselFactorization_extend_finite_prefix_one_step_of_mem_span
      (π := π) hπne hπmem
      (f := f) (g0 := g0) (h0 := h0) (a := a) (b := b) (e := e)
      (gbar := gbar) (m := m) (d := d) (n := N)
      hf hg0map hg0nat hgbar_nat hglead hh0deg hbezFactor hmd
      s.pCorr s.qCorr s.prefixFactor s.factor s.gDeg s.hDeg
  let p := Classical.choose hstep
  have hpstep := Classical.choose_spec hstep
  let q := Classical.choose hpstep
  have hqstep := Classical.choose_spec hpstep
  let fnNext := Classical.choose hqstep
  have hspec := Classical.choose_spec hqstep
  have hpdeg : p.natDegree ≤ m := hspec.1
  have hqdeg : q.natDegree ≤ d - m := hspec.2.1
  have hprefixOld :
      ∀ r : ℕ, r ≤ N →
        ∃ fr : R[X],
          f - henselFactorization_henselIterate π g0
                (Function.update s.pCorr (N + 1) p) r *
              henselFactorization_henselIterate π h0
                (Function.update s.qCorr (N + 1) q) r =
            Polynomial.C (π ^ (r + 1)) * fr := hspec.2.2.1
  have hfactorNext :
      f - henselFactorization_henselIterate π g0
            (Function.update s.pCorr (N + 1) p) (N + 1) *
          henselFactorization_henselIterate π h0
            (Function.update s.qCorr (N + 1) q) (N + 1) =
        Polynomial.C (π ^ (N + 2)) * fnNext := hspec.2.2.2.1
  have hgNextDeg :
      (henselFactorization_henselIterate π g0
        (Function.update s.pCorr (N + 1) p) (N + 1)).natDegree ≤ m :=
    hspec.2.2.2.2.1
  have hhNextDeg :
      (henselFactorization_henselIterate π h0
        (Function.update s.qCorr (N + 1) q) (N + 1)).natDegree ≤ d - m :=
    hspec.2.2.2.2.2.1
  have hgNextRed :
      ∀ i : ℕ,
        (henselFactorization_henselIterate π g0
            (Function.update s.pCorr (N + 1) p) (N + 1) - g0).coeff i ∈
          IsLocalRing.maximalIdeal R :=
    hspec.2.2.2.2.2.2.1
  have hhNextRed :
      ∀ i : ℕ,
        (henselFactorization_henselIterate π h0
            (Function.update s.qCorr (N + 1) q) (N + 1) - h0).coeff i ∈
          IsLocalRing.maximalIdeal R :=
    hspec.2.2.2.2.2.2.2
  refine
    { pCorr := Function.update s.pCorr (N + 1) p
      qCorr := Function.update s.qCorr (N + 1) q
      fErr := fnNext
      prefixFactor := ?_
      pCorrDeg := ?_
      qCorrDeg := ?_
      factor := ?_
      gDeg := hgNextDeg
      hDeg := hhNextDeg
      gRed := hgNextRed
      hRed := hhNextRed }
  · intro r hr
    by_cases htop : r = N + 1
    · subst r
      exact ⟨fnNext, by simpa [Nat.add_assoc] using hfactorNext⟩
    · have hrn : r ≤ N := Nat.lt_succ_iff.mp (lt_of_le_of_ne hr htop)
      exact hprefixOld r hrn
  · exact henselFactorization_update_corr_natDegree_le s.pCorrDeg hpdeg
  · exact henselFactorization_update_corr_natDegree_le s.qCorrDeg hqdeg
  · simpa [Nat.add_assoc] using hfactorNext

/-- recursively chosen compatible finite Hensel prefixes in
the displayed-factor displayed-factor form.-/
def henselFactorization_prefixStateSeq_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) :
    (N : ℕ) → HenselFactorizationFinitePrefixState π f g0 h0 m d N
  | 0 =>
      henselFactorization_initialPrefixState_of_factor
        (π := π) (f := f) (g0 := g0) (h0 := h0)
        (f1 := f1) (m := m) (d := d)
        hfactor0 hg0nat hh0deg
  | N + 1 =>
      henselFactorization_chosenNextPrefixState_of_mem_span
        (π := π) hπne hπmem
        (f := f) (g0 := g0) (h0 := h0) (a := a) (b := b) (e := e)
        (gbar := gbar) (m := m) (d := d) (N := N)
        hf hg0map hg0nat hgbar_nat hglead hh0deg hbezFactor hmd
        (henselFactorization_prefixStateSeq_of_mem_span
          (π := π) (f := f) (g0 := g0) (h0 := h0)
          (a := a) (b := b) (f1 := f1) (e := e)
          (gbar := gbar) (m := m) (d := d)
          hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
          hfactor0 hbezFactor hmd N)

/-- the infinite `p`-correction sequence from the
displayed-factor displayed-factor prefix construction.-/
def henselFactorization_infinitePCorr_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) (n : ℕ) : R[X] :=
  (henselFactorization_prefixStateSeq_of_mem_span
    (π := π) (f := f) (g0 := g0) (h0 := h0)
    (a := a) (b := b) (f1 := f1) (e := e)
    (gbar := gbar) (m := m) (d := d)
    hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
    hfactor0 hbezFactor hmd n).pCorr n

/-- the infinite `q`-correction sequence from the
displayed-factor displayed-factor prefix construction.-/
def henselFactorization_infiniteQCorr_of_mem_span
    {R : Type*} [CommRing R] [IsLocalRing R] [NoZeroDivisors R]
    {π : R} (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal R)
    {f g0 h0 a b f1 e : R[X]}
    {gbar : (IsLocalRing.ResidueField R)[X]} {m d : ℕ}
    (hf : f.natDegree ≤ d)
    (hg0map : g0.map (IsLocalRing.residue R) = gbar)
    (hg0nat : g0.natDegree = m)
    (hgbar_nat : gbar.natDegree = m)
    (hglead : gbar.leadingCoeff ≠ 0)
    (hh0deg : h0.natDegree ≤ d - m)
    (hfactor0 : f - g0 * h0 = Polynomial.C π * f1)
    (hbezFactor : a * g0 + b * h0 - 1 = Polynomial.C π * e)
    (hmd : m ≤ d) (n : ℕ) : R[X] :=
  (henselFactorization_prefixStateSeq_of_mem_span
    (π := π) (f := f) (g0 := g0) (h0 := h0)
    (a := a) (b := b) (f1 := f1) (e := e)
    (gbar := gbar) (m := m) (d := d)
    hπne hπmem hf hg0map hg0nat hgbar_nat hglead hh0deg
    hfactor0 hbezFactor hmd n).qCorr n

end Valuations
end AlgebraicNumberTheory

end
