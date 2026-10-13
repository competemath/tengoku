/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.Expander
public import Tengoku.Complexitylib.Complexitylib.Classes.PCP.Internal.Mixing
public import Tengoku

/-!
# Relabelling darts and padding with loops

Two bookkeeping operations on regular graphs, both preserving the spectral
bound in an explicit way.

* **Relabelling** the dart type along an equivalence. Constructions produce
  structured dart types — pairs, functions, sums — while `ExpanderFamily`
  wants `Fin degree`. The step operator is unchanged, so the bound is.

* **Padding** with self-loops, to raise the degree of a graph to a prescribed
  value. The new step is a convex combination of the old step and the identity,
  so by Jensen the bound becomes `μ² = α λ² + (1 - α)` with `α` the fraction of
  real darts.

## Main definitions

- `Complexity.RegGraph.relabel` — the same graph with darts renamed
- `Complexity.RegGraph.padLoops` — the graph with `k` self-loops added at every
  vertex

## Main results

- `Complexity.RegGraph.spectralBound_relabel`
- `Complexity.RegGraph.spectralBound_padLoops`
- `Complexity.RegGraph.relabelV`, `Complexity.RegGraph.spectralBound_relabelV` —
  renaming vertices
- `Complexity.RegGraph.toFinForm` — the same graph with both types numbered
-/

@[expose] public section

namespace Complexity

namespace RegGraph

variable (G : RegGraph)

/-! ### Relabelling -/

/-- The same graph with its darts renamed along `e`. -/
def relabel {D' : Type} [DecidableEq D'] [Fintype D'] (e : G.D ≃ D') : RegGraph where
  V := G.V
  D := D'
  decEqV := G.decEqV
  decEqD := inferInstance
  fintypeV := G.fintypeV
  fintypeD := inferInstance
  nonemptyD := ⟨e (Classical.arbitrary G.D)⟩
  rot := fun p => ((G.rot (p.1, e.symm p.2)).1, e (G.rot (p.1, e.symm p.2)).2)
  rot_involutive := by
    intro p
    simp only [Equiv.symm_apply_apply]
    have h := G.rot_involutive (p.1, e.symm p.2)
    rw [show (G.rot (p.1, e.symm p.2)).1 = (G.rot (p.1, e.symm p.2)).1 from rfl]
    conv_lhs => rw [show ((G.rot (p.1, e.symm p.2)).1, (G.rot (p.1, e.symm p.2)).2)
      = G.rot (p.1, e.symm p.2) from rfl]
    rw [h]
    simp

/--
@isnad1 id=eq.0h3v.s4.ab24b86edf9c from=translated src=- shape=d0bb49f5 vocab=c8e0f00b
-/
@[simp] theorem order_relabel {D' : Type} [DecidableEq D'] [Fintype D'] (e : G.D ≃ D') :
    (G.relabel e).order = G.order := rfl

/--
@isnad1 id=eq.0h3v.s4.46ac10580908 from=translated src=- shape=d0bb49f5 vocab=f4aaaaf1
-/
theorem deg_relabel {D' : Type} [DecidableEq D'] [Fintype D'] (e : G.D ≃ D') :
    (G.relabel e).deg = G.deg := by
  show Fintype.card D' = Fintype.card G.D
  exact (Fintype.card_congr e).symm

/--
@isnad1 id=eq.0h5v.s5.cb2cc3ad6cca from=translated src=- shape=e9ca197b vocab=6da83b82
-/
theorem step_relabel {D' : Type} [DecidableEq D'] [Fintype D'] (e : G.D ≃ D') (f : G.V → ℝ)
    (v : G.V) : (G.relabel e).step f v = G.step f v := by
  simp only [step, deg_relabel]
  congr 1
  show ∑ i : D', f (G.rot (v, e.symm i)).1 = ∑ i : G.D, f (G.rot (v, i)).1
  exact Fintype.sum_equiv e.symm _ _ fun i => rfl

/--
@isnad1 id=spectral.1h4v.s4.476b824136d8 from=translated src=- shape=4cae424d vocab=c72dc29f
-/
theorem spectralBound_relabel {D' : Type} [DecidableEq D'] [Fintype D'] (e : G.D ≃ D')
    {lam : ℝ} (h : G.SpectralBound lam) : (G.relabel e).SpectralBound lam := by
  intro f hf
  have := h f hf
  have hs : ∀ v, (G.relabel e).step f v = G.step f v := fun v => step_relabel G e f v
  simp only [hs]
  exact this

/-! ### Padding with loops -/

/-- The graph with `k` self-loops added at every vertex. -/
def padLoops (k : ℕ) : RegGraph where
  V := G.V
  D := G.D ⊕ Fin k
  decEqV := G.decEqV
  decEqD := inferInstance
  fintypeV := G.fintypeV
  fintypeD := inferInstance
  nonemptyD := ⟨Sum.inl (Classical.arbitrary G.D)⟩
  rot := fun p =>
    match p.2 with
    | Sum.inl i => ((G.rot (p.1, i)).1, Sum.inl (G.rot (p.1, i)).2)
    | Sum.inr j => (p.1, Sum.inr j)
  rot_involutive := by
    intro p
    obtain ⟨v, i | j⟩ := p
    · simp only
      have h := G.rot_involutive (v, i)
      conv_lhs => rw [show ((G.rot (v, i)).1, (G.rot (v, i)).2) = G.rot (v, i) from rfl]
      rw [h]
    · rfl

/--
@isnad1 id=eq.0h2v.s3.4a7847e60bc5 from=translated src=- shape=393de0b8 vocab=42c6e8e9
-/
@[simp] theorem order_padLoops (k : ℕ) : (G.padLoops k).order = G.order := rfl

/--
@isnad1 id=eq.0h2v.s4.35e400df49b5 from=translated src=- shape=42db545a vocab=7af09e18
-/
theorem deg_padLoops (k : ℕ) : (G.padLoops k).deg = G.deg + k := by
  show Fintype.card (G.D ⊕ Fin k) = _
  rw [Fintype.card_sum, Fintype.card_fin]
  rfl

/--
@isnad1 id=eq.0h4v.s6.da75ffb62efd from=translated src=- shape=d64a1fb0 vocab=e62460c4
-/
theorem step_padLoops (k : ℕ) (f : G.V → ℝ) (v : G.V) :
    (G.padLoops k).step f v
      = ((G.deg : ℝ) * G.step f v + (k : ℝ) * f v) / ((G.deg : ℝ) + k) := by
  have hd : (G.deg : ℝ) ≠ 0 := G.deg_ne_zero
  unfold step; erw [deg_padLoops]
  show (∑ i : G.D ⊕ Fin k, f ((G.padLoops k).nbr v i)) / ((G.deg + k : ℕ) : ℝ) = _
  rw [Fintype.sum_sum_type]
  have h1 : ∀ i : G.D, (G.padLoops k).nbr v (Sum.inl i) = G.nbr v i := fun i => rfl
  have h2 : ∀ j : Fin k, (G.padLoops k).nbr v (Sum.inr j) = v := fun j => rfl
  simp only [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  congr 1
  rw [mul_div_cancel₀ _ hd]

/-- **Padding keeps the bound**, with `μ² = α λ² + (1 - α)` for `α` the fraction of
real darts.
@isnad1 id=spectral.1h3v.s6.3b6446d608fe from=translated src=- shape=64a3611b vocab=9003b911
-/
theorem spectralBound_padLoops (k : ℕ) {lam : ℝ} (h : G.SpectralBound lam) :
    (G.padLoops k).SpectralBound
      (Real.sqrt (((G.deg : ℝ) * lam ^ 2 + k) / ((G.deg : ℝ) + k))) := by
  intro f hf
  have hspec := h f hf
  have hd : (0 : ℝ) < G.deg := by exact_mod_cast G.deg_pos
  have hD : (0 : ℝ) < (G.deg : ℝ) + k := by positivity
  rw [Real.sq_sqrt (by positivity)]
  set a : ℝ := (G.deg : ℝ) / ((G.deg : ℝ) + k) with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by rw [ha, div_le_one hD]; linarith
  have hb : (k : ℝ) / ((G.deg : ℝ) + k) = 1 - a := by
    rw [ha]; field_simp; ring
  -- Jensen for two terms
  have hpt : ∀ v, ((G.padLoops k).step f v) ^ 2 ≤ a * (G.step f v) ^ 2 + (1 - a) * (f v) ^ 2 := by
    intro v
    erw [step_padLoops]
    have hrw : ((G.deg : ℝ) * G.step f v + (k : ℝ) * f v) / ((G.deg : ℝ) + k)
        = a * G.step f v + (1 - a) * f v := by
      rw [← hb, ha]; field_simp
    rw [hrw]
    nlinarith [mul_nonneg ha0 (sub_nonneg.2 ha1), sq_nonneg (G.step f v - f v)]
  have hsum : ∑ v : G.V, ((G.padLoops k).step f v) ^ 2
      ≤ a * ∑ v : G.V, (G.step f v) ^ 2 + (1 - a) * ∑ v : G.V, (f v) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v _ => hpt v
  have hcoef : ((G.deg : ℝ) * lam ^ 2 + k) / ((G.deg : ℝ) + k) = a * lam ^ 2 + (1 - a) := by
    rw [← hb, ha]; field_simp
  rw [hcoef]
  show ∑ v : G.V, ((G.padLoops k).step f v) ^ 2 ≤ (a * lam ^ 2 + (1 - a)) * ∑ v : G.V, (f v) ^ 2
  nlinarith [hsum, mul_le_mul_of_nonneg_left hspec ha0]

/-! ### Renaming vertices -/

/-- The same graph with its vertices renamed along `e`. Constructions produce
structured vertex types — products, sums — while a family wants `Fin n`. -/
def relabelV {V' : Type} [DecidableEq V'] [Fintype V'] (e : G.V ≃ V') : RegGraph where
  V := V'
  D := G.D
  decEqV := inferInstance
  decEqD := G.decEqD
  fintypeV := inferInstance
  fintypeD := G.fintypeD
  nonemptyD := G.nonemptyD
  rot := fun p => (e (G.rot (e.symm p.1, p.2)).1, (G.rot (e.symm p.1, p.2)).2)
  rot_involutive := by
    intro p
    obtain ⟨v, i⟩ := p
    simp only [Equiv.symm_apply_apply]
    have h := G.rot_involutive (e.symm v, i)
    conv_lhs => rw [show ((G.rot (e.symm v, i)).1, (G.rot (e.symm v, i)).2)
      = G.rot (e.symm v, i) from rfl]
    rw [h]
    simp

/--
@isnad1 id=eq.0h3v.s4.3c67bb0d3f97 from=translated src=- shape=d0bb49f5 vocab=e61131f2
-/
@[simp] theorem deg_relabelV {V' : Type} [DecidableEq V'] [Fintype V'] (e : G.V ≃ V') :
    (G.relabelV e).deg = G.deg := rfl

/--
@isnad1 id=eq.0h3v.s4.be89a6a3c799 from=translated src=- shape=d0bb49f5 vocab=02d83513
-/
theorem order_relabelV {V' : Type} [DecidableEq V'] [Fintype V'] (e : G.V ≃ V') :
    (G.relabelV e).order = G.order := (Fintype.card_congr e).symm

/--
@isnad1 id=eq.0h5v.s6.de1ebe6225a8 from=translated src=- shape=472d76e6 vocab=f10e167b
-/
theorem step_relabelV {V' : Type} [DecidableEq V'] [Fintype V'] (e : G.V ≃ V')
    (f : V' → ℝ) (v : V') :
    (G.relabelV e).step f v = G.step (fun w => f (e w)) (e.symm v) := by
  simp only [step, deg_relabelV]
  congr 1

/--
@isnad1 id=spectral.1h4v.s4.705ca235d1c2 from=translated src=- shape=4cae424d vocab=2bd28efd
-/
theorem spectralBound_relabelV {V' : Type} [DecidableEq V'] [Fintype V'] (e : G.V ≃ V')
    {lam : ℝ} (h : G.SpectralBound lam) : (G.relabelV e).SpectralBound lam := by
  intro f hf
  have hf' : ∑ w : G.V, f (e w) = 0 := by
    rw [Fintype.sum_equiv e (fun w => f (e w)) f fun w => rfl]
    exact hf
  have hb := h (fun w => f (e w)) hf'
  calc ∑ v : V', ((G.relabelV e).step f v) ^ 2
      = ∑ w : G.V, (G.step (fun w => f (e w)) w) ^ 2 :=
        (Fintype.sum_equiv e (fun w => (G.step (fun w => f (e w)) w) ^ 2)
          (fun v => ((G.relabelV e).step f v) ^ 2) fun w => by
            show (G.step (fun w => f (e w)) w) ^ 2 = ((G.relabelV e).step f (e w)) ^ 2
            rw [step_relabelV (G := G) (e := e) (f := f) (v := e w), Equiv.symm_apply_apply]).symm
    _ ≤ lam ^ 2 * ∑ w : G.V, (f (e w)) ^ 2 := hb
    _ = lam ^ 2 * ∑ v : V', (f v) ^ 2 := by
        congr 1
        exact Fintype.sum_equiv e (fun w => (f (e w)) ^ 2) (fun v => (f v) ^ 2) fun w => rfl

/-! ### Numbering both types -/

/-- The same graph with its vertices numbered `Fin order` and its darts
`Fin deg`. Constructions build structured types; the merge and the expander
families want numbered ones. -/
noncomputable def toFinForm : RegGraph :=
  (G.relabelV (Fintype.equivFin G.V)).relabel (Fintype.equivFin G.D)

/--
@isnad1 id=eq.0h1v.s3.b1583bb91b6c from=translated src=- shape=8d4cac31 vocab=6ba9b534
-/
@[simp] theorem order_toFinForm : G.toFinForm.order = G.order := by
  unfold toFinForm; erw [ order_relabel, order_relabelV]

/--
@isnad1 id=eq.0h1v.s3.88b44a397eaa from=translated src=- shape=8d4cac31 vocab=536676c7
-/
@[simp] theorem deg_toFinForm : G.toFinForm.deg = G.deg := by
  unfold toFinForm; erw [ deg_relabel, deg_relabelV]

/--
@isnad1 id=spectral.1h2v.s3.4b1c14c1934a from=translated src=- shape=e8c79755 vocab=3f4e8839
-/
theorem spectralBound_toFinForm {lam : ℝ} (h : G.SpectralBound lam) :
    G.toFinForm.SpectralBound lam :=
  spectralBound_relabel _ _ (spectralBound_relabelV G (Fintype.equivFin G.V) h)

/-- The same graph numbered at sizes supplied by the caller, so that the
rotation map has the literal type `Fin N × Fin d → Fin N × Fin d` a numeric
construction expects, with no transport at the use site. -/
noncomputable def toFinFormOf (N d : ℕ) (hN : Fintype.card G.V = N)
    (hd : Fintype.card G.D = d) : RegGraph :=
  (G.relabelV ((Fintype.equivFin G.V).trans (finCongr hN))).relabel
    ((Fintype.equivFin G.D).trans (finCongr hd))

/--
@isnad1 id=eq.2h3v.s5.163cc51164b6 from=translated src=- shape=16cbe92b vocab=e7aef5fd
-/
theorem toFinFormOf_V (N d : ℕ) (hN : Fintype.card G.V = N) (hd : Fintype.card G.D = d) :
    (G.toFinFormOf N d hN hd).V = Fin N := rfl

/--
@isnad1 id=eq.2h3v.s5.ee2a90ca9271 from=translated src=- shape=eab93065 vocab=e7aef5fd
-/
theorem toFinFormOf_D (N d : ℕ) (hN : Fintype.card G.V = N) (hd : Fintype.card G.D = d) :
    (G.toFinFormOf N d hN hd).D = Fin d := rfl

/--
@isnad1 id=eq.2h3v.s5.15c62fee6d30 from=translated src=- shape=b212cba4 vocab=ea58e4ac
-/
@[simp] theorem order_toFinFormOf (N d : ℕ) (hN : Fintype.card G.V = N)
    (hd : Fintype.card G.D = d) : (G.toFinFormOf N d hN hd).order = N := Fintype.card_fin N

/--
@isnad1 id=eq.2h3v.s5.a5f3177352d5 from=translated src=- shape=e5ec1237 vocab=e32be055
-/
@[simp] theorem deg_toFinFormOf (N d : ℕ) (hN : Fintype.card G.V = N)
    (hd : Fintype.card G.D = d) : (G.toFinFormOf N d hN hd).deg = d := Fintype.card_fin d

/--
@isnad1 id=spectral.3h4v.s5.8a4b5a95e6bb from=translated src=- shape=8114481d vocab=689322e5
-/
theorem spectralBound_toFinFormOf (N d : ℕ) (hN : Fintype.card G.V = N)
    (hd : Fintype.card G.D = d) {lam : ℝ} (h : G.SpectralBound lam) :
    (G.toFinFormOf N d hN hd).SpectralBound lam :=
  spectralBound_relabel _ _ (spectralBound_relabelV G _ h)

/-- Its vertices are literally numbered.
@isnad1 id=eq.0h1v.s3.38b787868ed9 from=translated src=- shape=4726c159 vocab=266b2891
-/
theorem toFinForm_V : G.toFinForm.V = Fin (Fintype.card G.V) := rfl

/-- And so are its darts.
@isnad1 id=eq.0h1v.s3.782382bc30e2 from=translated src=- shape=4726c159 vocab=eb977e28
-/
theorem toFinForm_D : G.toFinForm.D = Fin (Fintype.card G.D) := rfl

end RegGraph

end Complexity
