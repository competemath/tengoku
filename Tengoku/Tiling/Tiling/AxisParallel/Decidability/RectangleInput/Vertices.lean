import Tengoku.Tiling.Tiling.AxisParallel.Decidability.RectangleInput.Rectangles

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Intrinsic-vertex labels computed from local rectangle occupancy

A point label records a real-coordinate corner label and an imaginary-coordinate
corner label. The four quadrant flags use strict and weak endpoint comparisons;
the vertex test detects a boundary in both coordinate directions. Geometric
correctness is separated from this total primitive-recursive implementation.
-/

set_option autoImplicit false

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.RectangleInput

abbrev PointLabel := ℕ × ℕ

def sideCovered (n : ℕ) (history : List Bool) (vertical negative : Bool)
    (a b i : ℕ) : Bool :=
  bif negative then
    strictLevel n history vertical a i && compare n history vertical i b
  else compare n history vertical a i && strictLevel n history vertical i b

def quadrantRectangle (input : TableInput) (p : PointLabel) (west south : Bool)
    (k : ℕ) : Bool :=
  sideCovered (2 * input.1) input.2 false west (2 * k) (2 * k + 1) p.1 &&
    sideCovered (2 * input.1) input.2 true south (2 * k) (2 * k + 1) p.2

def quadrantOccupiedBool (input : TableInput) (p : PointLabel)
    (west south : Bool) : Bool := anyBelow input.1 (quadrantRectangle input p west south)

def vertexFlag (input : TableInput) (p : PointLabel) : Bool :=
  let nw := quadrantOccupiedBool input p true false
  let sw := quadrantOccupiedBool input p true true
  let ne := quadrantOccupiedBool input p false false
  let se := quadrantOccupiedBool input p false true
  (Bool.xor nw sw || Bool.xor ne se) && (Bool.xor nw ne || Bool.xor sw se)

def vertexAccepted (input : TableInput) (p : PointLabel) : Bool :=
  canonicalLevel (2 * input.1) input.2 false p.1 &&
    canonicalLevel (2 * input.1) input.2 true p.2 && vertexFlag input p

def vertexLabels (input : TableInput) : List PointLabel :=
  (pairs (2 * input.1)).filter (vertexAccepted input)

/--
@isnad1 id=iff.0h2v.s6.c3195735b19e from=translated src=- shape=7ed32966 vocab=56229d10
-/
theorem mem_vertexLabels {input : TableInput} {p : PointLabel} :
    p ∈ vertexLabels input ↔
      p.1 < 2 * input.1 ∧ p.2 < 2 * input.1 ∧ vertexAccepted input p = true := by
  simp [vertexLabels, mem_pairs, and_assoc]

/--
@isnad1 id=nodup.0h1v.s2.5ec4191b3078 from=translated src=- shape=1a6c1393 vocab=6a8d8597
-/
theorem vertexLabels_nodup (input : TableInput) : (vertexLabels input).Nodup :=
  (pairs_nodup (2 * input.1)).filter (vertexAccepted input)

/--
@isnad1 id=primrec.7h8v.s6.36ae3279eeac from=translated src=- shape=b3d33b6d vocab=f767055c
-/
theorem sideCovered_comp {α : Type*} [Primcodable α]
    {n : α → ℕ} {h : α → List Bool} {v neg : α → Bool} {a b i : α → ℕ}
    (hn : Primrec n) (hh : Primrec h) (hv : Primrec v) (hneg : Primrec neg)
    (ha : Primrec a) (hb : Primrec b) (hi : Primrec i) :
    Primrec (fun x => sideCovered (n x) (h x) (v x) (neg x) (a x) (b x) (i x)) :=
  Primrec.cond hneg
    ((Primrec.dom_bool₂ Bool.and).comp
      (strictLevel_comp hn hh hv ha hi) (compare_comp hn hh hv hi hb))
    ((Primrec.dom_bool₂ Bool.and).comp
      (compare_comp hn hh hv ha hi) (strictLevel_comp hn hh hv hi hb))

/--
@isnad1 id=primrec.0h0v.s7.f71fdb920335 from=translated src=- shape=4e66ff14 vocab=0e4db3cc
-/
theorem quadrantRectangle_primrec :
    Primrec (fun x : (TableInput × PointLabel × Bool × Bool) × ℕ =>
      quadrantRectangle x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2) := by
  have hn : Primrec (fun x : (TableInput × PointLabel × Bool × Bool) × ℕ =>
      2 * x.1.1.1) := Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hh : Primrec (fun x : (TableInput × PointLabel × Bool × Bool) × ℕ => x.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have ha : Primrec (fun x : (TableInput × PointLabel × Bool × Bool) × ℕ => 2 * x.2) :=
    Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd
  have hb : Primrec (fun x : (TableInput × PointLabel × Bool × Bool) × ℕ =>
      2 * x.2 + 1) := Primrec.nat_add.comp ha (Primrec.const 1)
  have hp : Primrec (fun x : (TableInput × PointLabel × Bool × Bool) × ℕ => x.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hw : Primrec (fun x : (TableInput × PointLabel × Bool × Bool) × ℕ => x.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hs : Primrec (fun x : (TableInput × PointLabel × Bool × Bool) × ℕ => x.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  exact (Primrec.dom_bool₂ Bool.and).comp
    (sideCovered_comp hn hh (Primrec.const false) hw ha hb (Primrec.fst.comp hp))
    (sideCovered_comp hn hh (Primrec.const true) hs ha hb (Primrec.snd.comp hp))

/--
@isnad1 id=primrec.4h5v.s6.94796bc54e9e from=translated src=- shape=b6b5e359 vocab=a80950ff
-/
theorem quadrantOccupiedBool_comp {α : Type*} [Primcodable α]
    {input : α → TableInput} {p : α → PointLabel} {west south : α → Bool}
    (hi : Primrec input) (hp : Primrec p) (hw : Primrec west) (hs : Primrec south) :
    Primrec (fun x => quadrantOccupiedBool (input x) (p x) (west x) (south x)) :=
  anyBelow_primrec (Primrec.fst.comp hi)
    (quadrantRectangle_primrec.comp
      (((hi.comp Primrec.fst).pair ((hp.comp Primrec.fst).pair
        ((hw.comp Primrec.fst).pair (hs.comp Primrec.fst)))).pair Primrec.snd))

/--
@isnad1 id=primrec.0h0v.s4.71803b9ace86 from=translated src=- shape=93eefbde vocab=afd4f0c1
-/
theorem vertexFlag_primrec : Primrec₂ vertexFlag := by
  have hq (w s : Bool) :
      Primrec (fun x : TableInput × PointLabel => quadrantOccupiedBool x.1 x.2 w s) :=
    quadrantOccupiedBool_comp Primrec.fst Primrec.snd (Primrec.const w) (Primrec.const s)
  exact (Primrec.dom_bool₂ Bool.and).comp
    ((Primrec.dom_bool₂ Bool.or).comp
      ((Primrec.dom_bool₂ Bool.xor).comp (hq true false) (hq true true))
      ((Primrec.dom_bool₂ Bool.xor).comp (hq false false) (hq false true)))
    ((Primrec.dom_bool₂ Bool.or).comp
      ((Primrec.dom_bool₂ Bool.xor).comp (hq true false) (hq false false))
      ((Primrec.dom_bool₂ Bool.xor).comp (hq true true) (hq false true)))

/--
@isnad1 id=primrec.0h0v.s4.8263882e316d from=translated src=- shape=93eefbde vocab=41224fc7
-/
theorem vertexAccepted_primrec : Primrec₂ vertexAccepted := by
  have hn : Primrec (fun x : TableInput × PointLabel => 2 * x.1.1) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.fst)
  have hh : Primrec (fun x : TableInput × PointLabel => x.1.2) :=
    Primrec.snd.comp Primrec.fst
  exact (Primrec.dom_bool₂ Bool.and).comp
    ((Primrec.dom_bool₂ Bool.and).comp
      (canonicalLevel_comp hn hh (Primrec.const false) (Primrec.fst.comp Primrec.snd))
      (canonicalLevel_comp hn hh (Primrec.const true) (Primrec.snd.comp Primrec.snd)))
    vertexFlag_primrec

end Tiling.AxisParallel.Decidability.RectangleInput
