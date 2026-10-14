/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.FiniteCyclicPresentation
public import Tengoku

/-!
# Gallier--Xu P1 edge subdivision

This file formalizes the first primitive subdivision from Gallier--Xu, Definition 6.3. For a
chosen oriented edge `a`, P1 globally replaces

* `a` by `b c`, and
* `a⁻¹` by `c⁻¹ b⁻¹`.

The canonical finite implementation retains every old edge name through `Fin.castSucc`, uses the
retained name of `a` for `b`, and uses `Fin.last` for the fresh edge `c`. A contraction deletes
the fresh edge and sends every retained edge back to its old name. This contraction is a left
inverse on words, including cyclic words, so P1 both preserves and reflects cyclic rotation.
The selected underlying edge uses its positive stored orientation canonically. The
`SignedPresentationIso` in `P1Subdivision` allows the two target edge names to be renamed and
reoriented when a different orientation convention is desired.

The presentation-level construction preserves face positions, copies the multiplicity of `a` to
both subdivided edges, and preserves ordinary validity, face-incidence connectivity, and
`IsGallierValid`. `P1Subdivision` closes the canonical construction under signed presentation
isomorphism.
-/

@[expose] public section

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces
namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace P1

/-- Retain an old signed edge in the enlarged edge type. -/
def castSuccDart {n : ℕ} : SignedDart (Fin n) → SignedDart (Fin (n + 1))
  | .pos e => .pos e.castSucc
  | .neg e => .neg e.castSucc

/--
@isnad1 id=eq.0h2v.s5.f4bcef60f377 from=translated src=- shape=7412d20c vocab=d6d8462b
-/
@[simp]
theorem castSuccDart_pos {n : ℕ} (e : Fin n) :
    castSuccDart (.pos e) = .pos e.castSucc :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.4bec4f972da7 from=translated src=- shape=7412d20c vocab=5dc175b5
-/
@[simp]
theorem castSuccDart_neg {n : ℕ} (e : Fin n) :
    castSuccDart (.neg e) = .neg e.castSucc :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.810e5d9841c8 from=translated src=- shape=8591dcbc vocab=8c7bfc48
-/
@[simp]
theorem edgeOfDart_castSuccDart {n : ℕ} (d : SignedDart (Fin n)) :
    edgeOfDart (castSuccDart d) = (edgeOfDart d).castSucc := by
  cases d <;> rfl

/-- The fresh second subedge in the canonical P1 expansion. -/
def freshEdge (n : ℕ) : Fin (n + 1) :=
  Fin.last n

/-- The retained first subedge in the canonical P1 expansion. -/
def firstSubedge {n : ℕ} (a : Fin n) : Fin (n + 1) :=
  a.castSucc

/--
@isnad1 id=ne.0h2v.s4.2f7866536456 from=translated src=- shape=7451783b vocab=06081af9
-/
theorem firstSubedge_ne_freshEdge {n : ℕ} (a : Fin n) :
    firstSubedge a ≠ freshEdge n :=
  Fin.castSucc_ne_last a

/-- Substitute one signed occurrence according to Gallier--Xu P1. -/
def expandDart {n : ℕ} (a : Fin n) :
    SignedDart (Fin n) → List (SignedDart (Fin (n + 1)))
  | .pos e =>
      if e = a then
        [.pos (firstSubedge a), .pos (freshEdge n)]
      else
        [.pos e.castSucc]
  | .neg e =>
      if e = a then
        [.neg (freshEdge n), .neg (firstSubedge a)]
      else
        [.neg e.castSucc]

/--
@isnad1 id=eq.0h2v.s6.f15ecf2276ce from=translated src=- shape=ca701e22 vocab=b6a608e2
-/
@[simp]
theorem expandDart_pos_self {n : ℕ} (a : Fin n) :
    expandDart a (.pos a) = [.pos (firstSubedge a), .pos (freshEdge n)] := by
  simp [expandDart]

/--
@isnad1 id=eq.0h2v.s6.4ed7ce68d3e0 from=translated src=- shape=023948f8 vocab=a4cf7c76
-/
@[simp]
theorem expandDart_neg_self {n : ℕ} (a : Fin n) :
    expandDart a (.neg a) = [.neg (freshEdge n), .neg (firstSubedge a)] := by
  simp [expandDart]

/--
@isnad1 id=eq.1h3v.s6.ad5a57304e29 from=translated src=- shape=fa426f38 vocab=bd691216
-/
theorem expandDart_pos_of_ne {n : ℕ} {a e : Fin n} (h : e ≠ a) :
    expandDart a (.pos e) = [.pos e.castSucc] := by
  simp [expandDart, h]

/--
@isnad1 id=eq.1h3v.s6.c179b9e649ba from=translated src=- shape=fa426f38 vocab=c2ba9bf4
-/
theorem expandDart_neg_of_ne {n : ℕ} {a e : Fin n} (h : e ≠ a) :
    expandDart a (.neg e) = [.neg e.castSucc] := by
  simp [expandDart, h]

/-- P1 sends the opposite dart to the inverse of the substituted word.
@isnad1 id=eq.0h3v.s5.f255cb95d440 from=translated src=- shape=6726789f vocab=62a1a05c
-/
@[simp]
theorem expandDart_flip {n : ℕ} (a : Fin n) (d : SignedDart (Fin n)) :
    expandDart a d.flip = inverseWord (expandDart a d) := by
  cases d with
  | pos e =>
      by_cases h : e = a
      · subst e
        simp [expandDart, inverseWord, SignedDart.flip]
      · simp [expandDart, inverseWord, SignedDart.flip, h]
  | neg e =>
      by_cases h : e = a
      · subst e
        simp [expandDart, inverseWord, SignedDart.flip]
      · simp [expandDart, inverseWord, SignedDart.flip, h]

/--
@isnad1 id=mem.0h3v.s6.c2e7e81b79c3 from=translated src=- shape=722ad599 vocab=ef7fdf22
-/
theorem castSuccDart_mem_expandDart {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    castSuccDart d ∈ expandDart a d := by
  cases d with
  | pos e =>
      by_cases h : e = a
      · subst e
        simp [firstSubedge]
      · simp [expandDart, h]
  | neg e =>
      by_cases h : e = a
      · subst e
        simp [firstSubedge]
      · simp [expandDart, h]

/-- Contract one target dart: discard the fresh edge and retain every old edge. -/
def contractDart {n : ℕ} :
    SignedDart (Fin (n + 1)) → Option (SignedDart (Fin n))
  | .pos e => Fin.lastCases none (fun b ↦ some (.pos b)) e
  | .neg e => Fin.lastCases none (fun b ↦ some (.neg b)) e

/--
@isnad1 id=eq.0h2v.s5.36f92b904ec9 from=translated src=- shape=ff0ced94 vocab=7443559e
-/
@[simp]
theorem contractDart_pos_castSucc {n : ℕ} (e : Fin n) :
    contractDart (.pos e.castSucc) = some (.pos e) := by
  simp [contractDart]

/--
@isnad1 id=eq.0h2v.s5.3256a0221b74 from=translated src=- shape=ff0ced94 vocab=6980acbb
-/
@[simp]
theorem contractDart_neg_castSucc {n : ℕ} (e : Fin n) :
    contractDart (.neg e.castSucc) = some (.neg e) := by
  simp [contractDart]

/--
@isnad1 id=eq.0h1v.s4.1da26fe83445 from=translated src=- shape=5fa49746 vocab=e3bdd605
-/
@[simp]
theorem contractDart_pos_freshEdge (n : ℕ) :
    contractDart (.pos (freshEdge n)) = none := by
  simp [contractDart, freshEdge]

/--
@isnad1 id=eq.0h1v.s4.679dd1a0e0a6 from=translated src=- shape=5fa49746 vocab=ddc5c074
-/
@[simp]
theorem contractDart_neg_freshEdge (n : ℕ) :
    contractDart (.neg (freshEdge n)) = none := by
  simp [contractDart, freshEdge]

/-- Apply P1 simultaneously to every occurrence in a linear representative of a cyclic word. -/
def expandWord {n : ℕ} (a : Fin n) (word : List (SignedDart (Fin n))) :
    List (SignedDart (Fin (n + 1))) :=
  word.flatMap (expandDart a)

/-- Contract a P1 word by deleting the fresh subedge. -/
def contractWord {n : ℕ} (word : List (SignedDart (Fin (n + 1)))) :
    List (SignedDart (Fin n)) :=
  word.filterMap contractDart

/--
@isnad1 id=eq.0h2v.s5.545466748749 from=translated src=- shape=1f2c8196 vocab=b783403b
-/
@[simp]
theorem expandWord_nil {n : ℕ} (a : Fin n) :
    expandWord a [] = [] :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.68397cdc3297 from=translated src=- shape=70b37c99 vocab=74fc7559
-/
@[simp]
theorem expandWord_cons {n : ℕ} (a : Fin n) (d : SignedDart (Fin n))
    (word : List (SignedDart (Fin n))) :
    expandWord a (d :: word) = expandDart a d ++ expandWord a word :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.7906678b566e from=translated src=- shape=d83af7ab vocab=91fc5848
-/
theorem expandWord_singleton {n : ℕ} (a : Fin n) (d : SignedDart (Fin n)) :
    expandWord a [d] = expandDart a d := by
  simp [expandWord]

/--
@isnad1 id=eq.0h4v.s7.6f011bf68668 from=translated src=- shape=61dd9763 vocab=abd36165
-/
@[simp]
theorem expandWord_append {n : ℕ} (a : Fin n)
    (left right : List (SignedDart (Fin n))) :
    expandWord a (left ++ right) = expandWord a left ++ expandWord a right := by
  simp [expandWord]

/--
@isnad1 id=eq.0h1v.s4.a4127e528754 from=translated src=- shape=eebe8cda vocab=e44b9634
-/
@[simp]
theorem contractWord_nil {n : ℕ} :
    contractWord ([] : List (SignedDart (Fin (n + 1)))) = [] :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.62a5d654ffd3 from=translated src=- shape=f1a7e7f9 vocab=4a9f0138
-/
@[simp]
theorem contractWord_append {n : ℕ}
    (left right : List (SignedDart (Fin (n + 1)))) :
    contractWord (left ++ right) = contractWord left ++ contractWord right := by
  simp [contractWord]

/-- Contracting one substituted occurrence returns that occurrence.
@isnad1 id=eq.0h3v.s4.f2b8b0d17478 from=translated src=- shape=222b6600 vocab=6cb898e8
-/
@[simp]
theorem contractWord_expandDart {n : ℕ} (a : Fin n)
    (d : SignedDart (Fin n)) :
    contractWord (expandDart a d) = [d] := by
  cases d with
  | pos e =>
      by_cases h : e = a
      · subst e
        simp [contractWord, contractDart, firstSubedge, freshEdge]
      · simp [contractWord, contractDart, expandDart, h]
  | neg e =>
      by_cases h : e = a
      · subst e
        simp [contractWord, contractDart, firstSubedge, freshEdge]
      · simp [contractWord, contractDart, expandDart, h]

/-- Contracting the global P1 substitution returns the original word exactly.
@isnad1 id=eq.0h3v.s4.60575c0652b1 from=translated src=- shape=c7a10374 vocab=bd41b120
-/
@[simp]
theorem contractWord_expandWord {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) :
    contractWord (expandWord a word) = word := by
  induction word with
  | nil => rfl
  | cons d word ih =>
      rw [expandWord_cons, contractWord_append, contractWord_expandDart, ih]
      rfl

/--
@isnad1 id=iff.0h3v.s5.85da773f3cbe from=translated src=- shape=b4a782a7 vocab=b783403b
-/
@[simp]
theorem expandWord_eq_nil_iff {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) :
    expandWord a word = [] ↔ word = [] := by
  constructor
  · intro h
    have hcontract := congrArg contractWord h
    simpa only [contractWord_expandWord, contractWord_nil] using hcontract
  · rintro rfl
    rfl

/-- P1 commutes with reversal of an oriented cyclic boundary word.
@isnad1 id=eq.0h3v.s5.d0eeeefe1388 from=translated src=- shape=c158d2bc vocab=e54e7677
-/
@[simp]
theorem expandWord_inverseWord {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) :
    expandWord a (inverseWord word) = inverseWord (expandWord a word) := by
  induction word with
  | nil => rfl
  | cons d word ih =>
      calc
        expandWord a (inverseWord (d :: word)) =
            expandWord a (inverseWord word ++ [d.flip]) := by
              simp [inverseWord]
        _ = expandWord a (inverseWord word) ++ expandWord a [d.flip] :=
          expandWord_append a _ _
        _ = inverseWord (expandWord a word) ++ inverseWord (expandDart a d) := by
          rw [ih, expandWord_singleton, expandDart_flip]
        _ = inverseWord (expandDart a d ++ expandWord a word) :=
          (inverseWord_append _ _).symm
        _ = inverseWord (expandWord a (d :: word)) :=
          rfl

/-- A list-valued substitution preserves cyclic rotation.
@isnad1 id=isrotate.1h4v.s5.d5dbeed29e4e from=translated src=- shape=0cec546d vocab=d02b334a
-/
theorem expandWord_isRotated {n : ℕ} {a : Fin n}
    {left right : List (SignedDart (Fin n))}
    (h : left.IsRotated right) :
    (expandWord a left).IsRotated (expandWord a right) := by
  rcases h with ⟨k, rfl⟩
  let m := k % left.length
  have hleft : left = left.take m ++ left.drop m :=
    (List.take_append_drop m left).symm
  have hrotate : left.rotate k = left.drop m ++ left.take m := by
    simpa only [m] using
      (List.rotate_eq_drop_append_take_mod (l := left) (n := k))
  calc
    expandWord a left ~r expandWord a (left.drop m ++ left.take m) := by
      have hexpand :=
        congrArg (expandWord a) hleft
      rw [hexpand]
      simp only [expandWord_append]
      exact List.isRotated_append
    _ = expandWord a (left.rotate k) := congrArg (expandWord a) hrotate.symm

/-- Contraction preserves cyclic rotation even when the cut passes through a subdivided pair.
@isnad1 id=isrotate.1h3v.s6.a69ed99b0702 from=translated src=- shape=3046fb82 vocab=5485682a
-/
theorem contractWord_isRotated {n : ℕ}
    {left right : List (SignedDart (Fin (n + 1)))}
    (h : left.IsRotated right) :
    (contractWord left).IsRotated (contractWord right) := by
  rcases h with ⟨k, rfl⟩
  let m := k % left.length
  have hleft : left = left.take m ++ left.drop m :=
    (List.take_append_drop m left).symm
  have hrotate : left.rotate k = left.drop m ++ left.take m := by
    simpa only [m] using
      (List.rotate_eq_drop_append_take_mod (l := left) (n := k))
  calc
    contractWord left ~r contractWord (left.drop m ++ left.take m) := by
      have hcontract :=
        congrArg contractWord hleft
      rw [hcontract]
      simp only [contractWord_append]
      exact List.isRotated_append
    _ = contractWord (left.rotate k) := congrArg contractWord hrotate.symm

/-- P1 substitution preserves and reflects cyclic rotation.
@isnad1 id=iff.0h4v.s5.de0bf9f1a8bf from=translated src=- shape=608a27d3 vocab=d02b334a
-/
@[simp]
theorem expandWord_isRotated_iff {n : ℕ} (a : Fin n)
    (left right : List (SignedDart (Fin n))) :
    (expandWord a left).IsRotated (expandWord a right) ↔
      left.IsRotated right := by
  constructor
  · intro h
    simpa only [contractWord_expandWord] using contractWord_isRotated h
  · exact expandWord_isRotated

/-- The occurrence of every retained edge survives the expansion.
@isnad1 id=mem.1h4v.s7.91ff4acb65a2 from=translated src=- shape=430ae1ed vocab=c32854d4
-/
theorem castSucc_edge_mem_expandWord {n : ℕ} {a e : Fin n}
    {word : List (SignedDart (Fin n))}
    (h : e ∈ word.map edgeOfDart) :
    e.castSucc ∈ (expandWord a word).map edgeOfDart := by
  rcases List.mem_map.mp h with ⟨d, hd, rfl⟩
  refine List.mem_map.mpr ⟨castSuccDart d, ?_, edgeOfDart_castSuccDart d⟩
  exact List.mem_flatMap.mpr ⟨d, hd, castSuccDart_mem_expandDart a d⟩

/-- Each retained edge has exactly its old word multiplicity after P1.
@isnad1 id=eq.0h4v.s7.e0a2684ddbd8 from=translated src=- shape=441c62a0 vocab=f7629e1e
-/
theorem count_expandWord_castSucc {n : ℕ} (a e : Fin n)
    (word : List (SignedDart (Fin n))) :
    (word.map edgeOfDart).count e =
      ((expandWord a word).map edgeOfDart).count e.castSucc := by
  induction word with
  | nil => simp
  | cons d word ih =>
      cases d with
      | pos b =>
          by_cases h : b = a
          · subst b
            have hlast : Fin.last n ≠ e.castSucc :=
              Ne.symm (Fin.castSucc_ne_last e)
            simp [expandDart, ih, freshEdge, firstSubedge, edgeOfDart,
              List.count_cons, beq_iff_eq, hlast]
          · simp [expandDart, h, ih, edgeOfDart, List.count_cons, beq_iff_eq]
      | neg b =>
          by_cases h : b = a
          · subst b
            have hlast : Fin.last n ≠ e.castSucc :=
              Ne.symm (Fin.castSucc_ne_last e)
            simp [expandDart, ih, freshEdge, firstSubedge, edgeOfDart,
              List.count_cons, beq_iff_eq, hlast]
          · simp [expandDart, h, ih, edgeOfDart, List.count_cons, beq_iff_eq]

/-- The fresh edge receives exactly the old multiplicity of the subdivided edge.
@isnad1 id=eq.0h3v.s6.948b4efd2009 from=translated src=- shape=e744652f vocab=a63af6c3
-/
theorem count_expandWord_freshEdge {n : ℕ} (a : Fin n)
    (word : List (SignedDart (Fin n))) :
    (word.map edgeOfDart).count a =
      ((expandWord a word).map edgeOfDart).count (freshEdge n) := by
  induction word with
  | nil => simp
  | cons d word ih =>
      cases d with
      | pos b =>
          by_cases h : b = a
          · subst b
            simp [expandDart, ih, freshEdge, firstSubedge, edgeOfDart]
          · simp [expandDart, h, ih, freshEdge, edgeOfDart]
      | neg b =>
          by_cases h : b = a
          · subst b
            simp [expandDart, ih, freshEdge, firstSubedge, edgeOfDart]
          · simp [expandDart, h, ih, freshEdge, edgeOfDart]

/-- Canonical presentation-level P1 expansion. -/
abbrev expand (P : FiniteCyclicPresentation) (a : P.Edge) :
    FiniteCyclicPresentation where
  edgeCount := P.edgeCount + 1
  faces := P.faces.map (expandWord a)

/--
@isnad1 id=eq.0h2v.s4.4db739471d60 from=translated src=- shape=34012f48 vocab=b6f68337
-/
@[simp]
theorem expand_edgeCount (P : FiniteCyclicPresentation) (a : P.Edge) :
    (expand P a).edgeCount = P.edgeCount + 1 :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.2f3eefe08b22 from=translated src=- shape=e3a29f9c vocab=ddd1ecbb
-/
theorem expand_faces_length (P : FiniteCyclicPresentation) (a : P.Edge) :
    (expand P a).faces.length = P.faces.length := by
  simp [expand]

/-- P1 preserves face positions. -/
def faceEquiv (P : FiniteCyclicPresentation) (a : P.Edge) :
    P.Face ≃ (expand P a).Face :=
  finCongr (expand_faces_length P a).symm

/--
@isnad1 id=eq.0h3v.s6.c3fd78a8baa1 from=translated src=- shape=83866e07 vocab=2ddb8d27
-/
@[simp]
theorem faceEquiv_apply_val (P : FiniteCyclicPresentation) (a : P.Edge)
    (f : P.Face) :
    (faceEquiv P a f).val = f.val :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.f8be19574d56 from=translated src=- shape=def35049 vocab=7fb361ed
-/
@[simp]
theorem expand_boundary (P : FiniteCyclicPresentation) (a : P.Edge)
    (f : P.Face) :
    (expand P a).boundary (faceEquiv P a f) =
      expandWord a (P.boundary f) := by
  simp [boundary, List.get_eq_getElem, expand, faceEquiv]

/-- P1 copies every retained edge's facewise multiplicity.
@isnad1 id=eq.0h4v.s6.696ef40ae073 from=translated src=- shape=90989695 vocab=5bc3e68a
-/
theorem faceEdgeMultiplicity_expand_castSucc
    (P : FiniteCyclicPresentation) (a e : P.Edge) (f : P.Face) :
    P.faceEdgeMultiplicity f e =
      (expand P a).faceEdgeMultiplicity (faceEquiv P a f) e.castSucc := by
  simp only [faceEdgeMultiplicity, expand_boundary]
  exact count_expandWord_castSucc a e (P.boundary f)

/-- P1 gives the fresh edge the subdivided edge's facewise multiplicity.
@isnad1 id=eq.0h3v.s5.d64bfe38cf85 from=translated src=- shape=8f771589 vocab=2df6609e
-/
theorem faceEdgeMultiplicity_expand_freshEdge
    (P : FiniteCyclicPresentation) (a : P.Edge) (f : P.Face) :
    P.faceEdgeMultiplicity f a =
      (expand P a).faceEdgeMultiplicity (faceEquiv P a f)
        (freshEdge P.edgeCount) := by
  simp only [faceEdgeMultiplicity, expand_boundary]
  exact count_expandWord_freshEdge a (P.boundary f)

/-- P1 copies every retained edge's total multiplicity.
@isnad1 id=eq.0h3v.s4.ae9955e79364 from=translated src=- shape=40d22da0 vocab=5310cb6c
-/
theorem edgeMultiplicity_expand_castSucc
    (P : FiniteCyclicPresentation) (a e : P.Edge) :
    P.edgeMultiplicity e = (expand P a).edgeMultiplicity e.castSucc := by
  unfold edgeMultiplicity
  exact Fintype.sum_equiv (faceEquiv P a) _ _ fun f ↦
    faceEdgeMultiplicity_expand_castSucc P a e f

/-- P1 gives the fresh edge the subdivided edge's total multiplicity.
@isnad1 id=eq.0h2v.s4.9d36fd1ac2c8 from=translated src=- shape=ac2b719b vocab=80c3a167
-/
theorem edgeMultiplicity_expand_freshEdge
    (P : FiniteCyclicPresentation) (a : P.Edge) :
    P.edgeMultiplicity a =
      (expand P a).edgeMultiplicity (freshEdge P.edgeCount) := by
  unfold edgeMultiplicity
  exact Fintype.sum_equiv (faceEquiv P a) _ _ fun f ↦
    faceEdgeMultiplicity_expand_freshEdge P a f

/-- P1 sends source face adjacency to target face adjacency.
@isnad1 id=faceadja.1h4v.s6.33449b2d883e from=translated src=- shape=de051e3e vocab=f0e4dc9f
-/
theorem map_faceAdjacent
    (P : FiniteCyclicPresentation) (a : P.Edge) {f g : P.Face}
    (h : P.FaceAdjacent f g) :
    (expand P a).FaceAdjacent (faceEquiv P a f) (faceEquiv P a g) := by
  rcases h with ⟨e, hef, heg⟩
  refine ⟨e.castSucc, ?_, ?_⟩
  · rw [expand_boundary]
    exact castSucc_edge_mem_expandWord hef
  · rw [expand_boundary]
    exact castSucc_edge_mem_expandWord heg

/-- P1 preserves ordinary finite-presentation incidence validity.
@isnad1 id=issurfac.1h2v.s3.6327ef5c23aa from=translated src=- shape=8f4fd3ab vocab=a8d0b81a
-/
theorem expand_isSurfaceValid
    (P : FiniteCyclicPresentation) (a : P.Edge) (h : P.IsSurfaceValid) :
    (expand P a).IsSurfaceValid := by
  refine ⟨(faceEquiv P a).nonempty_congr.mp h.1, ?_, ?_, ?_⟩
  · intro q hq
    let f := (faceEquiv P a).symm q
    have hboundary :
        (expand P a).boundary (faceEquiv P a f) =
          expandWord a (P.boundary f) :=
      expand_boundary P a f
    rw [(faceEquiv P a).apply_symm_apply] at hboundary
    have hexpanded : expandWord a (P.boundary f) = [] := by
      rw [← hboundary]
      exact hq
    exact h.2.1 f ((expandWord_eq_nil_iff a (P.boundary f)).mp hexpanded)
  · intro q r hqr
    let f := (faceEquiv P a).symm q
    let g := (faceEquiv P a).symm r
    have htargetBoundary :
        ((expand P a).boundary (faceEquiv P a f)).IsRotated
          ((expand P a).boundary (faceEquiv P a g)) := by
      have hq : faceEquiv P a f = q :=
        (faceEquiv P a).apply_symm_apply q
      have hr : faceEquiv P a g = r :=
        (faceEquiv P a).apply_symm_apply r
      rw [hq, hr]
      exact hqr
    rw [expand_boundary, expand_boundary] at htargetBoundary
    have htarget :
        (expandWord a (P.boundary f)).IsRotated
          (expandWord a (P.boundary g)) :=
      htargetBoundary
    have hsource :=
      (expandWord_isRotated_iff a (P.boundary f) (P.boundary g)).mp htarget
    have hfg := h.2.2.1 f g hsource
    calc
      q = faceEquiv P a f := ((faceEquiv P a).apply_symm_apply q).symm
      _ = faceEquiv P a g := congrArg (faceEquiv P a) hfg
      _ = r := (faceEquiv P a).apply_symm_apply r
  · intro e
    change Fin (P.edgeCount + 1) at e
    refine Fin.lastCases ?_ (fun b ↦ ?_) e
    · have hmultiplicity := h.2.2.2 a
      rw [edgeMultiplicity_expand_freshEdge P a] at hmultiplicity
      simpa only [freshEdge] using hmultiplicity
    · have hmultiplicity := h.2.2.2 b
      rw [edgeMultiplicity_expand_castSucc P a b] at hmultiplicity
      exact hmultiplicity

/-- P1 preserves connectedness of the face-edge incidence graph.
@isnad1 id=isconnec.1h2v.s3.32317a59bb33 from=translated src=- shape=8f4fd3ab vocab=f5a4dec8
-/
theorem expand_isConnected
    (P : FiniteCyclicPresentation) (a : P.Edge) (h : P.IsConnected) :
    (expand P a).IsConnected := by
  refine ⟨(faceEquiv P a).nonempty_congr.mp h.1, ?_⟩
  intro q r
  have hchain := h.2 ((faceEquiv P a).symm q) ((faceEquiv P a).symm r)
  have hmapped := hchain.lift (faceEquiv P a) fun _ _ hadj ↦
    map_faceAdjacent P a hadj
  change Relation.ReflTransGen (expand P a).FaceAdjacent
    (faceEquiv P a ((faceEquiv P a).symm q))
    (faceEquiv P a ((faceEquiv P a).symm r)) at hmapped
  simpa only [(faceEquiv P a).apply_symm_apply] using hmapped

/-- P1 preserves the regular and exceptional branches of Gallier validity.

The exceptional branch is impossible here because selecting `a` already supplies an edge.
@isnad1 id=isgallie.1h2v.s3.63f6aebebcd7 from=translated src=- shape=8f4fd3ab vocab=050a9591
-/
theorem expand_isGallierValid
    (P : FiniteCyclicPresentation) (a : P.Edge) (h : P.IsGallierValid) :
    (expand P a).IsGallierValid := by
  rcases h with hregular | hempty
  · exact Or.inl
      ⟨expand_isSurfaceValid P a hregular.1,
        expand_isConnected P a hregular.2⟩
  · exact Fin.elim0 (Fin.cast hempty.edgeCount_eq_zero a)

end P1

/-- A Gallier--Xu P1 subdivision, closed under signed relabeling and cyclic face rotation.

This is a syntactic move relation and deliberately does not bundle source validity. The
preservation theorems below transport validity and connectivity when those hypotheses are
available. -/
def P1Subdivision (P Q : FiniteCyclicPresentation) : Prop :=
  ∃ a : P.Edge, Nonempty (SignedPresentationIso (P1.expand P a) Q)

namespace P1Subdivision

/-- The canonical expansion is a P1 subdivision.
@isnad1 id=p1subdiv.0h2v.s3.163b5a1dd7e5 from=translated src=- shape=20553ef8 vocab=c1b8d0e6
-/
theorem canonical (P : FiniteCyclicPresentation) (a : P.Edge) :
    P1Subdivision P (P1.expand P a) :=
  ⟨a, ⟨SignedPresentationIso.refl _⟩⟩

/-- P1 subdivisions preserve ordinary incidence validity.
@isnad1 id=issurfac.2h2v.s3.506b36cbbb27 from=translated src=- shape=a72c41e2 vocab=80dafbcf
-/
theorem isSurfaceValid {P Q : FiniteCyclicPresentation}
    (hPQ : P1Subdivision P Q) (h : P.IsSurfaceValid) :
    Q.IsSurfaceValid := by
  rcases hPQ with ⟨a, ⟨e⟩⟩
  exact e.isSurfaceValid (P1.expand_isSurfaceValid P a h)

/-- P1 subdivisions preserve face-incidence connectivity.
@isnad1 id=isconnec.2h2v.s3.8a1fd23f8bc8 from=translated src=- shape=a72c41e2 vocab=0504a747
-/
theorem isConnected {P Q : FiniteCyclicPresentation}
    (hPQ : P1Subdivision P Q) (h : P.IsConnected) :
    Q.IsConnected := by
  rcases hPQ with ⟨a, ⟨e⟩⟩
  exact e.isConnected (P1.expand_isConnected P a h)

/-- P1 subdivisions preserve Gallier validity.
@isnad1 id=isgallie.2h2v.s3.11fe89280230 from=translated src=- shape=a72c41e2 vocab=a64cd599
-/
theorem isGallierValid {P Q : FiniteCyclicPresentation}
    (hPQ : P1Subdivision P Q) (h : P.IsGallierValid) :
    Q.IsGallierValid := by
  rcases hPQ with ⟨a, ⟨e⟩⟩
  exact e.isGallierValid (P1.expand_isGallierValid P a h)

end P1Subdivision

end FiniteCyclicPresentation
end ClassificationOfSurfaces
end Topology
end LeanEval
