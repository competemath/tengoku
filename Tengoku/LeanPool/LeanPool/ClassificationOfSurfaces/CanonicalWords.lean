/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.CellComplexQuotient
public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.Representatives
public import Tengoku

/-!
# Canonical normal-form boundary words

This file gives finite signed-dart presentations for the orientable and nonorientable boundary
words encoded by the vendored `OrientableRel` and `NonOrientableRel`. It records their exact
lengths and edge multiplicities, then packages them as connected, incidence-valid one-face cell
complexes.

For Eval-admissible parameters, the words are nonempty and therefore also satisfy
`SurfaceCellComplex.OccurrencePairingValid`. These are combinatorial and polygonal-pairing
certificates. Their faithful polygonal realizations are compared with the closed-disc quotients
defined in `LeanEval/ChallengeDeps.lean` by the canonical realization layer.
-/

@[expose] public section

namespace LeanEval
namespace Topology
namespace ClassificationOfSurfaces

namespace SurfaceCellComplex

/-- Counting boundary positions by edge name agrees with counting the edge names in the word.
@isnad1 id=eq.0h3v.s5.6703e6864464 from=translated src=- shape=f76d9e70 vocab=d89e3bc1
-/
theorem wordEdgeOccurrences_card_eq_count_edgeName
    {Edge : Type} [DecidableEq Edge]
    (word : List (SignedDart Edge)) (e : Edge) :
    (wordEdgeOccurrences word e).card =
      (word.map SignedDart.edgeName).count e := by
  let v : List.Vector Edge word.length :=
    List.Vector.ofFn fun i ↦ SignedDart.edgeName (word.get i)
  simpa [wordEdgeOccurrences, v, List.ofFn_comp'] using
    Fin.card_filter_univ_eq_vector_get_eq_count e v

end SurfaceCellComplex

namespace NormalForm

open SurfaceCellComplex

/-- Edge names in the canonical orientable normal-form word. -/
inductive OrientableEdge (p n : ℕ)
  | a : Fin p → OrientableEdge p n
  | b : Fin p → OrientableEdge p n
  | c : Fin n → OrientableEdge p n
  | h : Fin n → OrientableEdge p n
  deriving DecidableEq, Repr, Fintype

/-- Edge names in the canonical nonorientable normal-form word. -/
inductive NonOrientableEdge (p n : ℕ)
  | a : Fin p → NonOrientableEdge p n
  | c : Fin n → NonOrientableEdge p n
  | h : Fin n → NonOrientableEdge p n
  deriving DecidableEq, Repr, Fintype

/-- The commutator block `aᵢ bᵢ aᵢ⁻¹ bᵢ⁻¹`. -/
def orientableHandleBlock {p n : ℕ} (i : Fin p) :
    List (SignedDart (OrientableEdge p n)) :=
  [.pos (.a i), .pos (.b i), .neg (.a i), .neg (.b i)]

/-- The boundary block `cᵢ hᵢ cᵢ⁻¹` in the orientable word. -/
def orientableBoundaryBlock {p n : ℕ} (i : Fin n) :
    List (SignedDart (OrientableEdge p n)) :=
  [.pos (.c i), .pos (.h i), .neg (.c i)]

/-- The square block `aᵢ aᵢ` in the nonorientable word. -/
def nonOrientableCrosscapBlock {p n : ℕ} (i : Fin p) :
    List (SignedDart (NonOrientableEdge p n)) :=
  [.pos (.a i), .pos (.a i)]

/-- The boundary block `cᵢ hᵢ cᵢ⁻¹` in the nonorientable word. -/
def nonOrientableBoundaryBlock {p n : ℕ} (i : Fin n) :
    List (SignedDart (NonOrientableEdge p n)) :=
  [.pos (.c i), .pos (.h i), .neg (.c i)]

/-- The canonical orientable signed boundary word. -/
def orientableBoundaryWord (p n : ℕ) : List (SignedDart (OrientableEdge p n)) :=
  (List.ofFn (fun i : Fin p ↦ orientableHandleBlock (n := n) i)).flatten ++
    (List.ofFn (fun i : Fin n ↦ orientableBoundaryBlock (p := p) i)).flatten

/-- The canonical nonorientable signed boundary word. -/
def nonOrientableBoundaryWord (p n : ℕ) :
    List (SignedDart (NonOrientableEdge p n)) :=
  (List.ofFn (fun i : Fin p ↦ nonOrientableCrosscapBlock (n := n) i)).flatten ++
    (List.ofFn (fun i : Fin n ↦ nonOrientableBoundaryBlock (p := p) i)).flatten

/--
@isnad1 id=eq.0h2v.s5.a78897fa16ad from=translated src=- shape=0602b253 vocab=d63a19fc
-/
theorem orientableBoundaryWord_length (p n : ℕ) :
    (orientableBoundaryWord p n).length = 4 * p + 3 * n := by
  simp [orientableBoundaryWord, orientableHandleBlock, orientableBoundaryBlock, List.sum_ofFn,
    Nat.mul_comm]

/--
@isnad1 id=eq.0h2v.s5.bde301cad551 from=translated src=- shape=0602b253 vocab=6ac37c90
-/
theorem nonOrientableBoundaryWord_length (p n : ℕ) :
    (nonOrientableBoundaryWord p n).length = 2 * p + 3 * n := by
  simp [nonOrientableBoundaryWord, nonOrientableCrosscapBlock, nonOrientableBoundaryBlock,
    List.sum_ofFn, Nat.mul_comm]

/-! ## Certified positions in the canonical words -/

private theorem finProdFinEquiv_symm_linear {m n : ℕ} (i : Fin m) (j : Fin n)
    (h : i.val * n + j.val < m * n) :
    finProdFinEquiv.symm (⟨i.val * n + j.val, h⟩ : Fin (m * n)) = (i, j) := by
  apply finProdFinEquiv.injective
  rw [finProdFinEquiv.apply_symm_apply]
  apply Fin.ext
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

@[simp] private theorem Fin.divNat_linear {m n : ℕ} (i : Fin m) (j : Fin n)
    (h : i.val * n + j.val < m * n) :
    (⟨i.val * n + j.val, h⟩ : Fin (m * n)).divNat = i := by
  have hpair := congrArg Prod.fst (finProdFinEquiv_symm_linear i j h)
  simpa [finProdFinEquiv] using hpair

private def orientableHandleLinearDart {p n : ℕ} (q : Fin (p * 4)) :
    SignedDart (OrientableEdge p n) :=
  let ij := finProdFinEquiv.symm q
  (orientableHandleBlock (n := n) ij.1).get ij.2

private def orientableBoundaryLinearDart {p n : ℕ} (q : Fin (n * 3)) :
    SignedDart (OrientableEdge p n) :=
  let ij := finProdFinEquiv.symm q
  (orientableBoundaryBlock (p := p) ij.1).get ij.2

private theorem orientableHandleWords_eq_ofFn (p n : ℕ) :
    (List.ofFn (fun i : Fin p ↦ orientableHandleBlock (n := n) i)).flatten =
      List.ofFn (orientableHandleLinearDart (p := p) (n := n)) := by
  rw [List.ofFn_mul]
  congr 2 with i
  simp [orientableHandleLinearDart, orientableHandleBlock]

private theorem orientableBoundaryWords_eq_ofFn (p n : ℕ) :
    (List.ofFn (fun i : Fin n ↦ orientableBoundaryBlock (p := p) i)).flatten =
      List.ofFn (orientableBoundaryLinearDart (p := p) (n := n)) := by
  rw [List.ofFn_mul]
  congr 2 with i
  simp [orientableBoundaryLinearDart, orientableBoundaryBlock]

/-- Position `k` in handle block `i` inside the full orientable boundary word. -/
def orientableHandlePosition (p n : ℕ) (i : Fin p) (k : Fin 4) :
    Fin (orientableBoundaryWord p n).length :=
  ⟨i.val * 4 + k.val, by
    rw [orientableBoundaryWord_length]
    omega⟩

/-- Position `k` in boundary block `j` inside the full orientable boundary word. -/
def orientableBoundaryPosition (p n : ℕ) (j : Fin n) (k : Fin 3) :
    Fin (orientableBoundaryWord p n).length :=
  ⟨4 * p + j.val * 3 + k.val, by
    rw [orientableBoundaryWord_length]
    omega⟩

/--
@isnad1 id=eq.0h4v.s5.56ee44a93e20 from=translated src=- shape=c2f1c89f vocab=5dbaac4c
-/
theorem orientableHandlePosition_val (p n : ℕ) (i : Fin p) (k : Fin 4) :
    (orientableHandlePosition p n i k).val = i.val * 4 + k.val :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.69c2ff666bc4 from=translated src=- shape=1e9d374c vocab=a3339daf
-/
@[simp]
theorem orientableBoundaryPosition_val (p n : ℕ) (j : Fin n) (k : Fin 3) :
    (orientableBoundaryPosition p n j k).val = 4 * p + j.val * 3 + k.val :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.3233c1170b50 from=translated src=- shape=0d6574a2 vocab=85be83e6
-/
theorem orientableBoundaryWord_get_handle_block (p n : ℕ) (i : Fin p) (k : Fin 4) :
    (orientableBoundaryWord p n).get (orientableHandlePosition p n i k) =
      (orientableHandleBlock (n := n) i).get k := by
  rw [List.get_eq_getElem?]
  change (orientableBoundaryWord p n)[i.val * 4 + k.val]?.get _ =
    (orientableHandleBlock (n := n) i).get k
  have hopt :
      (orientableBoundaryWord p n)[i.val * 4 + k.val]? =
        some ((orientableHandleBlock (n := n) i).get k) := by
    simp only [orientableBoundaryWord, orientableHandleWords_eq_ofFn]
    rw [List.getElem?_append_left (by simp; omega)]
    rw [List.getElem?_ofFn, dite_eq_left (by omega)]
    simp [orientableHandleLinearDart, orientableHandleBlock, Nat.mod_eq_of_lt k.isLt]
  simp only [hopt]
  exact Option.get_some _ _

/--
@isnad1 id=eq.0h4v.s5.f90390e58200 from=translated src=- shape=b31bbb07 vocab=15e24027
-/
theorem orientableBoundaryWord_get_boundary_block (p n : ℕ) (j : Fin n) (k : Fin 3) :
    (orientableBoundaryWord p n).get (orientableBoundaryPosition p n j k) =
      (orientableBoundaryBlock (p := p) j).get k := by
  rw [List.get_eq_getElem?]
  change (orientableBoundaryWord p n)[4 * p + j.val * 3 + k.val]?.get _ =
    (orientableBoundaryBlock (p := p) j).get k
  have hopt :
      (orientableBoundaryWord p n)[4 * p + j.val * 3 + k.val]? =
        some ((orientableBoundaryBlock (p := p) j).get k) := by
    simp only [orientableBoundaryWord, orientableHandleWords_eq_ofFn,
      orientableBoundaryWords_eq_ofFn]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    have hidx : 4 * p + j.val * 3 + k.val - p * 4 = j.val * 3 + k.val := by
      omega
    rw [hidx, List.getElem?_ofFn, dite_eq_left (by omega)]
    simp [orientableBoundaryLinearDart, orientableBoundaryBlock, Nat.mod_eq_of_lt k.isLt]
  simp only [hopt]
  exact Option.get_some _ _

/--
@isnad1 id=eq.0h3v.s5.d6d8fdc4ce45 from=translated src=- shape=875eefed vocab=848bc917
-/
theorem orientableBoundaryWord_get_handle_a_pos (p n : ℕ) (i : Fin p) :
    (orientableBoundaryWord p n).get (orientableHandlePosition p n i 0) =
      .pos (.a i) := by
  simpa [orientableHandleBlock] using
    orientableBoundaryWord_get_handle_block p n i (0 : Fin 4)

/--
@isnad1 id=eq.0h3v.s5.d52713c9a5c2 from=translated src=- shape=875eefed vocab=e8d10c3a
-/
theorem orientableBoundaryWord_get_handle_b_pos (p n : ℕ) (i : Fin p) :
    (orientableBoundaryWord p n).get (orientableHandlePosition p n i 1) =
      .pos (.b i) := by
  simpa [orientableHandleBlock] using
    orientableBoundaryWord_get_handle_block p n i (1 : Fin 4)

/--
@isnad1 id=eq.0h3v.s5.aa210508a276 from=translated src=- shape=875eefed vocab=4a260994
-/
theorem orientableBoundaryWord_get_handle_a_neg (p n : ℕ) (i : Fin p) :
    (orientableBoundaryWord p n).get (orientableHandlePosition p n i 2) =
      .neg (.a i) := by
  simpa [orientableHandleBlock] using
    orientableBoundaryWord_get_handle_block p n i (2 : Fin 4)

/--
@isnad1 id=eq.0h3v.s5.8fa6a3769c26 from=translated src=- shape=875eefed vocab=2323cf4a
-/
theorem orientableBoundaryWord_get_handle_b_neg (p n : ℕ) (i : Fin p) :
    (orientableBoundaryWord p n).get (orientableHandlePosition p n i 3) =
      .neg (.b i) := by
  simpa [orientableHandleBlock] using
    orientableBoundaryWord_get_handle_block p n i (3 : Fin 4)

/--
@isnad1 id=eq.0h3v.s5.d3cd9b4867a4 from=translated src=- shape=dda625ee vocab=d26a4644
-/
theorem orientableBoundaryWord_get_boundary_c_pos (p n : ℕ) (j : Fin n) :
    (orientableBoundaryWord p n).get (orientableBoundaryPosition p n j 0) =
      .pos (.c j) := by
  simpa [orientableBoundaryBlock] using
    orientableBoundaryWord_get_boundary_block p n j (0 : Fin 3)

/--
@isnad1 id=eq.0h3v.s5.16e9fc8df5b5 from=translated src=- shape=dda625ee vocab=12c86738
-/
theorem orientableBoundaryWord_get_boundary_h_pos (p n : ℕ) (j : Fin n) :
    (orientableBoundaryWord p n).get (orientableBoundaryPosition p n j 1) =
      .pos (.h j) := by
  simpa [orientableBoundaryBlock] using
    orientableBoundaryWord_get_boundary_block p n j (1 : Fin 3)

/--
@isnad1 id=eq.0h3v.s5.e4ab73f877a0 from=translated src=- shape=dda625ee vocab=ba3738c0
-/
theorem orientableBoundaryWord_get_boundary_c_neg (p n : ℕ) (j : Fin n) :
    (orientableBoundaryWord p n).get (orientableBoundaryPosition p n j 2) =
      .neg (.c j) := by
  simpa [orientableBoundaryBlock] using
    orientableBoundaryWord_get_boundary_block p n j (2 : Fin 3)

private def nonOrientableCrosscapLinearDart {p n : ℕ} (q : Fin (p * 2)) :
    SignedDart (NonOrientableEdge p n) :=
  let ij := finProdFinEquiv.symm q
  (nonOrientableCrosscapBlock (n := n) ij.1).get ij.2

private def nonOrientableBoundaryLinearDart {p n : ℕ} (q : Fin (n * 3)) :
    SignedDart (NonOrientableEdge p n) :=
  let ij := finProdFinEquiv.symm q
  (nonOrientableBoundaryBlock (p := p) ij.1).get ij.2

private theorem nonOrientableCrosscapWords_eq_ofFn (p n : ℕ) :
    (List.ofFn (fun i : Fin p ↦ nonOrientableCrosscapBlock (n := n) i)).flatten =
      List.ofFn (nonOrientableCrosscapLinearDart (p := p) (n := n)) := by
  rw [List.ofFn_mul]
  congr 2 with i
  simp [nonOrientableCrosscapLinearDart, nonOrientableCrosscapBlock]

private theorem nonOrientableBoundaryWords_eq_ofFn (p n : ℕ) :
    (List.ofFn (fun i : Fin n ↦ nonOrientableBoundaryBlock (p := p) i)).flatten =
      List.ofFn (nonOrientableBoundaryLinearDart (p := p) (n := n)) := by
  rw [List.ofFn_mul]
  congr 2 with i
  simp [nonOrientableBoundaryLinearDart, nonOrientableBoundaryBlock]

/-- Position `k` in crosscap block `i` inside the full nonorientable boundary word. -/
def nonOrientableCrosscapPosition (p n : ℕ) (i : Fin p) (k : Fin 2) :
    Fin (nonOrientableBoundaryWord p n).length :=
  ⟨i.val * 2 + k.val, by
    rw [nonOrientableBoundaryWord_length]
    omega⟩

/-- Position `k` in boundary block `j` inside the full nonorientable boundary word. -/
def nonOrientableBoundaryPosition (p n : ℕ) (j : Fin n) (k : Fin 3) :
    Fin (nonOrientableBoundaryWord p n).length :=
  ⟨2 * p + j.val * 3 + k.val, by
    rw [nonOrientableBoundaryWord_length]
    omega⟩

/--
@isnad1 id=eq.0h4v.s5.c5c248000b65 from=translated src=- shape=c2f1c89f vocab=10aa578a
-/
@[simp]
theorem nonOrientableCrosscapPosition_val (p n : ℕ) (i : Fin p) (k : Fin 2) :
    (nonOrientableCrosscapPosition p n i k).val = i.val * 2 + k.val :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.51e7df5bbc24 from=translated src=- shape=1e9d374c vocab=3aca7b96
-/
@[simp]
theorem nonOrientableBoundaryPosition_val (p n : ℕ) (j : Fin n) (k : Fin 3) :
    (nonOrientableBoundaryPosition p n j k).val = 2 * p + j.val * 3 + k.val :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.95a618700820 from=translated src=- shape=0d6574a2 vocab=b89f3258
-/
theorem nonOrientableBoundaryWord_get_crosscap_block
    (p n : ℕ) (i : Fin p) (k : Fin 2) :
    (nonOrientableBoundaryWord p n).get (nonOrientableCrosscapPosition p n i k) =
      (nonOrientableCrosscapBlock (n := n) i).get k := by
  rw [List.get_eq_getElem?]
  change (nonOrientableBoundaryWord p n)[i.val * 2 + k.val]?.get _ =
    (nonOrientableCrosscapBlock (n := n) i).get k
  have hopt :
      (nonOrientableBoundaryWord p n)[i.val * 2 + k.val]? =
        some ((nonOrientableCrosscapBlock (n := n) i).get k) := by
    simp only [nonOrientableBoundaryWord, nonOrientableCrosscapWords_eq_ofFn]
    rw [List.getElem?_append_left (by simp; omega)]
    rw [List.getElem?_ofFn, dite_eq_left (by omega)]
    simp [nonOrientableCrosscapLinearDart, nonOrientableCrosscapBlock,
      Nat.mod_eq_of_lt k.isLt]
  simp only [hopt]
  exact Option.get_some _ _

/--
@isnad1 id=eq.0h4v.s5.e58f1da72a64 from=translated src=- shape=b31bbb07 vocab=31071bbc
-/
theorem nonOrientableBoundaryWord_get_boundary_block
    (p n : ℕ) (j : Fin n) (k : Fin 3) :
    (nonOrientableBoundaryWord p n).get (nonOrientableBoundaryPosition p n j k) =
      (nonOrientableBoundaryBlock (p := p) j).get k := by
  rw [List.get_eq_getElem?]
  change (nonOrientableBoundaryWord p n)[2 * p + j.val * 3 + k.val]?.get _ =
    (nonOrientableBoundaryBlock (p := p) j).get k
  have hopt :
      (nonOrientableBoundaryWord p n)[2 * p + j.val * 3 + k.val]? =
        some ((nonOrientableBoundaryBlock (p := p) j).get k) := by
    simp only [nonOrientableBoundaryWord, nonOrientableCrosscapWords_eq_ofFn,
      nonOrientableBoundaryWords_eq_ofFn]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn]
    have hidx : 2 * p + j.val * 3 + k.val - p * 2 = j.val * 3 + k.val := by
      omega
    rw [hidx, List.getElem?_ofFn, dite_eq_left (by omega)]
    simp [nonOrientableBoundaryLinearDart, nonOrientableBoundaryBlock,
      Nat.mod_eq_of_lt k.isLt]
  simp only [hopt]
  exact Option.get_some _ _

/--
@isnad1 id=eq.0h3v.s5.a0bd2bf57949 from=translated src=- shape=875eefed vocab=54e7f81e
-/
theorem nonOrientableBoundaryWord_get_crosscap_a_first (p n : ℕ) (i : Fin p) :
    (nonOrientableBoundaryWord p n).get (nonOrientableCrosscapPosition p n i 0) =
      .pos (.a i) := by
  simpa [nonOrientableCrosscapBlock] using
    nonOrientableBoundaryWord_get_crosscap_block p n i (0 : Fin 2)

/--
@isnad1 id=eq.0h3v.s5.21af330af1e3 from=translated src=- shape=875eefed vocab=54e7f81e
-/
theorem nonOrientableBoundaryWord_get_crosscap_a_second (p n : ℕ) (i : Fin p) :
    (nonOrientableBoundaryWord p n).get (nonOrientableCrosscapPosition p n i 1) =
      .pos (.a i) := by
  simpa [nonOrientableCrosscapBlock] using
    nonOrientableBoundaryWord_get_crosscap_block p n i (1 : Fin 2)

/--
@isnad1 id=eq.0h3v.s5.b2af705f9691 from=translated src=- shape=dda625ee vocab=fa756bdb
-/
theorem nonOrientableBoundaryWord_get_boundary_c_pos (p n : ℕ) (j : Fin n) :
    (nonOrientableBoundaryWord p n).get (nonOrientableBoundaryPosition p n j 0) =
      .pos (.c j) := by
  simpa [nonOrientableBoundaryBlock] using
    nonOrientableBoundaryWord_get_boundary_block p n j (0 : Fin 3)

/--
@isnad1 id=eq.0h3v.s5.7202b808a008 from=translated src=- shape=dda625ee vocab=9425e7d6
-/
theorem nonOrientableBoundaryWord_get_boundary_h_pos (p n : ℕ) (j : Fin n) :
    (nonOrientableBoundaryWord p n).get (nonOrientableBoundaryPosition p n j 1) =
      .pos (.h j) := by
  simpa [nonOrientableBoundaryBlock] using
    nonOrientableBoundaryWord_get_boundary_block p n j (1 : Fin 3)

/--
@isnad1 id=eq.0h3v.s5.bd68937f332d from=translated src=- shape=dda625ee vocab=c5354387
-/
theorem nonOrientableBoundaryWord_get_boundary_c_neg (p n : ℕ) (j : Fin n) :
    (nonOrientableBoundaryWord p n).get (nonOrientableBoundaryPosition p n j 2) =
      .neg (.c j) := by
  simpa [nonOrientableBoundaryBlock] using
    nonOrientableBoundaryWord_get_boundary_block p n j (2 : Fin 3)

/--
@isnad1 id=eq.0h3v.s6.57553e1bf6f4 from=translated src=- shape=d231ab55 vocab=eb4fc873
-/
theorem orientableBoundaryWord_edge_occurrences (p n : ℕ) (e : OrientableEdge p n) :
    (wordEdgeOccurrences (orientableBoundaryWord p n) e).card =
      match e with
      | .a _ => 2
      | .b _ => 2
      | .c _ => 2
      | .h _ => 1 := by
  rw [wordEdgeOccurrences_card_eq_count_edgeName]
  cases e <;>
    simp [orientableBoundaryWord, orientableHandleBlock, orientableBoundaryBlock,
      SignedDart.edgeName, List.count_flatten, List.sum_ofFn, List.count_cons,
      List.count_nil, beq_iff_eq, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h3v.s6.93ed27f896ef from=translated src=- shape=a2c7f948 vocab=e635fbb3
-/
theorem nonOrientableBoundaryWord_edge_occurrences (p n : ℕ)
    (e : NonOrientableEdge p n) :
    (wordEdgeOccurrences (nonOrientableBoundaryWord p n) e).card =
      match e with
      | .a _ => 2
      | .c _ => 2
      | .h _ => 1 := by
  rw [wordEdgeOccurrences_card_eq_count_edgeName]
  cases e <;>
    simp [nonOrientableBoundaryWord, nonOrientableCrosscapBlock,
      nonOrientableBoundaryBlock, SignedDart.edgeName, List.count_flatten, List.sum_ofFn,
      List.count_cons, List.count_nil, beq_iff_eq, Finset.sum_add_distrib]

/-- The one-face incidence presentation carried by the canonical orientable word. -/
abbrev orientableCellComplex (p n : ℕ) : SurfaceCellComplex :=
  oneFacePresentation (OrientableEdge p n) (orientableBoundaryWord p n)

/-- The one-face incidence presentation carried by the canonical nonorientable word. -/
abbrev nonOrientableCellComplex (p n : ℕ) : SurfaceCellComplex :=
  oneFacePresentation (NonOrientableEdge p n) (nonOrientableBoundaryWord p n)

/--
@isnad1 id=eq.0h2v.s4.f65fc1060deb from=translated src=- shape=84fe26bf vocab=cb98d920
-/
@[simp]
theorem orientableCellComplex_boundary (p n : ℕ) :
    (orientableCellComplex p n).boundary PUnit.unit = orientableBoundaryWord p n := rfl

/--
@isnad1 id=eq.0h2v.s4.e31e1e2b03bf from=translated src=- shape=84fe26bf vocab=f0c503e0
-/
@[simp]
theorem nonOrientableCellComplex_boundary (p n : ℕ) :
    (nonOrientableCellComplex p n).boundary PUnit.unit =
      nonOrientableBoundaryWord p n := rfl

/--
@isnad1 id=eq.0h2v.s5.bb53a083b017 from=translated src=- shape=a5398645 vocab=9bf78f91
-/
@[simp]
theorem orientableCellComplex_faceBoundaryLength (p n : ℕ) :
    (orientableCellComplex p n).faceBoundaryLength PUnit.unit = 4 * p + 3 * n :=
  orientableBoundaryWord_length p n

/--
@isnad1 id=eq.0h2v.s5.99b495de12b1 from=translated src=- shape=a5398645 vocab=7b7ef7ce
-/
@[simp]
theorem nonOrientableCellComplex_faceBoundaryLength (p n : ℕ) :
    (nonOrientableCellComplex p n).faceBoundaryLength PUnit.unit = 2 * p + 3 * n :=
  nonOrientableBoundaryWord_length p n

/--
@isnad1 id=isconnec.0h2v.s3.27d6d98af674 from=translated src=- shape=b794339c vocab=6067dc60
-/
theorem orientableCellComplex_isConnected (p n : ℕ) :
    (orientableCellComplex p n).IsConnected :=
  oneFacePresentation_isConnected _ _

/--
@isnad1 id=isconnec.0h2v.s3.e782447a9ea1 from=translated src=- shape=b794339c vocab=98fcdfdd
-/
theorem nonOrientableCellComplex_isConnected (p n : ℕ) :
    (nonOrientableCellComplex p n).IsConnected :=
  oneFacePresentation_isConnected _ _

/--
@isnad1 id=issurfac.0h2v.s3.ab6b078df552 from=translated src=- shape=b794339c vocab=0e83a481
-/
theorem orientableCellComplex_isSurfaceValid (p n : ℕ) :
    (orientableCellComplex p n).IsSurfaceValid := by
  apply oneFacePresentation_isSurfaceValid
  intro e
  rw [orientableBoundaryWord_edge_occurrences]
  cases e <;> simp

/--
@isnad1 id=issurfac.0h2v.s3.f76e1d51dd29 from=translated src=- shape=b794339c vocab=257cdad7
-/
theorem nonOrientableCellComplex_isSurfaceValid (p n : ℕ) :
    (nonOrientableCellComplex p n).IsSurfaceValid := by
  apply oneFacePresentation_isSurfaceValid
  intro e
  rw [nonOrientableBoundaryWord_edge_occurrences]
  cases e <;> simp

/--
@isnad1 id=ne.1h2v.s5.953e90d6b7ca from=translated src=- shape=096044c8 vocab=4add2947
-/
theorem orientableBoundaryWord_ne_nil {p n : ℕ} (h : 1 ≤ p ∨ 1 ≤ n) :
    orientableBoundaryWord p n ≠ [] := by
  intro hnil
  have hlength := orientableBoundaryWord_length p n
  rw [hnil] at hlength
  simp only [List.length_nil] at hlength
  omega

/--
@isnad1 id=ne.1h2v.s4.c0e270f988ab from=translated src=- shape=631384e5 vocab=b5c326ba
-/
theorem nonOrientableBoundaryWord_ne_nil {p n : ℕ} (h : 1 ≤ p) :
    nonOrientableBoundaryWord p n ≠ [] := by
  intro hnil
  have hlength := nonOrientableBoundaryWord_length p n
  rw [hnil] at hlength
  simp only [List.length_nil] at hlength
  omega

/--
@isnad1 id=occurren.1h2v.s4.a2ead1aca91c from=translated src=- shape=46fa10a7 vocab=c6bbb272
-/
theorem orientableCellComplex_occurrencePairingValid {p n : ℕ}
    (h : 1 ≤ p ∨ 1 ≤ n) :
    (orientableCellComplex p n).OccurrencePairingValid := by
  apply oneFacePresentation_occurrencePairingValid
  · exact orientableBoundaryWord_ne_nil h
  · intro e
    rw [orientableBoundaryWord_edge_occurrences]
    cases e <;> simp

/--
@isnad1 id=occurren.1h2v.s4.cdfb300d9cbe from=translated src=- shape=5555e3ac vocab=53753bbb
-/
theorem nonOrientableCellComplex_occurrencePairingValid {p n : ℕ}
    (h : 1 ≤ p) :
    (nonOrientableCellComplex p n).OccurrencePairingValid := by
  apply oneFacePresentation_occurrencePairingValid
  · exact nonOrientableBoundaryWord_ne_nil h
  · intro e
    rw [nonOrientableBoundaryWord_edge_occurrences]
    cases e <;> simp

/-- The canonical incidence presentation attached to a named normal form. -/
def canonicalCellComplex : NormalForm → SurfaceCellComplex
  | .sphere => SurfaceCellComplex.sphere
  | .orientable p n => orientableCellComplex p n
  | .nonOrientable p n => nonOrientableCellComplex p n

/--
@isnad1 id=issurfac.0h1v.s2.174590575588 from=translated src=- shape=76a08d12 vocab=13d4b664
-/
theorem canonicalCellComplex_isSurfaceValid (N : NormalForm) :
    N.canonicalCellComplex.IsSurfaceValid := by
  cases N with
  | sphere => exact SurfaceCellComplex.sphere_isSurfaceValid
  | orientable p n => exact orientableCellComplex_isSurfaceValid p n
  | nonOrientable p n => exact nonOrientableCellComplex_isSurfaceValid p n

/--
@isnad1 id=isconnec.0h1v.s2.9b7bba7987bc from=translated src=- shape=76a08d12 vocab=4002fff2
-/
theorem canonicalCellComplex_isConnected (N : NormalForm) :
    N.canonicalCellComplex.IsConnected := by
  cases N with
  | sphere => exact SurfaceCellComplex.sphere_isConnected
  | orientable p n => exact orientableCellComplex_isConnected p n
  | nonOrientable p n => exact nonOrientableCellComplex_isConnected p n

end NormalForm

end ClassificationOfSurfaces
end Topology
end LeanEval
