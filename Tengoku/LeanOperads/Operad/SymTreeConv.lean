/-
# Symmetric cochains on binary trees: the symmetric convolution algebra

Let `E` be a set of binary generators with an involution `tw` (the action of the transposition of
the two inputs; a symmetric generator is a fixed point), and let `P` be a symmetric operad. The
cochains on the cofree cooperad on `E` with values in `P` that are equivariant for the symmetric
groups — the symmetric convolution algebra `Hom_𝔖(𝒯ᶜ(E), P)` — are determined by their values on
planar representatives of trees: every leaf-labelled tree is a planar binary tree, relabelled.
Two planar representatives of the same tree differ by swaps of the two subtrees at vertices,
twisting the vertex's generator by `tw`; so a cochain on planar trees with values in the
underlying non-symmetric operad of `P` is **symmetric** (`TConv.IsSymm`) when its value at a tree
swapped at a vertex is its value at the tree, relabelled along the induced permutation of the
leaves and multiplied by the sign of the swap, `-(-1)^(a b)` for subtrees with `a` and `b` leaves.
The sign is the one the operadic suspension of the library's signed product `⋆ₛ` dictates; in
weight one it is `+1`, so symmetric cochains of weight one are the equivariant generator data
(`TConv.isSymm_two_iff`).

**Symmetric cochains are closed under the convolution product** (`TConv.isSymm_sstar`), hence
under the graded bracket (`TConv.isSymm_gbracket`): they form a graded sub-pre-Lie algebra of the
planar convolution algebra of `Operad.TreeConv`, so the graded pre-Lie identity
(`sstar_assoc_symm`) and the graded Jacobi identity (`jacobiS`) hold on them. The proof writes the
product at a tree as a sum over the paths to its vertices and leaves (`TConv.sstar_apply_paths`),
and shows that a swap at a vertex `q` moves each term to the term at the moved path: a swap inside
the subtree at the path is a swap of the inserted cochain's tree (`BTree.swapAt_cut_of_prefix`),
and a swap elsewhere is a swap of the outer cochain's tree, which moves the inserted block of
leaves with the cut-off leaf (`BTree.swapAt_cut_of_not_prefix`, `BTree.swapPos_cut_of_not_prefix`)
and changes the sign exactly as the shifted slot does (`BTree.splitAt_cut_of_not_prefix`). On the
operad side, a relabelling of either factor of a positional composite is a relabelling of the
composite (`SymOperad.map_comp_map_left`, `SymOperad.map_comp_map_right`).

Two general facts complete the picture, for any non-symmetric operad:

* **the twisting identity** `⁅T, ⁅T, x⁆⁆ = ⁅T ⋆ₛ T, x⁆` for `T` of degree one, over any
  commutative ring (`gbracket_gbracket_eq`, from `brT_brT_eq` in the total space), so that
  `d_T² = 0` exactly when `T ⋆ₛ T` is central;
* **coefficients in an ideal**: a signed product or bracket with an element of an operad ideal,
  on either side, lies in the ideal (`OperadIdeal.sstar_mem_left`, `…_right`,
  `OperadIdeal.gbracket_mem_left`, `…_right`); an ideal of a symmetric operad, such as the kernel
  of `Σ : Perm → Com`, restricts to one of the underlying non-symmetric operad
  (`SymOperadIdeal.toNS`), and cochains with values in it form an ideal (`TConv.valuedIn`).
-/
import Tengoku.LeanOperads.Operad.LowWeight
import Tengoku.LeanOperads.Operad.SymNS
import Tengoku.LeanOperads.Operad.Cohomology
import Tengoku.LeanOperads.Operad.SymIdeal
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v w

namespace Operad

namespace BTree

variable {E : Type v}

/-! ## Paths

A path is a list of directions from the root, `false` for the left child and `true` for the
right one. A valid path ends at a vertex or at a leaf; the subtree there is `subAt`, the tree
with that subtree cut down to a leaf is `cutAt`, and the number of leaves to its left is
`posAt`. The tree is recovered by grafting (`graft_cutAt_subAt`). -/

/-- The subtree at the end of a path.-/
def subAt : BTree E → List Bool → BTree E
  | t, [] => t
  | leaf, _ :: _ => leaf
  | node _ l _, false :: p => l.subAt p
  | node _ _ r, true :: p => r.subAt p

/-- The tree with the subtree at the end of a path replaced by a leaf.-/
def cutAt : BTree E → List Bool → BTree E
  | _, [] => leaf
  | leaf, _ :: _ => leaf
  | node e l r, false :: p => node e (l.cutAt p) r
  | node e l r, true :: p => node e l (r.cutAt p)

/-- The number of leaves to the left of the subtree at the end of a path.-/
def posAt : BTree E → List Bool → ℕ
  | _, [] => 0
  | leaf, _ :: _ => 0
  | node _ l _, false :: p => l.posAt p
  | node _ l r, true :: p => l.arity + r.posAt p

/-- **The valid paths** of a tree: to its vertices and to its leaves.-/
def paths : BTree E → Finset (List Bool)
  | leaf => {[]}
  | node _ l r =>
    insert [] (l.paths.map ⟨List.cons false, List.cons_injective⟩ ∪
      r.paths.map ⟨List.cons true, List.cons_injective⟩)

@[simp] lemma subAt_nil (t : BTree E) : t.subAt [] = t := by cases t <;> rfl
@[simp] lemma cutAt_nil (t : BTree E) : t.cutAt [] = leaf := by cases t <;> rfl
@[simp] lemma posAt_nil (t : BTree E) : t.posAt [] = 0 := by cases t <;> rfl

@[simp] lemma subAt_false (e : E) (l r : BTree E) (p : List Bool) :
    (node e l r).subAt (false :: p) = l.subAt p := rfl
@[simp] lemma subAt_true (e : E) (l r : BTree E) (p : List Bool) :
    (node e l r).subAt (true :: p) = r.subAt p := rfl
@[simp] lemma cutAt_false (e : E) (l r : BTree E) (p : List Bool) :
    (node e l r).cutAt (false :: p) = node e (l.cutAt p) r := rfl
@[simp] lemma cutAt_true (e : E) (l r : BTree E) (p : List Bool) :
    (node e l r).cutAt (true :: p) = node e l (r.cutAt p) := rfl
@[simp] lemma posAt_false (e : E) (l r : BTree E) (p : List Bool) :
    (node e l r).posAt (false :: p) = l.posAt p := rfl
@[simp] lemma posAt_true (e : E) (l r : BTree E) (p : List Bool) :
    (node e l r).posAt (true :: p) = l.arity + r.posAt p := rfl

@[simp] lemma mem_paths_leaf (p : List Bool) : p ∈ (leaf : BTree E).paths ↔ p = [] := by
  simp [paths]

@[simp] lemma nil_mem_paths (t : BTree E) : [] ∈ t.paths := by
  cases t <;> simp [paths]

@[simp] lemma cons_false_mem_paths (e : E) (l r : BTree E) (p : List Bool) :
    false :: p ∈ (node e l r).paths ↔ p ∈ l.paths := by
  simp [paths]

@[simp] lemma cons_true_mem_paths (e : E) (l r : BTree E) (p : List Bool) :
    true :: p ∈ (node e l r).paths ↔ p ∈ r.paths := by
  simp [paths]

lemma cons_not_mem_paths_leaf (b : Bool) (p : List Bool) : b :: p ∉ (leaf : BTree E).paths := by
  simp

/-- **A tree is the graft of its cut at a path and the subtree there.**-/
theorem graft_cutAt_subAt : ∀ (t : BTree E) (p : List Bool), p ∈ t.paths →
    (t.cutAt p).graft (t.posAt p) (t.subAt p) = t
  | leaf, [], _ => rfl
  | node e l r, [], _ => rfl
  | leaf, _ :: _, h => absurd h (cons_not_mem_paths_leaf _ _)
  | node e l r, false :: p, h => by
    rw [cons_false_mem_paths] at h
    have hlt := posAt_lt_arity_cutAt l p h
    simp only [cutAt_false, posAt_false, subAt_false]
    rw [graft_node_of_lt r _ hlt, graft_cutAt_subAt l p h]
  | node e l r, true :: p, h => by
    rw [cons_true_mem_paths] at h
    simp only [cutAt_true, posAt_true, subAt_true]
    rw [graft_node_of_ge l _ (by omega), show l.arity + r.posAt p - l.arity = r.posAt p by omega,
      graft_cutAt_subAt r p h]
where
  /-- The cut-off leaf is a leaf of the cut tree.-/
  posAt_lt_arity_cutAt : ∀ (t : BTree E) (p : List Bool), p ∈ t.paths →
      t.posAt p < (t.cutAt p).arity
    | leaf, [], _ => by simp
    | node e l r, [], _ => by simp
    | leaf, _ :: _, h => absurd h (cons_not_mem_paths_leaf _ _)
    | node e l r, false :: p, h => by
      rw [cons_false_mem_paths] at h
      have := posAt_lt_arity_cutAt l p h
      simp only [cutAt_false, posAt_false, arity_node]
      omega
    | node e l r, true :: p, h => by
      rw [cons_true_mem_paths] at h
      have := posAt_lt_arity_cutAt r p h
      simp only [cutAt_true, posAt_true, arity_node]
      omega

/-- The cut-off leaf is a leaf of the cut tree.-/
lemma posAt_lt (t : BTree E) {p : List Bool} (h : p ∈ t.paths) :
    t.posAt p < (t.cutAt p).arity :=
  graft_cutAt_subAt.posAt_lt_arity_cutAt t p h

/-- Cutting at a path and keeping the subtree split the leaves.-/
lemma arity_cutAt (t : BTree E) {p : List Bool} (h : p ∈ t.paths) :
    (t.cutAt p).arity + (t.subAt p).arity = t.arity + 1 := by
  have := arity_graft (t.cutAt p) (t.posAt p) (t.subAt p) (t.posAt_lt h)
  rw [graft_cutAt_subAt t p h] at this
  omega

/-- The path to the leaf in position `a`.-/
def leafPath : BTree E → ℕ → List Bool
  | leaf, _ => []
  | node _ l r, a => if a < l.arity then false :: l.leafPath a else true :: r.leafPath (a - l.arity)

/-- **Every graft is a cut at a path**: grafting `s` at the leaf `a` of `t` puts `s` at the end of
the path to that leaf, cuts back to `t`, and leaves `a` leaves to its left.-/
theorem leafPath_graft : ∀ (t : BTree E) (a : ℕ) (s : BTree E), a < t.arity →
    t.leafPath a ∈ (t.graft a s).paths ∧ (t.graft a s).subAt (t.leafPath a) = s ∧
      (t.graft a s).cutAt (t.leafPath a) = t ∧ (t.graft a s).posAt (t.leafPath a) = a
  | leaf, a, s, h => by
    obtain rfl : a = 0 := by simp only [arity_leaf] at h; omega
    simp [leafPath]
  | node e l r, a, s, h => by
    simp only [arity_node] at h
    by_cases ha : a < l.arity
    · obtain ⟨h1, h2, h3, h4⟩ := leafPath_graft l a s ha
      simp only [leafPath, ite_eq_left ha, graft_node_of_lt r s ha, cons_false_mem_paths, subAt_false,
        cutAt_false, posAt_false]
      exact ⟨h1, h2, by rw [h3], h4⟩
    · obtain ⟨h1, h2, h3, h4⟩ := leafPath_graft r (a - l.arity) s (by omega)
      simp only [leafPath, ite_eq_right ha, graft_node_of_ge l s (by omega : l.arity ≤ a),
        cons_true_mem_paths, subAt_true, cutAt_true, posAt_true]
      exact ⟨h1, h2, by rw [h3], by omega⟩

/-- **Paths are told apart by their position and the size of their subtree.** Two subtrees with
the same leftmost leaf are nested, so they have different numbers of leaves.-/
theorem eq_of_posAt_eq : ∀ (t : BTree E) {p p' : List Bool}, p ∈ t.paths → p' ∈ t.paths →
    t.posAt p = t.posAt p' → (t.subAt p).arity = (t.subAt p').arity → p = p'
  | leaf, p, p', h, h', _, _ => by
    rw [mem_paths_leaf] at h h'
    rw [h, h']
  | node e l r, [], [], _, _, _, _ => rfl
  | node e l r, [], false :: p', _, h', _, ha => by
    rw [cons_false_mem_paths] at h'
    have := arity_cutAt l h'
    have := arity_pos (l.cutAt p')
    have := arity_pos r
    simp only [subAt_nil, arity_node, subAt_false] at ha
    omega
  | node e l r, [], true :: p', _, h', _, ha => by
    rw [cons_true_mem_paths] at h'
    have := arity_cutAt r h'
    have := arity_pos (r.cutAt p')
    have := arity_pos l
    simp only [subAt_nil, arity_node, subAt_true] at ha
    omega
  | node e l r, false :: p, [], h, _, _, ha => by
    rw [cons_false_mem_paths] at h
    have := arity_cutAt l h
    have := arity_pos (l.cutAt p)
    have := arity_pos r
    simp only [subAt_nil, arity_node, subAt_false] at ha
    omega
  | node e l r, true :: p, [], h, _, _, ha => by
    rw [cons_true_mem_paths] at h
    have := arity_cutAt r h
    have := arity_pos (r.cutAt p)
    have := arity_pos l
    simp only [subAt_nil, arity_node, subAt_true] at ha
    omega
  | node e l r, false :: p, false :: p', h, h', hp, ha => by
    rw [cons_false_mem_paths] at h h'
    rw [eq_of_posAt_eq l h h' hp ha]
  | node e l r, true :: p, true :: p', h, h', hp, ha => by
    rw [cons_true_mem_paths] at h h'
    simp only [posAt_true] at hp
    rw [eq_of_posAt_eq r h h' (by omega) ha]
  | node e l r, false :: p, true :: p', h, _, hp, _ => by
    rw [cons_false_mem_paths] at h
    have := posAt_lt l h
    have := arity_cutAt l h
    have := arity_pos (l.subAt p)
    simp only [posAt_false, posAt_true] at hp
    omega
  | node e l r, true :: p, false :: p', _, h', hp, _ => by
    rw [cons_false_mem_paths] at h'
    have := posAt_lt l h'
    have := arity_cutAt l h'
    have := arity_pos (l.subAt p')
    simp only [posAt_false, posAt_true] at hp
    omega

/-! ## Swaps

Swapping the two subtrees at a vertex, and twisting its label, is how the symmetric group acts on
planar representatives of symmetric trees. A swap at `q` moves the paths through the vertex `q` to
the other child (`swapPath`), sends the leaf in position `k` to position `swapPos t q k`, and
exchanges two blocks of leaves whose sizes are `splitAt t q`. -/

section Swap

variable (tw : E → E)

/-- **Swap the two subtrees at the vertex at the end of a path**, twisting its label by `tw`. The
identity if the path ends at a leaf.-/
def swapAt : BTree E → List Bool → BTree E
  | leaf, _ => leaf
  | node e l r, [] => node (tw e) r l
  | node e l r, false :: q => node e (l.swapAt q) r
  | node e l r, true :: q => node e l (r.swapAt q)

variable {tw}

@[simp] lemma swapAt_leaf (q : List Bool) : (leaf : BTree E).swapAt tw q = leaf := rfl
@[simp] lemma swapAt_nil (e : E) (l r : BTree E) :
    (node e l r).swapAt tw [] = node (tw e) r l := rfl
@[simp] lemma swapAt_false (e : E) (l r : BTree E) (q : List Bool) :
    (node e l r).swapAt tw (false :: q) = node e (l.swapAt tw q) r := rfl
@[simp] lemma swapAt_true (e : E) (l r : BTree E) (q : List Bool) :
    (node e l r).swapAt tw (true :: q) = node e l (r.swapAt tw q) := rfl

@[simp] theorem arity_swapAt : ∀ (t : BTree E) (q : List Bool), (t.swapAt tw q).arity = t.arity
  | leaf, _ => rfl
  | node e l r, [] => by simp [Nat.add_comm]
  | node e l r, false :: q => by simp [arity_swapAt l q]
  | node e l r, true :: q => by simp [arity_swapAt r q]

@[simp] theorem weight_swapAt : ∀ (t : BTree E) (q : List Bool), (t.swapAt tw q).weight = t.weight
  | leaf, _ => rfl
  | node e l r, [] => by simp only [swapAt_nil, weight_node]; omega
  | node e l r, false :: q => by simp [weight_swapAt l q]
  | node e l r, true :: q => by simp [weight_swapAt r q]

/-- **A swap is an involution** when the twist is.-/
theorem swapAt_swapAt (htw : Function.Involutive tw) :
    ∀ (t : BTree E) (q : List Bool), (t.swapAt tw q).swapAt tw q = t
  | leaf, _ => rfl
  | node e l r, [] => by simp [htw e]
  | node e l r, false :: q => by simp [swapAt_swapAt htw l q]
  | node e l r, true :: q => by simp [swapAt_swapAt htw r q]

/-- The effect of a swap at `q` on a path: a path through the vertex `q` takes the other direction
there.-/
def swapPath : List Bool → List Bool → List Bool
  | [], [] => []
  | [], b :: p => (!b) :: p
  | _ :: _, [] => []
  | c :: q, b :: p => if b = c then b :: swapPath q p else b :: p

@[simp] lemma swapPath_nil_nil : swapPath [] [] = [] := rfl
@[simp] lemma swapPath_nil_cons (b : Bool) (p : List Bool) : swapPath [] (b :: p) = (!b) :: p := rfl
@[simp] lemma swapPath_cons_nil (c : Bool) (q : List Bool) : swapPath (c :: q) [] = [] := rfl
lemma swapPath_cons_cons (c : Bool) (q : List Bool) (b : Bool) (p : List Bool) :
    swapPath (c :: q) (b :: p) = if b = c then b :: swapPath q p else b :: p := rfl

@[simp] lemma swapPath_cons_self (c : Bool) (q p : List Bool) :
    swapPath (c :: q) (c :: p) = c :: swapPath q p := by
  rw [swapPath_cons_cons, ite_eq_left rfl]

lemma swapPath_cons_ne {c b : Bool} (h : b ≠ c) (q p : List Bool) :
    swapPath (c :: q) (b :: p) = b :: p := by
  rw [swapPath_cons_cons, ite_eq_right h]

@[simp] lemma swapPath_true_false (q p : List Bool) :
    swapPath (true :: q) (false :: p) = false :: p := swapPath_cons_ne (by decide) q p

@[simp] lemma swapPath_false_true (q p : List Bool) :
    swapPath (false :: q) (true :: p) = true :: p := swapPath_cons_ne (by decide) q p

theorem swapPath_swapPath : ∀ (q p : List Bool), swapPath q (swapPath q p) = p
  | [], [] => rfl
  | [], b :: p => by simp
  | _ :: _, [] => rfl
  | c :: q, b :: p => by
    by_cases h : b = c
    · rw [swapPath_cons_cons, ite_eq_left h, swapPath_cons_cons, ite_eq_left h, swapPath_swapPath q p]
    · rw [swapPath_cons_cons, ite_eq_right h, swapPath_cons_cons, ite_eq_right h]

/-- A swap at a vertex below the end of a path does not move the path.-/
theorem swapPath_of_prefix : ∀ {q p : List Bool}, p <+: q → swapPath q p = p
  | [], [], _ => rfl
  | [], _ :: _, h => absurd (List.IsPrefix.length_le h) (by simp)
  | _ :: _, [], _ => rfl
  | c :: q, b :: p, h => by
    obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.1 h
    rw [swapPath_cons_cons, ite_eq_left rfl, swapPath_of_prefix h']

theorem mem_paths_swapAt : ∀ (t : BTree E) (q p : List Bool),
    p ∈ (t.swapAt tw q).paths ↔ swapPath q p ∈ t.paths
  | leaf, [], [] => by simp
  | leaf, [], b :: p => by simp
  | leaf, _ :: _, [] => by simp
  | leaf, c :: q, b :: p => by
    rw [swapPath_cons_cons]
    split_ifs <;> simp
  | node e l r, [], [] => by simp
  | node e l r, [], false :: p => by simp
  | node e l r, [], true :: p => by simp
  | node e l r, _ :: _, [] => by simp
  | node e l r, false :: q, false :: p => by
    simp only [swapAt_false, cons_false_mem_paths, swapPath_cons_self]
    exact mem_paths_swapAt l q p
  | node e l r, false :: q, true :: p => by simp
  | node e l r, true :: q, false :: p => by simp
  | node e l r, true :: q, true :: p => by
    simp only [swapAt_true, cons_true_mem_paths, swapPath_cons_self]
    exact mem_paths_swapAt r q p

/-- The new position of the leaf in position `k` after a swap at `q`.-/
def swapPos : BTree E → List Bool → ℕ → ℕ
  | leaf, _, k => k
  | node _ l r, [], k => if k < l.arity then k + r.arity else k - l.arity
  | node _ l _, false :: q, k => if k < l.arity then l.swapPos q k else k
  | node _ l r, true :: q, k => if k < l.arity then k else l.arity + r.swapPos q (k - l.arity)

/-- The old position of the leaf in position `k` after a swap at `q`.-/
def unswapPos : BTree E → List Bool → ℕ → ℕ
  | leaf, _, k => k
  | node _ l r, [], k => if k < r.arity then k + l.arity else k - r.arity
  | node _ l _, false :: q, k => if k < l.arity then l.unswapPos q k else k
  | node _ l r, true :: q, k => if k < l.arity then k else l.arity + r.unswapPos q (k - l.arity)

theorem swapPos_lt : ∀ (t : BTree E) (q : List Bool) {k : ℕ}, k < t.arity →
    t.swapPos q k < t.arity
  | leaf, _, _, h => h
  | node e l r, [], k, h => by
    simp only [arity_node] at h ⊢
    simp only [swapPos]
    split_ifs <;> omega
  | node e l r, false :: q, k, h => by
    simp only [arity_node] at h ⊢
    simp only [swapPos]
    split_ifs with hk
    · have := swapPos_lt l q hk
      omega
    · omega
  | node e l r, true :: q, k, h => by
    simp only [arity_node] at h ⊢
    simp only [swapPos]
    split_ifs with hk
    · omega
    · have := swapPos_lt r q (k := k - l.arity) (by omega)
      omega

theorem unswapPos_lt : ∀ (t : BTree E) (q : List Bool) {k : ℕ}, k < t.arity →
    t.unswapPos q k < t.arity
  | leaf, _, _, h => h
  | node e l r, [], k, h => by
    simp only [arity_node] at h ⊢
    simp only [unswapPos]
    split_ifs <;> omega
  | node e l r, false :: q, k, h => by
    simp only [arity_node] at h ⊢
    simp only [unswapPos]
    split_ifs with hk
    · have := unswapPos_lt l q hk
      omega
    · omega
  | node e l r, true :: q, k, h => by
    simp only [arity_node] at h ⊢
    simp only [unswapPos]
    split_ifs with hk
    · omega
    · have := unswapPos_lt r q (k := k - l.arity) (by omega)
      omega

theorem unswapPos_swapPos : ∀ (t : BTree E) (q : List Bool) {k : ℕ}, k < t.arity →
    t.unswapPos q (t.swapPos q k) = k
  | leaf, _, _, _ => rfl
  | node e l r, [], k, h => by
    simp only [arity_node] at h
    simp only [swapPos, unswapPos]
    split_ifs <;> omega
  | node e l r, false :: q, k, h => by
    simp only [arity_node] at h
    simp only [swapPos, unswapPos]
    split_ifs with hk hk'
    · exact unswapPos_swapPos l q hk
    · exact absurd (swapPos_lt l q hk) hk'
    · rfl
  | node e l r, true :: q, k, h => by
    simp only [arity_node] at h
    simp only [swapPos, unswapPos]
    split_ifs with hk hk'
    · rfl
    · omega
    · rw [show l.arity + r.swapPos q (k - l.arity) - l.arity = r.swapPos q (k - l.arity) by omega,
        unswapPos_swapPos r q (k := k - l.arity) (by omega)]
      omega

theorem swapPos_unswapPos : ∀ (t : BTree E) (q : List Bool) {k : ℕ}, k < t.arity →
    t.swapPos q (t.unswapPos q k) = k
  | leaf, _, _, _ => rfl
  | node e l r, [], k, h => by
    simp only [arity_node] at h
    simp only [swapPos, unswapPos]
    split_ifs <;> omega
  | node e l r, false :: q, k, h => by
    simp only [arity_node] at h
    simp only [swapPos, unswapPos]
    split_ifs with hk hk'
    · exact swapPos_unswapPos l q hk
    · exact absurd (unswapPos_lt l q hk) hk'
    · rfl
  | node e l r, true :: q, k, h => by
    simp only [arity_node] at h
    simp only [swapPos, unswapPos]
    split_ifs with hk hk'
    · rfl
    · omega
    · rw [show l.arity + r.unswapPos q (k - l.arity) - l.arity = r.unswapPos q (k - l.arity) by
        omega, swapPos_unswapPos r q (k := k - l.arity) (by omega)]
      omega

/-- The numbers of leaves of the two subtrees at the vertex at the end of a path.-/
def splitAt : BTree E → List Bool → ℕ × ℕ
  | leaf, _ => (0, 0)
  | node _ l r, [] => (l.arity, r.arity)
  | node _ l _, false :: q => l.splitAt q
  | node _ _ r, true :: q => r.splitAt q

/-! ### A swap above or beside a cut, and a swap inside it -/

/-- **A swap away from the subtree at `p`** moves the path, keeps the subtree, swaps the cut tree
at the same vertex, and moves the cut-off leaf as it moves the leaves of the cut tree.-/
theorem swapAt_cut_of_not_prefix : ∀ (t : BTree E) (q p : List Bool), p ∈ t.paths → ¬ p <+: q →
    (t.swapAt tw q).subAt (swapPath q p) = t.subAt p ∧
      (t.swapAt tw q).cutAt (swapPath q p) = (t.cutAt p).swapAt tw q ∧
      (t.swapAt tw q).posAt (swapPath q p) = (t.cutAt p).swapPos q (t.posAt p)
  | leaf, _, p, hp, hpq => by
    rw [mem_paths_leaf] at hp
    subst hp
    exact absurd List.nil_prefix hpq
  | node e l r, _, [], _, hpq => absurd List.nil_prefix hpq
  | node e l r, [], false :: p, hp, _ => by
    rw [cons_false_mem_paths] at hp
    have := posAt_lt l hp
    simp [swapPos, this, Nat.add_comm]
  | node e l r, [], true :: p, hp, _ => by
    rw [cons_true_mem_paths] at hp
    simp [swapPos]
  | node e l r, false :: q, false :: p, hp, hpq => by
    rw [cons_false_mem_paths] at hp
    have hpq' : ¬ p <+: q := fun h => hpq (List.cons_prefix_cons.2 ⟨rfl, h⟩)
    obtain ⟨h1, h2, h3⟩ := swapAt_cut_of_not_prefix l q p hp hpq'
    have := posAt_lt l hp
    simp only [swapAt_false, swapPath_cons_self, subAt_false, cutAt_false, posAt_false, swapPos,
      this, ite_true]
    exact ⟨h1, by rw [h2], h3⟩
  | node e l r, true :: q, true :: p, hp, hpq => by
    rw [cons_true_mem_paths] at hp
    have hpq' : ¬ p <+: q := fun h => hpq (List.cons_prefix_cons.2 ⟨rfl, h⟩)
    obtain ⟨h1, h2, h3⟩ := swapAt_cut_of_not_prefix r q p hp hpq'
    simp only [swapAt_true, swapPath_cons_self, subAt_true, cutAt_true, posAt_true, swapPos]
    refine ⟨h1, by rw [h2], ?_⟩
    rw [ite_eq_right (by omega), show l.arity + r.posAt p - l.arity = r.posAt p by omega, h3]
  | node e l r, true :: q, false :: p, hp, _ => by
    rw [cons_false_mem_paths] at hp
    have := posAt_lt l hp
    simp [swapPos, this]
  | node e l r, false :: q, true :: p, hp, _ => by
    rw [cons_true_mem_paths] at hp
    simp [swapPos]

/-- **A swap inside the subtree at `p`** swaps the subtree and keeps the cut tree and the cut-off
leaf.-/
theorem swapAt_cut_of_prefix : ∀ (t : BTree E) (q p : List Bool), p ∈ t.paths → p <+: q →
    (t.swapAt tw q).subAt p = (t.subAt p).swapAt tw (q.drop p.length) ∧
      (t.swapAt tw q).cutAt p = t.cutAt p ∧ (t.swapAt tw q).posAt p = t.posAt p
  | leaf, q, p, hp, _ => by
    rw [mem_paths_leaf] at hp
    subst hp
    simp
  | node e l r, q, [], _, _ => by simp
  | node e l r, [], _ :: _, _, hpq => absurd (List.IsPrefix.length_le hpq) (by simp)
  | node e l r, false :: q, false :: p, hp, hpq => by
    rw [cons_false_mem_paths] at hp
    obtain ⟨h1, h2, h3⟩ := swapAt_cut_of_prefix l q p hp (List.cons_prefix_cons.1 hpq).2
    simp only [swapAt_false, subAt_false, cutAt_false, posAt_false, List.length_cons,
      List.drop_succ_cons]
    exact ⟨h1, by rw [h2], h3⟩
  | node e l r, true :: q, true :: p, hp, hpq => by
    rw [cons_true_mem_paths] at hp
    obtain ⟨h1, h2, h3⟩ := swapAt_cut_of_prefix r q p hp (List.cons_prefix_cons.1 hpq).2
    simp only [swapAt_true, subAt_true, cutAt_true, posAt_true, List.length_cons,
      List.drop_succ_cons]
    exact ⟨h1, by rw [h2], by rw [h3]⟩
  | node e l r, true :: q, false :: p, _, hpq => absurd (List.cons_prefix_cons.1 hpq).1 (by simp)
  | node e l r, false :: q, true :: p, _, hpq => absurd (List.cons_prefix_cons.1 hpq).1 (by simp)

/-- Where the leaf `k ≠ a` of an outer tree goes when `n` leaves are grafted at its leaf `a`.-/
def shiftPos (a n k : ℕ) : ℕ := if k < a then k else k + n - 1

/-- **Leaf positions under a swap away from the subtree at `p`**: the leaves of the cut tree move
as in the swapped cut tree, and the leaves of the subtree move as one block, following the
cut-off leaf.-/
theorem swapPos_cut_of_not_prefix : ∀ (t : BTree E) (q p : List Bool), p ∈ t.paths →
    ¬ p <+: q →
    (∀ k, k < (t.cutAt p).arity → k ≠ t.posAt p →
      t.swapPos q (shiftPos (t.posAt p) (t.subAt p).arity k)
        = shiftPos ((t.cutAt p).swapPos q (t.posAt p)) (t.subAt p).arity
            ((t.cutAt p).swapPos q k)) ∧
    (∀ j, j < (t.subAt p).arity →
      t.swapPos q (t.posAt p + j) = (t.cutAt p).swapPos q (t.posAt p) + j)
  | leaf, _, p, hp, hpq => by
    rw [mem_paths_leaf] at hp
    subst hp
    exact absurd List.nil_prefix hpq
  | node e l r, _, [], _, hpq => absurd List.nil_prefix hpq
  | node e l r, [], false :: p, hp, _ => by
    rw [cons_false_mem_paths] at hp
    have h1 := posAt_lt l hp
    have h2 := arity_cutAt l hp
    have h3 := arity_pos (l.subAt p)
    simp only [subAt_false, cutAt_false, posAt_false, arity_node]
    refine ⟨fun k hk hka => ?_, fun j hj => ?_⟩
    · simp only [swapPos, shiftPos]
      split_ifs <;> omega
    · simp only [swapPos]
      split_ifs <;> omega
  | node e l r, [], true :: p, hp, _ => by
    rw [cons_true_mem_paths] at hp
    have h1 := posAt_lt r hp
    have h2 := arity_cutAt r hp
    have h3 := arity_pos (r.subAt p)
    simp only [subAt_true, cutAt_true, posAt_true, arity_node]
    refine ⟨fun k hk hka => ?_, fun j hj => ?_⟩
    · simp only [swapPos, shiftPos]
      split_ifs <;> omega
    · simp only [swapPos]
      split_ifs <;> omega
  | node e l r, false :: q, false :: p, hp, hpq => by
    rw [cons_false_mem_paths] at hp
    have hpq' : ¬ p <+: q := fun h => hpq (List.cons_prefix_cons.2 ⟨rfl, h⟩)
    obtain ⟨ih1, ih2⟩ := swapPos_cut_of_not_prefix l q p hp hpq'
    have h1 := posAt_lt l hp
    have h2 := arity_cutAt l hp
    have h3 := arity_pos (l.subAt p)
    have h4 := swapPos_lt (l.cutAt p) q h1
    simp only [subAt_false, cutAt_false, posAt_false, arity_node]
    refine ⟨fun k hk hka => ?_, fun j hj => ?_⟩
    · by_cases hkl : k < (l.cutAt p).arity
      · have e1 := ih1 k hkl hka
        have h5 := swapPos_lt (l.cutAt p) q hkl
        simp only [shiftPos] at e1 ⊢
        simp only [swapPos, ite_eq_left hkl, ite_eq_left h1]
        split_ifs at e1 ⊢ <;> omega
      · simp only [shiftPos, swapPos, ite_eq_right hkl, ite_eq_left h1]
        split_ifs <;> omega
    · have e2 := ih2 j hj
      simp only [swapPos, ite_eq_left h1]
      rw [ite_eq_left (by omega), e2]
  | node e l r, true :: q, true :: p, hp, hpq => by
    rw [cons_true_mem_paths] at hp
    have hpq' : ¬ p <+: q := fun h => hpq (List.cons_prefix_cons.2 ⟨rfl, h⟩)
    obtain ⟨ih1, ih2⟩ := swapPos_cut_of_not_prefix r q p hp hpq'
    have h1 := posAt_lt r hp
    have h2 := arity_cutAt r hp
    have h3 := arity_pos (r.subAt p)
    have h4 := swapPos_lt (r.cutAt p) q h1
    simp only [subAt_true, cutAt_true, posAt_true, arity_node]
    refine ⟨fun k hk hka => ?_, fun j hj => ?_⟩
    · by_cases hkl : k < l.arity
      · simp only [shiftPos, swapPos, ite_eq_left hkl, ite_eq_right (show ¬ l.arity + r.posAt p < l.arity
          by omega)]
        split_ifs <;> omega
      · have e1 := ih1 (k - l.arity) (by omega) (by omega)
        have h5 := swapPos_lt (r.cutAt p) q (k := k - l.arity) (by omega)
        simp only [shiftPos] at e1 ⊢
        simp only [swapPos, ite_eq_right hkl, ite_eq_right (show ¬ l.arity + r.posAt p < l.arity by omega),
          show l.arity + r.posAt p - l.arity = r.posAt p by omega]
        split_ifs at e1 ⊢ with c1 c2 c3 c4 <;> first
          | omega
          | (rw [show k + (r.subAt p).arity - 1 - l.arity
                = k - l.arity + (r.subAt p).arity - 1 by omega] at *; omega)
    · have e2 := ih2 j hj
      simp only [swapPos, ite_eq_right (show ¬ l.arity + r.posAt p + j < l.arity by omega),
        ite_eq_right (show ¬ l.arity + r.posAt p < l.arity by omega),
        show l.arity + r.posAt p + j - l.arity = r.posAt p + j by omega,
        show l.arity + r.posAt p - l.arity = r.posAt p by omega, e2]
      omega
  | node e l r, true :: q, false :: p, hp, _ => by
    rw [cons_false_mem_paths] at hp
    have h1 := posAt_lt l hp
    have h2 := arity_cutAt l hp
    have h3 := arity_pos (l.subAt p)
    simp only [subAt_false, cutAt_false, posAt_false, arity_node]
    refine ⟨fun k hk hka => ?_, fun j hj => ?_⟩
    · by_cases hkl : k < (l.cutAt p).arity
      · simp only [shiftPos, swapPos, ite_eq_left hkl, ite_eq_left h1]
        split_ifs <;> omega
      · have h5 := swapPos_lt r q (k := k - (l.cutAt p).arity) (by omega)
        have hs : shiftPos (l.posAt p) (l.subAt p).arity k = k + (l.subAt p).arity - 1 := by
          simp only [shiftPos]
          rw [ite_eq_right (by omega)]
        rw [hs]
        simp only [shiftPos, swapPos, ite_eq_right hkl, ite_eq_left h1]
        rw [ite_eq_right (by omega), ite_eq_right (by omega),
          show k + (l.subAt p).arity - 1 - l.arity = k - (l.cutAt p).arity by omega]
        omega
    · simp only [swapPos, ite_eq_left h1]
      rw [ite_eq_left (by omega)]
  | node e l r, false :: q, true :: p, hp, _ => by
    rw [cons_true_mem_paths] at hp
    have h1 := posAt_lt r hp
    have h2 := arity_cutAt r hp
    have h3 := arity_pos (r.subAt p)
    simp only [subAt_true, cutAt_true, posAt_true, arity_node]
    refine ⟨fun k hk hka => ?_, fun j hj => ?_⟩
    · by_cases hkl : k < l.arity
      · have h5 := swapPos_lt l q hkl
        simp only [shiftPos, swapPos, ite_eq_left hkl, ite_eq_right (show ¬ l.arity + r.posAt p < l.arity
          by omega)]
        split_ifs <;> omega
      · simp only [shiftPos, swapPos, ite_eq_right hkl, ite_eq_right (show ¬ l.arity + r.posAt p < l.arity
          by omega)]
        split_ifs <;> omega
    · simp only [swapPos, ite_eq_right (show ¬ l.arity + r.posAt p + j < l.arity by omega),
        ite_eq_right (show ¬ l.arity + r.posAt p < l.arity by omega)]

/-- **Leaf positions under a swap inside the subtree at `p`**: the block of the subtree is
permuted as the swap permutes the leaves of the subtree, and the other leaves stay.-/
theorem swapPos_cut_of_prefix : ∀ (t : BTree E) (q p : List Bool), p ∈ t.paths → p <+: q →
    ∀ m, m < t.arity → t.swapPos q m = if t.posAt p ≤ m ∧ m < t.posAt p + (t.subAt p).arity then
      t.posAt p + (t.subAt p).swapPos (q.drop p.length) (m - t.posAt p) else m
  | leaf, q, p, hp, _, m, _ => by
    rw [mem_paths_leaf] at hp
    subst hp
    simp [swapPos]
  | node e l r, q, [], _, _, m, hm => by
    simp only [posAt_nil, subAt_nil, List.length_nil, List.drop_zero, Nat.zero_le, true_and,
      Nat.zero_add, Nat.sub_zero, ite_eq_left hm]
  | node e l r, [], _ :: _, _, hpq, _, _ => absurd (List.IsPrefix.length_le hpq) (by simp)
  | node e l r, false :: q, false :: p, hp, hpq, m, hm' => by
    rw [cons_false_mem_paths] at hp
    have ih := swapPos_cut_of_prefix l q p hp (List.cons_prefix_cons.1 hpq).2
    have h1 := posAt_lt l hp
    have h2 := arity_cutAt l hp
    simp only [subAt_false, posAt_false, List.length_cons, List.drop_succ_cons, swapPos]
    by_cases hm : m < l.arity
    · rw [ite_eq_left hm, ih m hm]
    · rw [ite_eq_right hm, ite_eq_right (by omega)]
  | node e l r, true :: q, true :: p, hp, hpq, m, hm' => by
    rw [cons_true_mem_paths] at hp
    have ih := swapPos_cut_of_prefix r q p hp (List.cons_prefix_cons.1 hpq).2
    simp only [arity_node] at hm'
    simp only [subAt_true, posAt_true, List.length_cons, List.drop_succ_cons, swapPos]
    by_cases hm : m < l.arity
    · rw [ite_eq_left hm, ite_eq_right (by omega)]
    · rw [ite_eq_right hm, ih (m - l.arity) (by omega), Nat.sub_sub]
      split_ifs <;> omega
  | node e l r, true :: q, false :: p, _, hpq, _, _ =>
    absurd (List.cons_prefix_cons.1 hpq).1 (by simp)
  | node e l r, false :: q, true :: p, _, hpq, _, _ =>
    absurd (List.cons_prefix_cons.1 hpq).1 (by simp)

/-- **The sign of a swap away from the subtree at `p`**, against the sign of the same swap of the
cut tree: they differ exactly by the parity of the shift of the cut-off leaf, weighted by the
weight of the subtree.-/
theorem splitAt_cut_of_not_prefix : ∀ (t : BTree E) (q p : List Bool), p ∈ t.paths →
    ¬ p <+: q →
    ((t.splitAt q).1 * (t.splitAt q).2 + t.posAt p * (t.subAt p).weight) % 2
      = (((t.cutAt p).splitAt q).1 * ((t.cutAt p).splitAt q).2
          + (t.cutAt p).swapPos q (t.posAt p) * (t.subAt p).weight) % 2
  | leaf, _, p, hp, hpq => by
    rw [mem_paths_leaf] at hp
    subst hp
    exact absurd List.nil_prefix hpq
  | node e l r, _, [], _, hpq => absurd List.nil_prefix hpq
  | node e l r, [], false :: p, hp, _ => by
    rw [cons_false_mem_paths] at hp
    have h1 := posAt_lt l hp
    have h2 := arity_cutAt l hp
    have h3 := weight_add_one (l.subAt p)
    simp only [splitAt, subAt_false, cutAt_false, posAt_false, swapPos, ite_eq_left h1]
    have : l.arity = (l.cutAt p).arity + (l.subAt p).weight := by omega
    rw [this]
    ring_nf
  | node e l r, [], true :: p, hp, _ => by
    rw [cons_true_mem_paths] at hp
    have h1 := posAt_lt r hp
    have h2 := arity_cutAt r hp
    have h3 := weight_add_one (r.subAt p)
    simp only [splitAt, subAt_true, cutAt_true, posAt_true, swapPos,
      ite_eq_right (show ¬ l.arity + r.posAt p < l.arity by omega),
      show l.arity + r.posAt p - l.arity = r.posAt p by omega]
    have : r.arity = (r.cutAt p).arity + (r.subAt p).weight := by omega
    rw [this]
    have e : l.arity * ((r.cutAt p).arity + (r.subAt p).weight)
        + (l.arity + r.posAt p) * (r.subAt p).weight
        = l.arity * (r.cutAt p).arity + r.posAt p * (r.subAt p).weight
          + 2 * (l.arity * (r.subAt p).weight) := by ring
    rw [e]
    omega
  | node e l r, false :: q, false :: p, hp, hpq => by
    rw [cons_false_mem_paths] at hp
    have hpq' : ¬ p <+: q := fun h => hpq (List.cons_prefix_cons.2 ⟨rfl, h⟩)
    have ih := splitAt_cut_of_not_prefix l q p hp hpq'
    have h1 := posAt_lt l hp
    simp only [splitAt, subAt_false, cutAt_false, posAt_false, swapPos, ite_eq_left h1]
    exact ih
  | node e l r, true :: q, true :: p, hp, hpq => by
    rw [cons_true_mem_paths] at hp
    have hpq' : ¬ p <+: q := fun h => hpq (List.cons_prefix_cons.2 ⟨rfl, h⟩)
    have ih := splitAt_cut_of_not_prefix r q p hp hpq'
    simp only [splitAt, subAt_true, cutAt_true, posAt_true, swapPos,
      ite_eq_right (show ¬ l.arity + r.posAt p < l.arity by omega),
      show l.arity + r.posAt p - l.arity = r.posAt p by omega]
    have e1 : (l.arity + r.posAt p) * (r.subAt p).weight
        = r.posAt p * (r.subAt p).weight + l.arity * (r.subAt p).weight := by ring
    have e2 : (l.arity + (r.cutAt p).swapPos q (r.posAt p)) * (r.subAt p).weight
        = (r.cutAt p).swapPos q (r.posAt p) * (r.subAt p).weight
          + l.arity * (r.subAt p).weight := by ring
    rw [e1, e2]
    omega
  | node e l r, true :: q, false :: p, hp, _ => by
    rw [cons_false_mem_paths] at hp
    have h1 := posAt_lt l hp
    simp [splitAt, swapPos, h1]
  | node e l r, false :: q, true :: p, hp, _ => by
    rw [cons_true_mem_paths] at hp
    simp [splitAt, swapPos]

/-- The sign of a swap inside the subtree at `p` is the sign of the same swap of the subtree.-/
theorem splitAt_cut_of_prefix : ∀ (t : BTree E) (q p : List Bool), p ∈ t.paths → p <+: q →
    t.splitAt q = (t.subAt p).splitAt (q.drop p.length)
  | leaf, q, p, hp, _ => by
    rw [mem_paths_leaf] at hp
    subst hp
    rfl
  | node e l r, q, [], _, _ => by simp
  | node e l r, [], _ :: _, _, hpq => absurd (List.IsPrefix.length_le hpq) (by simp)
  | node e l r, false :: q, false :: p, hp, hpq => by
    rw [cons_false_mem_paths] at hp
    exact splitAt_cut_of_prefix l q p hp (List.cons_prefix_cons.1 hpq).2
  | node e l r, true :: q, true :: p, hp, hpq => by
    rw [cons_true_mem_paths] at hp
    exact splitAt_cut_of_prefix r q p hp (List.cons_prefix_cons.1 hpq).2
  | node e l r, true :: q, false :: p, _, hpq => absurd (List.cons_prefix_cons.1 hpq).1 (by simp)
  | node e l r, false :: q, true :: p, _, hpq => absurd (List.cons_prefix_cons.1 hpq).1 (by simp)

end Swap

/-! ## Vertices -/

/-- **A vertex** of a tree: a path ending at a vertex rather than at a leaf.-/
def IsVertex (t : BTree E) (q : List Bool) : Prop := q ∈ t.paths ∧ t.subAt q ≠ leaf

theorem subAt_append : ∀ (t : BTree E) (p q : List Bool), p ∈ t.paths →
    t.subAt (p ++ q) = (t.subAt p).subAt q
  | leaf, p, q, hp => by
    rw [mem_paths_leaf] at hp
    subst hp
    simp
  | node e l r, [], q, _ => by simp
  | node e l r, false :: p, q, hp => by
    rw [cons_false_mem_paths] at hp
    simp [subAt_append l p q hp]
  | node e l r, true :: p, q, hp => by
    rw [cons_true_mem_paths] at hp
    simp [subAt_append r p q hp]

theorem mem_paths_append : ∀ (t : BTree E) (p q : List Bool), p ∈ t.paths →
    (p ++ q ∈ t.paths ↔ q ∈ (t.subAt p).paths)
  | leaf, p, q, hp => by
    rw [mem_paths_leaf] at hp
    subst hp
    simp
  | node e l r, [], q, _ => by simp
  | node e l r, false :: p, q, hp => by
    rw [cons_false_mem_paths] at hp
    simp [mem_paths_append l p q hp]
  | node e l r, true :: p, q, hp => by
    rw [cons_true_mem_paths] at hp
    simp [mem_paths_append r p q hp]

/-- A vertex inside the subtree at `p` is a vertex of that subtree.-/
theorem isVertex_subAt {t : BTree E} {p q : List Bool} (hp : p ∈ t.paths) (hpq : p <+: q)
    (hq : t.IsVertex q) : (t.subAt p).IsVertex (q.drop p.length) := by
  obtain ⟨q', rfl⟩ := hpq
  simp only [List.drop_left]
  exact ⟨(mem_paths_append t p q' hp).1 hq.1, by rw [← subAt_append t p q' hp]; exact hq.2⟩

/-- A vertex away from the subtree at `p` is a vertex of the cut tree.-/
theorem isVertex_cutAt : ∀ (t : BTree E) (p q : List Bool), p ∈ t.paths → ¬ p <+: q →
    t.IsVertex q → (t.cutAt p).IsVertex q
  | leaf, _, q, _, _, hq => absurd (by cases q <;> rfl) hq.2
  | node e l r, [], _, _, hpq, _ => absurd List.nil_prefix hpq
  | node e l r, false :: _, [], _, _, _ => ⟨nil_mem_paths _, by simp⟩
  | node e l r, true :: _, [], _, _, _ => ⟨nil_mem_paths _, by simp⟩
  | node e l r, false :: p, false :: q, hp, hpq, hq => by
    rw [cons_false_mem_paths] at hp
    have hpq' : ¬ p <+: q := fun h => hpq (List.cons_prefix_cons.2 ⟨rfl, h⟩)
    have := isVertex_cutAt l p q hp hpq' ⟨(cons_false_mem_paths e l r q).1 hq.1, hq.2⟩
    exact ⟨(cons_false_mem_paths e _ r q).2 this.1, this.2⟩
  | node e l r, true :: p, true :: q, hp, hpq, hq => by
    rw [cons_true_mem_paths] at hp
    have hpq' : ¬ p <+: q := fun h => hpq (List.cons_prefix_cons.2 ⟨rfl, h⟩)
    have := isVertex_cutAt r p q hp hpq' ⟨(cons_true_mem_paths e l r q).1 hq.1, hq.2⟩
    exact ⟨(cons_true_mem_paths e l _ q).2 this.1, this.2⟩
  | node e l r, false :: p, true :: q, _, _, hq =>
    ⟨(cons_true_mem_paths e _ r q).2 ((cons_true_mem_paths e l r q).1 hq.1), hq.2⟩
  | node e l r, true :: p, false :: q, _, _, hq =>
    ⟨(cons_false_mem_paths e l _ q).2 ((cons_false_mem_paths e l r q).1 hq.1), hq.2⟩

end BTree

/-! ## Positional composition in a symmetric operad, and relabelling -/

namespace SymOperad

open Sym

variable {R : Type u} [CommRing R]
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

/-- The inputs of a positional composite at a `Fin` slot, in order: the outer inputs before the
slot, the inserted block, the outer inputs after the slot.-/
def compFinEquiv {m : ℕ} (i : Fin m) (n : ℕ) : Without (Fin m) i ⊕ Fin n ≃ Fin (m - 1 + n) :=
  ((compEquiv (finCongr (show m = (i : ℕ) + 1 + (m - i - 1) by have := i.isLt; omega))
      (Equiv.refl (Fin n)) i).trans
    ((slotEquiv (show finCongr (show m = (i : ℕ) + 1 + (m - i - 1) by have := i.isLt; omega) i
        = ⟨i, by have := i.isLt; omega⟩ from Fin.ext rfl)).trans
      (insertEquiv i (m - i - 1) n))).trans
    (finCongr (show (i : ℕ) + n + (m - i - 1) = m - 1 + n by have := i.isLt; omega))

lemma compFinEquiv_inl {m : ℕ} (i : Fin m) (n : ℕ) (k : Without (Fin m) i) :
    ((compFinEquiv i n (Sum.inl k) : Fin (m - 1 + n)) : ℕ) = BTree.shiftPos i n k.1 := by
  have hi := i.isLt
  exact insertEquiv_inl_val (i : ℕ) (m - i - 1) n
    ⟨⟨k.1, by omega⟩, fun h => k.2 (Fin.ext (by simpa using congrArg Fin.val h))⟩

lemma compFinEquiv_inr {m : ℕ} (i : Fin m) (n : ℕ) (j : Fin n) :
    ((compFinEquiv i n (Sum.inr j) : Fin (m - 1 + n)) : ℕ) = i + j := rfl

/-- **Relabelling the outer operation of a positional composite**: a relabelling `σ` of the outer
inputs and a relabelling `τ` of the composite which moves the inserted block with the slot.-/
lemma map_comp_map_left {m n : ℕ} (i : Fin m) (σ : Fin m ≃ Fin m)
    (τ : Fin (m - 1 + n) ≃ Fin (m - 1 + n))
    (hout : ∀ (k : Fin m) (hk : k ≠ i), (τ (compFinEquiv i n (Sum.inl ⟨k, hk⟩)) : ℕ)
      = BTree.shiftPos (σ i) n (σ k))
    (hin : ∀ j : Fin n, (τ (compFinEquiv i n (Sum.inr j)) : ℕ) = σ i + j)
    (x : P (Fin m)) (y : P (Fin n)) :
    map (R := R) (compFinEquiv (σ i) n) (comp (R := R) (σ i) (map (R := R) σ x) y)
      = map (R := R) τ (map (R := R) (compFinEquiv i n) (comp (R := R) i x y)) := by
  rw [comp_map_left, map_map, map_map]
  refine map_eq_of_equiv_eq (fun c => Fin.ext ?_) _
  rcases c with k | j
  · rw [Equiv.trans_apply, Equiv.trans_apply, hout k.1 k.2]
    simp only [compEquiv_inl, compFinEquiv_inl]
  · rw [Equiv.trans_apply, Equiv.trans_apply, hin j]
    simp only [compEquiv_inr, Equiv.refl_apply, compFinEquiv_inr]

/-- **Relabelling the inserted operation of a positional composite**: the relabelling acts on the
inserted block, and the other inputs stay.-/
lemma map_comp_map_right {m n : ℕ} (i : Fin m) (ρ : Fin n ≃ Fin n)
    (τ : Fin (m - 1 + n) ≃ Fin (m - 1 + n))
    (hout : ∀ k : Without (Fin m) i,
      τ (compFinEquiv i n (Sum.inl k)) = compFinEquiv i n (Sum.inl k))
    (hin : ∀ j : Fin n, (τ (compFinEquiv i n (Sum.inr j)) : ℕ) = i + ρ j)
    (x : P (Fin m)) (y : P (Fin n)) :
    map (R := R) (compFinEquiv i n) (comp (R := R) i x (map (R := R) ρ y))
      = map (R := R) τ (map (R := R) (compFinEquiv i n) (comp (R := R) i x y)) := by
  rw [comp_map_right, map_map, map_map]
  refine map_eq_of_equiv_eq (fun c => Fin.ext ?_) _
  rcases c with k | j
  · rw [Equiv.trans_apply, Equiv.trans_apply, hout k]
    rfl
  · rw [Equiv.trans_apply, Equiv.trans_apply, hin j]
    rfl

end SymOperad

/-! ## Symmetric cochains -/

namespace TConv

open BTree SymOperad

variable {R : Type u} [CommRing R] {E : Type v} (tw : E → E)
  {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type w}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]

/-- The tree swapped at the vertex at the end of a path.-/
def swapTree {n : ℕ} (t : OfArity E n) (q : List Bool) : OfArity E n :=
  ⟨t.1.swapAt tw q, (arity_swapAt t.1 q).trans t.2⟩

variable {tw}

/-- **The relabelling of the leaves effected by a swap.**-/
def swapPerm {n : ℕ} (t : OfArity E n) (q : List Bool) : Fin n ≃ Fin n where
  toFun k := ⟨t.1.swapPos q k, by
    have := swapPos_lt t.1 q (k := k) (by rw [t.2]; exact k.2)
    rwa [t.2] at this⟩
  invFun k := ⟨t.1.unswapPos q k, by
    have := unswapPos_lt t.1 q (k := k) (by rw [t.2]; exact k.2)
    rwa [t.2] at this⟩
  left_inv k := Fin.ext (unswapPos_swapPos t.1 q (by rw [t.2]; exact k.2))
  right_inv k := Fin.ext (swapPos_unswapPos t.1 q (by rw [t.2]; exact k.2))

@[simp] lemma swapPerm_val {n : ℕ} (t : OfArity E n) (q : List Bool) (k : Fin n) :
    ((swapPerm t q k : Fin n) : ℕ) = t.1.swapPos q k := rfl

variable (R) in
/-- **The sign of a swap**: exchanging blocks of `a` and `b` leaves costs `-(-1)^(a b)`.-/
def swapSign (t : BTree E) (q : List Bool) : R := (-1) ^ ((t.splitAt q).1 * (t.splitAt q).2 + 1)

/-- The value of a cochain at a tree, in the component of the symmetric operad.-/
def ev {n : ℕ} (f : TConv R E (toNS P) n) (t : OfArity E n) : P (Fin n) := f t

omit [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P] in
@[simp] lemma ev_zero {n : ℕ} (t : OfArity E n) : ev (0 : TConv R E (toNS P) n) t = 0 := rfl

omit [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P] in
@[simp] lemma ev_add {n : ℕ} (f g : TConv R E (toNS P) n) (t : OfArity E n) :
    ev (f + g) t = ev f t + ev g t := rfl

omit [SymOperad R P] in
@[simp] lemma ev_smul {n : ℕ} (c : R) (f : TConv R E (toNS P) n) (t : OfArity E n) :
    ev (c • f) t = c • ev f t := rfl

variable (tw) in
/-- **A symmetric cochain**: its value at a tree swapped at a vertex is its value at the tree,
relabelled along the swap and multiplied by the sign of the swap.-/
def IsSymm {n : ℕ} (f : TConv R E (toNS P) n) : Prop :=
  ∀ (t : OfArity E n) (q : List Bool), t.1.IsVertex q →
    ev f (swapTree tw t q) = swapSign R t.1 q • map (R := R) (swapPerm t q) (ev f t)

/-! ### The convolution product as a sum over the vertices and leaves of a tree -/

section Paths

variable {j k : ℕ} {t : OfArity E (j + k + 1)} {p : List Bool}

lemma arity_cutAt_eq (h : p ∈ t.1.paths ∧ (t.1.subAt p).arity = k + 1) :
    (t.1.cutAt p).arity = j + 1 := by
  have := arity_cutAt t.1 h.1
  rw [t.2, h.2] at this
  omega

lemma posAt_lt_succ (h : p ∈ t.1.paths ∧ (t.1.subAt p).arity = k + 1) : t.1.posAt p < j + 1 := by
  have := posAt_lt t.1 h.1
  rwa [arity_cutAt_eq h] at this

variable (R) in
/-- The term of a convolution product at a tree contributed by the subtree at the end of a path,
nonzero only when that subtree has the arity of the inserted cochain.-/
noncomputable def pathTerm (f : TConv R E (toNS P) (j + 1)) (g : TConv R E (toNS P) (k + 1))
    (t : OfArity E (j + k + 1)) (p : List Bool) : P (Fin (j + k + 1)) :=
  if h : p ∈ t.1.paths ∧ (t.1.subAt p).arity = k + 1 then
    ((-1 : R) ^ (t.1.posAt p * k)) •
      (map (R := R) (compFinEquiv (⟨t.1.posAt p, posAt_lt_succ h⟩ : Fin (j + 1)) (k + 1))
        (comp (R := R) (⟨t.1.posAt p, posAt_lt_succ h⟩ : Fin (j + 1))
          (ev f ⟨t.1.cutAt p, arity_cutAt_eq h⟩) (ev g ⟨t.1.subAt p, h.2⟩)) : P (Fin (j + k + 1)))
  else 0

end Paths

/-! ### Symmetric cochains are closed under the convolution product -/

section Closure

variable {j k : ℕ} {f : TConv R E (toNS P) (j + 1)} {g : TConv R E (toNS P) (k + 1)}

end Closure

/-! ### Linear structure and brackets -/

section Linear

variable {n : ℕ}

lemma isSymm_zero : IsSymm tw (0 : TConv R E (toNS P) n) := by
  intro t q _
  rw [ev_zero, ev_zero, map_zero, smul_zero]

lemma IsSymm.add {f g : TConv R E (toNS P) n} (hf : IsSymm tw f) (hg : IsSymm tw g) :
    IsSymm tw (f + g) := by
  intro t q hq
  rw [ev_add, ev_add, hf t q hq, hg t q hq, map_add, smul_add]

lemma IsSymm.smul {f : TConv R E (toNS P) n} (c : R) (hf : IsSymm tw f) : IsSymm tw (c • f) := by
  intro t q hq
  rw [ev_smul, ev_smul, hf t q hq, map_smul, smul_comm]

variable (R tw) in
/-- **The symmetric cochains of a given arity**, a submodule of all cochains.-/
def symmCochains (n : ℕ) : Submodule R (TConv R E (toNS P) n) where
  carrier := {f | IsSymm tw f}
  add_mem' hf hg := IsSymm.add hf hg
  zero_mem' := isSymm_zero
  smul_mem' c _ hf := IsSymm.smul c hf

end Linear

end TConv

/-! ## Twisting, and coefficients in an ideal, for any non-symmetric operad -/

section Twisting

variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]

/-- **Coefficients in an ideal.** Reindexing preserves an ideal.-/
lemma OperadIdeal.reindex_mem (I : OperadIdeal R P) {m n : ℕ} (h : m = n) {x : P m}
    (hx : x ∈ I.carrier m) : reindex R P h x ∈ I.carrier n := by
  subst h
  exact hx

lemma OperadIdeal.compFin_mem_left (I : OperadIdeal R P) {m n : ℕ} (i : Fin m) {α : P m}
    (hα : α ∈ I.carrier m) (β : P n) : compFin (R := R) i α β ∈ I.carrier (m - 1 + n) :=
  I.reindex_mem _ (I.comp_mem_left _ _ (I.reindex_mem _ hα) β)

lemma OperadIdeal.compFin_mem_right (I : OperadIdeal R P) {m n : ℕ} (i : Fin m) (α : P m)
    {β : P n} (hβ : β ∈ I.carrier n) : compFin (R := R) i α β ∈ I.carrier (m - 1 + n) :=
  I.reindex_mem _ (I.comp_mem_right _ _ _ hβ)

end Twisting

end Operad
