/-
# Mirror images of planar binary trees

Reversing the order of the inputs of a planar binary tree while relabelling its vertices along a
map `f` of generators (`BTree.mirror`) preserves the arity (`BTree.arity_mirror`), and for an
involution `f` it is an involution (`BTree.mirror_mirror`), so it permutes the trees of each arity
(`BTree.OfArity.mirrorEquiv`). On the named trees of `Operad.LowWeight` it exchanges left and right
combs in arity three (`OfArity.mirror_lc`, `OfArity.mirror_rc`) and permutes the five shapes of
arity four (`OfArity.mirror_ll`, …). For the planar operad of a presentation whose generators come
with a reversal, this is the reversal involution of the free non-symmetric operad.
-/
import Tengoku.LeanOperads.Operad.LowWeight

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe v

namespace Operad

namespace BTree

variable {E : Type v}

/-- **The mirror image** of a planar binary tree, its vertices relabelled along `f`.-/
def mirror (f : E → E) : BTree E → BTree E
  | leaf => leaf
  | node e l r => node (f e) (mirror f r) (mirror f l)

/--
@isnad1 id=eq.0h2v.s4.0f88476be7a2 from=translated src=- shape=d1393c91 vocab=f6c4b613
-/
@[simp] lemma mirror_leaf (f : E → E) : mirror f (leaf : BTree E) = leaf := rfl

/--
@isnad1 id=eq.0h5v.s5.f920877096a6 from=translated src=- shape=e3e28231 vocab=f73a6e71
-/
@[simp] lemma mirror_node (f : E → E) (e : E) (l r : BTree E) :
    mirror f (node e l r) = node (f e) (mirror f r) (mirror f l) := rfl

/-- The mirror image has the same number of leaves.
@isnad1 id=eq.0h3v.s4.e8a19cd2c9fc from=translated src=- shape=9cc98308 vocab=1d47b98c
-/
lemma arity_mirror (f : E → E) : ∀ t : BTree E, (mirror f t).arity = t.arity
  | leaf => rfl
  | node e l r => by
    rw [mirror_node, arity_node, arity_node, arity_mirror f l, arity_mirror f r, Nat.add_comm]

/-- Mirroring along an involution is an involution.
@isnad1 id=eq.1h3v.s4.08a63e329fd7 from=translated src=- shape=cdd07b5a vocab=22a03efb
-/
lemma mirror_mirror {f : E → E} (hf : Function.Involutive f) :
    ∀ t : BTree E, mirror f (mirror f t) = t
  | leaf => rfl
  | node e l r => by rw [mirror_node, mirror_node, mirror_mirror hf l, mirror_mirror hf r, hf e]

namespace OfArity

/-- **The mirror image** of a tree of arity `n`.-/
def mirror (f : E → E) {n : ℕ} (t : OfArity E n) : OfArity E n :=
  ⟨BTree.mirror f t.1, (BTree.arity_mirror f t.1).trans t.2⟩

/--
@isnad1 id=eq.1h4v.s4.c94cbb268ed6 from=translated src=- shape=e322a667 vocab=e3d98ff9
-/
lemma mirror_mirror {f : E → E} (hf : Function.Involutive f) {n : ℕ} (t : OfArity E n) :
    mirror f (mirror f t) = t :=
  Subtype.ext (BTree.mirror_mirror hf t.1)

/-- **Mirroring along an involution permutes the trees of each arity.**-/
def mirrorEquiv {f : E → E} (hf : Function.Involutive f) (n : ℕ) : OfArity E n ≃ OfArity E n where
  toFun := mirror f
  invFun := mirror f
  left_inv := mirror_mirror hf
  right_inv := mirror_mirror hf

/--
@isnad1 id=eq.1h4v.s6.bcce72f93ed5 from=translated src=- shape=a6e8e948 vocab=c500f257
-/
@[simp] lemma mirrorEquiv_apply {f : E → E} (hf : Function.Involutive f) {n : ℕ}
    (t : OfArity E n) : mirrorEquiv hf n t = mirror f t := rfl

/--
@isnad1 id=eq.0h3v.s5.5be7cafa00fc from=translated src=- shape=6bc471d0 vocab=debad99e
-/
@[simp] lemma mirror_cor (f : E → E) (e : E) : mirror f (cor e) = cor (f e) := rfl

/--
@isnad1 id=eq.0h4v.s5.19e6eb8d0e25 from=translated src=- shape=d8a4966b vocab=091a4de1
-/
@[simp] lemma mirror_lc (f : E → E) (e e' : E) : mirror f (lc e e') = rc (f e) (f e') := rfl

/--
@isnad1 id=eq.0h4v.s5.cb5f5c7357b8 from=translated src=- shape=d8a4966b vocab=091a4de1
-/
@[simp] lemma mirror_rc (f : E → E) (e e' : E) : mirror f (rc e e') = lc (f e) (f e') := rfl

/--
@isnad1 id=eq.0h5v.s5.6bf4307cd7c7 from=translated src=- shape=5bad0179 vocab=b3a2e264
-/
@[simp] lemma mirror_ll (f : E → E) (e₁ e₂ e₃ : E) :
    mirror f (ll e₁ e₂ e₃) = rr (f e₁) (f e₂) (f e₃) := rfl

/--
@isnad1 id=eq.0h5v.s5.2a6afbaac61a from=translated src=- shape=5bad0179 vocab=519858ff
-/
@[simp] lemma mirror_lr (f : E → E) (e₁ e₂ e₃ : E) :
    mirror f (lr e₁ e₂ e₃) = rl (f e₁) (f e₂) (f e₃) := rfl

/--
@isnad1 id=eq.0h5v.s5.5b957d982810 from=translated src=- shape=c2a6863a vocab=7785bfbd
-/
@[simp] lemma mirror_bl (f : E → E) (e₁ e₂ e₃ : E) :
    mirror f (bl e₁ e₂ e₃) = bl (f e₁) (f e₃) (f e₂) := rfl

/--
@isnad1 id=eq.0h5v.s5.c1c684e5a0b1 from=translated src=- shape=5bad0179 vocab=519858ff
-/
@[simp] lemma mirror_rl (f : E → E) (e₁ e₂ e₃ : E) :
    mirror f (rl e₁ e₂ e₃) = lr (f e₁) (f e₂) (f e₃) := rfl

/--
@isnad1 id=eq.0h5v.s5.3a1b0a1a7534 from=translated src=- shape=5bad0179 vocab=b3a2e264
-/
@[simp] lemma mirror_rr (f : E → E) (e₁ e₂ e₃ : E) :
    mirror f (rr e₁ e₂ e₃) = ll (f e₁) (f e₂) (f e₃) := rfl

end OfArity

end BTree

end Operad
