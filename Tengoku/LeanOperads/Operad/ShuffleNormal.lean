/-
# Normal forms in a shuffle operad with a quadratic Gröbner basis

Relators of arity three, functions `r` on the shuffle monomials of arity three, generate an ideal
of the free shuffle operad; in arity `n` it is spanned by their substitutions at the windows of
the monomials (`idealOf`). The relators are **a quadratic Gröbner basis** (`IsGroebner`) for the
path-lexicographic order of a ranking `rk` of the generators and a set `L` of arity-three
monomials when each monomial of `L` leads a relator, and no nonzero vector of the ideal is
supported on the monomials with no window in `L` (the normal monomials). Then:

* every non-normal monomial leads a vector of the ideal, and the normal monomials span a
  complement of the ideal in every arity (`IsGroebner.isCompl`): they are a basis of the operad
  presented by the relators (`Operad.isCompl_supportedOn`);
* **the normal form** (`LTree.nfOf`) of a shuffle monomial with distinct labels, on any set of
  labels, is the combination of normal monomials on the same labels congruent to it: the normal
  form of a normal monomial is itself (`LTree.nfOf_of_isNormal`), and the normal forms of the
  substitutions of a relator at an edge cancel (`LTree.sum_nfOf_substAt`). Normal forms only use
  that the normal monomials span a complement of the ideal in every arity.

Monomials on any set of labels are compared with those on `0, …, k - 1` by relabelling the leaves
in increasing order (`LTree.relabel`, `LTree.std`, `LTree.destd`), which keeps the shuffle
condition, the windows and the substitutions.
-/
import Tengoku.LeanOperads.Operad.ShuffleSubst
import Tengoku.LeanOperads.Operad.LeadingTerm
import Tengoku.Seed.Data.Nat.Nth
import Tengoku.Seed.LinearAlgebra.Projection
import Tengoku.Seed.LinearAlgebra.Finsupp.LinearCombination
import Tengoku.Seed.Algebra.Module.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Operad

namespace LTree

variable {E : Type*}

/-! ## Relabelling the leaves -/

/-- **Relabel the leaves** by `f`.-/
def relabel (f : ℕ → ℕ) : LTree E → LTree E
  | leaf a => leaf (f a)
  | node e l r => node e (l.relabel f) (r.relabel f)

/--
@isnad1 id=eq.0h3v.s4.95ff0c9fe33e from=translated src=- shape=124115c7 vocab=15208681
-/
@[simp] lemma relabel_leaf (f : ℕ → ℕ) (a : ℕ) : (leaf a : LTree E).relabel f = leaf (f a) := rfl

/--
@isnad1 id=eq.0h5v.s5.dc5b11a76546 from=translated src=- shape=801029ae vocab=96fc23e5
-/
@[simp] lemma relabel_node (f : ℕ → ℕ) (e : E) (l r : LTree E) :
    (node e l r).relabel f = node e (l.relabel f) (r.relabel f) := rfl

/--
@isnad1 id=eq.0h3v.s4.3d9a4aaa9da3 from=translated src=- shape=bd6b4ebc vocab=046bb41b
-/
@[simp] lemma labels_relabel (f : ℕ → ℕ) : ∀ t : LTree E, (t.relabel f).labels = t.labels.map f
  | leaf _ => rfl
  | node _ l r => by simp [labels_relabel f l, labels_relabel f r]

/--
@isnad1 id=eq.0h3v.s4.0ea44765d36f from=translated src=- shape=42929a1c vocab=eb46b378
-/
@[simp] lemma arity_relabel (f : ℕ → ℕ) (t : LTree E) : (t.relabel f).arity = t.arity := by
  rw [← length_labels, ← length_labels, labels_relabel, List.length_map]

/--
@isnad1 id=eq.0h4v.s5.50cd9d3f128a from=translated src=- shape=0e5f7640 vocab=07efcaeb
-/
lemma relabel_relabel (f g : ℕ → ℕ) : ∀ t : LTree E, (t.relabel f).relabel g = t.relabel (g ∘ f)
  | leaf _ => rfl
  | node _ l r => by simp [relabel_relabel f g l, relabel_relabel f g r]

/--
@isnad1 id=eq.1h4v.s5.cb4816d5f244 from=translated src=- shape=19bd163c vocab=cccf3631
-/
lemma relabel_congr {f g : ℕ → ℕ} : ∀ t : LTree E, (∀ a ∈ t.labels, f a = g a) →
    t.relabel f = t.relabel g
  | leaf a, h => by simp [h a (by simp)]
  | node _ l r, h => by
    simp only [relabel_node, labels_node, List.mem_append] at h ⊢
    rw [relabel_congr l fun a ha => h a (Or.inl ha), relabel_congr r fun a ha => h a (Or.inr ha)]

/--
@isnad1 id=eq.0h2v.s3.bb3da6446cb1 from=translated src=- shape=2033f3d1 vocab=50a6af62
-/
lemma relabel_id : ∀ t : LTree E, t.relabel id = t
  | leaf _ => rfl
  | node _ l r => by simp [relabel_id l, relabel_id r]

/--
@isnad1 id=eq.1h3v.s5.7e09ed0458b0 from=translated src=- shape=33e53570 vocab=cccf3631
-/
lemma relabel_eq_self {f : ℕ → ℕ} (t : LTree E) (h : ∀ a ∈ t.labels, f a = a) :
    t.relabel f = t :=
  (relabel_congr t (g := id) h).trans (relabel_id t)

/-- `f` is strictly increasing on the labels of `t`.-/
def StrictOn (f : ℕ → ℕ) (t : LTree E) : Prop :=
  ∀ a ∈ t.labels, ∀ b ∈ t.labels, a < b → f a < f b

/--
@isnad1 id=stricton.2h4v.s5.b514799bf568 from=translated src=- shape=4219bf0a vocab=b68db468
-/
lemma StrictOn.mono {f : ℕ → ℕ} {t u : LTree E} (h : StrictOn f t) (hu : u.labels ⊆ t.labels) :
    StrictOn f u := fun a ha b hb hab => h a (hu ha) b (hu hb) hab

/--
@isnad1 id=stricton.1h5v.s4.636f491ee7e2 from=translated src=- shape=aecbc07e vocab=ffcb4838
-/
lemma StrictOn.left {f : ℕ → ℕ} {e : E} {l r : LTree E} (h : StrictOn f (node e l r)) :
    StrictOn f l := h.mono fun _ ha => by simp [ha]

/--
@isnad1 id=stricton.1h5v.s4.3a42ff619ebb from=translated src=- shape=520fd2c4 vocab=ffcb4838
-/
lemma StrictOn.right {f : ℕ → ℕ} {e : E} {l r : LTree E} (h : StrictOn f (node e l r)) :
    StrictOn f r := h.mono fun _ ha => by simp [ha]

/--
@isnad1 id=iff.3h5v.s5.2cdb54256bd7 from=translated src=- shape=c0b3954d vocab=7cf5ea94
-/
lemma StrictOn.lt_iff {f : ℕ → ℕ} {t : LTree E} (h : StrictOn f t) {a b : ℕ} (ha : a ∈ t.labels)
    (hb : b ∈ t.labels) : f a < f b ↔ a < b := by
  refine ⟨fun hab => ?_, h a ha b hb⟩
  rcases lt_trichotomy a b with h' | rfl | h'
  · exact h'
  · exact absurd hab (lt_irrefl _)
  · exact absurd (h b hb a ha h') (not_lt.2 hab.le)

/--
@isnad1 id=eq.1h3v.s4.5e83b92c3201 from=translated src=- shape=ca4c154e vocab=acb07388
-/
lemma minLabel_relabel {f : ℕ → ℕ} : ∀ t : LTree E, StrictOn f t →
    (t.relabel f).minLabel = f t.minLabel
  | leaf _, _ => rfl
  | node e l r, h => by
    simp only [relabel_node, minLabel_node, minLabel_relabel l h.left,
      minLabel_relabel r h.right]
    have hl : l.minLabel ∈ (node e l r).labels := by simp [minLabel_mem]
    have hr : r.minLabel ∈ (node e l r).labels := by simp [minLabel_mem]
    rcases le_or_gt l.minLabel r.minLabel with hlr | hlr
    · rw [min_eq_left hlr]
      rcases hlr.lt_or_eq with hlr | hlr
      · exact min_eq_left (h _ hl _ hr hlr).le
      · rw [hlr, min_self]
    · rw [min_eq_right hlr.le]
      exact min_eq_right (h _ hr _ hl hlr).le

/--
@isnad1 id=iff.1h3v.s4.47925b82a4ee from=translated src=- shape=ec9c2eac vocab=2bb49e89
-/
lemma isShuffle_relabel {f : ℕ → ℕ} : ∀ t : LTree E, StrictOn f t →
    ((t.relabel f).IsShuffle ↔ t.IsShuffle)
  | leaf _, _ => Iff.rfl
  | node e l r, h => by
    have hl : l.minLabel ∈ (node e l r).labels := by simp [minLabel_mem]
    have hr : r.minLabel ∈ (node e l r).labels := by simp [minLabel_mem]
    simp only [relabel_node, isShuffle_node, minLabel_relabel l h.left,
      minLabel_relabel r h.right, isShuffle_relabel l h.left, isShuffle_relabel r h.right,
      h.lt_iff hl hr]

/--
@isnad1 id=eq.5h7v.s6.a7ee643a2a6b from=translated src=- shape=29ec51b4 vocab=8aef7f06
-/
lemma rank3_relabel {f : ℕ → ℕ} {t : LTree E} (h : StrictOn f t) {a b c x : ℕ} (ha : a ∈ t.labels)
    (hb : b ∈ t.labels) (hc : c ∈ t.labels) (hx : x ∈ t.labels) :
    rank3 (f a) (f b) (f c) (f x) = rank3 a b c x := by
  simp only [rank3, h.lt_iff ha hx, h.lt_iff hb hx, h.lt_iff hc hx]

/--
@isnad1 id=eq.0h4v.s4.d7816fb85683 from=translated src=- shape=cc10a89c vocab=a150b2ea
-/
lemma subtreeAt_relabel (f : ℕ → ℕ) :
    ∀ (t : LTree E) (p : List Bool), (t.relabel f).subtreeAt p = (t.subtreeAt p).relabel f
  | leaf _, [] => rfl
  | leaf _, _ :: _ => rfl
  | node _ _ _, [] => rfl
  | node _ l _, false :: p => subtreeAt_relabel f l p
  | node _ _ r, true :: p => subtreeAt_relabel f r p

/--
@isnad1 id=eq.0h5v.s5.1a380c4a0a80 from=translated src=- shape=cc117eed vocab=e66f7f8b
-/
lemma replaceAt_relabel (f : ℕ → ℕ) : ∀ (t : LTree E) (p : List Bool) (u : LTree E),
    (t.relabel f).replaceAt p (u.relabel f) = (t.replaceAt p u).relabel f
  | leaf _, [], _ => rfl
  | leaf _, _ :: _, _ => rfl
  | node _ _ _, [], _ => rfl
  | node e l r, false :: p, u => by simp only [relabel_node, replaceAt, replaceAt_relabel f l p u]
  | node e l r, true :: p, u => by simp only [relabel_node, replaceAt, replaceAt_relabel f r p u]

/--
@isnad1 id=eq.0h4v.s5.133f863d7711 from=translated src=- shape=79322cf6 vocab=9b5445b7
-/
lemma plug_relabel (f : ℕ → ℕ) (ins : ℕ → LTree E) :
    ∀ m : LTree E, (m.plug ins).relabel f = m.plug fun k => (ins k).relabel f
  | leaf _ => rfl
  | node e l r => by simp only [plug, relabel_node, plug_relabel f ins l, plug_relabel f ins r]

/--
@isnad1 id=iff.0h4v.s4.6d5f57506915 from=translated src=- shape=f4d5859d vocab=f00701e6
-/
lemma isEdgeRoot_relabel (f : ℕ → ℕ) :
    ∀ (u : LTree E) (s : Bool), (u.relabel f).IsEdgeRoot s ↔ u.IsEdgeRoot s
  | leaf _, _ => Iff.rfl
  | node _ (leaf _) (leaf _), _ => by cases ‹Bool› <;> exact Iff.rfl
  | node _ (node _ _ _) (leaf _), _ => by cases ‹Bool› <;> exact Iff.rfl
  | node _ (leaf _) (node _ _ _), _ => by cases ‹Bool› <;> exact Iff.rfl
  | node _ (node _ _ _) (node _ _ _), _ => by cases ‹Bool› <;> exact Iff.rfl

/--
@isnad1 id=iff.0h5v.s4.f8a4c3af5b9b from=translated src=- shape=42691785 vocab=be99db72
-/
lemma isEdge_relabel (f : ℕ → ℕ) (t : LTree E) (p : List Bool) (s : Bool) :
    (t.relabel f).IsEdge p s ↔ t.IsEdge p s := by
  unfold IsEdge
  rw [subtreeAt_relabel, isEdgeRoot_relabel]

/--
@isnad1 id=eq.2h5v.s5.29d1cfa6dfb2 from=translated src=- shape=3ceb88a3 vocab=714f5d9c
-/
lemma winIns_relabel {f : ℕ → ℕ} : ∀ (u : LTree E) (s : Bool), StrictOn f u → u.IsEdgeRoot s →
    ∀ k, (u.relabel f).winIns s k = (u.winIns s k).relabel f
  | node e (node g a b) c, false, h, _, k => by
    have hb : b.minLabel ∈ (node e (node g a b) c).labels := by simp [minLabel_mem]
    have hc : c.minLabel ∈ (node e (node g a b) c).labels := by simp [minLabel_mem]
    simp only [winIns, relabel_node, winInputs, minLabel_relabel b h.left.right,
      minLabel_relabel c h.right, h.lt_iff hb hc, ins3]
    split_ifs <;> rfl
  | node e c (node g a b), true, _, _, k => by
    have e1 : (node e (c.relabel f) (node g (a.relabel f) (b.relabel f))).winInputs true =
        (c.relabel f, a.relabel f, b.relabel f) := by cases c <;> rfl
    have e2 : (node e c (node g a b)).winInputs true = (c, a, b) := by cases c <;> rfl
    simp only [winIns, relabel_node, e1, e2, ins3]
    split_ifs <;> rfl

/--
@isnad1 id=eq.2h4v.s5.3d82b6c6de91 from=translated src=- shape=7fb950c8 vocab=230fe721
-/
lemma windowRoot_relabel {f : ℕ → ℕ} : ∀ (u : LTree E) (s : Bool), StrictOn f u →
    u.IsEdgeRoot s → (u.relabel f).windowRoot s = u.windowRoot s
  | node e (node g a b) c, false, h, _ => by
    have ha : a.minLabel ∈ (node e (node g a b) c).labels := by simp [minLabel_mem]
    have hb : b.minLabel ∈ (node e (node g a b) c).labels := by simp [minLabel_mem]
    have hc : c.minLabel ∈ (node e (node g a b) c).labels := by simp [minLabel_mem]
    simp only [relabel_node, windowRoot, minLabel_relabel a h.left.left,
      minLabel_relabel b h.left.right, minLabel_relabel c h.right, window,
      rank3_relabel h ha hb hc ha, rank3_relabel h ha hb hc hb, rank3_relabel h ha hb hc hc]
  | node e c (node g a b), true, h, _ => by
    have ha : a.minLabel ∈ (node e c (node g a b)).labels := by simp [minLabel_mem]
    have hb : b.minLabel ∈ (node e c (node g a b)).labels := by simp [minLabel_mem]
    have hc : c.minLabel ∈ (node e c (node g a b)).labels := by simp [minLabel_mem]
    have e1 : (node e (c.relabel f) (node g (a.relabel f) (b.relabel f))).windowRoot true =
        window e g true (a.relabel f).minLabel (b.relabel f).minLabel (c.relabel f).minLabel := by
      cases c <;> rfl
    have e2 : (node e c (node g a b)).windowRoot true =
        window e g true a.minLabel b.minLabel c.minLabel := by cases c <;> rfl
    rw [relabel_node, relabel_node, e1, e2, minLabel_relabel a h.right.left,
      minLabel_relabel b h.right.right, minLabel_relabel c h.left, window, window,
      rank3_relabel h ha hb hc ha, rank3_relabel h ha hb hc hb, rank3_relabel h ha hb hc hc]

/--
@isnad1 id=eq.2h5v.s5.82d6b7c862f0 from=translated src=- shape=fcaf65fb vocab=d4835af4
-/
lemma windowAt_relabel {f : ℕ → ℕ} {t : LTree E} (h : StrictOn f t) {p : List Bool} {s : Bool}
    (he : t.IsEdge p s) : (t.relabel f).windowAt p s = t.windowAt p s := by
  unfold windowAt
  rw [subtreeAt_relabel]
  exact windowRoot_relabel _ s (h.mono (labels_subtreeAt_subset t p)) he

/--
@isnad1 id=iff.1h4v.s5.21970ae704d3 from=translated src=- shape=3be01a49 vocab=4fbb6ddb
-/
lemma mem_windows_relabel {f : ℕ → ℕ} {t : LTree E} (h : StrictOn f t) (w : LTree E) :
    w ∈ (t.relabel f).windows ↔ w ∈ t.windows := by
  simp only [mem_windows_iff, isEdge_relabel]
  constructor
  · rintro ⟨p, s, he, rfl⟩
    exact ⟨p, s, he, (windowAt_relabel h he).symm⟩
  · rintro ⟨p, s, he, rfl⟩
    exact ⟨p, s, he, windowAt_relabel h he⟩

/--
@isnad1 id=iff.1h4v.s4.42fbf46bd71f from=translated src=- shape=a3fc2977 vocab=823a7a46
-/
lemma isNormal_relabel {f : ℕ → ℕ} {t : LTree E} (h : StrictOn f t) (L : Set (LTree E)) :
    IsNormal L (t.relabel f) ↔ IsNormal L t := by
  simp only [IsNormal, mem_windows_relabel h]

/-- **Relabelling commutes with substitution.**
@isnad1 id=eq.2h6v.s5.965baebc0f32 from=translated src=- shape=c5abebcb vocab=6268066e
-/
lemma substAt_relabel {f : ℕ → ℕ} {t : LTree E} (h : StrictOn f t) {p : List Bool} {s : Bool}
    (he : t.IsEdge p s) (m : LTree E) :
    (t.relabel f).substAt p s m = (t.substAt p s m).relabel f := by
  unfold substAt
  rw [← replaceAt_relabel, plug_relabel, subtreeAt_relabel]
  congr 2
  funext k
  exact winIns_relabel _ s (h.mono (labels_subtreeAt_subset t p)) he k

/-! ## Standardization -/

/-- The labels of a tree, as a finite set.-/
def labelSet (t : LTree E) : Finset ℕ := t.labels.toFinset

/-- **The standardization** of a tree: each label replaced by its rank among the labels.-/
noncomputable def std (t : LTree E) : LTree E := t.relabel (Nat.count (· ∈ t.labelSet))

/-- **Labels `0, …, k - 1` replaced by the elements of `A`**, in increasing order.-/
noncomputable def destd (A : Finset ℕ) (t : LTree E) : LTree E := t.relabel (Nat.nth (· ∈ A))

/--
@isnad1 id=finite.0h1v.s4.8171f9e8b0fd from=translated src=- shape=fcae1392 vocab=83624a4b
-/
lemma finite_mem (A : Finset ℕ) : (Set.ofPred (· ∈ A)).Finite := A.finite_toSet

/--
@isnad1 id=eq.0h1v.s4.73fcc8de3eb3 from=translated src=- shape=cf560fc4 vocab=f09d7413
-/
lemma card_finite_mem (A : Finset ℕ) : (finite_mem A).toFinset.card = A.card := by
  congr 1
  ext a
  simp

/--
@isnad1 id=stricton.0h2v.s5.23e46e3ad60d from=translated src=- shape=0cfc6cc3 vocab=bf69da9f
-/
lemma strictOn_count (t : LTree E) : StrictOn (Nat.count (· ∈ t.labelSet)) t :=
  fun a ha _ _ hab => Nat.count_strict_mono (by simpa [labelSet] using ha) hab

/--
@isnad1 id=lt.1h3v.s5.7e98ca388099 from=translated src=- shape=cc6118a4 vocab=4d65aabb
-/
lemma count_lt (t : LTree E) {a : ℕ} (ha : a ∈ t.labels) :
    Nat.count (· ∈ t.labelSet) a < t.labelSet.card := by
  rw [← card_finite_mem]
  exact Nat.count_lt_card (finite_mem _) (by simpa [labelSet] using ha)

/--
@isnad1 id=eq.1h2v.s4.979aec909717 from=translated src=- shape=636cc111 vocab=903cfa98
-/
lemma card_labelSet {t : LTree E} (hnd : t.labels.Nodup) : t.labelSet.card = t.arity := by
  rw [labelSet, List.toFinset_card_of_nodup hnd, length_labels]

/--
@isnad1 id=perm.3h2v.s5.d116f971fa20 from=translated src=- shape=9af693e5 vocab=6aa71dba
-/
lemma perm_range_of_nodup {l : List ℕ} {k : ℕ} (hnd : l.Nodup) (hlen : l.length = k)
    (hlt : ∀ a ∈ l, a < k) : l.Perm (List.range k) := by
  refine List.perm_of_nodup_nodup_toFinset_eq hnd List.nodup_range ?_
  refine Finset.eq_of_subset_of_card_le (fun a ha => ?_) ?_
  · simpa using hlt a (List.mem_toFinset.1 ha)
  · rw [List.toFinset_card_of_nodup hnd, List.toFinset_range, Finset.card_range, hlen]

/--
@isnad1 id=perm.1h2v.s4.e03896f1c577 from=translated src=- shape=3d568de8 vocab=ee440a1a
-/
lemma labels_std_perm {t : LTree E} (hnd : t.labels.Nodup) :
    (std t).labels.Perm (List.range t.arity) := by
  have hinj : ∀ a ∈ t.labels, ∀ b ∈ t.labels,
      Nat.count (· ∈ t.labelSet) a = Nat.count (· ∈ t.labelSet) b → a = b := by
    intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (strictOn_count t a ha b hb h).ne
    · exact h
    · exact absurd hab (strictOn_count t b hb a ha h).ne'
  refine perm_range_of_nodup ?_ (by simp [std]) ?_
  · rw [std, labels_relabel]
    exact hnd.map_on hinj
  · intro a ha
    rw [std, labels_relabel, List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    rw [← card_labelSet hnd]
    exact count_lt t hb

/--
@isnad1 id=isshuffl.1h2v.s3.af4beadf0bd2 from=translated src=- shape=6c92d0ec vocab=487579e8
-/
lemma isShuffle_std {t : LTree E} (hs : t.IsShuffle) : (std t).IsShuffle :=
  (isShuffle_relabel t (strictOn_count t)).2 hs

/--
@isnad1 id=iff.0h3v.s4.f4b8e9978af2 from=translated src=- shape=ffa5df8e vocab=c406da7d
-/
lemma isNormal_std {t : LTree E} (L : Set (LTree E)) : IsNormal L (std t) ↔ IsNormal L t :=
  isNormal_relabel (strictOn_count t) L

/--
@isnad1 id=eq.0h2v.s4.899d16502514 from=translated src=- shape=0913e22b vocab=06cbfcd3
-/
lemma destd_std {t : LTree E} : destd t.labelSet (std t) = t := by
  rw [destd, std, relabel_relabel]
  exact relabel_eq_self t fun a ha => Nat.nth_count (by simpa [labelSet] using ha)

/--
@isnad1 id=stricton.1h3v.s5.8505e4dd89de from=translated src=- shape=b84871ef vocab=0018c345
-/
lemma strictOn_nth (A : Finset ℕ) {t : LTree E} (ht : ∀ i ∈ t.labels, i < A.card) :
    StrictOn (Nat.nth (· ∈ A)) t := fun a ha b hb hab =>
  Nat.nth_strictMonoOn (finite_mem A) (by simpa [card_finite_mem] using ht a ha)
    (by simpa [card_finite_mem] using ht b hb) hab

/--
@isnad1 id=eq.1h3v.s4.a95356078241 from=translated src=- shape=b65c7e65 vocab=c83b311c
-/
lemma labelSet_destd (A : Finset ℕ) {t : LTree E} (ht : t.labels.Perm (List.range A.card)) :
    (destd A t).labelSet = A := by
  ext a
  simp only [labelSet, destd, labels_relabel, List.mem_toFinset, List.mem_map, ht.mem_iff,
    List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact Nat.nth_mem_of_lt_card (finite_mem A) (by simpa [card_finite_mem] using hi)
  · intro ha
    refine ⟨Nat.count (· ∈ A) a, ?_, Nat.nth_count ha⟩
    rw [← card_finite_mem]
    exact Nat.count_lt_card (finite_mem A) ha

/--
@isnad1 id=eq.1h3v.s4.86a062a38f1a from=translated src=- shape=564137e1 vocab=33fa577f
-/
lemma std_destd (A : Finset ℕ) {t : LTree E} (ht : t.labels.Perm (List.range A.card)) :
    std (destd A t) = t := by
  rw [std, labelSet_destd A ht, destd, relabel_relabel]
  refine relabel_eq_self t fun i hi => ?_
  have hi' : i < A.card := List.mem_range.1 (ht.subset hi)
  exact Nat.count_nth_of_lt_card_finite (finite_mem A) (by simpa [card_finite_mem] using hi')

/--
@isnad1 id=eq.1h3v.s4.49c6f244eb92 from=translated src=- shape=ec9d6f01 vocab=75a72fee
-/
lemma labelSet_eq_of_perm {t u : LTree E} (h : t.labels.Perm u.labels) : t.labelSet = u.labelSet :=
  List.toFinset_eq_of_perm _ _ h

/-- **Standardization commutes with substitution.**
@isnad1 id=eq.4h5v.s5.83b09ad98b75 from=translated src=- shape=f72c6604 vocab=cfee1185
-/
lemma std_substAt {t : LTree E} {p : List Bool} {s : Bool} (he : t.IsEdge p s)
    (hs : t.IsShuffle) (hnd : t.labels.Nodup) {m : LTree E} (hm : m.labels.Perm (List.range 3)) :
    std (t.substAt p s m) = (std t).substAt p s m := by
  rw [std, labelSet_eq_of_perm (perm_labels_substAt he hs hnd hm), std,
    substAt_relabel (strictOn_count t) he]

/--
@isnad1 id=iff.0h4v.s4.7ad69e385ebd from=translated src=- shape=222489f2 vocab=4500d011
-/
lemma isEdge_std {t : LTree E} {p : List Bool} {s : Bool} : (std t).IsEdge p s ↔ t.IsEdge p s :=
  isEdge_relabel _ t p s

end LTree

/-! ## The ideal of a space of relators -/

namespace LTree

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **The shuffle monomials of arity `n`.**-/
abbrev Mono (E : Type*) [Fintype E] [DecidableEq E] (n : ℕ) := {t : LTree E // t ∈ monomials n}

section Ideal

variable (K : Type*) [Field K]

/-- **The vector of a tree** in arity `n`: the basis vector of a monomial, zero otherwise.-/
def vecOf (n : ℕ) (t : LTree E) : Mono E n → K := fun y => if y.1 = t then 1 else 0

/-- **The substitution of a relator** `r` at the edge `(p, s)` of `t`.-/
def substVec (n : ℕ) (t : LTree E) (p : List Bool) (s : Bool) (r : Mono E 3 → K) : Mono E n → K :=
  ∑ σ, r σ • vecOf K n (t.substAt p s σ.1)

/-- **The ideal generated by relators of arity three**, in arity `n`: spanned by their
substitutions at the edges of the monomials.-/
def idealOf (R : Submodule K (Mono E 3 → K)) (n : ℕ) : Submodule K (Mono E n → K) :=
  Submodule.span K {v | ∃ t : Mono E n, ∃ p s, ∃ r ∈ R, t.1.IsEdge p s ∧ v = substVec K n t.1 p s r}

/-- **The normal monomials** of arity `n`: no window in `L`.-/
def normalSet (L : Set (LTree E)) (n : ℕ) : Set (Mono E n) := {y | IsNormal L y.1}

/--
@isnad1 id=mem.2h8v.s9.b486660bcfa0 from=translated src=- shape=a66cdd5c vocab=854582d1
-/
lemma substVec_mem_idealOf (R : Submodule K (Mono E 3 → K)) {n : ℕ} (t : Mono E n) {p : List Bool}
    {s : Bool} (he : t.1.IsEdge p s) {r : Mono E 3 → K} (hr : r ∈ R) :
    substVec K n t.1 p s r ∈ idealOf K R n :=
  Submodule.subset_span ⟨t, p, s, r, hr, he, rfl⟩

/-- **A quadratic Gröbner basis**: the relators `R` and the set `L` of arity-three monomials are
such that each monomial of `L` leads a relator for the path-lexicographic key of `rk`, and no
nonzero vector of the ideal is supported on the normal monomials.-/
structure IsGroebner (rk : E → ℕ) (L : Set (LTree E)) (R : Submodule K (Mono E 3 → K)) : Prop where
  mem : ∀ ℓ ∈ L, ℓ ∈ monomials 3
  lead : ∀ ℓ (hℓ : ℓ ∈ L), ∃ r ∈ R, r ⟨ℓ, mem ℓ hℓ⟩ ≠ 0 ∧
    ∀ σ : Mono E 3, σ.1 ≠ ℓ → r σ ≠ 0 → pathKey rk 3 σ.1 < pathKey rk 3 ℓ
  indep : ∀ n, ∀ v ∈ idealOf K R n, v ∈ supportedOn K (normalSet L n) → v = 0

variable {K}

/-- **A linear order on the monomials** of arity `n` refining the path-lexicographic key.-/
@[reducible] noncomputable def keyOrder (rk : E → ℕ) (n : ℕ) : LinearOrder (Mono E n) :=
  LinearOrder.lift' (fun y => toLex (pathKey rk n y.1, (Fintype.equivFin (Mono E n) y : ℕ)))
    fun x y h => by
      simp only [toLex_inj, Prod.mk.injEq] at h
      exact (Fintype.equivFin (Mono E n)).injective (Fin.ext h.2)

/--
@isnad1 id=lt.1h5v.s7.ee0ed212e158 from=translated src=- shape=d02a0b98 vocab=d031cfae
-/
lemma keyOrder_lt {rk : E → ℕ} {n : ℕ} {x y : Mono E n} (h : pathKey rk n x.1 < pathKey rk n y.1) :
    (keyOrder rk n).lt x y := by
  show @LT.lt (Lex (List ℕ × ℕ)) _ (toLex (pathKey rk n x.1, ((Fintype.equivFin (Mono E n) x : ℕ))))
    (toLex (pathKey rk n y.1, ((Fintype.equivFin (Mono E n) y : ℕ))))
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inl h)

variable {rk : E → ℕ} {L : Set (LTree E)} {R : Submodule K (Mono E 3 → K)}

/-! ### Normal forms

Normal forms only need the normal monomials to span a complement of the ideal in every arity
(`hc`), which a quadratic Gröbner basis provides (`IsGroebner.isCompl`). -/

variable (hc : ∀ n, IsCompl (idealOf K R n) (supportedOn K (normalSet L n)))

/-- **The normal form in arity `n`**: the projection onto the vectors on the normal monomials,
along the ideal.-/
noncomputable def nfProj (n : ℕ) : (Mono E n → K) →ₗ[K] (Mono E n → K) :=
  (supportedOn K (normalSet L n)).subtype ∘ₗ
    (supportedOn K (normalSet L n)).projectionOnto (idealOf K R n) (hc n).symm

include hc in
/--
@isnad1 id=eq.2h6v.s10.594c1640e570 from=translated src=- shape=c579eeb7 vocab=9f7e00d3
-/
lemma nfProj_eq_zero {n : ℕ} {v : Mono E n → K} (hv : v ∈ idealOf K R n) :
    nfProj hc n v = 0 := by
  simp [nfProj, Submodule.projectionOnto_apply_right (hc n).symm ⟨v, hv⟩]

include hc in
/--
@isnad1 id=eq.2h6v.s10.3c73b113ed3d from=translated src=- shape=aa7d6ce1 vocab=9f7e00d3
-/
lemma nfProj_eq_self {n : ℕ} {v : Mono E n → K} (hv : v ∈ supportedOn K (normalSet L n)) :
    nfProj hc n v = v := by
  simp [nfProj, Submodule.projectionOnto_apply_left (hc n).symm ⟨v, hv⟩]

/--
@isnad1 id=mem.1h6v.s10.cddc9dd30e97 from=translated src=- shape=564c5612 vocab=9f7e00d3
-/
lemma nfProj_mem (n : ℕ) (v : Mono E n → K) :
    nfProj hc n v ∈ supportedOn K (normalSet L n) := by
  simp [nfProj]

/--
@isnad1 id=mem.2h2v.s5.32ffdb566780 from=translated src=- shape=0fbf5884 vocab=0f2f49c8
-/
lemma std_mem_monomials {c : LTree E} (hs : c.IsShuffle) (hnd : c.labels.Nodup) :
    std c ∈ monomials c.arity :=
  (mem_monomials _ _).2 ⟨isShuffle_std hs, labels_std_perm hnd⟩

/-- **The normal form of a monomial** with distinct labels, on any set of labels: its
standardization reduced along the ideal, the labels put back.-/
noncomputable def nfOf (c : LTree E) : LTree E →₀ K :=
  ∑ m : Mono E c.arity,
    nfProj hc c.arity (vecOf K c.arity (std c)) m • Finsupp.single (destd c.labelSet m.1) (1 : K)

/--
@isnad1 id=eq.2h6v.s10.20c52b9af3a6 from=translated src=- shape=bdc51761 vocab=c2cb5897
-/
lemma nfOf_eq {c : LTree E} {k : ℕ} (hk : c.arity = k) :
    nfOf hc c = ∑ m : Mono E k,
      nfProj hc k (vecOf K k (std c)) m • Finsupp.single (destd c.labelSet m.1) (1 : K) := by
  subst hk
  rfl

/-- **The normal form of a normal monomial** is itself.
@isnad1 id=eq.4h5v.s9.2c11534aebfd from=translated src=- shape=e5aa8adc vocab=2e0345ba
-/
theorem nfOf_of_isNormal {c : LTree E} (hs : c.IsShuffle) (hnd : c.labels.Nodup)
    (hcn : IsNormal L c) : nfOf hc c = Finsupp.single c (1 : K) := by
  have hmem := std_mem_monomials hs hnd
  have hv : vecOf K c.arity (std c) ∈ supportedOn K (normalSet L c.arity) := by
    rw [mem_supportedOn]
    intro y hy
    simp only [vecOf]
    rw [ite_eq_right]
    intro h
    exact hy (by rw [normalSet, Set.mem_ofPred_eq, h]; exact (isNormal_std L).2 hcn)
  rw [nfOf, nfProj_eq_self hc hv, Finset.sum_eq_single ⟨std c, hmem⟩]
  · simp [vecOf, destd_std]
  · intro m _ hm
    simp only [vecOf]
    rw [ite_eq_right fun h => hm (Subtype.ext h), zero_smul]
  · simp

/-- **The normal forms of the substitutions of a relator at an edge cancel.**
@isnad1 id=eq.5h8v.s10.3870e54bf7ca from=translated src=- shape=99ebc56a vocab=16e6af41
-/
theorem sum_nfOf_substAt {c : LTree E} (hs : c.IsShuffle) (hnd : c.labels.Nodup)
    {p : List Bool} {s : Bool} (he : c.IsEdge p s) {r : Mono E 3 → K} (hr : r ∈ R) :
    ∑ σ : Mono E 3, r σ • nfOf hc (c.substAt p s σ.1) = 0 := by
  have hperm : ∀ σ : Mono E 3, (c.substAt p s σ.1).labels.Perm c.labels := fun σ =>
    perm_labels_substAt he hs hnd ((mem_monomials 3 σ.1).1 σ.2).2
  have harity : ∀ σ : Mono E 3, (c.substAt p s σ.1).arity = c.arity := fun σ => by
    rw [← length_labels, ← length_labels, (hperm σ).length_eq]
  have hset : ∀ σ : Mono E 3, (c.substAt p s σ.1).labelSet = c.labelSet := fun σ =>
    labelSet_eq_of_perm (hperm σ)
  have hstd : ∀ σ : Mono E 3, std (c.substAt p s σ.1) = (std c).substAt p s σ.1 := fun σ =>
    std_substAt he hs hnd ((mem_monomials 3 σ.1).1 σ.2).2
  simp_rw [fun σ => nfOf_eq hc (harity σ), hset, hstd, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [← Finset.sum_smul]
  have : ∑ σ : Mono E 3, r σ * nfProj hc c.arity (vecOf K c.arity ((std c).substAt p s σ.1)) m =
      nfProj hc c.arity (substVec K c.arity (std c) p s r) m := by
    simp only [substVec, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [this, nfProj_eq_zero hc (substVec_mem_idealOf K R ⟨std c, std_mem_monomials hs hnd⟩
    (isEdge_std.2 he) hr), Pi.zero_apply, zero_smul]

/-- **The normal form is a combination of normal monomials on the same labels.**
@isnad1 id=and.3h6v.s9.37930ec05527 from=translated src=- shape=170ca2b9 vocab=6eaae390
-/
theorem mem_support_nfOf {c : LTree E} (hnd : c.labels.Nodup)
    {y : LTree E} (hy : y ∈ (nfOf hc c).support) :
    y.IsShuffle ∧ y.labels.Perm c.labels ∧ IsNormal L y := by
  rw [nfOf, Finsupp.mem_support_iff, Finsupp.finsetSum_apply] at hy
  obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero] at hm
  by_cases hmy : destd c.labelSet m.1 = y
  swap
  · simp [hmy] at hm
  rw [ite_eq_left hmy] at hm
  subst hmy
  have hmn : IsNormal L m.1 := by
    by_contra hn
    exact hm ((mem_supportedOn.1 (nfProj_mem hc c.arity _)) m hn)
  have hmm := (mem_monomials _ _).1 m.2
  have hlt : ∀ i ∈ m.1.labels, i < c.labelSet.card := fun i hi => by
    rw [card_labelSet hnd]
    exact List.mem_range.1 (hmm.2.subset hi)
  have hst := strictOn_nth c.labelSet hlt
  have hperm : m.1.labels.Perm (List.range c.labelSet.card) := by
    rw [card_labelSet hnd]
    exact hmm.2
  refine ⟨(isShuffle_relabel _ hst).2 hmm.1, ?_, (isNormal_relabel hst L).2 hmn⟩
  refine List.perm_of_nodup_nodup_toFinset_eq ?_ hnd ?_
  · rw [destd, labels_relabel]
    refine (hmm.2.nodup_iff.2 List.nodup_range).map_on fun a ha b hb hab => ?_
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (hst a ha b hb h).ne
    · exact h
    · exact absurd hab (hst b hb a ha h).ne'
  · exact labelSet_destd c.labelSet hperm

end Ideal

end LTree

end Operad
