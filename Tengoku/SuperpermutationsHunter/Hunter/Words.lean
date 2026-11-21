/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Permutation words, overlap weight, and the successor edges (Hunter §2.2)

This file **ports** the word-level substrate of the sibling `Coeff2/` formalization into
the `Hunter` namespace (the two projects do not share a library, so the definitions are
copied verbatim and re-proved where a proof "comes along for free").

Contents:
* `IsPermWord k w` — a permutation of `[k] = {1,…,k}`, encoded as a `List ℕ`.
* `wt k u v` — the overlap weight `w(u→v)` of Hunter §2.2 (`sInf` of the valid offsets).
  The digest states this equals Hunter's edge weight `w` verbatim.
* `rho` (= Hunter's `σ`, the weight-1 successor), `door` (= Hunter's `τ`, the weight-2
  successor), `alphaWord` (= Hunter's `α`, a specific weight-3 successor).
* `RotClass`/`rotClass` — cyclic rotation classes; `c(v)` (the 1-cycle) is a fibre of
  `rotClass`.

All proofs here are ports; nothing in this file is new mathematics.
-/

namespace Hunter

open List

/-- Hunter §2.2 (Coeff2 `IsPermWord`): a *permutation of `[k]`*, as a word — distinct
symbols whose set is exactly `[k] = {1,…,k}` (hence length `k`).-/
def IsPermWord (k : ℕ) (w : List ℕ) : Prop :=
  w.Nodup ∧ w.toFinset = Finset.Icc 1 k

/-- Hunter §2.2 (Coeff2 `wt`): the overlap edge weight `w(u→v)` = least `d` with
`1 ≤ d ≤ k` and `u_{d+1}⋯u_k = v_1⋯v_{k−d}`, i.e. `u.drop d = v.take (k−d)`.  The digest
records that this is exactly Hunter's `w`.-/
noncomputable def wt (k : ℕ) (u v : List ℕ) : ℕ :=
  sInf {d | 1 ≤ d ∧ d ≤ k ∧ u.drop d = v.take (k - d)}

/-- Hunter §2.2 `σ` (Coeff2 `rho`): the weight-1 successor, the cyclic left rotation
`σ(π₁⋯π_k) = π₂⋯π_kπ₁`.-/
def rho (w : List ℕ) : List ℕ := w.rotate 1

/-- Hunter §2.2 `τ` (Coeff2 `door`): the weight-2 successor that is *not* `σ²`, namely
`τ(π₁⋯π_k) = π₃⋯π_kπ₂π₁`.-/
def door (w : List ℕ) : List ℕ := w.drop 2 ++ [w.getD 1 0, w.getD 0 0]

/-- Hunter §2.2 `α`: a specific weight-3 successor, `α(π₁⋯π_k) = π₄⋯π_kπ₃π₂π₁`
(reverse the first three symbols to the back).-/
def alphaWord (w : List ℕ) : List ℕ := w.drop 3 ++ (w.take 3).reverse

/-- Cyclic rotation classes of words (Coeff2 `RotClass`): the quotient of `List ℕ` by "is
a cyclic rotation of".  Hunter's 1-cycle `c(v)` is the fibre of `rotClass` through `v`.-/
abbrev RotClass : Type := Quotient (List.IsRotated.setoid ℕ)

/-- The rotation class of a word.-/
def rotClass (w : List ℕ) : RotClass := Quotient.mk _ w

/-! ## Ported basic API (proofs come along for free) -/

/--
@isnad1 id=nodup.1h2v.s3.fae11cbe9ee4 from=translated src=- shape=1fb49929 vocab=0c1fefc9
-/
theorem IsPermWord.nodup {k : ℕ} {w : List ℕ} (h : IsPermWord k w) : w.Nodup := h.1

/--
@isnad1 id=eq.1h2v.s4.ca7dbcf98da3 from=translated src=- shape=d2b800b8 vocab=8ef2a5cf
-/
theorem IsPermWord.toFinset_eq {k : ℕ} {w : List ℕ} (h : IsPermWord k w) :
    w.toFinset = Finset.Icc 1 k := h.2

/--
@isnad1 id=eq.1h2v.s3.0cec980691ba from=translated src=- shape=90664a9c vocab=3b04796f
-/
theorem IsPermWord.length {k : ℕ} {w : List ℕ} (h : IsPermWord k w) : w.length = k := by
  have h1 := List.toFinset_card_of_nodup h.1
  rw [h.2, Nat.card_Icc] at h1
  omega

/--
@isnad1 id=ne.2h2v.s4.a3073651ac7e from=translated src=- shape=43d52e2d vocab=d4774bd0
-/
theorem IsPermWord.ne_nil {k : ℕ} {w : List ℕ} (h : IsPermWord k w) (hk : 1 ≤ k) :
    w ≠ [] := by
  intro hw
  have hlen := h.length
  rw [hw] at hlen; simp at hlen; omega

/--
@isnad1 id=ispermwo.1h3v.s4.dc03f6ae3235 from=translated src=- shape=fdc5dd0e vocab=c9bca887
-/
theorem isPermWord_rotate {k : ℕ} {w : List ℕ} (h : IsPermWord k w) (j : ℕ) :
    IsPermWord k (w.rotate j) := by
  refine ⟨(List.rotate_perm w j).nodup_iff.mpr h.1, ?_⟩
  rw [List.toFinset_eq_of_perm _ _ (List.rotate_perm w j), h.2]

/-- Permutation-words are preserved by list permutations (same multiset of symbols).
@isnad1 id=ispermwo.2h3v.s4.3d336ef90593 from=translated src=- shape=9823251d vocab=1c27d540
-/
theorem IsPermWord.perm {k : ℕ} {w w' : List ℕ} (h : IsPermWord k w) (hp : w ~ w') :
    IsPermWord k w' :=
  ⟨hp.nodup_iff.mp h.1, by rw [← List.toFinset_eq_of_perm _ _ hp, h.2]⟩

/--
@isnad1 id=ispermwo.2h3v.s4.8c27c4bf5b98 from=translated src=- shape=9823251d vocab=11bee09a
-/
theorem isPermWord_of_isRotated {k : ℕ} {w w' : List ℕ} (h : IsPermWord k w)
    (hr : w ~r w') : IsPermWord k w' := by
  obtain ⟨j, rfl⟩ := hr; exact isPermWord_rotate h j

/-! ## Weight basics (ported) -/

/--
@isnad1 id=and.2h3v.s6.37b20d6881a1 from=translated src=- shape=cfa72111 vocab=6ccc195f
-/
theorem wt_spec {k : ℕ} {u v : List ℕ} (hk : 1 ≤ k) (hu : u.length ≤ k) :
    1 ≤ wt k u v ∧ wt k u v ≤ k ∧ u.drop (wt k u v) = v.take (k - wt k u v) :=
  Nat.sInf_mem (⟨k, hk, le_refl k, by simp [List.drop_eq_nil_of_le hu]⟩ :
    {d | 1 ≤ d ∧ d ≤ k ∧ u.drop d = v.take (k - d)}.Nonempty)

/--
@isnad1 id=le.3h4v.s5.968bf09b5e11 from=translated src=- shape=428c9c07 vocab=0e43e39e
-/
theorem wt_le {k : ℕ} {u v : List ℕ} {d : ℕ} (h1 : 1 ≤ d) (h2 : d ≤ k)
    (h3 : u.drop d = v.take (k - d)) : wt k u v ≤ d :=
  Nat.sInf_le ⟨h1, h2, h3⟩

/-- The rotation `σ` has weight 1.
@isnad1 id=eq.2h2v.s4.e048223849fc from=translated src=- shape=4440057f vocab=02a131ab
-/
theorem wt_rho {k : ℕ} {u : List ℕ} (hk : 1 ≤ k) (hu : IsPermWord k u) :
    wt k u (rho u) = 1 := by
  have hlen : u.length = k := hu.length
  have h1 : u.drop 1 = (rho u).take (k - 1) := by
    rw [rho, List.rotate_eq_drop_append_take (by omega),
      List.take_left' (by rw [List.length_drop]; omega)]
  have h2 := wt_le (le_refl 1) (by omega) h1
  have h3 := (wt_spec (u := u) (v := rho u) hk (by omega)).1
  omega

/-- A weight-1 edge between permutation words is the rotation `σ`.-/
theorem eq_rho_of_wt_one {k : ℕ} {u v : List ℕ} (hk : 1 ≤ k) (hu : IsPermWord k u)
    (hv : IsPermWord k v) (h : wt k u v = 1) : v = rho u := by
  have hspec := (wt_spec hk (le_of_eq hu.length) (v := v)).2.2
  rw [h] at hspec
  have hvlen := hv.length
  have hulen := hu.length
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (hu.ne_nil hk)
  have hdrop : (a :: t).drop 1 = t := rfl
  rw [hdrop] at hspec
  obtain ⟨z, hz⟩ : ∃ z, v.drop (k - 1) = [z] := by
    apply List.length_eq_one_iff.mp
    rw [List.length_drop]; omega
  have hveq : v = t ++ [z] := by
    conv_lhs => rw [← List.take_append_drop (k - 1) v]
    rw [hz, ← hspec]
  have htlen : t.length = k - 1 := by
    have := hulen; simp only [List.length_cons] at this; omega
  have hza : z = a := by
    have hzIcc : z ∈ Finset.Icc 1 k := by
      rw [← hv.toFinset_eq, hveq]; simp
    have huIcc : (a :: t).toFinset = Finset.Icc 1 k := hu.toFinset_eq
    rw [List.toFinset_cons] at huIcc
    rw [← huIcc, Finset.mem_insert] at hzIcc
    rcases hzIcc with h1 | h1
    · exact h1
    · exfalso
      have hvnd := hv.nodup
      rw [hveq] at hvnd
      rw [List.nodup_append] at hvnd
      rw [List.mem_toFinset] at h1
      exact hvnd.2.2 z h1 z (List.mem_singleton_self z) rfl
  rw [hveq, hza]
  show t ++ [a] = (a :: t).rotate 1
  simp

/-! ## Rotation classes (ported) -/

/--
@isnad1 id=iff.0h2v.s4.cd9f65fe4284 from=translated src=- shape=204223db vocab=6f5e5d9a
-/
theorem rotClass_eq_iff {w w' : List ℕ} : rotClass w = rotClass w' ↔ w ~r w' := by
  constructor
  · intro h; exact Quotient.exact h
  · intro h; exact Quotient.sound h

/-! ## Finiteness of the vertex set (ported, needed for the `Fintype (Vtx k)` instance) -/

/-- The duplicate-free words with symbol set exactly `S` (Coeff2 `permsOf`).-/
noncomputable def permsOf (S : Finset ℕ) : Finset (List ℕ) :=
  (S.sort (· ≤ ·)).permutations.toFinset

/--
@isnad1 id=iff.0h2v.s5.c494f7c27321 from=translated src=- shape=a8c5ef63 vocab=dacf9830
-/
theorem mem_permsOf {S : Finset ℕ} {w : List ℕ} :
    w ∈ permsOf S ↔ w.Nodup ∧ w.toFinset = S := by
  rw [permsOf, List.mem_toFinset, List.mem_permutations]
  constructor
  · intro h
    exact ⟨h.nodup_iff.mpr (S.sort_nodup _),
      by rw [List.toFinset_eq_of_perm _ _ h, S.sort_toFinset]⟩
  · rintro ⟨hnd, hS⟩
    exact List.perm_of_nodup_nodup_toFinset_eq hnd (S.sort_nodup _)
      (by rw [hS, S.sort_toFinset])

/--
@isnad1 id=finite.0h1v.s3.3f5e59a9e570 from=translated src=- shape=000de317 vocab=268c86c7
-/
theorem permWords_finite (k : ℕ) : {w | IsPermWord k w}.Finite := by
  have hset : {w | IsPermWord k w} = ↑(permsOf (Finset.Icc 1 k)) := by
    ext w
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, mem_permsOf]
    exact ⟨fun h => ⟨h.nodup, h.toFinset_eq⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [hset]; exact (permsOf _).finite_toSet

/-! ## `door`/`alphaWord` are permutations of the underlying word (closure lemmas) -/

/-- `door w` is a list-permutation of `w` (for `|w| ≥ 2`); hence preserves `IsPermWord`.
@isnad1 id=perm.1h1v.s4.06eac2ad7ed9 from=translated src=- shape=1690d7ff vocab=404caff9
-/
theorem door_perm {w : List ℕ} (hw : 2 ≤ w.length) : door w ~ w := by
  obtain ⟨a, b, s, rfl⟩ : ∃ a b s, w = a :: b :: s := by
    rcases w with _ | ⟨a, _ | ⟨b, s⟩⟩
    · simp at hw
    · simp at hw
    · exact ⟨a, b, s, rfl⟩
  have hdoor : door (a :: b :: s) = s ++ [b, a] := rfl
  rw [hdoor]
  calc s ++ [b, a] ~ [b, a] ++ s := List.perm_append_comm
    _ ~ [a, b] ++ s := ((List.Perm.swap b a []).append_right s).symm
    _ = a :: b :: s := rfl

/--
@isnad1 id=ispermwo.2h2v.s4.2c2a23f5bf53 from=translated src=- shape=6ea2118d vocab=e561e25d
-/
theorem door_isPermWord {k : ℕ} {w : List ℕ} (hk : 2 ≤ k) (hw : IsPermWord k w) :
    IsPermWord k (door w) :=
  hw.perm (door_perm (by rw [hw.length]; omega)).symm

/-- `alphaWord w` is a list-permutation of `w` (for `|w| ≥ 3`).
@isnad1 id=perm.0h1v.s3.0b3642331b99 from=translated src=- shape=77afba9e vocab=5eb1d6fb
-/
theorem alphaWord_perm {w : List ℕ} : alphaWord w ~ w := by
  have h1 : alphaWord w ~ w.drop 3 ++ w.take 3 :=
    (List.perm_append_left_iff _).mpr (List.reverse_perm _)
  have h2 : w.drop 3 ++ w.take 3 ~ w.take 3 ++ w.drop 3 := List.perm_append_comm
  rw [List.take_append_drop] at h2
  exact h1.trans h2

/--
@isnad1 id=ispermwo.1h2v.s3.7eb6efe7e30e from=translated src=- shape=cd29e5e1 vocab=3b8d8896
-/
theorem alphaWord_isPermWord {k : ℕ} {w : List ℕ} (hw : IsPermWord k w) :
    IsPermWord k (alphaWord w) :=
  hw.perm alphaWord_perm.symm

end Hunter
