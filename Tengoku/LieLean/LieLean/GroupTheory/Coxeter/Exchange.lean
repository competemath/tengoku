/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.Seed.GroupTheory.Coxeter.Inversion
import Tengoku.Seed.Tactic.IntervalCases
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The strong exchange condition for Coxeter systems

For a Coxeter system `(W, S)` (Mathlib's `CoxeterSystem`) we prove the strong exchange condition:
if `ω` is a reduced word and `t` is a reflection with `ℓ(π ω * t) < ℓ(π ω)`, then `t` occurs in
the right inversion sequence of `ω`, hence `π ω * t` is obtained from `ω` by deleting one letter.
As a consequence we obtain the lemma on which the construction of the Iwahori–Hecke algebra
rests: if `ℓ(s w t) = ℓ(w)` and `ℓ(s w) = ℓ(w t)` for simple reflections `s, t`, then
`s w = w t`.

The proof is the one of [BB] §§1.3–1.4 via the *reflection representation*: the simple reflections
act on `W × ZMod 2` by `s • (t, ε) = (s t s, ε + [t = s])`. These permutations satisfy the Coxeter
relations (the key point is that the right inversion sequence of the word `(s s')^m`, for
`m = m(s, s')`, is periodic of period `m`), so they define an action of `W`, and the second
coordinate of `w • (t, 0)` counts, modulo `2`, the occurrences of `t` in the right inversion
sequence of any word for `w`.

## Main definitions

* `CoxeterSystem.reflRep`: the action of `W` on `W × ZMod 2` (cf. [BB] Thm. 1.3.2, on `T × {±1}`).
* `CoxeterSystem.inversionParity`: `n(w, t) ∈ ZMod 2`, the parity of the number of occurrences
  of `t` in the right inversion sequence of a word for `w`.

## Main results

* `CoxeterSystem.mem_rightInvSeq_iff`: for a reduced word `ω` and a reflection `t`,
  `t ∈ ris ω ↔ ℓ(π ω * t) < ℓ(π ω)` (strong exchange condition, [BB] Thm. 1.4.3, Cor. 1.4.4;
  [HumC] §5.8).
* `CoxeterSystem.exists_mul_eq_wordProd_eraseIdx`: the (strong) exchange condition in the form
  `π ω * t = π (ω.eraseIdx j)`.
* `CoxeterSystem.simple_mul_eq_mul_simple`: if `ℓ(s w t) = ℓ(w)` and `ℓ(s w) = ℓ(w t)` then
  `s w = w t` ([GP] Lemma 1.2.6).
* `CoxeterSystem.induction_mul_simple`, `CoxeterSystem.induction_simple_mul`: induction along
  reduced words.

## References

* [BB] A. Björner, F. Brenti, *Combinatorics of Coxeter groups*, GTM 231, §§1.3–1.4.
* [HumC] J. E. Humphreys, *Reflection groups and Coxeter groups*, CUP 1990, §5.8.
* [GP] M. Geck, G. Pfeiffer, *Characters of finite Coxeter groups and Iwahori–Hecke algebras*,
  LMS Monographs 21, OUP 2000, Lemma 1.2.6.
-/

namespace CoxeterSystem

open List

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd
local prefix:100 "ℓ " => cs.length
local prefix:100 "ris " => cs.rightInvSeq
local prefix:100 "lis " => cs.leftInvSeq

/--
@isnad1 id=eq.0h6v.s6.1d1798290a93 from=translated src=- shape=1278724e vocab=33565f1e
-/
theorem rightInvSeq_cons (i : B) (ω : List B) :
    ris (i :: ω) = (π ω)⁻¹ * s i * π ω :: ris ω := rfl

/-- Conjugating the right inversion sequence of `ω` by `π ω` gives its left inversion
sequence.
@isnad1 id=eq.0h5v.s8.c777e0bd6cb5 from=translated src=- shape=3c7e0ec2 vocab=ebef5631
-/
theorem map_conj_rightInvSeq (ω : List B) : (ris ω).map (MulAut.conj (π ω)) = lis ω := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [rightInvSeq, leftInvSeq, ← ih, wordProd_cons, map_cons, map_map]
    congr 1
    · simp only [MulAut.conj_apply]
      group
    · congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]

/-- If `π ω = 1`, the left and right inversion sequences of `ω` agree.
@isnad1 id=eq.1h5v.s5.35ad5ea2b934 from=translated src=- shape=0811d25f vocab=235ca906
-/
theorem rightInvSeq_eq_leftInvSeq_of_wordProd_eq_one {ω : List B} (h : π ω = 1) :
    ris ω = lis ω := by
  rw [← map_conj_rightInvSeq, h, map_one]
  simp

/--
@isnad1 id=eq.0h7v.s6.e31638d68348 from=translated src=- shape=fec9e8b3 vocab=79f1ddf2
-/
theorem wordProd_alternatingWord_two_mul (i i' : B) (m : ℕ) :
    π (alternatingWord i i' (2 * m)) = (s i * s i') ^ m := by
  rw [prod_alternatingWord_eq_mul_pow]
  simp

/--
@isnad1 id=eq.0h6v.s6.32abbd41c194 from=translated src=- shape=47c684f6 vocab=62762cd0
-/
theorem prod_map_alternatingWord_two_mul {G : Type*} [Monoid G] (f : B → G) (i i' : B) (m : ℕ) :
    ((alternatingWord i i' (2 * m)).map f).prod = (f i * f i') ^ m := by
  induction m with
  | zero => simp [alternatingWord]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, alternatingWord_succ, alternatingWord_succ]
    simp [ih, pow_succ]

section reflRep

variable [DecidableEq W]

/-- The number of occurrences of any element in the right inversion sequence of the braid word
`(s s')^{m(s,s')}` is even.
@isnad1 id=even.0h7v.s5.bfe62e94198c from=translated src=- shape=6f1e871c vocab=d3b39238
-/
theorem even_count_rightInvSeq_alternatingWord (i i' : B) (t : W) :
    Even ((ris (alternatingWord i i' (2 * M i i'))).count t) := by
  set p := M i i'
  set L := ris (alternatingWord i i' (2 * p))
  have hπ : π (alternatingWord i i' (2 * p)) = 1 := by
    rw [wordProd_alternatingWord_two_mul, cs.simple_mul_simple_pow]
  have hL : L = lis (alternatingWord i i' (2 * p)) :=
    cs.rightInvSeq_eq_leftInvSeq_of_wordProd_eq_one hπ
  have hlen : L.length = 2 * p := by simp [L]
  have hdrop : L.drop p = L.take p := by
    apply List.ext_getElem (by simp [hlen]; lia)
    intro k h₁ h₂
    have hk : k < p := by simp [hlen] at h₂; lia
    simp only [getElem_drop, getElem_take]
    simp only [L, hL]
    rw [cs.getElem_leftInvSeq_alternatingWord i i' p (p + k) (by lia),
      cs.getElem_leftInvSeq_alternatingWord i i' p k (by lia), prod_alternatingWord_eq_mul_pow,
      prod_alternatingWord_eq_mul_pow]
    have e₁ : (2 * (p + k) + 1) / 2 = k + p := by lia
    have e₂ : (2 * k + 1) / 2 = k := by lia
    have hp : (s i' * s i) ^ p = 1 := by
      simp only [p, M.symmetric i i', cs.simple_mul_simple_pow]
    rw [e₁, e₂, pow_add, hp, mul_one]
    have o₁ : ¬ Even (2 * (p + k) + 1) := by simp [parity_simps]
    have o₂ : ¬ Even (2 * k + 1) := by simp [parity_simps]
    simp [o₁, o₂]
  rw [← List.take_append_drop p L, hdrop, List.count_append]
  exact ⟨_, rfl⟩

/-- The permutation of `W × ZMod 2` attached to the simple reflection `s i`:
`(t, ε) ↦ (s t s, ε + [t = s])` ([BB] §1.3).-/
def reflPerm (i : B) : Equiv.Perm (W × ZMod 2) :=
  Function.Involutive.toPerm
    (fun x ↦ (s i * x.1 * s i, x.2 + if x.1 = s i then 1 else 0)) <| by
      rintro ⟨t, ε⟩
      have h : s i * t * s i = s i ↔ t = s i := by
        constructor
        · intro h
          have := congrArg (fun x ↦ s i * x * s i) h
          simpa [mul_assoc] using this
        · rintro rfl
          simp
      ext
      · simp [← mul_assoc]
      · simp only [h, add_assoc]
        split_ifs <;> simp [show (1 : ZMod 2) + 1 = 0 from rfl]

/--
@isnad1 id=eq.0h6v.s8.f19130bc46ca from=translated src=- shape=9b176c67 vocab=c2589649
-/
theorem reflPerm_apply (i : B) (x : W × ZMod 2) :
    cs.reflPerm i x = (s i * x.1 * s i, x.2 + if x.1 = s i then 1 else 0) := rfl

/--
@isnad1 id=eq.0h7v.s8.c24849f85996 from=translated src=- shape=bfa369f1 vocab=2cd87da1
-/
theorem prod_map_reflPerm_apply (ω : List B) (t : W) (ε : ZMod 2) :
    (ω.map cs.reflPerm).prod (t, ε) = (π ω * t * (π ω)⁻¹, ε + ((ris ω).count t : ZMod 2)) := by
  induction ω generalizing t ε with
  | nil => simp
  | cons i ω ih =>
    rw [map_cons, prod_cons, Equiv.Perm.mul_apply, ih, reflPerm_apply, wordProd_cons,
      rightInvSeq_cons, count_cons]
    have h : π ω * t * (π ω)⁻¹ = s i ↔ ((π ω)⁻¹ * s i * π ω == t) = true := by
      rw [beq_iff_eq]
      constructor
      · rintro h; rw [← h]; group
      · rintro h; rw [← h]; group
    ext
    · simp only [mul_inv_rev, inv_simple]
      group
    · simp only [h]
      split_ifs <;> push_cast <;> ring

/--
@isnad1 id=isliftab.0h4v.s6.bad1e510f945 from=translated src=- shape=4e96aa09 vocab=40b5a377
-/
theorem isLiftable_reflPerm : M.IsLiftable cs.reflPerm := by
  intro i i'
  ext ⟨t, ε⟩ : 1
  rw [← prod_map_alternatingWord_two_mul, prod_map_reflPerm_apply,
    wordProd_alternatingWord_two_mul, cs.simple_mul_simple_pow]
  obtain ⟨k, hk⟩ := cs.even_count_rightInvSeq_alternatingWord i i' t
  rw [hk]
  simp only [one_mul, inv_one, mul_one, Nat.cast_add, Equiv.Perm.coe_one, id_eq]
  congr 1
  rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]

/-- The reflection representation of `W` on `W × ZMod 2`, `s • (t, ε) = (s t s, ε + [t = s])`
(cf. [BB] Thm. 1.3.2, where it acts on `T × {±1}`).-/
def reflRep : W →* Equiv.Perm (W × ZMod 2) := cs.lift ⟨cs.reflPerm, cs.isLiftable_reflPerm⟩

/--
@isnad1 id=eq.0h5v.s7.4b15e71bf25a from=translated src=- shape=e9284e3e vocab=ab4babe1
-/
theorem reflRep_simple (i : B) : cs.reflRep (s i) = cs.reflPerm i :=
  cs.lift_apply_simple cs.isLiftable_reflPerm i

/--
@isnad1 id=eq.0h5v.s7.2d87ec2a46be from=translated src=- shape=b8b6f1b9 vocab=82fe3884
-/
theorem reflRep_wordProd (ω : List B) : cs.reflRep (π ω) = (ω.map cs.reflPerm).prod := by
  rw [wordProd, map_list_prod, map_map]
  congr 1
  exact List.map_congr_left fun i _ ↦ cs.reflRep_simple i

/-- `n(w, t) ∈ ZMod 2`: the parity of the number of occurrences of `t` in the right inversion
sequence of any word for `w`. [BB] §1.3 count occurrences in left inversion sequences instead
((1.13), (1.17)), so `(-1)^{n(w, t)}` is their `η(w⁻¹; t)` (compare `reflRep_apply` with (1.18)).-/
def inversionParity (w t : W) : ZMod 2 := (cs.reflRep w (t, 0)).2

/--
@isnad1 id=eq.0h6v.s6.4b03947b8843 from=translated src=- shape=53df9b11 vocab=a3c290a8
-/
theorem inversionParity_wordProd (ω : List B) (t : W) :
    cs.inversionParity (π ω) t = (ris ω).count t := by
  simp [inversionParity, reflRep_wordProd, prod_map_reflPerm_apply]

/--
@isnad1 id=eq.0h7v.s8.abd3646e67f7 from=translated src=- shape=9174cbf2 vocab=bddf9d4b
-/
theorem reflRep_apply (w t : W) (ε : ZMod 2) :
    cs.reflRep w (t, ε) = (w * t * w⁻¹, ε + cs.inversionParity w t) := by
  obtain ⟨ω, -, rfl⟩ := cs.exists_isReduced w
  rw [inversionParity_wordProd, reflRep_wordProd, prod_map_reflPerm_apply]

/--
@isnad1 id=eq.0h5v.s6.7c12a381eb6b from=translated src=- shape=ecfe1c46 vocab=0448854b
-/
theorem inversionParity_one (t : W) : cs.inversionParity 1 t = 0 := by
  simp [inversionParity]

/-- The cocycle property of `n`.
@isnad1 id=eq.0h7v.s7.eb2b9d3f16f1 from=translated src=- shape=f89e2569 vocab=987e162d
-/
theorem inversionParity_mul (u v t : W) :
    cs.inversionParity (u * v) t = cs.inversionParity v t + cs.inversionParity u (v * t * v⁻¹) := by
  have := cs.reflRep_apply (u * v) t 0
  rw [map_mul, Equiv.Perm.mul_apply, reflRep_apply, reflRep_apply] at this
  simpa using (congrArg Prod.snd this).symm

/--
@isnad1 id=eq.0h6v.s7.87d01d7ae1d1 from=translated src=- shape=1cf15f9e vocab=336760d7
-/
theorem inversionParity_simple (i : B) (t : W) :
    cs.inversionParity (s i) t = if t = s i then 1 else 0 := by
  simp [inversionParity, reflRep_simple, reflPerm_apply]

/--
@isnad1 id=eq.1h5v.s6.0f33342032e3 from=translated src=- shape=10b4a512 vocab=d53cfd61
-/
theorem inversionParity_self {t : W} (ht : cs.IsReflection t) : cs.inversionParity t t = 1 := by
  obtain ⟨u, i, rfl⟩ := ht
  have h₁ := cs.inversionParity_mul (u * s i) u⁻¹ (u * s i * u⁻¹)
  have h₂ := cs.inversionParity_mul u (s i) (u⁻¹ * (u * s i * u⁻¹) * u⁻¹⁻¹)
  have h₃ := cs.inversionParity_mul u u⁻¹ (u * s i * u⁻¹)
  have e : u⁻¹ * (u * s i * u⁻¹) * u⁻¹⁻¹ = s i := by group
  have e' : s i * s i * (s i)⁻¹ = s i := by group
  rw [e, cs.inversionParity_simple, e'] at h₂
  simp only [↓reduceIte] at h₂
  rw [e] at h₁
  rw [mul_inv_cancel, inversionParity_one, e] at h₃
  rw [h₁, h₂]
  linear_combination -h₃

/--
@isnad1 id=eq.1h6v.s7.3dcab70d07df from=translated src=- shape=f2924845 vocab=3ed7be84
-/
theorem inversionParity_mul_self {t : W} (ht : cs.IsReflection t) (w : W) :
    cs.inversionParity (w * t) t = 1 + cs.inversionParity w t := by
  rw [inversionParity_mul, inversionParity_self cs ht]
  congr 2
  group

/--
@isnad1 id=iff.1h6v.s6.57e3a797311c from=translated src=- shape=28039c08 vocab=4ee831e9
-/
theorem inversionParity_eq_one_iff {ω : List B} (hω : cs.IsReduced ω) (t : W) :
    cs.inversionParity (π ω) t = 1 ↔ t ∈ ris ω := by
  rw [inversionParity_wordProd, ← List.count_pos_iff]
  have := List.nodup_iff_count_le_one.mp hω.nodup_rightInvSeq t
  interval_cases h : (ris ω).count t <;> simp

end reflRep

/-- The strong exchange condition: for a reduced word `ω`, the right inversions of `π ω` are
exactly the entries of the right inversion sequence of `ω` ([BB] Cor. 1.4.4,
[HumC] §5.8).
@isnad1 id=iff.1h6v.s5.055c491b864f from=translated src=- shape=1e2527ec vocab=0719ccd0
-/
theorem mem_rightInvSeq_iff {ω : List B} (hω : cs.IsReduced ω) {t : W} :
    t ∈ ris ω ↔ cs.IsRightInversion (π ω) t := by
  classical
  refine ⟨cs.isRightInversion_of_mem_rightInvSeq hω, fun ⟨ht, hlt⟩ ↦ ?_⟩
  by_contra hmem
  rw [← inversionParity_eq_one_iff cs hω] at hmem
  have h0 : cs.inversionParity (π ω) t = 0 := by
    generalize cs.inversionParity (π ω) t = x at hmem
    revert x; decide
  obtain ⟨ω', hω', he⟩ := cs.exists_isReduced (π ω * t)
  have h1 : cs.inversionParity (π ω') t = 1 := by
    rw [← he, inversionParity_mul_self cs ht, h0, add_zero]
  rw [inversionParity_eq_one_iff cs hω'] at h1
  have := (cs.isRightInversion_of_mem_rightInvSeq hω' h1).2
  rw [← he, mul_assoc, ht.mul_self, mul_one] at this
  lia

/-- The strong exchange condition: if `ω` is reduced and `t` is a reflection with
`ℓ(π ω * t) < ℓ(π ω)`, then `π ω * t` is obtained from `ω` by deleting a letter
([BB] Thm. 1.4.3).
@isnad1 id=ex.2h6v.s7.b43934131b4f from=translated src=- shape=150516c5 vocab=855d00a0
-/
theorem exists_mul_eq_wordProd_eraseIdx {ω : List B} (hω : cs.IsReduced ω) {t : W}
    (ht : cs.IsRightInversion (π ω) t) :
    ∃ (j : ℕ) (hj : j < ω.length), t = (ris ω)[j]'(by simpa using hj) ∧
      π ω * t = π (ω.eraseIdx j) := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ((cs.mem_rightInvSeq_iff hω).mpr ht)
  refine ⟨j, by simpa using hj, rfl, ?_⟩
  rw [← cs.wordProd_mul_getD_rightInvSeq, List.getD_eq_getElem]

/-- If `ℓ(s w t) = ℓ(w)` and `ℓ(s w) = ℓ(w t)` for simple reflections `s = sᵢ`, `t = sⱼ`, then
`s w = w t` ([GP] Lemma 1.2.6; the proof uses the exchange condition).
@isnad1 id=eq.2h7v.s7.27154bc3e5d2 from=translated src=- shape=1ba3fcdb vocab=45d3276f
-/
theorem simple_mul_eq_mul_simple {i j : B} {w : W} (h₁ : ℓ (s i * w * s j) = ℓ w)
    (h₂ : ℓ (s i * w) = ℓ (w * s j)) : s i * w = w * s j := by
  -- First the case `ℓ(s w) > ℓ(w)`.
  have key : ∀ w : W, ℓ (s i * w * s j) = ℓ w → ℓ (s i * w) = ℓ (w * s j) →
      ℓ w < ℓ (s i * w) → s i * w = w * s j := by
    intro w h₁ h₂ hlt
    obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    have hω' : cs.IsReduced (i :: ω) := by
      rw [IsReduced, wordProd_cons, length_cons]
      rcases cs.length_simple_mul (π ω) i with h | h
      · rw [h, hω.eq]
      · lia
    have hinv : cs.IsRightInversion (π (i :: ω)) (s j) := by
      refine ⟨cs.isReflection_simple j, ?_⟩
      rw [wordProd_cons, h₁]
      exact hlt
    rw [← mem_rightInvSeq_iff cs hω', rightInvSeq_cons, mem_cons] at hinv
    rcases hinv with h | h
    · rw [h]; group
    · have := (cs.isRightInversion_of_mem_rightInvSeq hω h).2
      lia
  rcases cs.length_simple_mul w i with h | h
  · exact key w h₁ h₂ (by lia)
  · -- Apply the first case to `w' = s w`.
    have h' := key (s i * w) (by rw [simple_mul_simple_cancel_left, h₂])
      (by rw [simple_mul_simple_cancel_left, h₁])
      (by rw [simple_mul_simple_cancel_left]; lia)
    rw [simple_mul_simple_cancel_left] at h'
    nth_rewrite 1 [h']
    simp only [← mul_assoc, simple_mul_simple_self, one_mul]

/-! ### Induction on the length -/

/-- Induction along reduced words, adding simple reflections on the right: a property that holds
for `1` and passes from `w` to `w sᵢ` whenever `ℓ(w sᵢ) > ℓ(w)` holds for all `w`.
@isnad1 id=var.0h8v.s6.7dc592aff5bf from=translated src=- shape=bb83a583 vocab=17d9ffd0
-/
theorem induction_mul_simple {p : W → Prop} (one : p 1)
    (mul_simple : ∀ w i, ℓ w < ℓ (w * s i) → p w → p (w * s i)) (w : W) : p w := by
  induction h : ℓ w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    rcases eq_or_ne w 1 with rfl | hw
    · exact one
    obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hw
    have e : w * s i * s i = w := cs.simple_mul_simple_cancel_right i
    rw [← e]
    refine mul_simple _ i (by rw [e]; exact hi) (ih _ ?_ _ rfl)
    rw [← h]
    exact hi

/-- Induction along reduced words, adding simple reflections on the left: a property that holds
for `1` and passes from `w` to `sᵢ w` whenever `ℓ(sᵢ w) > ℓ(w)` holds for all `w`.
@isnad1 id=var.0h8v.s6.2d633859d040 from=translated src=- shape=a00c2ae1 vocab=17d9ffd0
-/
theorem induction_simple_mul {p : W → Prop} (one : p 1)
    (simple_mul : ∀ w i, ℓ w < ℓ (s i * w) → p w → p (s i * w)) (w : W) : p w := by
  induction h : ℓ w using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    rcases eq_or_ne w 1 with rfl | hw
    · exact one
    obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hw
    have e : s i * (s i * w) = w := cs.simple_mul_simple_cancel_left i
    rw [← e]
    refine simple_mul _ i (by rw [e]; exact hi) (ih _ ?_ _ rfl)
    rw [← h]
    exact hi

end CoxeterSystem
