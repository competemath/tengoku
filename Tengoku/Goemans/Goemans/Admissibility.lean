/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: Weaver (exploration and formalization); GPT-5.6 Sol (review).
-/
import Tengoku.Goemans.Goemans.Model

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Lemma 1: the admissibility structure of `H*`

Under a routing `S`, the load can exceed `x_a + D` only on the chain arcs
`s→u`, `u→v`, `v→w`; admissibility is equivalent to the three linear
inequalities of Lemma 1. Consequences: the empty routing and all singletons
are admissible, admissibility is downward closed, and blocked pairs/triples
yield the strict linear inequalities driving Lemmas 2 and 3.
-/

namespace Goemans

namespace FlowInstance

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
variable (I : FlowInstance K)

/-- **Lemma 1 (admissibility structure).** A routing `S` is admissible iff the
three chain-arc inequalities hold:
(i) `Σ_{i∈S∩{0,1}} dᵢ ≤ f₀ + f₁ + D` (arc `s→u`, after cancelling `d₂`);
(ii) `Σ_{i∈S} dᵢ ≤ f₀ + f₁ + f₂ + D` (arc `u→v`);
(iii) `Σ_{i∈S∩{1,2}} dᵢ ≤ f₁ + f₂ + D` (arc `v→w`).
@isnad1 id=iff.0h3v.s9.943145e5ea78 from=translated src=- shape=2d6155a5 vocab=10c787bd
-/
theorem admissible_iff (S : Finset Terminal) :
    I.Admissible S ↔
      ((if 0 ∈ S then I.d 0 else 0) + (if 1 ∈ S then I.d 1 else 0)
          ≤ I.f 0 + I.f 1 + I.dmax) ∧
      ((if 0 ∈ S then I.d 0 else 0) + (if 1 ∈ S then I.d 1 else 0) +
            (if 2 ∈ S then I.d 2 else 0)
          ≤ I.f 0 + I.f 1 + I.f 2 + I.dmax) ∧
      ((if 1 ∈ S then I.d 1 else 0) + (if 2 ∈ S then I.d 2 else 0)
          ≤ I.f 1 + I.f 2 + I.dmax) := by
  have hd0 := I.d_le_dmax 0
  have hd1 := I.d_le_dmax 1
  have hd2 := I.d_le_dmax 2
  have hf0 := I.f_nonneg 0
  have hf1 := I.f_nonneg 1
  have hf2 := I.f_nonneg 2
  have hfd0 := I.f_le_d 0
  have hfd1 := I.f_le_d 1
  have hfd2 := I.f_le_d 2
  constructor
  · intro h
    have h1 := h Arc.su
    have h2 := h Arc.uv
    have h3 := h Arc.vw
    rw [load_su, x_su] at h1
    rw [load_uv, x_uv] at h2
    rw [load_vw, x_vw] at h3
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩ a
    cases a <;>
      simp only [load_st1, load_st2, load_su, load_ut3, load_uv, load_vt1,
        load_vw, load_wt2, load_wt3, x_st1, x_st2, x_su, x_ut3, x_uv, x_vt1,
        x_vw, x_wt2, x_wt3] <;>
      split_ifs at h1 h2 h3 ⊢ <;> linarith

/-- The empty routing (everything expensive) is always admissible.
@isnad1 id=admissib.0h2v.s5.813fe7db6cb9 from=translated src=- shape=b4ab3652 vocab=bc975d5b
-/
theorem admissible_empty : I.Admissible ∅ := by
  rw [admissible_iff]
  have hf0 := I.f_nonneg 0
  have hf1 := I.f_nonneg 1
  have hf2 := I.f_nonneg 2
  have hD := I.dmax_pos
  simp only [Finset.notMem_empty, ite_false]
  refine ⟨by linarith, by linarith, by linarith⟩

private lemma adm_single0 : I.Admissible {0} := by
  rw [admissible_iff]
  have hd0 := I.d_le_dmax 0
  have hf0 := I.f_nonneg 0
  have hf1 := I.f_nonneg 1
  have hf2 := I.f_nonneg 2
  have hD := I.dmax_pos
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith

private lemma adm_single1 : I.Admissible {1} := by
  rw [admissible_iff]
  have hd1 := I.d_le_dmax 1
  have hf0 := I.f_nonneg 0
  have hf1 := I.f_nonneg 1
  have hf2 := I.f_nonneg 2
  have hD := I.dmax_pos
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith

private lemma adm_single2 : I.Admissible {2} := by
  rw [admissible_iff]
  have hd2 := I.d_le_dmax 2
  have hf0 := I.f_nonneg 0
  have hf1 := I.f_nonneg 1
  have hf2 := I.f_nonneg 2
  have hD := I.dmax_pos
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith

/-- Every singleton routing is admissible.
@isnad1 id=admissib.0h3v.s5.f6ed03267f7d from=translated src=- shape=4b34a79a vocab=a430570c
-/
theorem admissible_singleton (k : Terminal) : I.Admissible {k} := by
  fin_cases k
  exacts [adm_single0 I, adm_single1 I, adm_single2 I]

/-- Admissibility is downward closed (subsets of admissible sets are
admissible).
@isnad1 id=admissib.2h4v.s5.ac074185c560 from=translated src=- shape=d67059e7 vocab=e1cc8ec9
-/
theorem admissible_mono {S T : Finset Terminal} (hST : S ⊆ T)
    (hT : I.Admissible T) : I.Admissible S := by
  rw [admissible_iff] at hT ⊢
  have key : ∀ i : Terminal,
      (if i ∈ S then I.d i else 0) ≤ (if i ∈ T then I.d i else 0) := by
    intro i
    split_ifs with h1 h2
    · exact le_refl _
    · exact absurd (hST h1) h2
    · exact le_of_lt (I.d_pos i)
    · exact le_refl _
  obtain ⟨h1, h2, h3⟩ := hT
  exact ⟨by linarith [key 0, key 1], by linarith [key 0, key 1, key 2],
    by linarith [key 1, key 2]⟩

/-! ### Blocked pairs and the blocked triple

`{i, j}` is *blocked* when the routing `{i, j}` is inadmissible. The
following extraction lemmas retain the strict inequalities supplied by
inadmissibility. Closed variants are provided for compatibility with the
non-strict upper-bound argument. -/

/--
@isnad1 id=lt.1h2v.s7.a4ccb9e5b34a from=translated src=- shape=011683e9 vocab=075bdffd
-/
theorem blocked_pair01_lt (h : ¬ I.Admissible {0, 1}) :
    I.f 0 + I.f 1 < I.d 0 + I.d 1 - I.dmax := by
  by_contra! hc
  refine h ?_
  rw [admissible_iff]
  have hd1 := I.d_le_dmax 1
  have hf1 := I.f_nonneg 1
  have hf2 := I.f_nonneg 2
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith

/--
@isnad1 id=le.1h2v.s7.610e32456297 from=translated src=- shape=011683e9 vocab=d158f80c
-/
theorem blocked_pair01 (h : ¬ I.Admissible {0, 1}) :
    I.f 0 + I.f 1 ≤ I.d 0 + I.d 1 - I.dmax :=
  (I.blocked_pair01_lt h).le

/--
@isnad1 id=lt.1h2v.s7.b6197787be44 from=translated src=- shape=011683e9 vocab=075bdffd
-/
theorem blocked_pair12_lt (h : ¬ I.Admissible {1, 2}) :
    I.f 1 + I.f 2 < I.d 1 + I.d 2 - I.dmax := by
  by_contra! hc
  refine h ?_
  rw [admissible_iff]
  have hd1 := I.d_le_dmax 1
  have hf0 := I.f_nonneg 0
  have hf1 := I.f_nonneg 1
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith

/--
@isnad1 id=le.1h2v.s7.2a00b8fe81fc from=translated src=- shape=011683e9 vocab=d158f80c
-/
theorem blocked_pair12 (h : ¬ I.Admissible {1, 2}) :
    I.f 1 + I.f 2 ≤ I.d 1 + I.d 2 - I.dmax :=
  (I.blocked_pair12_lt h).le

/--
@isnad1 id=lt.1h2v.s7.747a5e642e61 from=translated src=- shape=ddf38934 vocab=075bdffd
-/
theorem blocked_pair02_lt (h : ¬ I.Admissible {0, 2}) :
    I.f 0 + I.f 1 + I.f 2 < I.d 0 + I.d 2 - I.dmax := by
  by_contra! hc
  refine h ?_
  rw [admissible_iff]
  have hd0 := I.d_le_dmax 0
  have hd2 := I.d_le_dmax 2
  have hf0 := I.f_nonneg 0
  have hf1 := I.f_nonneg 1
  have hf2 := I.f_nonneg 2
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith

/--
@isnad1 id=le.1h2v.s7.75c9df037f98 from=translated src=- shape=ddf38934 vocab=d158f80c
-/
theorem blocked_pair02 (h : ¬ I.Admissible {0, 2}) :
    I.f 0 + I.f 1 + I.f 2 ≤ I.d 0 + I.d 2 - I.dmax :=
  (I.blocked_pair02_lt h).le

/-- If both `{0,1}` and `{1,2}` are admissible but the full routing is
blocked, then constraint (ii) fails for the triple: the total demand exceeds
the total cheap flow plus `D` (strictly).
@isnad1 id=lt.3h2v.s8.44a0313d83c4 from=translated src=- shape=e0691c72 vocab=36ac559e
-/
theorem blocked_triple (h01 : I.Admissible {0, 1}) (h12 : I.Admissible {1, 2})
    (h : ¬ I.Admissible Finset.univ) :
    I.f 0 + I.f 1 + I.f 2 + I.dmax < I.d 0 + I.d 1 + I.d 2 := by
  by_contra! hc
  refine h ?_
  rw [admissible_iff] at h01 h12 ⊢
  have h01a :
      I.d 0 + I.d 1 ≤ I.f 0 + I.f 1 + I.dmax := by
    simpa using h01.1
  have h12c :
      I.d 1 + I.d 2 ≤ I.f 1 + I.f 2 + I.dmax := by
    simpa using h12.2.2
  have hall :
      I.d 0 + I.d 1 ≤ I.f 0 + I.f 1 + I.dmax ∧
        I.d 0 + I.d 1 + I.d 2 ≤
          I.f 0 + I.f 1 + I.f 2 + I.dmax ∧
        I.d 1 + I.d 2 ≤ I.f 1 + I.f 2 + I.dmax :=
    ⟨h01a, hc, h12c⟩
  simpa using hall

end FlowInstance

end Goemans
