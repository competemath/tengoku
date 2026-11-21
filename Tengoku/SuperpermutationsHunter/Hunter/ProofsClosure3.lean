/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uku Raudvere
-/
import Tengoku.SuperpermutationsHunter.Hunter.Words
import Tengoku.SuperpermutationsHunter.Hunter.Graph
import Tengoku.SuperpermutationsHunter.Hunter.ProofsConfinement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hunter Theorem 2, §3 — the CLOSURE LEMMA (`Hunter/ProofsClosure3.lean`)

The deterministic τ₂/τ₃ chart of Hunter §3 runs `m − 1 = k − 3` complete weight-2 loops of
length `k − 1` (the "runs"), stepped between by the fresh weight-3 door τ₃.  At the very end of
the last run the chart reaches a **final exit** `x`.  This file proves, purely at the word /
rotation-class level, that **every weight-2 and weight-3 successor of `x` lies in a rotation
class the chart has already visited**; hence any continuation edge from `x` to an *unvisited*
class has weight `≥ 4`.

## Conventions (Hunter/Words.lean), and the port from `PROOF_S3.md` (document *s3a*)

`rho = rotate 1` is Hunter's `σ`; `door w = w.drop 2 ++ [w[1],w[0]]` is Hunter's `τ`; the block
**exit** of an entry `u` is `u.rotate (k−1)` (right rotation).  The chart's *fresh* weight-2
step is `door ∘ exit`, which is exactly *s3a*'s `tau2` (rotate the first `k−1` letters, fix the
last).  We port *s3a*'s chart-entry formula `C_{j,i} = rot_i(P_j b) c`.

Parametrization (`campaign/closure3/calib.py`, verified k = 4..8, our conventions).  Write the
start as `A' ++ [z, b, c]` where `A' = a₁…a_{m-1}`, `z = aₘ`, `b = a_{k-1}`, `c = a_k`.  Put
`n := A'.length` (`= k − 3`), so `k = n + 3` and `m := n + 1 = k − 2`, and `A := A' ++ [z]`
(`= a₁…aₘ`).  Then:
* chart entry `chartWord A' z b c j i = ((A.rotate j ++ [b]).rotate i) ++ [c]  (= C_{j,i})`,
* final exit `finalExit A' z b c = c :: b :: z :: A'  (= exit(C_{m-1,m}))`.

Every displayed identity reduces to `List.rotate_append_length_eq`.

All results are `sorry`-free and introduce no new axioms.
-/

namespace Hunter.ProofsClosure3

open List Hunter

/-- The chart entry `C_{j,i} = rot_i(P_j b) c` in our parametrization, where `P_j = A.rotate j`
and `A = A' ++ [z]`.  See the module docstring.-/
def chartWord (A' : List ℕ) (z b c : ℕ) (j i : ℕ) : List ℕ :=
  (((A' ++ [z]).rotate j ++ [b]).rotate i) ++ [c]

/-- The final exit `x = c b aₘ a₁…a_{m-1}` of the completed chart (`= exit(C_{m-1,m})`).-/
def finalExit (A' : List ℕ) (z b c : ℕ) : List ℕ := c :: b :: z :: A'

variable (A' : List ℕ) (z b c : ℕ)

/-- `rotClass` is invariant under `rotate` (a rotation is a rotation).
@isnad1 id=eq.0h2v.s3.fc9d9f6b712f from=translated src=- shape=3f6df2cf vocab=6c177b7f
-/
theorem rotClass_rotate (w : List ℕ) (n : ℕ) : rotClass (w.rotate n) = rotClass w :=
  Quotient.sound (List.IsRotated.forall w n)

/-! ## Closed forms of the six chart entries used in the closure identities

Chart index witnesses (in `[0,m) × [0,m]`, `m = n+1`): `(0,0)`, `(0,n)=(0,m-1)`, `(0,n+1)=(0,m)`,
`(n,0)=(m-1,0)`, `(n,1)=(m-1,1)`, `(n,n+1)=(m-1,m)`. -/

/--
@isnad1 id=eq.0h4v.s5.beb8524f74cb from=translated src=- shape=af599744 vocab=e01a41fa
-/
theorem chartWord_00 : chartWord A' z b c 0 0 = A' ++ [z, b, c] := by
  simp [chartWord, List.rotate_zero, List.append_assoc]

/--
@isnad1 id=eq.0h4v.s5.c4d20b6c599f from=translated src=- shape=cbe7bf19 vocab=830e912d
-/
theorem chartWord_0n : chartWord A' z b c 0 A'.length = z :: b :: A' ++ [c] := by
  unfold chartWord
  rw [List.rotate_zero, show (A' ++ [z]) ++ [b] = A' ++ [z, b] by simp,
    List.rotate_append_length_eq]
  rfl

/--
@isnad1 id=eq.0h4v.s5.c5372230e9ad from=translated src=- shape=7b14dcfe vocab=a73a2be6
-/
theorem chartWord_0n1 :
    chartWord A' z b c 0 (A'.length + 1) = b :: A' ++ [z, c] := by
  unfold chartWord
  rw [List.rotate_zero, show A'.length + 1 = (A' ++ [z]).length by simp,
    List.rotate_append_length_eq]
  simp [List.append_assoc]

/--
@isnad1 id=eq.0h4v.s5.10ce0d01bda5 from=translated src=- shape=a327e386 vocab=830e912d
-/
theorem chartWord_n0 : chartWord A' z b c A'.length 0 = z :: A' ++ [b, c] := by
  unfold chartWord
  rw [List.rotate_append_length_eq, List.rotate_zero]
  simp [List.append_assoc]

/--
@isnad1 id=eq.0h4v.s5.8710ee8dc19e from=translated src=- shape=c38800ef vocab=830e912d
-/
theorem chartWord_n1 : chartWord A' z b c A'.length 1 = A' ++ [b, z, c] := by
  unfold chartWord
  rw [List.rotate_append_length_eq,
    show ([z] ++ A') ++ [b] = [z] ++ (A' ++ [b]) by simp,
    show (1 : ℕ) = ([z] : List ℕ).length from rfl, List.rotate_append_length_eq]
  simp

/--
@isnad1 id=eq.0h4v.s5.695159bb930c from=translated src=- shape=e03ef74f vocab=a73a2be6
-/
theorem chartWord_nn1 :
    chartWord A' z b c A'.length (A'.length + 1) = b :: z :: A' ++ [c] := by
  unfold chartWord
  rw [List.rotate_append_length_eq,
    show A'.length + 1 = ([z] ++ A').length by simp, List.rotate_append_length_eq]
  simp

/-! ## `door` and `σ²` of the final exit -/

/-- The fresh weight-2 successor of `x`: `door x = z A' b c  (= C_{m-1,0})`.
@isnad1 id=eq.0h4v.s5.ffa218edc4b1 from=translated src=- shape=af7edb5a vocab=4dc3fc34
-/
theorem door_finalExit : door (finalExit A' z b c) = z :: A' ++ [b, c] := rfl

/-- The `σ²` weight-2 successor of `x`: `x.rotate 2 = z A' c b`.
@isnad1 id=eq.0h4v.s5.c30da342df35 from=translated src=- shape=16aa1c8b vocab=80901b79
-/
theorem rotate2_finalExit : (finalExit A' z b c).rotate 2 = z :: A' ++ [c, b] := by
  rw [show finalExit A' z b c = [c, b] ++ (z :: A') from rfl,
    show (2 : ℕ) = ([c, b] : List ℕ).length from rfl, List.rotate_append_length_eq]

/-- `x` itself is a rotation of the last chart entry: `x.rotate 1 = C_{m-1,m}`.
@isnad1 id=eq.0h4v.s5.c8e71dca35bc from=translated src=- shape=00de4308 vocab=3918aa71
-/
theorem finalExit_rotate1 :
    (finalExit A' z b c).rotate 1 = chartWord A' z b c A'.length (A'.length + 1) := by
  rw [chartWord_nn1]
  rw [show finalExit A' z b c = [c] ++ (b :: z :: A') from rfl,
    show (1 : ℕ) = ([c] : List ℕ).length from rfl, List.rotate_append_length_eq]

/-! ## Permutation-word transfer for the final exit -/

/-- The final exit is a list-permutation of the start `A' ++ [z,b,c]`.
@isnad1 id=perm.0h4v.s5.6beb8dd17aa3 from=translated src=- shape=8a5dd56a vocab=9a3cc0b0
-/
theorem perm_finalExit_start : (finalExit A' z b c) ~ (A' ++ [z, b, c]) := by
  show c :: b :: z :: A' ~ A' ++ [z, b, c]
  have h1 : c :: b :: z :: A' ~ A' ++ [c, b, z] :=
    (List.perm_append_comm (l₁ := A') (l₂ := [c, b, z])).symm
  refine h1.trans (List.Perm.append_left A' ?_)
  -- [c, b, z] ~ [z, b, c]
  exact (List.Perm.cons c (List.Perm.swap z b [])).trans
    ((List.Perm.swap z c [b]).trans (List.Perm.cons z (List.Perm.swap b c [])))

/-- Hence the final exit is a permutation word whenever the start is.
@isnad1 id=ispermwo.1h4v.s6.048fd4b5a965 from=translated src=- shape=b5fae1ff vocab=d58abd92
-/
theorem isPermWord_finalExit (hs : IsPermWord (A'.length + 3) (A' ++ [z, b, c])) :
    IsPermWord (A'.length + 3) (finalExit A' z b c) :=
  hs.perm (perm_finalExit_start A' z b c).symm

/-! ## The chart-visited predicate and the closure identities

`VisitedByChart K` says `K` is the rotation class of some honest chart entry `C_{j,i}`,
`0 ≤ j < m = n+1`, `0 ≤ i ≤ m` (`n = A'.length`). -/

/-- `K` is a rotation class visited by the chart.-/
def VisitedByChart (A' : List ℕ) (z b c : ℕ) (K : RotClass) : Prop :=
  ∃ j i, j ≤ A'.length ∧ i ≤ A'.length + 1 ∧ K = rotClass (chartWord A' z b c j i)

/-- The final exit's own class is visited (`x.rotate 1 = C_{m-1,m}`).
@isnad1 id=visitedb.0h4v.s4.a5945901d1b3 from=translated src=- shape=29261ece vocab=16a1ad4e
-/
theorem visited_finalExit :
    VisitedByChart A' z b c (rotClass (finalExit A' z b c)) :=
  ⟨A'.length, A'.length + 1, le_refl _, le_refl _, by
    rw [← finalExit_rotate1, rotClass_rotate]⟩

/-- The fresh weight-2 door `door x` is visited (`= C_{m-1,0}`).
@isnad1 id=visitedb.0h4v.s4.73374a7c3215 from=translated src=- shape=3a9053df vocab=15e05c7d
-/
theorem visited_door :
    VisitedByChart A' z b c (rotClass (door (finalExit A' z b c))) :=
  ⟨A'.length, 0, le_refl _, by omega, by rw [door_finalExit, chartWord_n0]⟩

/-- **Weight-2 closure.**  Every word sharing the length-`(k−2)` overlap of `x`
(in particular every weight-2 successor of `x`) lies in a chart-visited rotation class.
@isnad1 id=visitedb.3h5v.s6.83af9a37033f from=translated src=- shape=e69f3383 vocab=2bd33cf2
-/
theorem chart_closure_w2 (hs : IsPermWord (A'.length + 3) (A' ++ [z, b, c]))
    {v : List ℕ} (hv : IsPermWord (A'.length + 3) v)
    (hover : (finalExit A' z b c).drop 2 = v.take (A'.length + 3 - 2)) :
    VisitedByChart A' z b c (rotClass v) := by
  have hx : IsPermWord (A'.length + 3) (finalExit A' z b c) := isPermWord_finalExit A' z b c hs
  rcases ProofsConfinement.wt_two_word_cases (k := A'.length + 3) (by omega) hx hv hover with
    hrot | hdoor
  · -- v = x.rotate 2 : same class as x
    rw [hrot, rotClass_rotate]
    exact visited_finalExit A' z b c
  · -- v = door x
    rw [hdoor]
    exact visited_door A' z b c

/-! ## The six weight-3 successor identities (`V1`…`V6`)

`x = c b z A'`; a weight-3 successor is `A' ++ (a permutation of z,b,c)`.  The six are:
`V1 = A'zbc = C₀₀`, `V2 = A'zcb = σ(C_{0,m})`, `V3 = A'bzc = C_{m-1,1}`,
`V4 = A'bcz = σ(C_{m-1,0})`, `V5 = A'czb = σ²(C_{0,m-1})`, `V6 = A'cbz = σ²(C_{m-1,m})`. -/

/--
@isnad1 id=visitedb.0h4v.s5.df9ba68f2274 from=translated src=- shape=a64f34f2 vocab=944b4876
-/
theorem visited_V1 : VisitedByChart A' z b c (rotClass (A' ++ [z, b, c])) :=
  ⟨0, 0, by omega, by omega, by rw [chartWord_00]⟩

/--
@isnad1 id=visitedb.0h4v.s5.b674880de6db from=translated src=- shape=1d647284 vocab=944b4876
-/
theorem visited_V2 : VisitedByChart A' z b c (rotClass (A' ++ [z, c, b])) := by
  refine ⟨0, A'.length + 1, by omega, le_refl _, ?_⟩
  rw [← rotClass_rotate (chartWord A' z b c 0 (A'.length + 1)) 1, chartWord_0n1,
    show b :: A' ++ [z, c] = [b] ++ (A' ++ [z, c]) from rfl,
    show (1 : ℕ) = ([b] : List ℕ).length from rfl, List.rotate_append_length_eq,
    show (A' ++ [z, c]) ++ [b] = A' ++ [z, c, b] by simp]

/--
@isnad1 id=visitedb.0h4v.s5.0c03a748a99c from=translated src=- shape=75d9a2e5 vocab=944b4876
-/
theorem visited_V3 : VisitedByChart A' z b c (rotClass (A' ++ [b, z, c])) :=
  ⟨A'.length, 1, le_refl _, by omega, by rw [chartWord_n1]⟩

/--
@isnad1 id=visitedb.0h4v.s5.20b4c4e145c2 from=translated src=- shape=e36c010c vocab=944b4876
-/
theorem visited_V4 : VisitedByChart A' z b c (rotClass (A' ++ [b, c, z])) := by
  refine ⟨A'.length, 0, le_refl _, by omega, ?_⟩
  rw [← rotClass_rotate (chartWord A' z b c A'.length 0) 1, chartWord_n0,
    show z :: A' ++ [b, c] = [z] ++ (A' ++ [b, c]) from rfl,
    show (1 : ℕ) = ([z] : List ℕ).length from rfl, List.rotate_append_length_eq,
    show (A' ++ [b, c]) ++ [z] = A' ++ [b, c, z] by simp]

/--
@isnad1 id=visitedb.0h4v.s5.a4f45ef52004 from=translated src=- shape=db618fdf vocab=944b4876
-/
theorem visited_V5 : VisitedByChart A' z b c (rotClass (A' ++ [c, z, b])) := by
  refine ⟨0, A'.length, by omega, by omega, ?_⟩
  rw [← rotClass_rotate (chartWord A' z b c 0 A'.length) 2, chartWord_0n,
    show z :: b :: A' ++ [c] = [z, b] ++ (A' ++ [c]) from rfl,
    show (2 : ℕ) = ([z, b] : List ℕ).length from rfl, List.rotate_append_length_eq,
    show (A' ++ [c]) ++ [z, b] = A' ++ [c, z, b] by simp]

/--
@isnad1 id=visitedb.0h4v.s5.23d4dc40a521 from=translated src=- shape=a0b4b274 vocab=944b4876
-/
theorem visited_V6 : VisitedByChart A' z b c (rotClass (A' ++ [c, b, z])) := by
  refine ⟨A'.length, A'.length + 1, le_refl _, le_refl _, ?_⟩
  rw [← rotClass_rotate (chartWord A' z b c A'.length (A'.length + 1)) 2, chartWord_nn1,
    show b :: z :: A' ++ [c] = [b, z] ++ (A' ++ [c]) from rfl,
    show (2 : ℕ) = ([b, z] : List ℕ).length from rfl, List.rotate_append_length_eq,
    show (A' ++ [c]) ++ [b, z] = A' ++ [c, b, z] by simp]

/-! ## Weight-3 successor enumeration (the six-way completeness)

A weight-3 successor `v` of `x = c b z A'` shares the length-`(k−3)` prefix `A'` with `x`, and
its last three letters are a permutation of the three missing symbols `{z,b,c} = x.take 3`.
Hence `v` is exactly one of `V1…V6`. -/
/--
@isnad1 id=or.3h5v.s8.7bbe09345455 from=translated src=- shape=c98f6432 vocab=66ecbaf3
-/
theorem w3_six_cases (hx : IsPermWord (A'.length + 3) (finalExit A' z b c))
    {v : List ℕ} (hv : IsPermWord (A'.length + 3) v)
    (hover : (finalExit A' z b c).drop 3 = v.take (A'.length + 3 - 3)) :
    v = A' ++ [z, b, c] ∨ v = A' ++ [z, c, b] ∨ v = A' ++ [b, z, c] ∨
      v = A' ++ [b, c, z] ∨ v = A' ++ [c, z, b] ∨ v = A' ++ [c, b, z] := by
  have hvlen : v.length = A'.length + 3 := hv.length
  -- overlap: v.take A'.length = A'
  rw [show (finalExit A' z b c).drop 3 = A' from rfl, show A'.length + 3 - 3 = A'.length by omega]
    at hover
  set r := v.drop A'.length with hrdef
  have hvsplit : v = A' ++ r := by
    conv_lhs => rw [← List.take_append_drop A'.length v]; rw [← hover]
  have hrlen : r.length = 3 := by
    have h := hvlen; rw [hvsplit, List.length_append] at h; omega
  -- nodup facts about the four blocks A', z, b, c
  have hnd : (c :: b :: z :: A').Nodup := hx.nodup
  obtain ⟨hcm, hbm, hzm, hAnd⟩ := by
    rw [List.nodup_cons, List.nodup_cons, List.nodup_cons] at hnd; exact hnd
  simp only [List.mem_cons, not_or] at hcm hbm
  obtain ⟨hcb, hcz, hcA⟩ := hcm
  obtain ⟨hbz, hbA⟩ := hbm
  -- r.Nodup
  have hrnd : r.Nodup := by
    have := hv.nodup; rw [hvsplit] at this; exact (List.nodup_append.mp this).2.1
  -- z, b, c ∈ r
  have hmemv : ∀ {w : ℕ}, w ∈ (c :: b :: z :: A') → w ∈ v := by
    intro w hw
    rw [← List.mem_toFinset, hv.toFinset_eq, ← hx.toFinset_eq]; exact List.mem_toFinset.mpr hw
  have hzr : z ∈ r := by
    have := hmemv (w := z) (by simp); rw [hvsplit, List.mem_append] at this
    exact this.resolve_left hzm
  have hbr : b ∈ r := by
    have := hmemv (w := b) (by simp); rw [hvsplit, List.mem_append] at this
    exact this.resolve_left hbA
  have hcr : c ∈ r := by
    have := hmemv (w := c) (by simp); rw [hvsplit, List.mem_append] at this
    exact this.resolve_left hcA
  -- r.toFinset = {z, b, c}
  have hcard3 : ({z, b, c} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hbz, Ne.symm hcz]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hcb]), Finset.card_singleton]
  have hsub : ({z, b, c} : Finset ℕ) ⊆ r.toFinset := by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact List.mem_toFinset.mpr hzr
    · exact List.mem_toFinset.mpr hbr
    · exact List.mem_toFinset.mpr hcr
  have hrtf : ({z, b, c} : Finset ℕ) = r.toFinset :=
    Finset.eq_of_subset_of_card_le hsub
      (by rw [hcard3]; exact le_trans (List.toFinset_card_le r) (le_of_eq hrlen))
  -- destructure r and pin each entry into {z, b, c}
  obtain ⟨r0, r1, r2, hr⟩ := List.length_eq_three.mp hrlen
  have hmem : ∀ {w : ℕ}, w ∈ r → w = z ∨ w = b ∨ w = c := by
    intro w hw
    have : w ∈ ({z, b, c} : Finset ℕ) := hrtf ▸ List.mem_toFinset.mpr hw
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have m0 := hmem (show r0 ∈ r by rw [hr]; simp)
  have m1 := hmem (show r1 ∈ r by rw [hr]; simp)
  have m2 := hmem (show r2 ∈ r by rw [hr]; simp)
  -- distinctness of r0, r1, r2
  rw [hr, List.nodup_cons, List.nodup_cons, List.nodup_cons] at hrnd
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrnd
  obtain ⟨⟨hr01, hr02⟩, hr12, _⟩ := hrnd
  -- 27-way split, 21 killed by distinctness, 6 constructive
  rw [hvsplit, hr]
  rcases m0 with h0 | h0 | h0 <;> rcases m1 with h1 | h1 | h1 <;> rcases m2 with h2 | h2 | h2 <;>
    subst h0 <;> subst h1 <;> subst h2 <;>
    first
      | exact absurd rfl hr01
      | exact absurd rfl hr02
      | exact absurd rfl hr12
      | tauto

/-- **Weight-3 closure.**  Every word sharing the length-`(k−3)` overlap of `x`
(in particular every weight-3 successor of `x`) lies in a chart-visited rotation class.
@isnad1 id=visitedb.3h5v.s6.c9a03163763e from=translated src=- shape=e69f3383 vocab=2bd33cf2
-/
theorem chart_closure_w3 (hs : IsPermWord (A'.length + 3) (A' ++ [z, b, c]))
    {v : List ℕ} (hv : IsPermWord (A'.length + 3) v)
    (hover : (finalExit A' z b c).drop 3 = v.take (A'.length + 3 - 3)) :
    VisitedByChart A' z b c (rotClass v) := by
  have hx : IsPermWord (A'.length + 3) (finalExit A' z b c) := isPermWord_finalExit A' z b c hs
  rcases w3_six_cases A' z b c hx hv hover with h | h | h | h | h | h
  · rw [h]; exact visited_V1 A' z b c
  · rw [h]; exact visited_V2 A' z b c
  · rw [h]; exact visited_V3 A' z b c
  · rw [h]; exact visited_V4 A' z b c
  · rw [h]; exact visited_V5 A' z b c
  · rw [h]; exact visited_V6 A' z b c

/-! ## The closure corollary: any continuation to an unvisited class is heavy (weight ≥ 4) -/

/-- **§3 CLOSURE LEMMA.**  From the completed chart's final exit `x = c b aₘ a₁…a_{m-1}`
(`k = |A'| + 3 ≥ 4`), any successor `v` whose rotation class the chart has *not* visited has
edge weight `≥ 4`.  Equivalently (Sections 4–5 of `PROOF_S3.md`): every weight-1, weight-2, and
weight-3 successor of `x` is already in a visited class, so the τ₃-orbit closes.
@isnad1 id=le.4h5v.s6.584bc86711a9 from=translated src=- shape=ab9b3198 vocab=9ded77b7
-/
theorem chart_closure (hn : 1 ≤ A'.length)
    (hs : IsPermWord (A'.length + 3) (A' ++ [z, b, c]))
    {v : List ℕ} (hv : IsPermWord (A'.length + 3) v)
    (hvis : ¬ VisitedByChart A' z b c (rotClass v)) :
    4 ≤ wt (A'.length + 3) (finalExit A' z b c) v := by
  by_contra hlt
  have hx : IsPermWord (A'.length + 3) (finalExit A' z b c) := isPermWord_finalExit A' z b c hs
  have hk : (1 : ℕ) ≤ A'.length + 3 := by omega
  obtain ⟨h1, _, hov⟩ := wt_spec (u := finalExit A' z b c) (v := v) hk (le_of_eq hx.length)
  have hval : wt (A'.length + 3) (finalExit A' z b c) v = 1 ∨
      wt (A'.length + 3) (finalExit A' z b c) v = 2 ∨
      wt (A'.length + 3) (finalExit A' z b c) v = 3 := by omega
  rcases hval with hw | hw | hw
  · -- weight-1 successor: the rotation σ(x), same class as x (a chart class)
    apply hvis
    rw [eq_rho_of_wt_one hk hx hv hw,
      show rho (finalExit A' z b c) = (finalExit A' z b c).rotate 1 from rfl, rotClass_rotate]
    exact visited_finalExit A' z b c
  · -- weight-2 successor
    exact hvis (chart_closure_w2 A' z b c hs hv (by rw [hw] at hov; exact hov))
  · -- weight-3 successor
    exact hvis (chart_closure_w3 A' z b c hs hv (by rw [hw] at hov; exact hov))

end Hunter.ProofsClosure3

/-! ## Exports for `Hunter.Proved` (consumed by §2's forced-step induction / the endgame) -/

namespace Hunter.Proved

/-- `Hunter.Proved.ChartVisited A' z b c K`: `K` is a rotation class visited by the deterministic
τ₂/τ₃ chart started at `A' ++ [z,b,c]`.-/
abbrev ChartVisited := Hunter.ProofsClosure3.VisitedByChart

/-- `Hunter.Proved.chart_closure` — the §3 closure lemma: from the final exit, any successor to an
unvisited rotation class has weight `≥ 4`.
@isnad1 id=le.4h5v.s6.0a07bef1dbcd from=translated src=- shape=ab9b3198 vocab=be918f5a
-/
theorem chart_closure (A' : List ℕ) (z b c : ℕ) (hn : 1 ≤ A'.length)
    (hs : IsPermWord (A'.length + 3) (A' ++ [z, b, c]))
    {v : List ℕ} (hv : IsPermWord (A'.length + 3) v)
    (hvis : ¬ ChartVisited A' z b c (rotClass v)) :
    4 ≤ wt (A'.length + 3) (Hunter.ProofsClosure3.finalExit A' z b c) v :=
  Hunter.ProofsClosure3.chart_closure A' z b c hn hs hv hvis

/-- `Hunter.Proved.chart_closure_w2` — every weight-2 successor of the final exit is chart-visited.
@isnad1 id=chartvis.3h5v.s6.d6b1cd587329 from=translated src=- shape=e69f3383 vocab=4ff27988
-/
theorem chart_closure_w2 (A' : List ℕ) (z b c : ℕ)
    (hs : IsPermWord (A'.length + 3) (A' ++ [z, b, c]))
    {v : List ℕ} (hv : IsPermWord (A'.length + 3) v)
    (hover : (Hunter.ProofsClosure3.finalExit A' z b c).drop 2 = v.take (A'.length + 3 - 2)) :
    ChartVisited A' z b c (rotClass v) :=
  Hunter.ProofsClosure3.chart_closure_w2 A' z b c hs hv hover

/-- `Hunter.Proved.chart_closure_w3` — every weight-3 successor of the final exit is chart-visited.
@isnad1 id=chartvis.3h5v.s6.0cd17257cc6b from=translated src=- shape=e69f3383 vocab=4ff27988
-/
theorem chart_closure_w3 (A' : List ℕ) (z b c : ℕ)
    (hs : IsPermWord (A'.length + 3) (A' ++ [z, b, c]))
    {v : List ℕ} (hv : IsPermWord (A'.length + 3) v)
    (hover : (Hunter.ProofsClosure3.finalExit A' z b c).drop 3 = v.take (A'.length + 3 - 3)) :
    ChartVisited A' z b c (rotClass v) :=
  Hunter.ProofsClosure3.chart_closure_w3 A' z b c hs hv hover

end Hunter.Proved
