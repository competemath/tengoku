/-
Copyright (c) 2026 Keston Aquino-Michaels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keston Aquino-Michaels
-/
module

public import Tengoku.LeanPool.LeanPool.CriticalPortraits.Injectivity
public import Tengoku

/-!
# Surjectivity of `T` via the balance forest `β` (Part II of the bijection).

For a level-canonical `(d-1)`-subset `U ⊆ ZMod (d*m)`, the **balance forest** `β(U)` is the
explicit critical portrait with `T(β(U)) = U` — the discriminating section property (a wrong
parent rule fails this).  Construction (paper Part II / bare-Lean `betaParent`):

* For a survivor `u` (fiber `φ = u.val % m`, level `lu = u.val / m`) and level `k`, the
  **deficiency** is `D(k) = S(φ+k·m, u) − (lu−k−1)` where `S(x,y) = #{t∈U : x<t.val<y}` (`Scount`).
* `betaK U u` is the largest `k ≤ lu−1` with `D(k)=0` (`Nat.findGreatest`); `betaParent U u` is
  the fiber-`φ` point at level `betaK`.
* `β(U)` (`beta`) is the set of connected components (`betaBlock`) of the parent edges `(v*(u),u)`,
  recovered via `Relation.ReflTransGen` of the adjacency relation `bAdj`.  Each block's `minVal`
  is its non-`U` root (`betaRoot`); the survivors of each block are exactly its `U`-points.

PROVED (sorry-free, axioms ⊆ {propext, Classical.choice, Quot.sound}):
* `discrete_ivt` — discrete IVT via `Nat.findGreatest`; `exists_balance` (E) + `betaK_max` (M2).
* `Defc_pos_after` — M2 *strict positivity* (the prefix/GPRE bound): the deficiency is `> 0`
  strictly past the balance index (a second use of the discrete IVT, on `[j, lu-1]`).
* `betaParent_inj` (I, parent injectivity, via the deficiency additive split + maximality).
* **`T_beta` — `T(β(U)) = U`** (the load-bearing, discriminating spec).
* `betaBlock_critical` (IsCriticalSet per block), `beta_pairwise_disjoint`, `beta_weight`
  (∑(|S|−1)=d−1) — three of the four `Portrait` conjuncts.
* `beta_unlinked` (N) is REDUCED to `beta_interval_closed` and PROVED from it.

NOW FULLY PROVED (no remaining `sorry`):
* `beta_interval_closed` — the geometric heart of N: a point of one block strictly inside another
  block's `.val`-span forces the whole block inside.  Proved via the no-escape property `P`
  (`noEscape`, a second discrete IVT on ψ-points anchored by the `Q` deficiency bound, with the
  `GPRE` prefix bound and `N0` window lemma; the `ψ ≥ φ / ψ < φ` fiber split is handled by
  `sep_master`), then the laminarity bridge (`root_ge`, `descend_cross`) turns `P` into the
  two-sided `.val`-span containment using `betaBlock_disjoint`.  Downstream (`beta_unlinked`,
  `beta_portrait`, `T_surjOn`) is therefore complete: SURJECTIVITY of `T` (all `d`) is proved.
  Axioms: `{propext, Classical.choice, Quot.sound}` (no `sorryAx`, no `native_decide`).
-/

@[expose] public section

namespace CriticalPortraits

open Finset
open scoped BigOperators

/-! ## Layer 0: discrete IVT via Nat.findGreatest. -/

/-- **Discrete IVT.** An integer-valued sequence with `D 0 ≤ 0`, `0 ≤ D L`, and unit-bounded
    up-steps (`D (k+1) ≤ D k + 1`) hits zero somewhere in `[0, L]`.
@isnad1 id=ex.3h2v.s6.47926befc593 from=translated src=- shape=f678d7e0 vocab=5c6f3c94
-/
theorem discrete_ivt (D : ℕ → ℤ) (L : ℕ) (h0 : D 0 ≤ 0) (hL : 0 ≤ D L)
    (hstep : ∀ k, k < L → D (k + 1) ≤ D k + 1) : ∃ k ≤ L, D k = 0 := by
  classical
  set K := Nat.findGreatest (fun k => D k ≤ 0) L with hK
  have hspec : D K ≤ 0 := by
    have := Nat.findGreatest_spec (P := fun k => D k ≤ 0) (m := 0) (Nat.zero_le L) h0
    simp only [hK]; exact this
  have hKle : K ≤ L := Nat.findGreatest_le L
  refine ⟨K, hKle, ?_⟩
  rcases Nat.lt_or_ge K L with hlt | hge
  · -- K < L: findGreatest is greatest, so ¬(D (K+1) ≤ 0), i.e. 0 < D (K+1)
    have hnot : ¬ (D (K+1) ≤ 0) := by
      have := Nat.findGreatest_is_greatest (P := fun k => D k ≤ 0)
        (k := K+1) (n := L) (by simp [hK]) hlt
      simpa using this
    have hpos : 0 < D (K+1) := by omega
    have := hstep K hlt
    omega
  · -- K ≥ L, with K ≤ L, so K = L; use hL
    have hKeq : K = L := le_antisymm hKle hge
    rw [hKeq] at hspec ⊢
    omega

/-! ## Layer 1: Scount and the deficiency. -/

/-- `S(x,y) = #{t ∈ U : x < t.val < y}`. -/
def Scount {d m : ℕ} (U : Finset (ZMod (d * m))) (x y : ℕ) : ℕ :=
  (U.filter (fun t => x < t.val ∧ t.val < y)).card

/-- Enlarging the lower endpoint shrinks the open interval: `Scount` is antitone in `x`.
@isnad1 id=le.1h6v.s5.85b800168d1e from=translated src=- shape=9a78c058 vocab=4187567b
-/
lemma Scount_antitone_left {d m : ℕ} (U : Finset (ZMod (d * m))) {x x' y : ℕ}
    (hxx : x ≤ x') : Scount U x' y ≤ Scount U x y := by
  unfold Scount
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, lt_of_le_of_lt hxx ht.2.1, ht.2.2⟩

/-- The integer **deficiency** of survivor `u` (column `φ`, level `lu`) at index `k`:
    `D(k) = Scount U (φ + k*m) u.val − (lu − k − 1)`. -/
def Defc {d m : ℕ} (U : Finset (ZMod (d * m))) (φ lu uval k : ℕ) : ℤ :=
  (Scount U (φ + k*m) uval : ℤ) - ((lu : ℤ) - (k : ℤ) - 1)

/-- The deficiency has unit-bounded up-steps (the E3 step bound).
@isnad1 id=le.1h7v.s6.34ea9c5dc691 from=translated src=- shape=24ecb0e3 vocab=85224596
-/
lemma Defc_step {d m : ℕ} (_hm : 0 < m) (U : Finset (ZMod (d * m))) (φ lu uval k : ℕ) :
    Defc U φ lu uval (k+1) ≤ Defc U φ lu uval k + 1 := by
  unfold Defc
  have hmono : Scount U (φ + (k+1)*m) uval ≤ Scount U (φ + k*m) uval := by
    apply Scount_antitone_left
    simp_all
  have h1 : (Scount U (φ + (k+1)*m) uval : ℤ) ≤ (Scount U (φ + k*m) uval : ℤ) := by
    exact_mod_cast hmono
  push_cast
  omega

/-- **E1 (upper boundary).** `D(lu-1) ≥ 0`: the constant `(lu - (lu-1) - 1) = 0`
    and `Scount ≥ 0`.
@isnad1 id=le.1h6v.s5.2c504646e120 from=translated src=- shape=55ae6bdf vocab=9ba10fe1
-/
lemma Defc_top_nonneg {d m : ℕ} (U : Finset (ZMod (d * m))) (φ lu uval : ℕ) (hlu : 1 ≤ lu) :
    0 ≤ Defc U φ lu uval (lu - 1) := by
  unfold Defc
  simp_all

/-- The scount bound from canonicity: `#{t ∈ U : φ < t.val < u.val} ≤ lu - 1`.
@isnad1 id=le.4h4v.s7.8e41d5328761 from=translated src=- shape=e8e5d44c vocab=1cdd51c3
-/
lemma Scount_bot_le {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) :
    Scount U (u.val % m) u.val ≤ u.val / m - 1 := by
  have : NeZero (d*m) := ⟨by positivity⟩
  -- key arithmetic facts about u.val
  have hdm : u.val % m + (u.val / m) * m = u.val := Nat.mod_add_div' u.val m
  have hφ : u.val % m < m := Nat.mod_lt _ hm
  have hlud : u.val / m < d := by
    have hlt : u.val < d * m := ZMod.val_lt u
    by_contra hge
    push Not at hge
    have : d * m ≤ (u.val / m) * m := Nat.mul_le_mul_right m hge
    omega
  -- {t : φ < t.val < u.val} ⊆ filter (level ≤ lu) \ {u}
  have hsub : U.filter (fun t => u.val % m < t.val ∧ t.val < u.val)
      ⊆ (U.filter (fun i => i.val / m ≤ u.val / m)).erase u := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htU, _, htlt⟩ := ht
    rw [Finset.mem_erase, Finset.mem_filter]
    have htlevel : t.val / m ≤ u.val / m := by
      have hdiv : t.val / m * m ≤ t.val := Nat.div_mul_le_self t.val m
      by_contra hgt
      push Not at hgt
      have : (u.val / m + 1) ≤ t.val / m := hgt
      have h2 : (u.val / m + 1) * m ≤ (t.val / m) * m := Nat.mul_le_mul_right m this
      rw [Nat.add_mul, Nat.one_mul] at h2
      omega
    refine ⟨?_, htU, htlevel⟩
    intro htu; rw [htu] at htlt; omega
  have humem : u ∈ U.filter (fun i => i.val / m ≤ u.val / m) := by
    rw [Finset.mem_filter]; exact ⟨hu, le_refl _⟩
  have hcard1 : (U.filter (fun t => u.val % m < t.val ∧ t.val < u.val)).card
      ≤ ((U.filter (fun i => i.val / m ≤ u.val / m)).erase u).card := Finset.card_le_card hsub
  have hcard2 : ((U.filter (fun i => i.val / m ≤ u.val / m)).erase u).card
      = (U.filter (fun i => i.val / m ≤ u.val / m)).card - 1 :=
    Finset.card_erase_of_mem humem
  have hcanon_lu : (U.filter (fun i => i.val / m ≤ u.val / m)).card ≤ u.val / m :=
    hcanon (u.val / m) hlud
  unfold Scount
  omega

/-- **E2 (lower boundary).** `D(0) ≤ 0` from canonicity.
@isnad1 id=le.5h4v.s7.9c6f27610189 from=translated src=- shape=7747ef3f vocab=e1de6785
-/
lemma Defc_bot_nonpos {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m) :
    Defc U (u.val % m) (u.val / m) u.val 0 ≤ 0 := by
  have hScount := Scount_bot_le hd hm hcanon hu
  unfold Defc
  simp only [Nat.zero_mul, Nat.add_zero]
  push_cast
  omega

/-! ## Layer 2: existence of a balance index. -/

/-- **Existence (E).** For a survivor `u` of a canonical `U` with level `≥ 1`, some balance index
    `k ≤ lu-1` has deficiency `0`.
@isnad1 id=ex.5h4v.s7.07a3a93f3990 from=translated src=- shape=7bee5341 vocab=6c67754f
-/
lemma exists_balance {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m) :
    ∃ k ≤ u.val / m - 1, Defc U (u.val % m) (u.val / m) u.val k = 0 := by
  apply discrete_ivt (fun k => Defc U (u.val % m) (u.val / m) u.val k) (u.val / m - 1)
  · exact Defc_bot_nonpos hd hm hcanon hu hlu
  · exact Defc_top_nonneg U (u.val % m) (u.val / m) u.val hlu
  · intro k _
    exact Defc_step hm U (u.val % m) (u.val / m) u.val k

/-- Every position has level `< d`.
@isnad1 id=lt.1h3v.s5.66838770d77c from=translated src=- shape=09881a5f vocab=af465e6f
-/
lemma level_lt_d {d m : ℕ} (_hm : 0 < m) (x : ZMod (d * m)) [NeZero (d * m)] : x.val / m < d := by
  have hlt : x.val < d * m := ZMod.val_lt x
  have hdiv : (x.val / m) * m ≤ x.val := Nat.div_mul_le_self x.val m
  by_contra hge
  push Not at hge
  have : d * m ≤ (x.val / m) * m := Nat.mul_le_mul_right m hge
  omega

/-! ## Layer 3: the balance index `betaK`, parent value and parent point. -/

open Classical in
/-- The **largest balance index** `K` of survivor `u` (the highest balance parent's level). -/
noncomputable def betaK {d m : ℕ} (U : Finset (ZMod (d * m))) (u : ZMod (d * m)) : ℕ :=
  Nat.findGreatest (fun k => Defc U (u.val % m) (u.val / m) u.val k = 0) (u.val / m - 1)

/-- `betaK ≤ lu - 1`.
@isnad1 id=le.0h4v.s6.8dbfb6154985 from=translated src=- shape=db891ec4 vocab=5c7da764
-/
lemma betaK_le {d m : ℕ} (U : Finset (ZMod (d * m))) (u : ZMod (d * m)) :
    betaK U u ≤ u.val / m - 1 := Nat.findGreatest_le _

/-- `betaK` is a balance index: deficiency `0` there.
@isnad1 id=eq.5h4v.s7.64cd3bc4c632 from=translated src=- shape=463b94d5 vocab=ba8cccd3
-/
lemma betaK_spec {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m) :
    Defc U (u.val % m) (u.val / m) u.val (betaK U u) = 0 := by
  classical
  obtain ⟨k, hkle, hkdef⟩ := exists_balance hd hm hcanon hu hlu
  have := Nat.findGreatest_spec (P := fun k => Defc U (u.val % m) (u.val / m) u.val k = 0)
    (m := k) (n := u.val / m - 1) hkle hkdef
  exact this

/-- **Maximality (M2).** For `betaK < j ≤ lu-1`, deficiency at `j` is nonzero.
@isnad1 id=ne.2h5v.s7.a21695bc6a16 from=translated src=- shape=5e65c11d vocab=79cef5f2
-/
lemma betaK_max {d m : ℕ} {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} {j : ℕ}
    (hj1 : betaK U u < j) (hj2 : j ≤ u.val / m - 1) :
    Defc U (u.val % m) (u.val / m) u.val j ≠ 0 := by
  classical
  exact Nat.findGreatest_is_greatest (P := fun k => Defc U (u.val % m) (u.val / m) u.val k = 0)
    hj1 hj2

/-- The **parent value**: `φ + betaK*m` (same fiber as `u`, level `betaK`). -/
noncomputable def betaParentVal {d m : ℕ} (U : Finset (ZMod (d * m))) (u : ZMod (d * m)) : ℕ :=
  u.val % m + betaK U u * m

/-- The parent value is `< d*m` (so its ZMod point round-trips).
@isnad1 id=lt.3h4v.s6.0058a3fd7c4d from=translated src=- shape=07790177 vocab=42f7f411
-/
lemma betaParentVal_lt {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} (hlu : 1 ≤ u.val / m) :
    betaParentVal U u < d * m := by
  have : NeZero (d*m) := ⟨by positivity⟩
  unfold betaParentVal
  have hφ : u.val % m < m := Nat.mod_lt _ hm
  have hlud : u.val / m < d := by
    have hlt : u.val < d * m := ZMod.val_lt u
    have hdiv : (u.val / m) * m ≤ u.val := Nat.div_mul_le_self u.val m
    by_contra hge
    push Not at hge
    have : d * m ≤ (u.val / m) * m := Nat.mul_le_mul_right m hge
    omega
  have hK : betaK U u ≤ u.val / m - 1 := betaK_le U u
  -- betaK ≤ d - 2, so φ + betaK*m < m + (d-1)*m = d*m
  have hKd : betaK U u ≤ d - 1 := by omega
  have hmul : betaK U u * m ≤ (d-1) * m := Nat.mul_le_mul_right m hKd
  have hdm : (d-1) * m + m = d * m := by
    have : (d - 1) * m + 1 * m = (d - 1 + 1) * m := by rw [← Nat.add_mul]
    rw [Nat.one_mul] at this
    rw [this]
    congr 1
    omega
  omega

/-- The **parent point**: the ZMod element at `betaParentVal`. -/
noncomputable def betaParent {d m : ℕ} (U : Finset (ZMod (d * m))) (u : ZMod (d * m)) :
    ZMod (d * m) :=
  (betaParentVal U u : ZMod (d*m))

/-- `betaParent`'s `.val` is exactly `betaParentVal` (round-trips since it is `< d*m`).
@isnad1 id=eq.3h4v.s6.71d030f13ed0 from=translated src=- shape=2c9726d9 vocab=c85089fb
-/
lemma betaParent_val {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} (hlu : 1 ≤ u.val / m) :
    (betaParent U u).val = betaParentVal U u := by
  have : NeZero (d*m) := ⟨by positivity⟩
  unfold betaParent
  exact ZMod.val_natCast_of_lt (betaParentVal_lt hd hm hlu)

/-- `betaParent` shares `u`'s fiber.
@isnad1 id=eq.3h4v.s6.19a7812166d2 from=translated src=- shape=4310c4cc vocab=81bc2932
-/
lemma betaParent_fiber {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} (hlu : 1 ≤ u.val / m) :
    (betaParent U u).val % m = u.val % m := by
  rw [betaParent_val hd hm hlu]
  unfold betaParentVal
  simp_all

/-- `betaParent`'s level is `betaK` (strictly below `u`'s level).
@isnad1 id=eq.3h4v.s6.16e18b86da70 from=translated src=- shape=1986265b vocab=8c003708
-/
lemma betaParent_level {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} (hlu : 1 ≤ u.val / m) :
    (betaParent U u).val / m = betaK U u := by
  rw [betaParent_val hd hm hlu]
  unfold betaParentVal
  have hφ : u.val % m < m := Nat.mod_lt _ hm
  rw [Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hφ, Nat.zero_add]

/-- `betaParent`'s level is strictly below `u`'s level.
@isnad1 id=lt.3h4v.s6.df97edf043ea from=translated src=- shape=daf6e628 vocab=680e2c10
-/
lemma betaParent_level_lt {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} (hlu : 1 ≤ u.val / m) :
    (betaParent U u).val / m < u.val / m := by
  rw [betaParent_level hd hm hlu]
  have := betaK_le U u
  omega

/-- `betaParent`'s `.val` is strictly below `u`'s `.val`.
@isnad1 id=lt.3h4v.s6.8eb6d5d7e88c from=translated src=- shape=856260bd vocab=680e2c10
-/
lemma betaParent_val_lt {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} (hlu : 1 ≤ u.val / m) :
    (betaParent U u).val < u.val := by
  have hlev : (betaParent U u).val / m < u.val / m := betaParent_level_lt hd hm hlu
  exact sameblock_lt (x := betaParent U u) (y := u) hm hlev

/-! ## Layer 4: adjacency, reachability, and blocks as components. -/

variable {d m : ℕ}

/-- The (directed) **parent step**: `b` is a survivor (level ≥ 1) and `a` is its balance parent. -/
def bEdge (U : Finset (ZMod (d * m))) (a b : ZMod (d * m)) : Prop :=
  b ∈ U ∧ 1 ≤ b.val / m ∧ a = betaParent U b

/-- The **adjacency** relation (symmetrized parent step). -/
def bAdj (U : Finset (ZMod (d * m))) (a b : ZMod (d * m)) : Prop :=
  bEdge U a b ∨ bEdge U b a

/--
@isnad1 id=badj.1h5v.s5.7963505765e3 from=translated src=- shape=221c6198 vocab=d6abf068
-/
lemma bAdj_symm {U : Finset (ZMod (d * m))} {a b : ZMod (d * m)} (h : bAdj U a b) : bAdj U b a := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- **Reachability**: the reflexive-transitive closure of adjacency. -/
def bReach (U : Finset (ZMod (d * m))) (a b : ZMod (d * m)) : Prop :=
  Relation.ReflTransGen (bAdj U) a b

/--
@isnad1 id=breach.0h4v.s5.14913f08c050 from=translated src=- shape=d71a5df7 vocab=7675848b
-/
lemma bReach_refl {U : Finset (ZMod (d * m))} (a : ZMod (d * m)) : bReach U a a :=
  Relation.ReflTransGen.refl

/--
@isnad1 id=breach.1h5v.s5.7bf155b29e42 from=translated src=- shape=221c6198 vocab=7675848b
-/
lemma bReach_symm {U : Finset (ZMod (d * m))} {a b : ZMod (d * m)} (h : bReach U a b) :
    bReach U b a := by
  unfold bReach at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y _ hxy ih => exact Relation.ReflTransGen.head (bAdj_symm hxy) ih

/--
@isnad1 id=breach.2h6v.s6.5350be0e40c1 from=translated src=- shape=8b64d6f3 vocab=7675848b
-/
lemma bReach_trans {U : Finset (ZMod (d * m))} {a b c : ZMod (d * m)}
    (h1 : bReach U a b) (h2 : bReach U b c) : bReach U a c :=
  Relation.ReflTransGen.trans h1 h2

noncomputable instance bReachDecidable (U : Finset (ZMod (d * m))) (a b : ZMod (d * m)) :
    Decidable (bReach U a b) := Classical.dec _

/-- The active vertices of `β(U)`: the survivors and their balance parents. -/
noncomputable def bVerts (U : Finset (ZMod (d * m))) : Finset (ZMod (d*m)) :=
  U ∪ U.image (betaParent U)

/-- The **block** of a point `x`: everything in `bVerts U` reachable from `x`. -/
noncomputable def betaBlock (U : Finset (ZMod (d * m))) (x : ZMod (d * m)) :
    Finset (ZMod (d * m)) :=
  (bVerts U).filter (fun y => @decide (bReach U x y) (bReachDecidable U x y))

/--
@isnad1 id=iff.0h5v.s7.193ab441b385 from=translated src=- shape=88a192c9 vocab=83b0b190
-/
lemma mem_betaBlock {U : Finset (ZMod (d * m))} {x y : ZMod (d * m)} :
    y ∈ betaBlock U x ↔ y ∈ bVerts U ∧ bReach U x y := by
  unfold betaBlock; simp_all

/-- **The balance forest** `β(U)`: the connected components of the parent edges. -/
noncomputable def beta (U : Finset (ZMod (d * m))) : Finset (Finset (ZMod (d * m))) :=
  (bVerts U).image (betaBlock U)

/-! ## Layer 5: structural facts. -/

/-- Canonical `U`: every survivor has level `≥ 1` (canonicity at `j = 0`).
@isnad1 id=le.3h4v.s6.9380111940a1 from=translated src=- shape=66206137 vocab=390052d2
-/
lemma survivor_level_pos {d m : ℕ} (hd : 0 < d) {U : Finset (ZMod (d * m))}
    (hcanon : LevelCanonical d m U) {u : ZMod (d * m)} (hu : u ∈ U) : 1 ≤ u.val / m := by
  by_contra hlt
  push Not at hlt
  have hlt0 : u.val / m ≤ 0 := by omega
  have hmem : u ∈ U.filter (fun i => i.val / m ≤ 0) := by
    rw [Finset.mem_filter]; exact ⟨hu, hlt0⟩
  have hcanon0 : (U.filter (fun i => i.val / m ≤ 0)).card ≤ 0 := hcanon 0 hd
  have hempty : (U.filter (fun i => i.val / m ≤ 0)).card = 0 := Nat.le_zero.mp hcanon0
  rw [Finset.card_eq_zero] at hempty
  rw [hempty] at hmem
  exact absurd hmem (by simp)

/-- A single adjacency step preserves the fiber.
@isnad1 id=eq.4h5v.s6.cc30a34e5b00 from=translated src=- shape=f85aa5c3 vocab=c94d002f
-/
lemma bAdj_sameFiber {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (_hcanon : LevelCanonical d m U) {a b : ZMod (d * m)} (h : bAdj U a b) :
    a.val % m = b.val % m := by
  rcases h with ⟨hbU, hblu, hab⟩ | ⟨haU, halu, hba⟩
  · rw [hab]; exact betaParent_fiber hd hm hblu
  · rw [hba]; exact (betaParent_fiber hd hm halu).symm

/-- Reachability preserves the fiber.
@isnad1 id=eq.4h5v.s6.b02f6a025a94 from=translated src=- shape=f85aa5c3 vocab=d0358a43
-/
lemma bReach_sameFiber {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcanon : LevelCanonical d m U) {a b : ZMod (d * m)} (h : bReach U a b) :
    a.val % m = b.val % m := by
  unfold bReach at h
  induction h with
  | refl => rfl
  | @tail x y _ hxy ih => rw [ih]; exact bAdj_sameFiber hd hm hcanon hxy

/-! ## Layer 6: Scount additivity and parent injectivity (I). -/

/-- **Scount split** through an interior `U`-point `w`: if `x < w.val < y` and `w ∈ U`, then
    `Scount U x y = Scount U x w.val + 1 + Scount U w.val y`.
@isnad1 id=eq.3h6v.s7.ef4e2887d13b from=translated src=- shape=a0257328 vocab=8de4e354
-/
lemma Scount_split {d m : ℕ} [NeZero (d * m)] {U : Finset (ZMod (d * m))} {x y : ℕ}
    {w : ZMod (d * m)}
    (hwU : w ∈ U) (hxw : x < w.val) (hwy : w.val < y) :
    Scount U x y = Scount U x w.val + 1 + Scount U w.val y := by
  classical
  unfold Scount
  -- the filter for (x,y) splits as (x,w) ∪ {w} ∪ (w,y)
  have hsplit : U.filter (fun t => x < t.val ∧ t.val < y)
      = U.filter (fun t => x < t.val ∧ t.val < w.val)
        ∪ {w}
        ∪ U.filter (fun t => w.val < t.val ∧ t.val < y) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨htU, htx, hty⟩
      rcases lt_trichotomy t.val w.val with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨htU, htx, hlt⟩)
      · exact Or.inl (Or.inr (ZMod.val_injective _ heq))
      · exact Or.inr ⟨htU, hgt, hty⟩
    · rintro (((⟨htU, htx, htw⟩) | rfl) | ⟨htU, htw, hty⟩)
      · exact ⟨htU, htx, lt_trans htw hwy⟩
      · exact ⟨hwU, hxw, hwy⟩
      · exact ⟨htU, lt_trans hxw htw, hty⟩
  rw [hsplit]
  -- the three parts are pairwise disjoint
  have hdisj1 : Disjoint (U.filter (fun t => x < t.val ∧ t.val < w.val))
      ({w} : Finset (ZMod (d * m))) := by
    simp_all
  have hdisj2 : Disjoint (U.filter (fun t => x < t.val ∧ t.val < w.val) ∪ {w})
      (U.filter (fun t => w.val < t.val ∧ t.val < y)) := by
    rw [Finset.disjoint_union_left]
    constructor
    · rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_filter] at ha hb
      omega
    · simp_all
  rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
    Finset.card_singleton]

/-- The balance identity at `betaK`: `Scount U (betaParent).val u.val = lu - betaK - 1`.
@isnad1 id=eq.5h4v.s7.ceeabe9300f8 from=translated src=- shape=83476b7f vocab=8056f6ee
-/
lemma betaParent_balance {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m) :
    (Scount U (betaParent U u).val u.val : ℤ)
      = ((u.val / m : ℕ) : ℤ) - ((betaK U u : ℕ) : ℤ) - 1 := by
  have hspec := betaK_spec hd hm hcanon hu hlu
  have hpval : (betaParent U u).val = u.val % m + betaK U u * m := by
    rw [betaParent_val hd hm hlu]; rfl
  unfold Defc at hspec
  rw [hpval]
  -- hspec : (Scount U (u.val%m + betaK U u * m) u.val : ℤ) - ((u.val/m) - betaK U u - 1) = 0
  linarith

/-- **Injectivity (I).** The parent map is injective on survivors of canonical `U`.
@isnad1 id=eq.6h5v.s7.e08eda9e616d from=translated src=- shape=95a11967 vocab=67c1b040
-/
lemma betaParent_inj {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u1 u2 : ZMod (d * m)} (hu1 : u1 ∈ U) (hu2 : u2 ∈ U)
    (heq : betaParent U u1 = betaParent U u2) : u1 = u2 := by
  have : NeZero (d*m) := ⟨by positivity⟩
  have hlu1 : 1 ≤ u1.val / m := survivor_level_pos hd hcanon hu1
  have hlu2 : 1 ≤ u2.val / m := survivor_level_pos hd hcanon hu2
  -- same fiber
  have hfib : u1.val % m = u2.val % m := by
    have h1 : (betaParent U u1).val % m = u1.val % m := betaParent_fiber hd hm hlu1
    have h2 : (betaParent U u2).val % m = u2.val % m := betaParent_fiber hd hm hlu2
    rw [heq] at h1; rw [← h1, h2]
  -- WLOG handle by symmetry: prove for u1.val < u2.val a contradiction; equal vals ⇒ equal
  by_contra hne
  -- val inequality
  have hvalne : u1.val ≠ u2.val := fun h => hne (ZMod.val_injective _ h)
  -- the shared parent's val
  have hpv : (betaParent U u1).val = (betaParent U u2).val := by rw [heq]
  -- a symmetric core: if a.val < b.val then contradiction
  have core : ∀ a b : ZMod (d*m), a ∈ U → b ∈ U → 1 ≤ a.val / m → 1 ≤ b.val / m →
      a.val % m = b.val % m → (betaParent U a).val = (betaParent U b).val →
      a.val < b.val → False := by
    intro a b haU hbU hla hlb hfibab hpvab hab
    -- shared parent val = φ + K*m, same K for both (since fiber same)
    -- betaParent a level = betaK a, betaParent b level = betaK b
    have hlevA : (betaParent U a).val / m = betaK U a := betaParent_level hd hm hla
    have hlevB : (betaParent U b).val / m = betaK U b := betaParent_level hd hm hlb
    have hKeq : betaK U a = betaK U b := by rw [← hlevA, ← hlevB, hpvab]
    -- parent val < a.val (parent strictly below a)
    have hpa_lt : (betaParent U a).val < a.val := betaParent_val_lt hd hm hla
    have hpb_lt : (betaParent U b).val < b.val := betaParent_val_lt hd hm hlb
    -- a.val = φ + (level a)*m, with level a > betaK a
    have hlevAa : betaK U a < a.val / m := by
      have hll : (betaParent U a).val / m < a.val / m := betaParent_level_lt hd hm hla
      rw [hlevA] at hll; exact hll
    -- a.val < b.val, same fiber ⇒ level a < level b
    have hlevab : a.val / m < b.val / m := by
      rcases lt_or_eq_of_le ((val_le_iff_level_le_of_sameFiber hfibab).mp hab.le) with h | h
      · exact h
      · exact absurd (level_injOn_fiber hfibab h) (fun heq2 => by rw [heq2] at hab; omega)
    -- the balance identities
    have hbalA := betaParent_balance hd hm hcanon haU hla
    have hbalB := betaParent_balance hd hm hcanon hbU hlb
    -- Scount split: Scount p b = Scount p a + 1 + Scount a b  (a interior, in U, p < a < b)
    have hpab : (betaParent U b).val < a.val := by rw [← hpvab]; exact hpa_lt
    have hsplit : Scount U (betaParent U b).val b.val
        = Scount U (betaParent U b).val a.val + 1 + Scount U a.val b.val :=
      Scount_split haU hpab hab
    -- rewrite Scount p_b a using p_b = p_a
    have hScpaa : Scount U (betaParent U b).val a.val = Scount U (betaParent U a).val a.val := by
      rw [hpvab]
    -- Now the deficiency of b at index (level a) is 0
    have hDef_b_la : Defc U (b.val % m) (b.val / m) b.val (a.val / m) = 0 := by
      unfold Defc
      -- φ + (level a)*m = a.val
      have haval : b.val % m + (a.val / m) * m = a.val := by
        rw [← hfibab]
        have := Nat.mod_add_div' a.val m; omega
      rw [haval]
      -- Scount a.val b.val = (lb - la - 1)
      have hScab : (Scount U a.val b.val : ℤ)
          = ((b.val / m : ℕ) : ℤ) - ((a.val / m : ℕ) : ℤ) - 1 := by
        have e1 : (Scount U (betaParent U b).val b.val : ℤ)
            = (Scount U (betaParent U a).val a.val : ℤ) + 1 + (Scount U a.val b.val : ℤ) := by
          rw [hsplit, hScpaa]; push_cast; ring
        rw [hbalB, hbalA, hKeq] at e1
        linarith
      rw [hScab]; ring
    -- contradiction with maximality: betaK b < level a ≤ level b - 1
    have hlt1 : betaK U b < a.val / m := by rw [← hKeq]; exact hlevAa
    have hlt2 : a.val / m ≤ b.val / m - 1 := by omega
    exact betaK_max hlt1 hlt2 hDef_b_la
  rcases lt_trichotomy u1.val u2.val with h | h | h
  · exact core u1 u2 hu1 hu2 hlu1 hlu2 hfib hpv h
  · exact hvalne h
  · exact core u2 u1 hu2 hu1 hlu2 hlu1 hfib.symm hpv.symm h

/-! ## Layer 7: the root function (descend to the non-U sink). -/

/-- One descent step: parent if a survivor (level ≥ 1), else stay. -/
noncomputable def bStep {d m : ℕ} (U : Finset (ZMod (d * m))) (x : ZMod (d * m)) :
    ZMod (d * m) :=
  if _hx : x ∈ U then betaParent U x else x

/-- The step strictly decreases `.val` when `x ∈ U`.
@isnad1 id=lt.4h4v.s7.5ff46292e100 from=translated src=- shape=0586d35d vocab=f5c641b8
-/
lemma bStep_lt {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x : ZMod (d * m)} (hx : x ∈ U) :
    (bStep U x).val < x.val := by
  unfold bStep; rw [dite_eq_left hx]
  exact betaParent_val_lt hd hm (survivor_level_pos hd hcanon hx)

/-- The **root** of `x`: iterate `bStep` until a non-`U` point. Well-founded on `.val`. -/
noncomputable def betaRoot {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) (x : ZMod (d * m)) : ZMod (d*m) :=
  if _hx : x ∈ U then betaRoot hd hm hcanon (betaParent U x) else x
termination_by x.val
decreasing_by exact betaParent_val_lt hd hm (survivor_level_pos hd hcanon _hx)

/-- If `x ∉ U`, the root is `x`.
@isnad1 id=eq.4h4v.s7.78f78ffb6dc6 from=translated src=- shape=df215b49 vocab=4661f31a
-/
lemma betaRoot_of_not_mem {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x : ZMod (d * m)} (hx : x ∉ U) :
    betaRoot hd hm hcanon x = x := by
  rw [betaRoot]; rw [dite_eq_right hx]

/-- If `x ∈ U`, the root descends to its parent's root.
@isnad1 id=eq.4h4v.s7.7566136bcaed from=translated src=- shape=0f149e92 vocab=74cf3f2a
-/
lemma betaRoot_of_mem {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x : ZMod (d * m)} (hx : x ∈ U) :
    betaRoot hd hm hcanon x = betaRoot hd hm hcanon (betaParent U x) := by
  rw [betaRoot]; rw [dite_eq_left hx]

/-- The root is never in `U`.
@isnad1 id=not.3h4v.s6.02e0cdccdf28 from=translated src=- shape=1ad4e629 vocab=4661f31a
-/
lemma betaRoot_not_mem {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) (x : ZMod (d * m)) :
    betaRoot hd hm hcanon x ∉ U := by
  induction hn : x.val using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    subst hn
    by_cases hx : x ∈ U
    · rw [betaRoot_of_mem hd hm hcanon hx]
      exact ih (betaParent U x).val (betaParent_val_lt hd hm (survivor_level_pos hd hcanon hx))
        (betaParent U x) rfl
    · rw [betaRoot_of_not_mem hd hm hcanon hx]; exact hx

/-- The root's `.val` is `≤ x.val`.
@isnad1 id=le.3h4v.s6.f94ae1100b4e from=translated src=- shape=03e60198 vocab=03e0bb1a
-/
lemma betaRoot_le {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) (x : ZMod (d * m)) :
    (betaRoot hd hm hcanon x).val ≤ x.val := by
  induction hn : x.val using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    subst hn
    by_cases hx : x ∈ U
    · rw [betaRoot_of_mem hd hm hcanon hx]
      have hlt : (betaParent U x).val < x.val :=
        betaParent_val_lt hd hm (survivor_level_pos hd hcanon hx)
      exact le_trans (ih (betaParent U x).val hlt (betaParent U x) rfl) (le_of_lt hlt)
    · rw [betaRoot_of_not_mem hd hm hcanon hx]

/-- For `x ∈ U`, the root is strictly below `x`.
@isnad1 id=lt.4h4v.s7.4ddadc25eed8 from=translated src=- shape=36921431 vocab=28c11bd8
-/
lemma betaRoot_lt {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x : ZMod (d * m)} (hx : x ∈ U) :
    (betaRoot hd hm hcanon x).val < x.val := by
  rw [betaRoot_of_mem hd hm hcanon hx]
  have hlt : (betaParent U x).val < x.val :=
    betaParent_val_lt hd hm (survivor_level_pos hd hcanon hx)
  exact lt_of_le_of_lt (betaRoot_le hd hm hcanon (betaParent U x)) hlt

/-- `x` reaches its root.
@isnad1 id=breach.3h4v.s6.1c645a2b9a0f from=translated src=- shape=8789bc07 vocab=0cecceab
-/
lemma bReach_betaRoot {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) (x : ZMod (d * m)) :
    bReach U x (betaRoot hd hm hcanon x) := by
  induction hn : x.val using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    subst hn
    by_cases hx : x ∈ U
    · rw [betaRoot_of_mem hd hm hcanon hx]
      have hlu := survivor_level_pos hd hcanon hx
      have hstep : bAdj U x (betaParent U x) :=
        Or.inr ⟨hx, hlu, rfl⟩
      have hlt : (betaParent U x).val < x.val := betaParent_val_lt hd hm hlu
      have hrec := ih (betaParent U x).val hlt (betaParent U x) rfl
      exact bReach_trans (Relation.ReflTransGen.single hstep) hrec
    · rw [betaRoot_of_not_mem hd hm hcanon hx]; exact bReach_refl x

/-- The root is invariant under one adjacency step.
@isnad1 id=eq.4h5v.s6.d34f69dfa022 from=translated src=- shape=91ad0bca vocab=cc33cee9
-/
lemma betaRoot_bAdj {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x y : ZMod (d * m)}
    (h : bAdj U x y) : betaRoot hd hm hcanon x = betaRoot hd hm hcanon y := by
  rcases h with ⟨hyU, _, hxy⟩ | ⟨hxU, _, hyx⟩
  · -- bEdge U x y: y ∈ U, x = betaParent y
    rw [hxy, ← betaRoot_of_mem hd hm hcanon hyU]
  · -- bEdge U y x: x ∈ U, y = betaParent x
    rw [hyx, ← betaRoot_of_mem hd hm hcanon hxU]

/-- The root is invariant along reachability.
@isnad1 id=eq.4h5v.s6.ab113ed06962 from=translated src=- shape=91ad0bca vocab=0cecceab
-/
lemma betaRoot_bReach {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x y : ZMod (d * m)}
    (h : bReach U x y) : betaRoot hd hm hcanon x = betaRoot hd hm hcanon y := by
  unfold bReach at h
  induction h with
  | refl => rfl
  | @tail w z _ hwz ih => rw [ih]; exact betaRoot_bAdj hd hm hcanon hwz

/-! ## Layer 8: block membership and the min = root. -/

/-- A `U`-point is a vertex.
@isnad1 id=mem.1h4v.s7.8e0ca69806de from=translated src=- shape=510c5f46 vocab=543b224c
-/
lemma mem_bVerts_of_mem {d m : ℕ} {U : Finset (ZMod (d * m))} {x : ZMod (d * m)} (hx : x ∈ U) :
    x ∈ bVerts U := by
  unfold bVerts; exact Finset.mem_union_left _ hx

/-- A balance parent of a `U`-point is a vertex.
@isnad1 id=mem.1h4v.s7.6b8227b7d227 from=translated src=- shape=8d7a7342 vocab=ac556fbd
-/
lemma betaParent_mem_bVerts {d m : ℕ} {U : Finset (ZMod (d * m))} {u : ZMod (d * m)} (hu : u ∈ U) :
    betaParent U u ∈ bVerts U := by
  unfold bVerts
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hu)

/-- One adjacency step from a vertex lands on a vertex.
@isnad1 id=mem.1h5v.s6.df087d60d411 from=translated src=- shape=dc080d18 vocab=3b82e883
-/
lemma bAdj_mem_bVerts {d m : ℕ} {U : Finset (ZMod (d * m))} {x y : ZMod (d * m)}
    (h : bAdj U x y) : y ∈ bVerts U := by
  rcases h with ⟨hyU, _, _⟩ | ⟨hxU, _, hyx⟩
  · exact mem_bVerts_of_mem hyU
  · rw [hyx]; exact betaParent_mem_bVerts hxU

/-- Reachability from a vertex stays in `bVerts`.
@isnad1 id=mem.2h5v.s7.fc2bd250cbfb from=translated src=- shape=af17b8a5 vocab=64ea9f18
-/
lemma bReach_mem_bVerts {d m : ℕ} {U : Finset (ZMod (d * m))} {x y : ZMod (d * m)}
    (hx : x ∈ bVerts U) (h : bReach U x y) : y ∈ bVerts U := by
  unfold bReach at h
  induction h with
  | refl => exact hx
  | @tail w z _ hwz _ => exact bAdj_mem_bVerts hwz

/-- The root of a vertex is a vertex.
@isnad1 id=mem.4h4v.s7.0a42703b3bdb from=translated src=- shape=844458df vocab=ae7d8802
-/
lemma betaRoot_mem_bVerts {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x : ZMod (d * m)}
    (hx : x ∈ bVerts U) : betaRoot hd hm hcanon x ∈ bVerts U :=
  bReach_mem_bVerts hx (bReach_betaRoot hd hm hcanon x)

/-- The root is in the block of `x`.
@isnad1 id=mem.4h4v.s7.8c127ebb7b38 from=translated src=- shape=c3de30eb vocab=ce6b37ea
-/
lemma betaRoot_mem_block {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x : ZMod (d * m)}
    (hx : x ∈ bVerts U) : betaRoot hd hm hcanon x ∈ betaBlock U x := by
  rw [mem_betaBlock]
  exact ⟨betaRoot_mem_bVerts hd hm hcanon hx, bReach_betaRoot hd hm hcanon x⟩

/-- The root is `.val`-minimal in the block.
@isnad1 id=le.4h5v.s7.7b04357f47b9 from=translated src=- shape=b69b45d2 vocab=aad22934
-/
lemma betaRoot_min_in_block {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x y : ZMod (d * m)}
    (hy : y ∈ betaBlock U x) : (betaRoot hd hm hcanon x).val ≤ y.val := by
  rw [mem_betaBlock] at hy
  obtain ⟨_, hreach⟩ := hy
  have hroot_eq : betaRoot hd hm hcanon x = betaRoot hd hm hcanon y :=
    betaRoot_bReach hd hm hcanon hreach
  rw [hroot_eq]
  exact betaRoot_le hd hm hcanon y

/-- The block of a vertex is nonempty.
@isnad1 id=nonempty.1h4v.s6.6db88b274d30 from=translated src=- shape=2593f0c0 vocab=16185efe
-/
lemma betaBlock_nonempty {d m : ℕ} {U : Finset (ZMod (d * m))} {x : ZMod (d * m)}
    (hx : x ∈ bVerts U) : (betaBlock U x).Nonempty :=
  ⟨x, by rw [mem_betaBlock]; exact ⟨hx, bReach_refl x⟩⟩

/-- The minimum of a block is its root.
@isnad1 id=eq.4h4v.s7.fea7204f1add from=translated src=- shape=2d155b63 vocab=f0e165ea
-/
lemma minVal_betaBlock {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x : ZMod (d * m)}
    (hx : x ∈ bVerts U) :
    minVal (betaBlock U x) (betaBlock_nonempty hx) = betaRoot hd hm hcanon x := by
  have : NeZero (d*m) := ⟨by positivity⟩
  set h := betaBlock_nonempty hx
  -- minVal ≤ root.val and root.val ≤ minVal.val (root is min)
  have h1 : (minVal (betaBlock U x) h).val ≤ (betaRoot hd hm hcanon x).val :=
    minVal_le (betaBlock U x) h _ (betaRoot_mem_block hd hm hcanon hx)
  have h2 : (betaRoot hd hm hcanon x).val ≤ (minVal (betaBlock U x) h).val :=
    betaRoot_min_in_block hd hm hcanon (minVal_mem (betaBlock U x) h)
  exact ZMod.val_injective _ (le_antisymm h1 h2)

/-- A block member that is not the root is a survivor (`∈ U`).
@isnad1 id=mem.5h5v.s7.56b9ee5bb361 from=translated src=- shape=515189a1 vocab=f3fcef22
-/
lemma mem_U_of_mem_block_ne_root {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x y : ZMod (d * m)}
    (hy : y ∈ betaBlock U x) (hne : y ≠ betaRoot hd hm hcanon x) : y ∈ U := by
  rw [mem_betaBlock] at hy
  obtain ⟨hyv, hreach⟩ := hy
  by_contra hyU
  -- y ∉ U ⇒ betaRoot y = y; but betaRoot y = betaRoot x
  have hself : betaRoot hd hm hcanon y = y := betaRoot_of_not_mem hd hm hcanon hyU
  have heq : betaRoot hd hm hcanon x = betaRoot hd hm hcanon y :=
    betaRoot_bReach hd hm hcanon hreach
  simp_all

/-- `betaBlock U x ∈ beta U` for a vertex `x`.
@isnad1 id=mem.1h4v.s7.aca227d3b8cf from=translated src=- shape=db21bd44 vocab=a7005523
-/
lemma betaBlock_mem_beta {d m : ℕ} {U : Finset (ZMod (d * m))} {x : ZMod (d * m)}
    (hx : x ∈ bVerts U) : betaBlock U x ∈ beta U :=
  Finset.mem_image_of_mem _ hx

/--
@isnad1 id=iff.0h4v.s7.a82ae1373cbe from=translated src=- shape=3050409b vocab=a7005523
-/
lemma mem_beta_iff {d m : ℕ} {U : Finset (ZMod (d * m))} {S : Finset (ZMod (d * m))} :
    S ∈ beta U ↔ ∃ v ∈ bVerts U, betaBlock U v = S := by
  unfold beta; rw [Finset.mem_image]

/-! ## Layer 9: T(β U) = U. -/

/-- **The load-bearing spec.** `T(β U) = U` for canonical `U`.
@isnad1 id=eq.3h3v.s6.9ef32bd366b1 from=translated src=- shape=d1e829f3 vocab=1d717122
-/
theorem T_beta {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcanon : LevelCanonical d m U) : T (beta U) = U := by
  have : NeZero (d*m) := ⟨by positivity⟩
  ext x
  rw [mem_T]
  constructor
  · -- x ∈ eraseMin S, S = betaBlock U v ⇒ x ∈ U
    rintro ⟨S, hS, hxS⟩
    rw [mem_beta_iff] at hS
    obtain ⟨v, hv, hSeq⟩ := hS
    subst hSeq
    have hne : (betaBlock U v).Nonempty := betaBlock_nonempty hv
    rw [mem_eraseMin (betaBlock U v) hne] at hxS
    obtain ⟨hxmem, hxneq⟩ := hxS
    -- minVal = betaRoot v
    rw [minVal_betaBlock hd hm hcanon hv] at hxneq
    exact mem_U_of_mem_block_ne_root hd hm hcanon hxmem hxneq
  · -- x ∈ U ⇒ x ∈ eraseMin (betaBlock U x)
    intro hxU
    have hxv : x ∈ bVerts U := mem_bVerts_of_mem hxU
    refine ⟨betaBlock U x, betaBlock_mem_beta hxv, ?_⟩
    have hne : (betaBlock U x).Nonempty := betaBlock_nonempty hxv
    rw [mem_eraseMin (betaBlock U x) hne]
    constructor
    · rw [mem_betaBlock]; exact ⟨hxv, bReach_refl x⟩
    · rw [minVal_betaBlock hd hm hcanon hxv]
      -- x ∈ U but betaRoot x ∉ U
      intro hcontra
      have hroot_notmem : betaRoot hd hm hcanon x ∉ U := betaRoot_not_mem hd hm hcanon x
      rw [← hcontra] at hroot_notmem
      exact hroot_notmem hxU

/-! ## Layer 10: β U is a Portrait — IsCriticalSet per block. -/

/-- Every block member shares the vertex's fiber.
@isnad1 id=eq.4h5v.s7.1ce044b4c2cd from=translated src=- shape=44b75b15 vocab=d1eb9c5f
-/
lemma betaBlock_sameFiber {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {x y : ZMod (d * m)}
    (hy : y ∈ betaBlock U x) : y.val % m = x.val % m := by
  rw [mem_betaBlock] at hy
  obtain ⟨_, hreach⟩ := hy
  exact (bReach_sameFiber hd hm hcanon hreach).symm

/-- Every block contains a second point besides its root (its root has a `U`-child, or the
    vertex itself is a `U`-point).
@isnad1 id=le.4h4v.s7.ceb8d0fcae94 from=translated src=- shape=4af59ec6 vocab=6590bedf
-/
lemma betaBlock_two_le {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {v : ZMod (d * m)}
    (hv : v ∈ bVerts U) : 2 ≤ (betaBlock U v).card := by
  have : NeZero (d*m) := ⟨by positivity⟩
  -- find a U-point u with u in the block (u = v if v ∈ U, else v = betaParent u)
  rcases Finset.mem_union.mp hv with hvU | hvImg
  · -- v ∈ U: block contains v and betaParent v, distinct
    have hlu := survivor_level_pos hd hcanon hvU
    have hp_mem : betaParent U v ∈ betaBlock U v := by
      rw [mem_betaBlock]
      refine ⟨betaParent_mem_bVerts hvU, ?_⟩
      exact Relation.ReflTransGen.single (Or.inr ⟨hvU, hlu, rfl⟩)
    have hv_mem : v ∈ betaBlock U v := by rw [mem_betaBlock]; exact ⟨hv, bReach_refl v⟩
    have hne : betaParent U v ≠ v := by
      intro h
      have hlt : (betaParent U v).val < v.val := betaParent_val_lt hd hm hlu
      rw [h] at hlt; omega
    have hsub : ({betaParent U v, v} : Finset (ZMod (d*m))) ⊆ betaBlock U v := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h <;> subst h
      · exact hp_mem
      · exact hv_mem
    have hcard2 : ({betaParent U v, v} : Finset (ZMod (d*m))).card = 2 :=
      Finset.card_pair_eq_two_iff.mpr hne
    calc 2 = ({betaParent U v, v} : Finset (ZMod (d*m))).card := hcard2.symm
      _ ≤ (betaBlock U v).card := Finset.card_le_card hsub
  · -- v ∈ image(betaParent): v = betaParent u, u ∈ U; block contains v and u
    rw [Finset.mem_image] at hvImg
    obtain ⟨u, huU, hvu⟩ := hvImg
    have hlu := survivor_level_pos hd hcanon huU
    have hu_mem : u ∈ betaBlock U v := by
      rw [mem_betaBlock]
      refine ⟨mem_bVerts_of_mem huU, ?_⟩
      -- v = betaParent u, so bAdj v u (bEdge U v u)
      rw [← hvu]
      exact Relation.ReflTransGen.single (Or.inl ⟨huU, hlu, rfl⟩)
    have hv_mem : v ∈ betaBlock U v := by rw [mem_betaBlock]; exact ⟨hv, bReach_refl v⟩
    have hne : u ≠ v := by
      intro h
      have hlt : (betaParent U u).val < u.val := betaParent_val_lt hd hm hlu
      rw [hvu, h] at hlt; omega
    have hsub : ({u, v} : Finset (ZMod (d*m))) ⊆ betaBlock U v := by
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h <;> subst h
      · exact hu_mem
      · exact hv_mem
    have hcard2 : ({u, v} : Finset (ZMod (d*m))).card = 2 :=
      Finset.card_pair_eq_two_iff.mpr hne
    calc 2 = ({u, v} : Finset (ZMod (d*m))).card := hcard2.symm
      _ ≤ (betaBlock U v).card := Finset.card_le_card hsub

/-- Each block is a critical set.
@isnad1 id=iscritic.4h4v.s6.bc954d92dfa2 from=translated src=- shape=88da7875 vocab=3d46883d
-/
lemma betaBlock_critical {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) {v : ZMod (d * m)}
    (hv : v ∈ bVerts U) : IsCriticalSet d m (betaBlock U v) := by
  have : NeZero (d*m) := ⟨by positivity⟩
  refine ⟨⟨v.val % m, Nat.mod_lt _ hm, ?_⟩, betaBlock_two_le hd hm hcanon hv⟩
  intro y hy
  exact betaBlock_sameFiber hd hm hcanon hy

/-! ## Layer 11: blocks determined by reachability; Disjoint. -/

/-- Reachable vertices have the same block.
@isnad1 id=eq.1h5v.s6.d3a310838bd5 from=translated src=- shape=bc2d9753 vocab=340f6000
-/
lemma betaBlock_eq_of_bReach {d m : ℕ} {U : Finset (ZMod (d * m))} {v1 v2 : ZMod (d * m)}
    (h : bReach U v1 v2) : betaBlock U v1 = betaBlock U v2 := by
  ext z
  rw [mem_betaBlock, mem_betaBlock]
  constructor
  · rintro ⟨hzv, hreach⟩; exact ⟨hzv, bReach_trans (bReach_symm h) hreach⟩
  · rintro ⟨hzv, hreach⟩; exact ⟨hzv, bReach_trans h hreach⟩

/-- Distinct blocks are vertex-disjoint.
@isnad1 id=disjoint.1h5v.s6.b10b0498aa56 from=translated src=- shape=f80790e1 vocab=1d298adb
-/
lemma betaBlock_disjoint {d m : ℕ} {U : Finset (ZMod (d * m))} {v1 v2 : ZMod (d * m)}
    (hne : betaBlock U v1 ≠ betaBlock U v2) : Disjoint (betaBlock U v1) (betaBlock U v2) := by
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  rw [mem_betaBlock] at hz1 hz2
  obtain ⟨_, hr1⟩ := hz1
  obtain ⟨_, hr2⟩ := hz2
  -- v1 reaches z, v2 reaches z ⇒ v1 reaches v2 ⇒ blocks equal
  have hv12 : bReach U v1 v2 := bReach_trans hr1 (bReach_symm hr2)
  exact hne (betaBlock_eq_of_bReach hv12)

/-- Distinct blocks of `β U` are disjoint.
@isnad1 id=disjoint.3h5v.s7.49eb2ef5a262 from=translated src=- shape=3431e28e vocab=e7a4718c
-/
lemma beta_pairwise_disjoint {d m : ℕ} {U : Finset (ZMod (d * m))} :
    ∀ A ∈ beta U, ∀ B ∈ beta U, A ≠ B → Disjoint A B := by
  intro A hA B hB hAB
  rw [mem_beta_iff] at hA hB
  obtain ⟨v1, _, hA1⟩ := hA
  obtain ⟨v2, _, hB1⟩ := hB
  subst hA1; subst hB1
  exact betaBlock_disjoint hAB

/-! ## Layer 12: the weight identity ∑(|S|-1) = d-1. -/

/-- **Weight.** `∑ S ∈ β U, (|S| - 1) = d - 1` (counted via `T(β U) = U`).
@isnad1 id=eq.4h3v.s7.8a4ca19ae1f6 from=translated src=- shape=57805312 vocab=7fd8e256
-/
lemma beta_weight {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcard : U.card = d - 1) (hcanon : LevelCanonical d m U) :
    ∑ S ∈ beta U, (S.card - 1) = d - 1 := by
  have : NeZero (d*m) := ⟨by positivity⟩
  classical
  -- pairwise disjoint eraseMin
  have hpd : (↑(beta U) : Set (Finset (ZMod (d*m)))).PairwiseDisjoint eraseMin := by
    intro A hA B hB hAB
    exact (beta_pairwise_disjoint A hA B hB hAB).mono (eraseMin_subset A) (eraseMin_subset B)
  have hTcard : (T (beta U)).card = ∑ S ∈ beta U, (S.card - 1) := by
    unfold T
    rw [Finset.sup_eq_biUnion, Finset.card_biUnion hpd]
    apply Finset.sum_congr rfl
    intro S hS
    rw [mem_beta_iff] at hS
    obtain ⟨v, hv, hSeq⟩ := hS
    subst hSeq
    exact eraseMin_card (betaBlock U v) (betaBlock_nonempty hv)
  rw [← hTcard, T_beta hd hm hcanon, hcard]

/-! ## Layer 12b: M2 strict positivity past the balance index (the prefix bound). -/

/-- **M2 strict positivity.** For a survivor `u` of canonical `U` and `betaK U u < j ≤ lu-1`,
    the deficiency at `j` is strictly positive.  If it were `≤ 0`, then since `D(lu-1) ≥ 0` (E1)
    and up-steps are `≤ 1`, the discrete IVT on `[j, lu-1]` yields an exact zero `> K`,
    contradicting maximality `betaK_max`.
@isnad1 id=lt.7h5v.s7.d8bc9cf774f9 from=translated src=- shape=5cf7be79 vocab=5ef90a9c
-/
lemma Defc_pos_after {d m : ℕ} (_hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (_hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (_hu : u ∈ U) (hlu : 1 ≤ u.val / m) {j : ℕ}
    (hj1 : betaK U u < j) (hj2 : j ≤ u.val / m - 1) :
    0 < Defc U (u.val % m) (u.val / m) u.val j := by
  classical
  set φ := u.val % m with hφ
  set lu := u.val / m with hludef
  by_contra hle
  push Not at hle
  -- shifted sequence E i := D (j + i), defined on [0, (lu-1) - j]
  set L := (lu - 1) - j with hLdef
  set E : ℕ → ℤ := fun i => Defc U φ lu u.val (j + i) with hEdef
  have hE0 : E 0 ≤ 0 := by simpa [hEdef] using hle
  have hEL : 0 ≤ E L := by
    have : j + L = lu - 1 := by omega
    simp only [hEdef]
    rw [this]
    exact Defc_top_nonneg U φ lu u.val hlu
  have hEstep : ∀ i, i < L → E (i+1) ≤ E i + 1 := by
    intro i _
    simp only [hEdef]
    have : j + (i + 1) = (j + i) + 1 := by omega
    rw [this]
    exact Defc_step hm U φ lu u.val (j + i)
  obtain ⟨i, hiL, hEi⟩ := discrete_ivt E L hE0 hEL hEstep
  -- j + i is a zero of D, with K < j ≤ j + i ≤ lu - 1
  have hzero : Defc U φ lu u.val (j + i) = 0 := by simpa [hEdef] using hEi
  have hKlt : betaK U u < j + i := by omega
  have hle_lu : j + i ≤ lu - 1 := by omega
  exact betaK_max hKlt hle_lu hzero

/-! ## Layer 12c: the no-escape property `P` and the laminarity bridge to interval-closure. -/

/-- Any balance index `≤ betaK`: `betaK` is the *largest* zero of the deficiency.
@isnad1 id=le.2h5v.s7.3e0f588dfe43 from=translated src=- shape=b86ed209 vocab=cb2785f3
-/
lemma betaK_ge {d m : ℕ} {U : Finset (ZMod (d * m))} {s : ZMod (d * m)} {k : ℕ}
    (hk : Defc U (s.val % m) (s.val / m) s.val k = 0) (hkle : k ≤ s.val / m - 1) :
    k ≤ betaK U s := by
  classical
  exact Nat.le_findGreatest hkle hk

/-- Two disjoint open subintervals fit inside the whole: `Scount` is superadditive.
@isnad1 id=le.2h6v.s5.54c520097087 from=translated src=- shape=8084df7f vocab=d7c1e3dd
-/
lemma Scount_add_le {d m : ℕ} (U : Finset (ZMod (d * m))) {x y z : ℕ}
    (hxy : x ≤ y) (hyz : y ≤ z) :
    Scount U x y + Scount U y z ≤ Scount U x z := by
  classical
  unfold Scount
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro t ht
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at ht
    rw [Finset.mem_filter]
    rcases ht with ⟨htU, h1, h2⟩ | ⟨htU, h1, h2⟩
    · exact ⟨htU, h1, lt_of_lt_of_le h2 hyz⟩
    · exact ⟨htU, lt_of_le_of_lt hxy h1, h2⟩
  · rw [Finset.disjoint_left]
    intro t ht1 ht2
    rw [Finset.mem_filter] at ht1 ht2
    omega

/-- **GPRE prefix bound.** For a survivor `u` of canonical `U`, with `K := betaK U u` and a
    `φ`-column index `j` with `K < j ≤ lu`, the survivor count from `v*(u)` up to the `φ`-point at
    level `j` is at most `j - K - 1`.
@isnad1 id=le.7h5v.s8.9a0fb7ec01f0 from=translated src=- shape=e6c6004d vocab=12288d5e
-/
lemma GPRE {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m) {j : ℕ}
    (hj1 : betaK U u < j) (hj2 : j ≤ u.val / m) :
    (Scount U (betaParent U u).val (u.val % m + j * m) : ℤ) ≤ (j : ℤ) - (betaK U u : ℤ) - 1 := by
  have : NeZero (d*m) := ⟨by positivity⟩
  classical
  set φ := u.val % m with hφ
  set lu := u.val / m with hludef
  set K := betaK U u with hKdef
  -- v = betaParent val = φ + K*m
  have hpval : (betaParent U u).val = φ + K * m := by
    rw [betaParent_val hd hm hlu]; rfl
  -- w' = φ + j*m, and v ≤ w' ≤ u.val
  have hvw : (betaParent U u).val ≤ φ + j * m := by
    rw [hpval]
    have : K * m ≤ j * m := Nat.mul_le_mul_right m (le_of_lt hj1)
    omega
  have hwu : φ + j * m ≤ u.val := by
    have hdm : φ + lu * m = u.val := by rw [hφ, hludef]; exact Nat.mod_add_div' u.val m
    have : j * m ≤ lu * m := Nat.mul_le_mul_right m hj2
    omega
  -- additive: Scount v w' + Scount w' u ≤ Scount v u
  have hadd := Scount_add_le U hvw hwu
  -- balance identity: Scount v u = lu - K - 1
  have hbal := betaParent_balance hd hm hcanon hu hlu
  -- Scount w' u ≥ lu - j (Defc_pos_after for j<lu; trivial for j=lu)
  have hsuf : (lu : ℤ) - (j : ℤ) ≤ (Scount U (φ + j * m) u.val : ℤ) := by
    rcases lt_or_eq_of_le hj2 with hjlt | hjeq
    · -- j < lu
      have hjle : j ≤ lu - 1 := by omega
      have hpos := Defc_pos_after hd hm hcanon hu hlu hj1 hjle
      unfold Defc at hpos
      -- hpos : 0 < Scount U (φ + j*m) u.val - (lu - j - 1)
      push_cast at hpos ⊢
      linarith
    · -- j = lu: w' = u.val, Scount = 0
      simp_all
  -- combine
  push_cast at hadd hbal ⊢
  linarith

/-- **N0.** No survivor lies strictly inside one column-window above an edge bottom:
    there is no `t ∈ U` with `v*(u) < t.val < v*(u) + m`.
@isnad1 id=false.8h5v.s8.05bcfe13a0dc from=translated src=- shape=a8cf7a19 vocab=1eacf2d6
-/
lemma N0 {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m)
    {t : ZMod (d * m)} (htU : t ∈ U)
    (hlo : (betaParent U u).val < t.val) (hhi : t.val < (betaParent U u).val + m) : False := by
  have : NeZero (d*m) := ⟨by positivity⟩
  classical
  set φ := u.val % m with hφ
  set lu := u.val / m with hludef
  set K := betaK U u with hKdef
  have hpval : (betaParent U u).val = φ + K * m := by
    rw [betaParent_val hd hm hlu]; rfl
  have hKle : K ≤ lu - 1 := betaK_le U u
  -- GPRE at j = K+1: Scount v (φ+(K+1)*m) ≤ 0
  have hj1 : K < K + 1 := by omega
  have hj2 : K + 1 ≤ lu := by omega
  have hgpre := GPRE hd hm hcanon hu hlu hj1 hj2
  -- (φ + (K+1)*m) = v + m
  have hwval : φ + (K + 1) * m = (betaParent U u).val + m := by
    rw [hpval]; ring
  rw [hwval] at hgpre
  -- hgpre : Scount v (v+m) ≤ (K+1) - K - 1 = 0
  have hzero : Scount U (betaParent U u).val ((betaParent U u).val + m) = 0 := by
    simp_all
  -- but t is in that window
  have htmem : t ∈ U.filter (fun w => (betaParent U u).val < w.val ∧
      w.val < (betaParent U u).val + m) := by
    rw [Finset.mem_filter]; exact ⟨htU, hlo, hhi⟩
  have hpos : 0 < Scount U (betaParent U u).val ((betaParent U u).val + m) := by
    unfold Scount
    exact Finset.card_pos.mpr ⟨t, htmem⟩
  omega

/-- Shrinking the upper endpoint shrinks the open interval: `Scount` is monotone in `y`.
@isnad1 id=le.1h6v.s5.807306622e23 from=translated src=- shape=0deb7ca0 vocab=4187567b
-/
lemma Scount_mono_right {d m : ℕ} (U : Finset (ZMod (d * m))) {x y y' : ℕ}
    (hyy : y ≤ y') : Scount U x y ≤ Scount U x y' := by
  unfold Scount
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, ht.2.1, lt_of_lt_of_le ht.2.2 hyy⟩

/-- **Q (the deficiency-sign anchor).** For an edge `(v,u) = (v*(u), u)` and an interior survivor
    `s` (fiber `ψ`), if `y = ψ + ly*m` is the `ψ`-point in `[v, v+m)`, then the deficiency of `s`
    at level `ly` is `≤ 0`.
@isnad1 id=le.10h6v.s8.c19407b136dd from=translated src=- shape=be8dd25c vocab=483b3864
-/
lemma Q {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u s : ZMod (d * m)} (hu : u ∈ U) (hlu : 1 ≤ u.val / m) (hs : s ∈ U)
    (hslo : (betaParent U u).val < s.val) (hshi : s.val < u.val) {ly : ℕ}
    (hwlo : (betaParent U u).val ≤ s.val % m + ly * m)
    (hwhi : s.val % m + ly * m < (betaParent U u).val + m) :
    Defc U (s.val % m) (s.val / m) s.val ly ≤ 0 := by
  have : NeZero (d*m) := ⟨by positivity⟩
  classical
  set φ := u.val % m with hφdef
  set ψ := s.val % m with hψdef
  set lu := u.val / m with hludef
  set ls := s.val / m with hlsdef
  set K := betaK U u with hKdef
  have hφlt : φ < m := Nat.mod_lt _ hm
  have hψlt : ψ < m := Nat.mod_lt _ hm
  have hpval : (betaParent U u).val = φ + K * m := by
    rw [betaParent_val hd hm hlu]; rfl
  have hsval : ψ + ls * m = s.val := by rw [hψdef, hlsdef]; exact Nat.mod_add_div' s.val m
  have huval : φ + lu * m = u.val := by rw [hφdef, hludef]; exact Nat.mod_add_div' u.val m
  set yVal := ψ + ly * m with hyVal
  -- window: v ≤ yVal < v + m
  rw [hpval] at hwlo hwhi
  -- ly ∈ {K, K+1}
  have hlyK : K ≤ ly := by
    by_contra hc; push Not at hc
    have := sep_master (m := m) (p := ψ) (q := φ) hψlt hφlt hc
    omega
  have hlyK1 : ly ≤ K + 1 := by
    by_contra hc; push Not at hc
    have hlt : K + 1 < ly := by omega
    have hsm := sep_master (m := m) (p := φ) (q := ψ) hφlt hψlt hlt
    have he : (K + 1) * m = K * m + m := by ring
    omega
  -- choose w' = φ + j*m, j ∈ {ls, ls+1}
  set j := if φ < ψ then ls + 1 else ls with hjdef
  -- s.val ≤ w' < s.val + m
  have hsW : s.val ≤ φ + j * m := by
    rw [hjdef]; split
    · rename_i h
      have hsm := sep_master (m := m) (p := ψ) (q := φ) hψlt hφlt (show ls < ls + 1 by omega)
      omega
    · rename_i h
      push Not at h
      have hle : ψ + ls * m ≤ φ + ls * m := by omega
      omega
  have hWs : φ + j * m < s.val + m := by
    rw [hjdef]; split
    · rename_i h
      -- φ + (ls+1)*m < ψ + ls*m + m  ↔ φ < ψ
      have he : (ls + 1) * m = ls * m + m := by ring
      omega
    · rename_i h; push Not at h
      -- ¬(φ < ψ) ⟹ ψ ≤ φ; goal φ + ls*m < ψ + ls*m + m ↔ φ < ψ + m, from φ < m
      omega
  -- K < j ≤ lu
  have hKj : K < j := by
    by_contra hc; push Not at hc
    -- j ≤ K ⟹ φ + j*m ≤ φ + K*m = v < s.val ≤ w', contradiction
    have h1 : φ + j * m ≤ φ + K * m := by
      have := Nat.mul_le_mul_right m hc; omega
    omega
  have hjlu : j ≤ lu := by
    by_contra hc; push Not at hc
    have h1 : φ + (lu + 1) * m ≤ φ + j * m := by
      have := Nat.mul_le_mul_right m (show lu + 1 ≤ j by omega); omega
    have h2 : φ + (lu + 1) * m = u.val + m := by
      have : φ + (lu + 1) * m = (φ + lu * m) + m := by ring
      rw [this, huval]
    omega
  -- GPRE bound on Scount(v, w')
  have hgpre := GPRE hd hm hcanon hu hlu hKj hjlu
  rw [hpval] at hgpre
  -- Scount(yVal, s.val) ≤ Scount(v, s.val) (antitone in lower endpoint; yVal ≥ v)
  have hanti : Scount U yVal s.val ≤ Scount U (φ + K * m) s.val := by
    apply Scount_antitone_left; rw [hyVal]; omega
  -- the key Defc inequality, split on ψ = φ
  unfold Defc
  rw [← hyVal]
  by_cases hψφ : ψ = φ
  · -- ψ = φ ⟹ ly = K (window forces yVal = v) and j = ls
    -- (φ ≤ ψ false here? φ=ψ so φ≤ψ true ⟹ j=ls+1)
    -- recompute: with ψ=φ, w' = φ + (ls+1)*m but s.val = φ + ls*m, so s.val < w', use split anyway.
    -- yVal: from window with ψ=φ: φ + ly*m in [φ+K*m, φ+K*m+m) ⟹ ly = K
    have hlyEq : ly = K := by
      rcases (lt_or_eq_of_le hlyK1) with h | h
      · omega
      · -- ly = K+1: yVal = ψ+(K+1)*m ≥ φ+K*m+m, contradicts hwhi (ψ=φ)
        exfalso
        have he : (K + 1) * m = K * m + m := by ring
        rw [hyVal, h] at hwhi
        omega
    simp_all
  · -- ψ ≠ φ ⟹ s.val < w' strictly, use Scount_split for the -1, then case ly/j
    have hsltw : s.val < φ + j * m := by
      rcases lt_or_eq_of_le hsW with h | h
      · exact h
      · -- s.val = w' = φ+j*m ⟹ ψ + ls*m = φ + j*m, same fiber ⟹ ψ=φ via mod
        exfalso
        have : (ψ + ls * m) % m = (φ + j * m) % m := by rw [hsval, h]
        rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt hψlt, Nat.mod_eq_of_lt hφlt] at this
        exact hψφ this
    have hsplit : Scount U (φ + K * m) (φ + j * m)
        = Scount U (φ + K * m) s.val + 1 + Scount U s.val (φ + j * m) := by
      apply Scount_split hs
      · rw [← hpval] at *; omega
      · exact hsltw
    have hsplitZ : (Scount U (φ + K * m) (φ + j * m) : ℤ)
        = (Scount U (φ + K * m) s.val : ℤ) + 1 + (Scount U s.val (φ + j * m) : ℤ) := by
      exact_mod_cast hsplit
    have hge0 : (0 : ℤ) ≤ (Scount U s.val (φ + j * m) : ℤ) := by exact_mod_cast Nat.zero_le _
    have hantiZ : (Scount U yVal s.val : ℤ) ≤ (Scount U (φ + K * m) s.val : ℤ) := by
      exact_mod_cast hanti
    -- pin j and ly
    have hjcase : j = ls ∨ j = ls + 1 := by rw [hjdef]; split <;> [right; left] <;> rfl
    -- We need: Scount(yVal, s.val) - (ls - ly - 1) ≤ 0, i.e. Scount(yVal,s.val) ≤ ls - ly - 1.
    -- have: Scount(yVal,s) ≤ Scount(v,s); Scount(v,s)+1 ≤ Scount(v,w') ≤ j-K-1.
    -- ⟹ Scount(yVal,s) ≤ j - K - 2. Need j+ly ≤ ls+K+1.
    have hbound : (Scount U yVal s.val : ℤ) ≤ (j : ℤ) - K - 2 := by linarith
    have hjly : (j : ℤ) + ly ≤ ls + K + 1 := by
      -- enumerate ly∈{K,K+1}, j∈{ls,ls+1}; exclude (ly=K+1 ∧ j=ls+1)
      rcases (lt_or_eq_of_le hlyK1) with hlylt | hlyeq
      · -- ly = K
        have : ly = K := by omega
        subst this
        rcases hjcase with hj | hj <;> rw [hj] <;> push_cast <;> omega
      · -- ly = K+1 ⟹ ψ < φ (from hwhi)
        -- hwhi : ψ + ly*m < φ + K*m + m, with ly = K+1
        have hψφlt : ψ < φ := by
          rw [hyVal, hlyeq] at hwhi
          have he2 : (K + 1) * m = K * m + m := by ring
          omega
        -- then j = ls (else j=ls+1 ⟹ φ<ψ, contra)
        have hjeq : j = ls := by
          rw [hjdef]; rw [ite_eq_right (by omega)]
        rw [hlyeq, hjeq]; push_cast; omega
    linarith

/-- **P (no escape).** For an edge `(v,u) = (v*(u), u)` of canonical `U` and an interior survivor
    `s` (`v < s.val < u.val`), the balance parent of `s` does not escape below `v`:
    `v*(u).val ≤ v*(s).val`.
@isnad1 id=le.7h5v.s8.b21e81bc62a2 from=translated src=- shape=ed8b9bbc vocab=fb2bb71e
-/
lemma noEscape {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u s : ZMod (d * m)} (hu : u ∈ U) (hs : s ∈ U)
    (hslo : (betaParent U u).val < s.val) (hshi : s.val < u.val) :
    (betaParent U u).val ≤ (betaParent U s).val := by
  have : NeZero (d*m) := ⟨by positivity⟩
  classical
  have hlu : 1 ≤ u.val / m := survivor_level_pos hd hcanon hu
  have hls : 1 ≤ s.val / m := survivor_level_pos hd hcanon hs
  set φ := u.val % m with hφdef
  set ψ := s.val % m with hψdef
  set lu := u.val / m with hludef
  set ls := s.val / m with hlsdef
  set K := betaK U u with hKdef
  have hφlt : φ < m := Nat.mod_lt _ hm
  have hψlt : ψ < m := Nat.mod_lt _ hm
  have hpval : (betaParent U u).val = φ + K * m := by
    rw [betaParent_val hd hm hlu]; rfl
  have hsval : ψ + ls * m = s.val := by rw [hψdef, hlsdef]; exact Nat.mod_add_div' s.val m
  -- ly and window
  set ly := if ψ < φ then K + 1 else K with hlydef
  have hwlo : (betaParent U u).val ≤ ψ + ly * m := by
    rw [hpval, hlydef]; split
    · rename_i h
      have he : (K + 1) * m = K * m + m := by ring
      omega
    · rename_i h; push Not at h; omega
  have hwhi : ψ + ly * m < (betaParent U u).val + m := by
    rw [hpval, hlydef]; split
    · rename_i h
      have he : (K + 1) * m = K * m + m := by ring
      omega
    · rename_i h; push Not at h; omega
  -- Q gives the start bound; build the shifted IVT
  have hQ := Q hd hm hcanon hu hlu hs hslo hshi (ly := ly) hwlo hwhi
  -- N0: s.val ≥ v + m, so ly < ls
  have hsge : (betaParent U u).val + m ≤ s.val := by
    by_contra hc; push Not at hc
    exact N0 hd hm hcanon hu hlu hs hslo hc
  have hwhi' : ψ + ly * m < φ + K * m + m := by rw [← hpval]; exact hwhi
  have hlyls : ly < ls := by
    -- yVal = ψ+ly*m < v+m ≤ s.val = ψ+ls*m ⟹ ly < ls
    have h1 : ψ + ly * m < ψ + ls * m := by
      rw [hsval]; rw [hpval] at hsge; omega
    by_contra hc; push Not at hc
    have : ψ + ls * m ≤ ψ + ly * m := by
      have := Nat.mul_le_mul_right m hc; omega
    omega
  -- E i := Defc U ψ ls s.val (ly + i), L = (ls - 1) - ly
  set L := (ls - 1) - ly with hLdef
  set E : ℕ → ℤ := fun i => Defc U ψ ls s.val (ly + i) with hEdef
  have hE0 : E 0 ≤ 0 := by
    simp_all
  have hEL : 0 ≤ E L := by
    have hjL : ly + L = ls - 1 := by omega
    simp only [hEdef]
    rw [hjL]
    rw [hlsdef] at *
    exact Defc_top_nonneg U ψ (s.val / m) s.val hls
  have hEstep : ∀ i, i < L → E (i + 1) ≤ E i + 1 := by
    intro i _
    simp only [hEdef]
    have : ly + (i + 1) = (ly + i) + 1 := by omega
    rw [this]
    rw [hlsdef] at *
    exact Defc_step hm U ψ (s.val / m) s.val (ly + i)
  obtain ⟨i, hiL, hEi⟩ := discrete_ivt E L hE0 hEL hEstep
  have hzero : Defc U ψ ls s.val (ly + i) = 0 := by simpa [hEdef] using hEi
  -- betaK s ≥ ly + i ≥ ly
  have hkle : ly + i ≤ s.val / m - 1 := by rw [← hlsdef]; omega
  have hge : ly + i ≤ betaK U s := by
    apply betaK_ge (k := ly + i)
    · rw [hψdef, hlsdef] at hzero; exact hzero
    · exact hkle
  have hbetaKge : ly ≤ betaK U s := by omega
  -- (betaParent U s).val = ψ + betaK s * m ≥ ψ + ly*m ≥ v
  have hspval : (betaParent U s).val = ψ + betaK U s * m := by
    rw [betaParent_val hd hm hls]; rw [hψdef]; rfl
  rw [hspval, hpval]
  -- goal: φ + K*m ≤ ψ + betaK s * m; from φ+K*m ≤ ψ+ly*m (hwlo) and ly ≤ betaK s
  have hmm : ψ + ly * m ≤ ψ + betaK U s * m := by
    have := Nat.mul_le_mul_right m hbetaKge; omega
  rw [hpval] at hwlo
  omega

/-- The **root stays above the edge bottom**: for an edge `(v,u)` and any vertex `w` strictly
    inside its val-interval, the root of `w` has val `≥ v`.
@isnad1 id=le.7h5v.s8.ef67a614138a from=translated src=- shape=e01706d5 vocab=3cb88c0c
-/
lemma root_ge {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U)
    {u : ZMod (d * m)} (hu : u ∈ U) :
    ∀ w : ZMod (d*m), w ∈ bVerts U →
      (betaParent U u).val < w.val → w.val < u.val →
      (betaParent U u).val ≤ (betaRoot hd hm hcanon w).val := by
  have : NeZero (d*m) := ⟨by positivity⟩
  intro w
  induction hn : w.val using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    subst hn
    intro hwv h1 h2
    by_cases hwU : w ∈ U
    · -- survivor: noEscape ⟹ betaParent w ≥ v, and inj ⟹ strict ⟹ recurse
      have hesc := noEscape hd hm hcanon hu hwU h1 h2
      -- betaParent w ≠ betaParent u (else w = u, but w.val < u.val)
      have hne : (betaParent U w).val ≠ (betaParent U u).val := by
        intro heqv
        have heq : betaParent U w = betaParent U u := ZMod.val_injective _ heqv
        have := betaParent_inj hd hm hcanon hwU hu heq
        rw [this] at h2; omega
      have hstrict : (betaParent U u).val < (betaParent U w).val :=
        lt_of_le_of_ne hesc (Ne.symm hne)
      have hpw_lt : (betaParent U w).val < w.val :=
        betaParent_val_lt hd hm (survivor_level_pos hd hcanon hwU)
      have hpw_ltu : (betaParent U w).val < u.val := lt_trans hpw_lt h2
      have hpwv : betaParent U w ∈ bVerts U := betaParent_mem_bVerts hwU
      have hrec := ih (betaParent U w).val hpw_lt (betaParent U w) rfl hpwv hstrict hpw_ltu
      rw [betaRoot_of_mem hd hm hcanon hwU]
      exact hrec
    · -- non-survivor: root is itself
      rw [betaRoot_of_not_mem hd hm hcanon hwU]
      exact le_of_lt h1

/-- **Descend across a threshold.** If `w` is a vertex with `betaRoot w ≤ L < w.val`,
    then descending
    the parent chain crosses `L`: some survivor `b` reachable from `w` has
    `v*(b).val ≤ L < b.val`.
@isnad1 id=ex.5h5v.s7.5ff3e38ddd9f from=translated src=- shape=91815a51 vocab=faed856f
-/
lemma descend_cross {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    {U : Finset (ZMod (d * m))} (hcanon : LevelCanonical d m U) (L : ℕ) :
    ∀ w : ZMod (d*m), (betaRoot hd hm hcanon w).val ≤ L → L < w.val →
      ∃ b : ZMod (d*m), b ∈ U ∧ bReach U w b ∧ (betaParent U b).val ≤ L ∧ L < b.val := by
  intro w
  induction hn : w.val using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    subst hn
    intro hroot hLw
    by_cases hwU : w ∈ U
    · -- w is a survivor; either its parent already ≤ L (done with b=w) or recurse
      have hlu := survivor_level_pos hd hcanon hwU
      have hpw_lt : (betaParent U w).val < w.val := betaParent_val_lt hd hm hlu
      by_cases hpL : (betaParent U w).val ≤ L
      · exact ⟨w, hwU, bReach_refl w, hpL, hLw⟩
      · push Not at hpL  -- L < (betaParent U w).val
        have hpwv : betaParent U w ∈ bVerts U := betaParent_mem_bVerts hwU
        have hrooteq : betaRoot hd hm hcanon (betaParent U w) = betaRoot hd hm hcanon w :=
          (betaRoot_of_mem hd hm hcanon hwU).symm
        have hroot' : (betaRoot hd hm hcanon (betaParent U w)).val ≤ L := by
          rw [hrooteq]; exact hroot
        obtain ⟨b, hbU, hbreach, hb1, hb2⟩ :=
          ih (betaParent U w).val hpw_lt (betaParent U w) rfl hroot' hpL
        refine ⟨b, hbU, ?_, hb1, hb2⟩
        exact bReach_trans (Relation.ReflTransGen.single (Or.inr ⟨hwU, hlu, rfl⟩)) hbreach
    · -- w ∉ U ⟹ betaRoot w = w ⟹ w.val ≤ L, contradicting L < w.val
      rw [betaRoot_of_not_mem hd hm hcanon hwU] at hroot
      omega

/--
@isnad1 id=and.10h7v.s9.90d9c9d2462c from=translated src=- shape=7c751c53 vocab=c9e385c0
-/
lemma beta_interval_closed {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcanon : LevelCanonical d m U) {x z : ZMod (d * m)}
    (hx : x ∈ bVerts U) (hz : z ∈ bVerts U)
    (hne : betaBlock U x ≠ betaBlock U z)
    {p : ZMod (d * m)} (hp : p ∈ betaBlock U z)
    (hlo : (minVal (betaBlock U x) (betaBlock_nonempty hx)).val < p.val)
    (hhi : p.val < (maxVal (betaBlock U x) (betaBlock_nonempty hx)).val) :
    ∀ q ∈ betaBlock U z, (minVal (betaBlock U x) (betaBlock_nonempty hx)).val ≤ q.val ∧
      q.val ≤ (maxVal (betaBlock U x) (betaBlock_nonempty hx)).val := by
  have : NeZero (d*m) := ⟨by positivity⟩
  classical
  set Xne := betaBlock_nonempty hx with hXne
  set minX := minVal (betaBlock U x) Xne with hminX
  set maxX := maxVal (betaBlock U x) Xne with hmaxX
  have hdisj : Disjoint (betaBlock U x) (betaBlock U z) := betaBlock_disjoint hne
  -- minX = betaRoot x
  have hminroot : minX = betaRoot hd hm hcanon x := minVal_betaBlock hd hm hcanon hx
  -- maxX ∈ block x; maxX.val is the block maximum
  have hmaxX_mem : maxX ∈ betaBlock U x := maxVal_mem _ Xne
  have hxreach_max : bReach U x maxX := (mem_betaBlock.mp hmaxX_mem).2
  -- p ∈ block z, so bReach z p, betaRoot z = betaRoot p
  have hzreach_p : bReach U z p := (mem_betaBlock.mp hp).2
  have hrootzp : betaRoot hd hm hcanon z = betaRoot hd hm hcanon p :=
    betaRoot_bReach hd hm hcanon hzreach_p
  -- == Step A: enclosing X-edge of p ==
  -- betaRoot maxX = betaRoot x = minX
  have hroot_max : betaRoot hd hm hcanon maxX = betaRoot hd hm hcanon x :=
    (betaRoot_bReach hd hm hcanon hxreach_max).symm
  have hroot_max_val : (betaRoot hd hm hcanon maxX).val < p.val := by
    rw [hroot_max, ← hminroot]; exact hlo
  obtain ⟨cstar, hcU, hreach_max_c, hgle, hpc⟩ :=
    descend_cross hd hm hcanon p.val maxX (le_of_lt hroot_max_val) hhi
  -- cstar ∈ block x
  have hxreach_c : bReach U x cstar := bReach_trans hxreach_max hreach_max_c
  have hc_mem : cstar ∈ betaBlock U x := by
    rw [mem_betaBlock]
    exact ⟨bReach_mem_bVerts hx hxreach_c, hxreach_c⟩
  have hclu : 1 ≤ cstar.val / m := survivor_level_pos hd hcanon hcU
  -- g* = betaParent cstar ∈ block x, g*.val ≤ p.val
  have hxreach_g : bReach U x (betaParent U cstar) :=
    bReach_trans hxreach_c (Relation.ReflTransGen.single (Or.inr ⟨hcU, hclu, rfl⟩))
  have hg_mem : betaParent U cstar ∈ betaBlock U x := by
    rw [mem_betaBlock]
    exact ⟨bReach_mem_bVerts hx hxreach_g, hxreach_g⟩
  -- minX.val ≤ g*.val (root is block-min)
  have hminX_le_g : minX.val ≤ (betaParent U cstar).val := by
    rw [hminroot]; exact betaRoot_min_in_block hd hm hcanon hg_mem
  -- g*.val < p.val (strict: else g* = p ∈ X ∩ Z)
  have hg_lt_p : (betaParent U cstar).val < p.val := by
    rcases lt_or_eq_of_le hgle with h | h
    · exact h
    · exfalso
      have : betaParent U cstar = p := ZMod.val_injective _ h
      have hpX : p ∈ betaBlock U x := by rw [← this]; exact hg_mem
      exact (Finset.disjoint_left.mp hdisj hpX) hp
  -- == Step B: lower bound. root_ge ⟹ minX.val ≤ (betaRoot p).val ==
  have hrootp_ge : (betaParent U cstar).val ≤ (betaRoot hd hm hcanon p).val :=
    root_ge hd hm hcanon hcU p (bReach_mem_bVerts hz hzreach_p) hg_lt_p hpc
  have hminX_le_rootz : minX.val ≤ (betaRoot hd hm hcanon z).val := by
    rw [hrootzp]; exact le_trans hminX_le_g hrootp_ge
  -- == the main statement ==
  intro q hq
  have hqz : bReach U z q := (mem_betaBlock.mp hq).2
  have hrootz_le_q : (betaRoot hd hm hcanon z).val ≤ q.val :=
    betaRoot_min_in_block hd hm hcanon hq
  refine ⟨le_trans hminX_le_rootz hrootz_le_q, ?_⟩
  -- upper bound by contradiction
  by_contra hqgt
  push Not at hqgt  -- maxX.val < q.val
  -- c*.val ≤ maxX.val
  have hc_le_maxX : cstar.val ≤ maxX.val := maxVal_ge _ Xne _ hc_mem
  -- (betaRoot q).val = (betaRoot z).val ≤ p.val < c*.val (root z below p, p < c*)
  have hrootq : betaRoot hd hm hcanon q = betaRoot hd hm hcanon z :=
    (betaRoot_bReach hd hm hcanon hqz).symm
  have hrootz_le_p : (betaRoot hd hm hcanon z).val ≤ p.val := by
    rw [hrootzp]; exact betaRoot_le hd hm hcanon p
  have hrootq_le_c : (betaRoot hd hm hcanon q).val ≤ cstar.val := by
    rw [hrootq]; exact le_trans hrootz_le_p (le_of_lt hpc)
  have hq_gt_c : cstar.val < q.val := lt_of_le_of_lt hc_le_maxX hqgt
  -- descend Z from q crossing c*.val
  obtain ⟨bz, hbzU, hqreach_bz, haz_le, hc_lt_bz⟩ :=
    descend_cross hd hm hcanon cstar.val q hrootq_le_c hq_gt_c
  -- bz ∈ block z, a_z = betaParent bz ∈ block z
  have hzreach_bz : bReach U z bz := bReach_trans hqz hqreach_bz
  have hbzlu : 1 ≤ bz.val / m := survivor_level_pos hd hcanon hbzU
  have hzreach_az : bReach U z (betaParent U bz) :=
    bReach_trans hzreach_bz (Relation.ReflTransGen.single (Or.inr ⟨hbzU, hbzlu, rfl⟩))
  have haz_mem : betaParent U bz ∈ betaBlock U z := by
    rw [mem_betaBlock]
    exact ⟨bReach_mem_bVerts hz hzreach_az, hzreach_az⟩
  -- a_z.val < c*.val strict (else a_z = cstar ∈ X ∩ Z)
  have haz_lt_c : (betaParent U bz).val < cstar.val := by
    rcases lt_or_eq_of_le haz_le with h | h
    · exact h
    · exfalso
      have : betaParent U bz = cstar := ZMod.val_injective _ h
      have hcZ : cstar ∈ betaBlock U z := by rw [← this]; exact haz_mem
      exact (Finset.disjoint_left.mp hdisj hc_mem) hcZ
  -- root_ge: a_z.val ≤ (betaRoot cstar).val = minX.val
  have hrootc : betaRoot hd hm hcanon cstar = betaRoot hd hm hcanon x :=
    (betaRoot_bReach hd hm hcanon hxreach_c).symm
  have haz_le_minX : (betaParent U bz).val ≤ minX.val := by
    have := root_ge hd hm hcanon hbzU cstar (bReach_mem_bVerts hx hxreach_c) haz_lt_c hc_lt_bz
    simp_all
  -- but a_z ∈ Z so a_z.val ≥ (betaRoot z).val ≥ minX.val
  have haz_ge_minX : minX.val ≤ (betaParent U bz).val :=
    le_trans hminX_le_rootz (betaRoot_min_in_block hd hm hcanon haz_mem)
  have haz_eq : (betaParent U bz).val = minX.val := le_antisymm haz_le_minX haz_ge_minX
  have haz_eq_pt : betaParent U bz = minX := ZMod.val_injective _ haz_eq
  -- minX ∈ block x; betaParent bz ∈ block z ⟹ disjoint contradiction
  have hminX_mem : minX ∈ betaBlock U x := by
    rw [hminroot]; exact betaRoot_mem_block hd hm hcanon hx
  have hminX_in_Z : minX ∈ betaBlock U z := by rw [← haz_eq_pt]; exact haz_mem
  exact (Finset.disjoint_left.mp hdisj hminX_mem) hminX_in_Z

/-- **Unlinked (N).** Distinct blocks of `β U` are unlinked.
@isnad1 id=unlinked.6h5v.s7.cb7fc9ed4a72 from=translated src=- shape=3daab6d4 vocab=a6bbacdb
-/
lemma beta_unlinked {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcanon : LevelCanonical d m U) :
    ∀ A ∈ beta U, ∀ B ∈ beta U, A ≠ B → Unlinked A B := by
  have : NeZero (d*m) := ⟨by positivity⟩
  intro A hA B hB hAB
  rw [mem_beta_iff] at hA hB
  obtain ⟨x, hx, hAx⟩ := hA
  obtain ⟨z, hz, hBz⟩ := hB
  subst hAx; subst hBz
  intro hL
  -- destructure the crossing quadruple
  obtain ⟨a1, ha1, a2, ha2, b1, hb1, b2, hb2, hcase⟩ := hL
  -- both cases are symmetric; reduce to a1<b1<a2<b2 form by relabelling
  -- nonempty witnesses
  have hAne := betaBlock_nonempty hx
  have hBne := betaBlock_nonempty hz
  -- helper: a "linked" quadruple across two distinct blocks forces equal blocks (contradiction).
  -- symmetric in the two block-vertices.
  have core : ∀ s t : ZMod (d*m), s ∈ bVerts U → t ∈ bVerts U →
      betaBlock U s ≠ betaBlock U t →
      ∀ p1 p2 q1 q2 : ZMod (d*m),
      p1 ∈ betaBlock U s → p2 ∈ betaBlock U s → q1 ∈ betaBlock U t → q2 ∈ betaBlock U t →
      p1.val < q1.val → q1.val < p2.val → p2.val < q2.val → False := by
    intro s t hs ht hst p1 p2 q1 q2 hp1 hp2 hq1 hq2 ho1 ho2 ho3
    have hSne := betaBlock_nonempty hs
    have hTne := betaBlock_nonempty ht
    -- q1 strictly inside S's span
    have hminS_le_p1 : (minVal (betaBlock U s) hSne).val ≤ p1.val := minVal_le _ hSne _ hp1
    have hp2_le_maxS : p2.val ≤ (maxVal (betaBlock U s) hSne).val := maxVal_ge _ hSne _ hp2
    have hq1_loS : (minVal (betaBlock U s) hSne).val < q1.val := by omega
    have hq1_hiS : q1.val < (maxVal (betaBlock U s) hSne).val := by omega
    -- T ⊆ [minS, maxS]
    have hTin := beta_interval_closed hd hm hcanon hs ht hst hq1 hq1_loS hq1_hiS
    -- p2 strictly inside T's span
    have hminT_le_q1 : (minVal (betaBlock U t) hTne).val ≤ q1.val := minVal_le _ hTne _ hq1
    have hq2_le_maxT : q2.val ≤ (maxVal (betaBlock U t) hTne).val := maxVal_ge _ hTne _ hq2
    have hp2_loT : (minVal (betaBlock U t) hTne).val < p2.val := by omega
    have hp2_hiT : p2.val < (maxVal (betaBlock U t) hTne).val := by omega
    -- S ⊆ [minT, maxT]
    have hSin := beta_interval_closed hd hm hcanon ht hs (Ne.symm hst) hp2 hp2_loT hp2_hiT
    have hmS_mem : minVal (betaBlock U s) hSne ∈ betaBlock U s := minVal_mem _ hSne
    have hmT_mem : minVal (betaBlock U t) hTne ∈ betaBlock U t := minVal_mem _ hTne
    -- T ⊆ [minS,maxS] ⇒ minS ≤ minT; S ⊆ [minT,maxT] ⇒ minT ≤ minS
    have h1 : (minVal (betaBlock U s) hSne).val ≤ (minVal (betaBlock U t) hTne).val :=
      (hTin _ hmT_mem).1
    have h2 : (minVal (betaBlock U t) hTne).val ≤ (minVal (betaBlock U s) hSne).val :=
      (hSin _ hmS_mem).1
    have hmineq : (minVal (betaBlock U s) hSne).val = (minVal (betaBlock U t) hTne).val := by omega
    have hmineq' : minVal (betaBlock U s) hSne = minVal (betaBlock U t) hTne :=
      ZMod.val_injective _ hmineq
    have hdisj := betaBlock_disjoint hst
    have hmS_in_T : minVal (betaBlock U s) hSne ∈ betaBlock U t := by rw [hmineq']; exact hmT_mem
    exact (Finset.disjoint_left.mp hdisj hmS_mem) hmS_in_T
  rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact core x z hx hz hAB a1 a2 b1 b2 ha1 ha2 hb1 hb2 h1 h2 h3
  · exact core z x hz hx (Ne.symm hAB) b1 b2 a1 a2 hb1 hb2 ha1 ha2 h1 h2 h3

/-! ## Layer 14: β U is a Portrait, and surjectivity. -/

/-- **β(U) is a valid portrait.**
@isnad1 id=portrait.4h3v.s6.f4c9911f1bfa from=translated src=- shape=77d6c486 vocab=7d3294c1
-/
theorem beta_portrait {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcard : U.card = d - 1) (hcanon : LevelCanonical d m U) : Portrait d m (beta U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- IsCriticalSet
    intro S hS
    rw [mem_beta_iff] at hS
    obtain ⟨v, hv, hSeq⟩ := hS
    subst hSeq
    exact betaBlock_critical hd hm hcanon hv
  · -- Disjoint
    exact beta_pairwise_disjoint
  · -- Unlinked
    exact beta_unlinked hd hm hcanon
  · -- weight
    exact beta_weight hd hm hcard hcanon

/-- **Surjectivity.** `T` is surjective onto canonical `(d-1)`-subsets.
@isnad1 id=surjon.2h2v.s7.1d79c5a64e96 from=translated src=- shape=9551e1bb vocab=0e2da7d3
-/
theorem T_surjOn {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    Set.SurjOn (T (N := d*m)) {P | Portrait d m P}
      {U | U.card = d - 1 ∧ LevelCanonical d m U} := by
  intro U hU
  exact ⟨beta U, beta_portrait hd hm hU.1 hU.2, T_beta hd hm hU.2⟩

end CriticalPortraits
