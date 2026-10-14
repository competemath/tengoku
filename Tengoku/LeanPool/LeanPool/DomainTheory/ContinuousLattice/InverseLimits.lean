/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.ContinuousLattice.FunctionSpaces
import Tengoku.LeanPool.LeanPool.DomainTheory.ContinuousLattice.Constructions

/-!
# Inverse limits of continuous lattices (Scott 1972, §4)

We formalize Scott's **Proposition 4.1**: the inverse limit `D_∞` of an ω-system
of continuous
lattices `⟨Dₙ, jₙ⟩` with each `jₙ : D_{n+1} → Dₙ` a projection is again a
continuous lattice.

Scott proves this through injectivity (`D_∞` is an injective `T₀`-space, hence —
Theorem 2.12 — a
continuous lattice), using the maximal-extension Proposition 3.8 and the
compatibility Lemma 3.9.
The *retraction* of `∏ Dₙ` onto `D_∞` that Scott's argument constructs (extend the
identity of
`D_∞` along its inclusion) is realized here **order-theoretically and without
topology**:

* each projection `jₙ = (P n).retr` is the upper adjoint of its embedding `iₙ = (P
n).incl`
  (`projection_galoisConnection`), hence preserves arbitrary infima;
* therefore the compatibility predicate is closed under pointwise `sInf`, making
`D_∞` a complete
  lattice (`completeLatticeOfInf`);
* the inclusion `D_∞ ↪ ∏ Dₙ` preserves infima, so it has a **left adjoint** `r : ∏
Dₙ → D_∞`
  (`invLimRetr`); a left adjoint preserves all suprema, in particular directed
  ones, so `r` is
  Scott-continuous, and `r ∘ incl = id`.

Thus `D_∞` is a (Scott-continuous) retract of the continuous lattice `∏ Dₙ` (Prop
2.9a), so by
Prop 2.10a it is a continuous lattice. This is exactly the retraction Scott builds
via injectivity,
obtained here as the adjoint of the inclusion.
-/

@[expose] public section

namespace Domain.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))

/-- The embedding–projection pair of a projection is a Galois connection `iₙ ⊣
jₙ`: from
`jₙ ∘ iₙ = id` and `iₙ ∘ jₙ ⊑ id` we get `iₙ x ⊑ y ↔ x ⊑ jₙ y`. In particular `jₙ`
(the upper
adjoint) preserves arbitrary infima.
@isnad1 id=galoisco.0h3v.s8.574fc983827b from=translated src=- shape=be13c50e vocab=f0b1f38b
-/
theorem projection_galoisConnection (n : ℕ) :
    GaloisConnection ((P n).incl : D n → D (n + 1)) ((P n).retr : D (n + 1) → D n) := by
  intro x y
  constructor
  · intro h
    have h' := (P n).retr.monotone h
    rwa [(P n).retr_incl] at h'
  · intro h
    exact le_trans ((P n).incl.monotone h) ((P n).incl_retr_le y)

/-- Compatibility of a sequence: `jₙ(x_{n+1}) = xₙ` for all `n`. -/
def Compatible (x : ∀ n, D n) : Prop := ∀ n, (P n).retr (x (n + 1)) = x n

/-- **Scott 1972, §4.** The inverse limit `D_∞` as the subspace of compatible
sequences. -/
abbrev InverseLimit : Type u := {x : ∀ n, D n // Compatible D P x}

/-- `jₙ` preserves arbitrary infima (it is the upper adjoint of `iₙ`).
@isnad1 id=eq.0h4v.s9.35795df4dd2a from=translated src=- shape=68acd4ba vocab=22c62232
-/
theorem retr_sInf (n : ℕ) (A : Set (D (n + 1))) :
    (P n).retr (sInf A) = sInf ((P n).retr '' A) := by
  rw [(projection_galoisConnection D P n).u_sInf, sInf_image]

/-- The pointwise infimum of compatible sequences is compatible.
@isnad1 id=compatib.0h3v.s7.cde3888289b3 from=translated src=- shape=52d79625 vocab=611b5179
-/
theorem compatible_sInf (S : Set (InverseLimit D P)) :
    Compatible D P (sInf (Subtype.val '' S)) := by
  intro n
  rw [sInf_apply_eq_sInf_image, sInf_apply_eq_sInf_image, retr_sInf]
  congr 1
  rw [Set.image_image]
  exact Set.image_congr (by rintro _ ⟨x, _, rfl⟩; exact x.2 n)

noncomputable instance : InfSet (InverseLimit D P) :=
  ⟨fun S => ⟨sInf (Subtype.val '' S), compatible_sInf D P S⟩⟩

/--
@isnad1 id=eq.0h3v.s7.4821c60bf5db from=translated src=- shape=fd171601 vocab=611b5179
-/
theorem coe_sInf (S : Set (InverseLimit D P)) :
    ((sInf S : InverseLimit D P) : ∀ n, D n) = sInf (Subtype.val '' S) := rfl

/--
@isnad1 id=isglb.0h3v.s6.f961b07fa4d6 from=translated src=- shape=1ca517e2 vocab=5eefc8e8
-/
theorem isGLB_sInf' (S : Set (InverseLimit D P)) : IsGLB S (sInf S) := by
  constructor
  · intro x hx
    refine Subtype.coe_le_coe.mp ?_
    rw [coe_sInf]
    exact sInf_le (Set.mem_image_of_mem _ hx)
  · intro b hb
    refine Subtype.coe_le_coe.mp ?_
    rw [coe_sInf]
    refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Subtype.coe_le_coe.mpr (hb hx)

noncomputable instance instCompleteLattice : CompleteLattice (InverseLimit D P) :=
  completeLatticeOfInf (InverseLimit D P) (isGLB_sInf' D P)

/-- For a directed, nonempty family, the inverse-limit supremum is computed
pointwise (each `jₙ`
is Scott-continuous, so the pointwise sup of compatible sequences is compatible
and is the least
upper bound in `D_∞`).
@isnad1 id=eq.2h3v.s7.474937f8e037 from=translated src=- shape=772ac950 vocab=554de737
-/
theorem coe_sSup_of_directed (S : Set (InverseLimit D P)) (hSne : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) :
    ((sSup S : InverseLimit D P) : ∀ n, D n) = sSup (Subtype.val '' S) := by
  have hcompat : Compatible D P (sSup (Subtype.val '' S)) := by
    intro n
    rw [sSup_apply_eq_sSup_image, sSup_apply_eq_sSup_image]
    set A : Set (D (n + 1)) := (fun f : ∀ m, D m => f (n + 1)) '' (Subtype.val '' S) with hA
    have hAne : A.Nonempty := (hSne.image _).image _
    have hAdir : DirectedOn (· ≤ ·) A := by
      rintro _ ⟨_, ⟨x, hxS, rfl⟩, rfl⟩ _ ⟨_, ⟨y, hyS, rfl⟩, rfl⟩
      obtain ⟨z, hzS, hxz, hyz⟩ := hSdir x hxS y hyS
      exact ⟨z.1 (n + 1), ⟨z.1, ⟨z, hzS, rfl⟩, rfl⟩, hxz (n + 1), hyz (n + 1)⟩
    rw [(P n).retr.preservesDirectedSup_coe A hAne hAdir]
    congr 1
    rw [hA, Set.image_image]
    exact Set.image_congr (by rintro _ ⟨x, _, rfl⟩; exact x.2 n)
  set p : InverseLimit D P := ⟨sSup (Subtype.val '' S), hcompat⟩ with hp
  have hlub : IsLUB S p := by
    constructor
    · intro x hx
      refine Subtype.coe_le_coe.mp ?_
      exact le_sSup (Set.mem_image_of_mem _ hx)
    · intro b hb
      refine Subtype.coe_le_coe.mp ?_
      refine sSup_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact Subtype.coe_le_coe.mpr (hb hx)
  rw [(isLUB_sSup S).unique hlub]

/-- The inclusion `D_∞ ↪ ∏ Dₙ` preserves directed suprema.
@isnad1 id=preserve.0h2v.s6.9112e8f54f84 from=translated src=- shape=706b1e66 vocab=07774a7a
-/
theorem incl_preservesDirectedSup :
    PreservesDirectedSup (Subtype.val : InverseLimit D P → ∀ n, D n) := by
  intro S hSne hSdir
  exact coe_sSup_of_directed D P S hSne hSdir

/-- Scott's retraction `r : ∏ Dₙ → D_∞`, realized as the **left adjoint** of the
inclusion:
`r y = ⊓ { x ∈ D_∞ : y ⊑ x }`, the least compatible sequence above `y`. -/
noncomputable def invLimRetr (y : ∀ n, D n) : InverseLimit D P :=
  sInf {x : InverseLimit D P | y ≤ x.1}

/--
@isnad1 id=le.0h3v.s6.ec4dae646cdb from=translated src=- shape=c8d75d73 vocab=8df784d3
-/
theorem le_coe_invLimRetr (y : ∀ n, D n) : y ≤ (invLimRetr D P y).1 := by
  rw [invLimRetr, coe_sInf]
  simp_all

/-- `r ⊣ incl`: the retraction is left adjoint to the inclusion.
@isnad1 id=galoisco.0h2v.s7.2a56fbd64b2f from=translated src=- shape=0c5e6e91 vocab=82acdb15
-/
theorem invLimRetr_galoisConnection :
    GaloisConnection (invLimRetr D P) (Subtype.val : InverseLimit D P → ∀ n, D n) := by
  intro y x
  constructor
  · intro h
    exact le_trans (le_coe_invLimRetr D P y) (Subtype.coe_le_coe.mpr h)
  · intro h
    exact sInf_le (show x ∈ {x' : InverseLimit D P | y ≤ x'.1} from h)

/-- The retraction preserves directed suprema (a left adjoint preserves all
suprema).
@isnad1 id=preserve.0h2v.s6.632e2f4f9fb7 from=translated src=- shape=67cb9388 vocab=a928c81b
-/
theorem invLimRetr_preservesDirectedSup :
    PreservesDirectedSup (invLimRetr D P) := by
  intro S _ _
  rw [(invLimRetr_galoisConnection D P).l_sSup, sSup_image]

/-- `r ∘ incl = id`: the retraction fixes `D_∞`.
@isnad1 id=eq.0h3v.s6.a70e0309a9bb from=translated src=- shape=a88918f7 vocab=2924ce5c
-/
theorem invLimRetr_incl (x : InverseLimit D P) : invLimRetr D P x.1 = x := by
  refine le_antisymm ?_ ?_
  · exact sInf_le (show x ∈ {x' : InverseLimit D P | (x.1 : ∀ n, D n) ≤ x'.1} from le_refl x.1)
  · refine le_sInf ?_
    simp_all

/-- `D_∞` is a Scott-continuous retract of the product `∏ Dₙ`. -/
noncomputable def inverseLimitRetraction :
    IsContinuousLatticeRetraction (InverseLimit D P) (∀ n, D n) where
  incl := ⟨Subtype.val, continuous_of_preservesDirectedSup (incl_preservesDirectedSup D P)⟩
  retr := ⟨invLimRetr D P, continuous_of_preservesDirectedSup (invLimRetr_preservesDirectedSup D P)⟩
  retr_incl := invLimRetr_incl D P

/-- **Scott 1972, Proposition 4.1.** The inverse limit `D_∞` of an ω-system of
continuous lattices
with projection bonding maps is itself a continuous lattice. The product `∏ Dₙ` is
a continuous
lattice (Prop 2.9a) and `D_∞` is a retract of it (`inverseLimitRetraction`), so
Prop 2.10a applies.
@isnad1 id=iscontin.1h2v.s6.d03d62b10da2 from=translated src=- shape=bb3d7887 vocab=cad715b4
-/
theorem proposition_4_1 (hD : ∀ n, IsContinuousLattice (D n)) :
    IsContinuousLattice (InverseLimit D P) :=
  proposition_2_10_a (inverseLimitRetraction D P) (proposition_2_9_a D hD)

/-! ### Proposition 4.2: the maps `j_{∞n}` are projections

We construct Scott's embeddings `i_{n∞} : Dₙ → D_∞` and show that `⟨i_{n∞},
j_{∞n}⟩` is a
projection, where `j_{∞n}(x) = xₙ`. The component `i_{n∞}(x)_m` climbs the tower
of embeddings
`iₖ = (P k).incl` for `m ≥ n` (`embLE`) and descends the tower of projections `jₖ
= (P k).retr`
for `m < n` (`projLE`). -/

/-- Climb the tower of embeddings: for `n ≤ m`, `embLE h = i_{m-1} ∘ … ∘ iₙ : Dₙ →
D_m`. -/
def embLE {n m : ℕ} (h : n ≤ m) (x : D n) : D m :=
  Nat.leRecOn h (fun {k} (y : D k) => (P k).incl y) x

/--
@isnad1 id=eq.1h4v.s6.49ccfb612958 from=translated src=- shape=1f24e375 vocab=4f538d94
-/
theorem embLE_self {n : ℕ} (h : n ≤ n) (x : D n) : embLE D P h x = x := by
  simp only [embLE, Nat.leRecOn_self]

/--
@isnad1 id=eq.2h5v.s8.18d4a031faca from=translated src=- shape=8b0e9c77 vocab=29edc4fd
-/
theorem embLE_succ {n m : ℕ} (h1 : n ≤ m) (h2 : n ≤ m + 1) (x : D n) :
    embLE D P h2 x = (P m).incl (embLE D P h1 x) := by
  simp only [embLE]
  rw [Nat.leRecOn_succ h1]

/--
@isnad1 id=eq.2h5v.s8.a48ffefbe47c from=translated src=- shape=206bd58d vocab=29edc4fd
-/
theorem embLE_succ_left {n m : ℕ} (h1 : n ≤ m) (h2 : n + 1 ≤ m) (x : D n) :
    embLE D P h2 ((P n).incl x) = embLE D P h1 x := by
  simp only [embLE]
  exact Nat.leRecOn_succ_left x h1 h2

/--
@isnad1 id=le.2h6v.s7.6caf5ce1c69b from=translated src=- shape=cfe77e8a vocab=4f538d94
-/
theorem embLE_mono {n m : ℕ} (h : n ≤ m) {x y : D n} (hxy : x ≤ y) :
    embLE D P h x ≤ embLE D P h y := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [embLE_self, embLE_self]
      exact hxy
  | succ k hk ih =>
      rw [embLE_succ D P hk (Nat.le_succ_of_le hk), embLE_succ D P hk (Nat.le_succ_of_le hk)]
      exact (P k).incl.monotone ih

/-- Descend the tower of projections: for `m ≤ n`, `projLE h = j_m ∘ … ∘ j_{n-1} :
D_n → Dₘ`. -/
def projLE {m n : ℕ} (h : m ≤ n) (x : D n) : D m :=
  Nat.leRecOn (C := fun k => D k → D m) h
    (fun {k} (g : D k → D m) (w : D (k + 1)) => g ((P k).retr w)) id x

/--
@isnad1 id=eq.1h4v.s6.54fed43b3947 from=translated src=- shape=1f24e375 vocab=cec2d909
-/
theorem projLE_self {m : ℕ} (h : m ≤ m) (x : D m) : projLE D P h x = x := by
  simp only [projLE, Nat.leRecOn_self, id_eq]

/--
@isnad1 id=eq.2h5v.s8.0129b0d3ed65 from=translated src=- shape=ef583ab7 vocab=a2d6d09a
-/
theorem projLE_succ {m n : ℕ} (h1 : m ≤ n) (h2 : m ≤ n + 1) (z : D (n + 1)) :
    projLE D P h2 z = projLE D P h1 ((P n).retr z) := by
  simp only [projLE]
  rw [Nat.leRecOn_succ (C := fun k => D k → D m) h1]

/--
@isnad1 id=le.2h6v.s7.cbca36204d11 from=translated src=- shape=ae4534b5 vocab=cec2d909
-/
theorem projLE_mono {m n : ℕ} (h : m ≤ n) {x y : D n} (hxy : x ≤ y) :
    projLE D P h x ≤ projLE D P h y := by
  induction n, h using Nat.le_induction with
  | base =>
      rw [projLE_self, projLE_self]
      exact hxy
  | succ k hk ih =>
      rw [projLE_succ D P hk (Nat.le_succ_of_le hk), projLE_succ D P hk (Nat.le_succ_of_le hk)]
      exact ih ((P k).retr.monotone hxy)

/-- Peeling the last projection: `(P m).retr ∘ projLE (m+1 ≤ n) = projLE (m ≤ n)`.
@isnad1 id=eq.1h5v.s8.0a1109460594 from=translated src=- shape=a98a7aa1 vocab=33f23a4d
-/
theorem projLE_retr {m : ℕ} : ∀ {n : ℕ} (h : m + 1 ≤ n) (x : D n),
    (P m).retr (projLE D P h x) = projLE D P (Nat.le_of_succ_le h) x := by
  intro n h
  induction n, h using Nat.le_induction with
  | base =>
      intro x
      rw [projLE_succ D P (le_refl m) (Nat.le_of_succ_le (le_refl (m + 1))) x]
      simp only [projLE_self]
  | succ k hk ih =>
      intro x
      rw [projLE_succ D P hk (Nat.le_succ_of_le hk) x, ih ((P k).retr x),
        projLE_succ D P (Nat.le_of_succ_le hk) (Nat.le_of_succ_le (Nat.le_succ_of_le hk)) x]

/-- Scott's embedding component `i_{n∞}(x)_m`: climb for `m ≥ n`, descend for `m <
n`. -/
def iComp (n : ℕ) (x : D n) (m : ℕ) : D m :=
  if h : n ≤ m then embLE D P h x else projLE D P (le_of_lt (not_le.mp h)) x

/--
@isnad1 id=eq.1h5v.s6.287c090924c4 from=translated src=- shape=741852a9 vocab=dc4f793d
-/
theorem iComp_of_le {n m : ℕ} (h : n ≤ m) (x : D n) : iComp D P n x m = embLE D P h x :=
  dite_eq_left h

/--
@isnad1 id=eq.1h5v.s6.b73ae8fb9e67 from=translated src=- shape=df0799a2 vocab=d55f2d16
-/
theorem iComp_of_ge {n m : ℕ} (h : ¬ n ≤ m) (x : D n) :
    iComp D P n x m = projLE D P (le_of_lt (not_le.mp h)) x :=
  dite_eq_right h

/--
@isnad1 id=eq.0h4v.s6.480b20712b08 from=translated src=- shape=fbe0c9ad vocab=5c565f07
-/
theorem iComp_self (n : ℕ) (x : D n) : iComp D P n x n = x := by
  rw [iComp_of_le D P (le_refl n), embLE_self]

/-- The sequence `i_{n∞}(x)` is compatible, hence a genuine point of `D_∞`.
@isnad1 id=compatib.0h4v.s6.30c49e2ff49e from=translated src=- shape=11564ee0 vocab=8a646d2c
-/
theorem iComp_compatible (n : ℕ) (x : D n) : Compatible D P (iComp D P n x) := by
  intro m
  by_cases h1 : n ≤ m
  · rw [iComp_of_le D P h1, iComp_of_le D P (Nat.le_succ_of_le h1),
      embLE_succ D P h1 (Nat.le_succ_of_le h1), (P m).retr_incl]
  · by_cases h2 : n ≤ m + 1
    · have hn : n = m + 1 := le_antisymm h2 (not_le.mp h1)
      subst hn
      rw [iComp_of_le D P (le_refl (m + 1)), embLE_self, iComp_of_ge D P h1,
        projLE_succ D P (le_refl m) (le_of_lt (not_le.mp h1)) x, projLE_self]
    · rw [iComp_of_ge D P h2, iComp_of_ge D P h1,
        projLE_retr D P (le_of_lt (not_le.mp h2)) x]

/-- For a compatible sequence `y`, descending from level `n` to `m ≤ n` recovers
`yₘ`.
@isnad1 id=eq.1h5v.s6.f16de08d428d from=translated src=- shape=3298eeac vocab=25d33443
-/
theorem projLE_compatible {m : ℕ} (y : InverseLimit D P) :
    ∀ {n : ℕ} (h : m ≤ n), projLE D P h (y.1 n) = y.1 m := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => rw [projLE_self]
  | succ k hk ih => rw [projLE_succ D P hk (Nat.le_succ_of_le hk), y.2 k, ih]

/-- For a compatible sequence `y`, climbing `yₙ` up to level `m ≥ n` stays below
`yₘ`.
@isnad1 id=le.1h5v.s7.c0c7f84439b5 from=translated src=- shape=c41ce48a vocab=8eed2c78
-/
theorem embLE_le {n : ℕ} (y : InverseLimit D P) {m : ℕ} (h : n ≤ m) :
    embLE D P h (y.1 n) ≤ y.1 m := by
  induction m, h using Nat.le_induction with
  | base => exact le_of_eq (embLE_self D P _ _)
  | succ k hk ih =>
      rw [embLE_succ D P hk (Nat.le_succ_of_le hk)]
      calc (P k).incl (embLE D P hk (y.1 n))
          ≤ (P k).incl (y.1 k) := (P k).incl.monotone ih
        _ = (P k).incl ((P k).retr (y.1 (k + 1))) := by rw [y.2 k]
        _ ≤ y.1 (k + 1) := (P k).incl_retr_le _

/-- `i_{n∞}(yₙ) ⊑ y` coordinatewise (the heart of `incl_retr_le` for `j_{∞n}`).
@isnad1 id=le.0h5v.s6.d0693697d3dc from=translated src=- shape=85ec6795 vocab=11dda9a5
-/
theorem iComp_incl_le (n : ℕ) (y : InverseLimit D P) (m : ℕ) :
    iComp D P n (y.1 n) m ≤ y.1 m := by
  by_cases h : n ≤ m
  · rw [iComp_of_le D P h]; exact embLE_le D P y h
  · rw [iComp_of_ge D P h]
    exact le_of_eq (projLE_compatible D P y (le_of_lt (not_le.mp h)))

/-- The tower of embeddings is Scott-continuous (a composite of the `iₖ`).
@isnad1 id=preserve.1h4v.s6.1f6d288f9c5f from=translated src=- shape=35968436 vocab=cb31b282
-/
theorem embLE_preservesDirectedSup {n m : ℕ} (h : n ≤ m) :
    PreservesDirectedSup (embLE D P h) := by
  induction m, h using Nat.le_induction with
  | base =>
      have hid : embLE D P (le_refl n) = id := funext (fun x => embLE_self D P (le_refl n) x)
      rw [hid]; intro S _ _; simp
  | succ k hk ih =>
      have hfun : embLE D P (Nat.le_succ_of_le hk)
          = (fun y : D k => (P k).incl y) ∘ embLE D P hk :=
        funext (fun x => embLE_succ D P hk (Nat.le_succ_of_le hk) x)
      rw [hfun]
      exact ScottMap.preservesDirectedSup_comp
        (fun S hS hd => (P k).incl.preservesDirectedSup_coe S hS hd) ih

/-- The tower of projections is Scott-continuous (a composite of the `jₖ`).
@isnad1 id=preserve.1h4v.s6.502476f0dbb7 from=translated src=- shape=440790e4 vocab=996187a3
-/
theorem projLE_preservesDirectedSup {m n : ℕ} (h : m ≤ n) :
    PreservesDirectedSup (projLE D P h) := by
  induction n, h using Nat.le_induction with
  | base =>
      have hid : projLE D P (le_refl m) = id := funext (fun x => projLE_self D P (le_refl m) x)
      rw [hid]; intro S _ _; simp
  | succ k hk ih =>
      have hfun : projLE D P (Nat.le_succ_of_le hk)
          = projLE D P hk ∘ (fun z : D (k + 1) => (P k).retr z) :=
        funext (fun x => projLE_succ D P hk (Nat.le_succ_of_le hk) x)
      rw [hfun]
      exact ScottMap.preservesDirectedSup_comp ih
        (fun S hS hd => (P k).retr.preservesDirectedSup_coe S hS hd)

/--
@isnad1 id=preserve.0h4v.s6.8fb2fe0d85b6 from=translated src=- shape=66c716b7 vocab=ee251f53
-/
theorem iComp_preservesDirectedSup (n m : ℕ) :
    PreservesDirectedSup (fun x : D n => iComp D P n x m) := by
  by_cases h : n ≤ m
  · have hfun : (fun x : D n => iComp D P n x m) = embLE D P h :=
      funext (fun x => iComp_of_le D P h x)
    rw [hfun]; exact embLE_preservesDirectedSup D P h
  · have hfun : (fun x : D n => iComp D P n x m) = projLE D P (le_of_lt (not_le.mp h)) :=
      funext (fun x => iComp_of_ge D P h x)
    rw [hfun]; exact projLE_preservesDirectedSup D P _

/--
@isnad1 id=monotone.0h4v.s6.f61fdc7c72c8 from=translated src=- shape=66c716b7 vocab=9d6f5731
-/
theorem iComp_monotone (n m : ℕ) : Monotone (fun x : D n => iComp D P n x m) :=
  preservesDirectedSup_monotone (iComp_preservesDirectedSup D P n m)

/-- The embedding `i_{n∞} : Dₙ → D_∞` as a bare function into the inverse limit. -/
def embInfFun (n : ℕ) (x : D n) : InverseLimit D P := ⟨iComp D P n x, iComp_compatible D P n x⟩

/--
@isnad1 id=eq.0h4v.s6.cd2cebf085ff from=translated src=- shape=bffa68e0 vocab=60e71b2e
-/
@[simp] theorem embInfFun_coe (n : ℕ) (x : D n) : (embInfFun D P n x).1 = iComp D P n x := rfl

/--
@isnad1 id=monotone.0h3v.s6.c1beaeb28c47 from=translated src=- shape=685f469b vocab=b4f08498
-/
theorem embInf_monotone (n : ℕ) : Monotone (embInfFun D P n) := by
  intro x x' hxx
  rw [← Subtype.coe_le_coe]
  intro m
  exact iComp_monotone D P n m hxx

/--
@isnad1 id=preserve.0h3v.s6.e9edd4c58936 from=translated src=- shape=685f469b vocab=da026d36
-/
theorem embInf_preservesDirectedSup (n : ℕ) : PreservesDirectedSup (embInfFun D P n) := by
  intro S hS hSdir
  have hTne : (embInfFun D P n '' S).Nonempty := hS.image _
  have hTdir : DirectedOn (· ≤ ·) (embInfFun D P n '' S) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨embInfFun D P n c, Set.mem_image_of_mem _ hc,
      embInf_monotone D P n hac, embInf_monotone D P n hbc⟩
  apply Subtype.ext
  rw [coe_sSup_of_directed D P (embInfFun D P n '' S) hTne hTdir]
  funext m
  have heq : Function.eval m '' (Subtype.val '' (embInfFun D P n '' S))
      = (fun x => iComp D P n x m) '' S := by
    simp only [Set.image_image, embInfFun_coe, Function.eval]
  rw [sSup_apply_eq_sSup_image, heq]
  exact iComp_preservesDirectedSup D P n m hS hSdir

/-- The projection `j_{∞n} : D_∞ → Dₙ` as a bare function. -/
def projInfFun (n : ℕ) (y : InverseLimit D P) : D n := y.1 n

/--
@isnad1 id=preserve.0h3v.s6.b97a84157fde from=translated src=- shape=a2efe975 vocab=971f55bc
-/
theorem eval_preservesDirectedSup (n : ℕ) : PreservesDirectedSup (projInfFun D P n) := by
  intro S hS hSdir
  have hL : (sSup S : InverseLimit D P).1 n = sSup ((fun y : InverseLimit D P => y.1 n) '' S) := by
    rw [coe_sSup_of_directed D P S hS hSdir, sSup_apply_eq_sSup_image]
    congr 1
    rw [Set.image_image]
  exact hL

/-- The embedding `i_{n∞} : Dₙ → D_∞`, Scott-continuous. -/
noncomputable def embInf (n : ℕ) : ScottMap (D n) (InverseLimit D P) :=
  ⟨embInfFun D P n, continuous_of_preservesDirectedSup (embInf_preservesDirectedSup D P n)⟩

/-- The projection `j_{∞n} : D_∞ → Dₙ`, Scott-continuous. -/
noncomputable def projInf (n : ℕ) : ScottMap (InverseLimit D P) (D n) :=
  ⟨projInfFun D P n, continuous_of_preservesDirectedSup (eval_preservesDirectedSup D P n)⟩

/-- **Scott 1972, Proposition 4.2.** Each `j_{∞n} : D_∞ → Dₙ` is a projection of
continuous
lattices, with embedding `i_{n∞} = embInf n`. -/
noncomputable def proposition_4_2 (n : ℕ) :
    IsContinuousLatticeProjection (D n) (InverseLimit D P) where
  incl := embInf D P n
  retr := projInf D P n
  retr_incl x := iComp_self D P n x
  incl_retr_le y := by
    rw [← Subtype.coe_le_coe]
    intro m
    exact iComp_incl_le D P n y m

/-- **Scott 1972, §4 (recursion equation).** `i_{n∞} = i_{(n+1)∞} ∘ iₙ`.
@isnad1 id=eq.0h4v.s8.111e10c282c2 from=translated src=- shape=5fcd49cb vocab=0db83a37
-/
theorem embInf_succ (n : ℕ) (x : D n) :
    embInf D P (n + 1) ((P n).incl x) = embInf D P n x := by
  apply Subtype.ext
  funext m
  change iComp D P (n + 1) ((P n).incl x) m = iComp D P n x m
  by_cases h1 : n ≤ m
  · by_cases h2 : n + 1 ≤ m
    · rw [iComp_of_le D P h2, iComp_of_le D P h1, embLE_succ_left D P h1 h2]
    · have hmn : m = n := le_antisymm (Nat.lt_succ_iff.mp (not_le.mp h2)) h1
      subst hmn
      rw [iComp_self, iComp_of_ge D P h2,
        projLE_succ D P (le_refl m) (le_of_lt (not_le.mp h2)) ((P m).incl x),
        projLE_self, (P m).retr_incl]
  · have h2 : ¬ n + 1 ≤ m := fun h => h1 (le_trans (Nat.le_succ n) h)
    rw [iComp_of_ge D P h2, iComp_of_ge D P h1,
      projLE_succ D P (le_of_lt (not_le.mp h1)) (le_of_lt (not_le.mp h2)) ((P n).incl x),
      (P n).retr_incl]

/-- The family `n ↦ i_{n∞}(xₙ)` is monotone (the lub defining `x` is monotone).
@isnad1 id=le.0h4v.s8.37aa5f9d0bfc from=translated src=- shape=057e78b7 vocab=b5ac7edb
-/
theorem embInf_le_succ (x : InverseLimit D P) (n : ℕ) :
    embInf D P n (x.1 n) ≤ embInf D P (n + 1) (x.1 (n + 1)) := by
  rw [← embInf_succ D P n (x.1 n)]
  exact embInf_monotone D P (n + 1)
    (by calc (P n).incl (x.1 n) = (P n).incl ((P n).retr (x.1 (n + 1))) := by rw [x.2 n]
          _ ≤ x.1 (n + 1) := (P n).incl_retr_le _)

/--
@isnad1 id=directed.0h3v.s7.acf263cbf98f from=translated src=- shape=dc6a135d vocab=1a0d8dcb
-/
theorem embInf_family_directed (x : InverseLimit D P) :
    DirectedOn (· ≤ ·) (Set.range (fun n => embInf D P n (x.1 n))) :=
  directedOn_range.2 (monotone_nat_of_le_succ (embInf_le_succ D P x)).directed_le

/-- **Scott 1972, §4.** Each `x ∈ D_∞` is the (monotone) lub of its projections:
`x = ⨆ₙ i_{n∞}(xₙ)`.
@isnad1 id=eq.0h3v.s7.1a6e90c7fff3 from=translated src=- shape=10b78fd7 vocab=c4a9c07d
-/
theorem inverseLimit_eq_iSup (x : InverseLimit D P) :
    x = ⨆ n, embInf D P n (x.1 n) := by
  have hdir := embInf_family_directed D P x
  have hne : (Set.range (fun n => embInf D P n (x.1 n))).Nonempty := Set.range_nonempty _
  refine le_antisymm ?_ ?_
  · rw [← Subtype.coe_le_coe]
    have hcoe : ((⨆ n, embInf D P n (x.1 n) : InverseLimit D P)).1
        = sSup (Subtype.val '' Set.range (fun n => embInf D P n (x.1 n))) := by
      rw [← sSup_range]
      exact coe_sSup_of_directed D P _ hne hdir
    rw [hcoe]
    intro m
    have hmem : (embInf D P m (x.1 m)).1
        ∈ Subtype.val '' Set.range (fun n => embInf D P n (x.1 n)) :=
      ⟨embInf D P m (x.1 m), ⟨m, rfl⟩, rfl⟩
    have hle := (le_sSup hmem) m
    rwa [show (embInf D P m (x.1 m)).1 m = x.1 m from iComp_self D P m (x.1 m)] at hle
  · exact iSup_le fun n => by
      rw [← Subtype.coe_le_coe]; intro m; exact iComp_incl_le D P n x m

/-- **Scott 1972, §4 (functional equation, "the remark following 4.2").** The
identity of `D_∞` is
the directed lub of the approximating projections `rₙ = i_{n∞} ∘ j_{∞n}`:
`id = ⨆ₙ i_{n∞} ∘ j_{∞n}`. This is the algebraic identity at the heart of Theorem
4.4.
@isnad1 id=eq.0h2v.s7.e55d96dfa75f from=translated src=- shape=992dbc0e vocab=b4c7bba5
-/
theorem idInf_eq_iSup :
    (ScottMap.idMap : ScottMap (InverseLimit D P) (InverseLimit D P))
      = ⨆ n, (embInf D P n).comp (projInf D P n) := by
  apply ScottMap.ext
  intro x
  rw [show (⨆ n, (embInf D P n).comp (projInf D P n))
        = sSup (Set.range fun n => (embInf D P n).comp (projInf D P n)) from sSup_range.symm,
    ScottMap.sSup_apply, ScottMap.idMap_apply, ← Set.range_comp, sSup_range]
  exact inverseLimit_eq_iSup D P x

/-- **Scott 1972, Lemma 4.5.** A criterion for recognizing projections out of the
limit: if a
sequence `u : ∀ n, D_{n+1}` satisfies the (shifted) recursion `j_{n+1}(u_{n+2}) =
u_{n+1}`, then the
monotone limit `u_∞ = ⨆ₙ i_{(n+1)∞}(uₙ)` has `j_{∞(n+1)}(u_∞) = uₙ`.

Proof: extend `u` to a *compatible* sequence `w` (`w₀ = j₀(u₀)`, `w_{k+1} = u_k`);
then `w` is a
point of `D_∞`, and since the family `k ↦ i_{k∞}(w_k)` is monotone, dropping its
`0`-th term does
not change the lub (`Monotone.iSup_nat_add`), so `u_∞ = ⨆ₖ i_{k∞}(w_k) = w` by
`inverseLimit_eq_iSup`.
Hence `j_{∞(n+1)}(u_∞) = w_{n+1} = uₙ`.
@isnad1 id=eq.1h4v.s9.9525c052539b from=translated src=- shape=cb6fdd5b vocab=f8ff3743
-/
theorem lemma_4_5 (u : ∀ n, D (n + 1))
    (hu : ∀ n, (P (n + 1)).retr (u (n + 1)) = u n) (n : ℕ) :
    (⨆ k, embInf D P (k + 1) (u k) : InverseLimit D P).1 (n + 1) = u n := by
  have hw : Compatible D P (fun k => Nat.casesOn k ((P 0).retr (u 0)) (fun m => u m)) := by
    intro k
    cases k with
    | zero => rfl
    | succ m => exact hu m
  set wlim : InverseLimit D P :=
    ⟨fun k => Nat.casesOn k ((P 0).retr (u 0)) (fun m => u m), hw⟩ with hwlim
  have hGmono : Monotone (fun k => embInf D P k (wlim.1 k)) :=
    monotone_nat_of_le_succ (embInf_le_succ D P wlim)
  have hsup : (⨆ k, embInf D P (k + 1) (u k) : InverseLimit D P) = wlim := by
    have h1 : (⨆ k, embInf D P (k + 1) (u k) : InverseLimit D P)
        = ⨆ k, embInf D P (k + 1) (wlim.1 (k + 1)) := rfl
    rw [h1, Monotone.iSup_nat_add hGmono 1, ← inverseLimit_eq_iSup D P wlim]
  rw [hsup]

/-! ### Corollary 4.3: `D_∞` is also the *direct* limit

Given continuous `fₙ : Dₙ → D'` into any complete lattice with `fₙ = f_{n+1} ∘
iₙ`, the map
`f∞(x) = ⨆ₙ fₙ(xₙ)` is the unique continuous mediating map with `fₙ = f∞ ∘
i_{n∞}`. -/

variable {D' : Type*} [CompleteLattice D']

/-- The mediating map of Corollary 4.3: `f∞(x) = ⨆ₙ fₙ(xₙ)`. -/
def coconeInf (f : ∀ n, ScottMap (D n) D') (x : InverseLimit D P) : D' :=
  ⨆ n, f n (x.1 n)

/--
@isnad1 id=eq.0h5v.s7.dca21d24b1eb from=translated src=- shape=20832484 vocab=db4d800b
-/
theorem coconeInf_apply (f : ∀ n, ScottMap (D n) D') (x : InverseLimit D P) :
    coconeInf D P f x = ⨆ n, f n (x.1 n) := rfl

/-- Climbing then applying `f` is constant: `f_m(i_{m-1}…iₙ x) = fₙ(x)`.
@isnad1 id=eq.2h7v.s8.405aee804a55 from=translated src=- shape=627485b0 vocab=66bd26c0
-/
theorem coconeInf_climb (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) {n : ℕ} (x : D n) :
    ∀ {m : ℕ} (h : n ≤ m), f m (embLE D P h x) = f n x := by
  intro m h
  induction m, h using Nat.le_induction with
  | base => rw [embLE_self]
  | succ k hk ih => rw [embLE_succ D P hk (Nat.le_succ_of_le hk), ← hf k, ih]

/-- Descending then applying `f` only decreases: `f_m(j_m…j_{n-1} x) ⊑ fₙ(x)`.
@isnad1 id=le.2h7v.s8.2361beb398d7 from=translated src=- shape=07937b08 vocab=c611776e
-/
theorem coconeInf_descend (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) {m : ℕ} :
    ∀ {n : ℕ} (h : m ≤ n) (x : D n), f m (projLE D P h x) ≤ f n x := by
  intro n h
  induction n, h using Nat.le_induction with
  | base => intro x; exact le_of_eq (congrArg (f m) (projLE_self D P (le_refl m) x))
  | succ k hk ih =>
      intro x
      rw [projLE_succ D P hk (Nat.le_succ_of_le hk)]
      calc f m (projLE D P hk ((P k).retr x)) ≤ f k ((P k).retr x) := ih ((P k).retr x)
        _ = f (k + 1) ((P k).incl ((P k).retr x)) := hf k _
        _ ≤ f (k + 1) x := (f (k + 1)).monotone ((P k).incl_retr_le x)

/-- **Scott 1972, Corollary 4.3 (factorization).** `fₙ = f∞ ∘ i_{n∞}`.
@isnad1 id=eq.1h6v.s8.2028347c5e4b from=translated src=- shape=39fca9a8 vocab=6fa92a79
-/
theorem coconeInf_comp_embInf (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) (n : ℕ) (x : D n) :
    coconeInf D P f (embInf D P n x) = f n x := by
  apply le_antisymm
  · change (⨆ m, f m ((embInf D P n x).1 m)) ≤ f n x
    refine iSup_le fun m => ?_
    change f m (iComp D P n x m) ≤ f n x
    by_cases h : n ≤ m
    · rw [iComp_of_le D P h]; exact le_of_eq (coconeInf_climb D P f hf x h)
    · rw [iComp_of_ge D P h]; exact coconeInf_descend D P f hf (le_of_lt (not_le.mp h)) x
  · refine le_trans (le_of_eq ?_) (le_iSup (fun m => f m ((embInf D P n x).1 m)) n)
    rw [show (embInf D P n x).1 n = x from iComp_self D P n x]

/-- `f∞` is Scott-continuous: `f∞(⊔S) = ⊔ f∞(S)` for directed `S` (each `fₙ` is
continuous and a
double `⨆` over `ℕ × S` commutes).
@isnad1 id=preserve.0h4v.s6.cd9103cacdb4 from=translated src=- shape=78f778c7 vocab=4013bf34
-/
theorem coconeInf_preservesDirectedSup (f : ∀ n, ScottMap (D n) D') :
    PreservesDirectedSup (coconeInf D P f) := by
  intro S hS hSdir
  have hev : ∀ n, DirectedOn (· ≤ ·) ((fun s : InverseLimit D P => s.1 n) '' S) := by
    intro n
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨c.1 n, ⟨c, hc, rfl⟩, hac n, hbc n⟩
  have key : ∀ n, f n ((sSup S).1 n) = sSup ((fun s : InverseLimit D P => f n (s.1 n)) '' S) := by
    intro n
    have h1 : (sSup S).1 n = sSup ((fun s : InverseLimit D P => s.1 n) '' S) :=
      eval_preservesDirectedSup D P n hS hSdir
    rw [h1, (f n).preservesDirectedSup_coe _ (hS.image _) (hev n), Set.image_image]
  change (⨆ n, f n ((sSup S).1 n)) = sSup (coconeInf D P f '' S)
  simp_rw [key, sSup_image', coconeInf_apply]
  rw [iSup_comm]

/-- **Scott 1972, Corollary 4.3.** Within complete lattices, `D_∞` is also the
*direct* limit of
the `Dₙ` along the embeddings `iₙ`: for every compatible cocone `fₙ : Dₙ → D'`
(continuous, with
`fₙ = f_{n+1} ∘ iₙ`) there is a **unique** continuous `f∞ : D_∞ → D'` with `fₙ =
f∞ ∘ i_{n∞}`,
namely `f∞(x) = ⨆ₙ fₙ(xₙ)`.
@isnad1 id=existsun.1h4v.s9.e2c9bdb37761 from=translated src=- shape=f46e816d vocab=8e0973cf
-/
theorem corollary_4_3 (f : ∀ n, ScottMap (D n) D')
    (hf : ∀ n x, f n x = f (n + 1) ((P n).incl x)) :
    ∃! g : ScottMap (InverseLimit D P) D', ∀ n x, f n x = g (embInf D P n x) := by
  refine ⟨⟨coconeInf D P f,
    continuous_of_preservesDirectedSup (coconeInf_preservesDirectedSup D P f)⟩, ?_, ?_⟩
  · exact fun n x => (coconeInf_comp_embInf D P f hf n x).symm
  · intro g hg
    ext x
    -- `g x = f∞ x`, since `x = ⨆ₙ i_{n∞}(xₙ)` and `g` is continuous on this
    -- directed family
    calc g x = g (⨆ n, embInf D P n (x.1 n)) := by rw [← inverseLimit_eq_iSup D P x]
      _ = g (sSup (Set.range fun n => embInf D P n (x.1 n))) := by rw [sSup_range]
      _ = sSup (g '' Set.range fun n => embInf D P n (x.1 n)) :=
          g.preservesDirectedSup_coe _ (Set.range_nonempty _) (embInf_family_directed D P x)
      _ = ⨆ n, g (embInf D P n (x.1 n)) := by rw [← Set.range_comp, sSup_range]; rfl
      _ = ⨆ n, f n (x.1 n) := by simp_rw [← hg]

end InverseLimit

end Domain.ContinuousLattice
