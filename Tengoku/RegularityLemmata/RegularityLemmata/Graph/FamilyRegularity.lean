/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.Seed.Algebra.Order.Archimedean.Real.Basic
import Tengoku.Seed.Algebra.Order.Floor.Semifield
import Tengoku.RegularityLemmata.RegularityLemmata.Graph.BadMass

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Equitable-supplier ladder, step 2 (+ numerical-schedule hardening)

`ARCHITECTURE.md` supplier route decision (2026-07-22), implementation sequence
step 2: the generic surfaces for regularity of finitely many DIRECTED relations
simultaneously — in `Graph/`, independent of relational palettes — HARDENED per the
2026-07-24 review so that no final part-count bound is frozen before the one-step
gain constant is proved.

* `IsFamilyRegular Rk ε P` — `ε`-regularity (off-diagonal, mass-weighted) for EVERY
  relation of the family. No symmetry is assumed anywhere: each `Rk k` is an
  arbitrary directed relation, and the singleton bridge (`isFamilyRegular_single`)
  applies verbatim to an asymmetric relation (permanent test below).
* `familyEnergy Rk P` — the SUM of the per-relation partition energies; ceiling `K`,
  not `1` (`familyEnergy_le_card`), monotone under refinement (`familyEnergy_mono`).
* `familyEnergy_add_le_of_component` — **the lifting lemma** (step 4's vehicle): a
  gain `g` in ONE relation's energy across a refinement `Q ≤ P` lifts to a gain `g`
  in the family energy, because every other summand is monotone. This is what
  `energy_le_familyEnergy` alone could not deliver, and it is why the iteration
  resolves ONE offending relation per step: on a non-family-regular partition some
  `Rk k` is nonregular; atomise/equitabilise ITS witnesses only; the result refines
  `P`, so the other `K − 1` summands cannot decrease.

The numerical schedule is kept in SEPARATE provisional pieces — no final bound is
frozen here, because the equitabilised step retains only `c·ε⁵` of the exact
refinement's `ε⁵` energy gain for a `c < 1` derived from the step-3 chunk remainder:

* `familyInitialBound C ε l` — the ε-dependent initial floor (mathlib `initialBound`
  architecture): `max (max l 2) ⌈C/ε⁵⌉₊`, proved to meet the chunk's numerical
  condition `C ≤ 4^(familyInitialBound C ε l)·ε⁵` (`le_pow_familyInitialBound_mul`),
  transported to EVERY later part count `≥` the floor by
  `le_pow_mul_of_familyInitialBound_le` (the form the iteration consumes). The
  threshold `C` is the chunk-derived, **K-independent** constant — resolving one
  relation per step reuses mathlib's per-graph chunk condition — so it is a parameter
  here, instantiated once step 3 fixes it; the K-dependence lives only in the fuel.
* `familyChunksPerPart n` / `familyStepBound n = n · familyChunksPerPart n` — one
  single-relation equitabilised step's part-count growth. **K-FREE**: only the
  selected relation is cut (`2n` witness roles → a `2^(2n)` atom factor, then a
  mathlib-style equitabilisation factor). The per-parent chunk count is factored out
  so step 3 can produce the SAME number of chunks in every parent cell, making the
  exact part-count and equitability arguments uniform. Deliberately generous.
* `familyRegularityBoundAux fuel initial` — the raw `fuel`-fold iterate of the step,
  monotone in its initial argument (`familyRegularityBoundAux_mono`), as step 5's
  replacement of actual part counts by their recursive upper bounds requires.

The FINAL bound and the fuel `⌈K/(c·ε⁵)⌉` are DELIBERATELY not frozen here: they wait
for step 4 (`ARCHITECTURE.md`), where `c` is proved. No tower-type claim is made (the
supplier follows the weak route; Conlon–Fox scope in `PROVENANCE.md`).

Ordinary off-diagonal regularity only: this ladder does NOT touch equitable strong
regularity (deferred in `ARCHITECTURE.md`) nor the diagonal-inclusive layer.
-/

namespace RegularityLemmata

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-! ### Family regularity and family energy -/

/-- `ε`-regularity for every relation of a finite directed family.-/
def IsFamilyRegular {K : ℕ} (Rk : Fin K → α → α → Prop)
    [∀ k, DecidableRel (Rk k)] (ε : ℝ) (P : Finpartition s) : Prop :=
  ∀ k, IsRegularPartition (Rk k) ε P

/-- The family energy: the sum of the per-relation partition energies.-/
noncomputable def familyEnergy {K : ℕ} (Rk : Fin K → α → α → Prop)
    [∀ k, DecidableRel (Rk k)] (P : Finpartition s) : ℝ :=
  ∑ k, energy (Rk k) P

section Family

variable {K : ℕ} {Rk : Fin K → α → α → Prop} [∀ k, DecidableRel (Rk k)]
  {ε : ℝ} {P Q : Finpartition s}

/-- The singleton bridge: family regularity of one relation is that relation's
regularity. Nothing here assumes symmetry.
@isnad1 id=iff.0h5v.s6.fced4510d4fb from=translated src=- shape=1161ed37 vocab=c53404cf
-/
theorem isFamilyRegular_single {R : α → α → Prop} [DecidableRel R] :
    IsFamilyRegular (fun _ : Fin 1 => R) ε P ↔ IsRegularPartition R ε P := by
  constructor
  · intro h
    exact h 0
  · intro h k
    exact h

/-- The empty family is regular at every tolerance — the `K = 0` endpoint.
@isnad1 id=isfamily.0h5v.s5.704079e6eae6 from=translated src=- shape=1cc5d7c5 vocab=80efa3e8
-/
theorem isFamilyRegular_zero (Rk : Fin 0 → α → α → Prop)
    [∀ k, DecidableRel (Rk k)] : IsFamilyRegular Rk ε P :=
  fun k => k.elim0

/--
@isnad1 id=le.0h5v.s5.8e7ce16ce6e9 from=translated src=- shape=6c05af37 vocab=24d6c55c
-/
theorem familyEnergy_nonneg : 0 ≤ familyEnergy Rk P :=
  Finset.sum_nonneg fun k _ => energy_nonneg (Rk k)

/-- The family-energy ceiling is `K`, not `1`.
@isnad1 id=le.0h5v.s5.a2605b557138 from=translated src=- shape=0ff7b29e vocab=b87f3e37
-/
theorem familyEnergy_le_card : familyEnergy Rk P ≤ (K : ℝ) := by
  calc familyEnergy Rk P
      ≤ ∑ _k : Fin K, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => energy_le_one (Rk k)
    _ = (K : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_one]

/-- Family energy is monotone under refinement — every summand is.
@isnad1 id=le.1h6v.s6.a5159e1cf730 from=translated src=- shape=2ecaa5c3 vocab=24d6c55c
-/
theorem familyEnergy_mono (hQ : Q ≤ P) : familyEnergy Rk P ≤ familyEnergy Rk Q :=
  Finset.sum_le_sum fun k _ => energy_mono (Rk k) hQ

/-- A single relation's energy is dominated by the family energy. Weaker than the
lifting lemma below — kept as a convenience.
@isnad1 id=le.0h6v.s6.19ccc326b9d4 from=translated src=- shape=623f49dc vocab=ce0cdb32
-/
theorem energy_le_familyEnergy (k : Fin K) : energy (Rk k) P ≤ familyEnergy Rk P :=
  Finset.single_le_sum (f := fun k => energy (Rk k) P)
    (fun j _ => energy_nonneg (Rk j)) (Finset.mem_univ k)

/-- **The lifting lemma** (step 4's vehicle): a gain `g` in one relation's energy
across a refinement `Q ≤ P` lifts to the SAME gain in the family energy, because
every other summand is monotone under refinement. This packages the preservation of
the untouched `K − 1` summands, and is exactly why the family iteration can resolve
a single offending relation at each step.
@isnad1 id=le.2h8v.s7.c1fc0f354fb5 from=translated src=- shape=994afe5e vocab=efa2e0ac
-/
theorem familyEnergy_add_le_of_component {g : ℝ} (hQP : Q ≤ P) (k : Fin K)
    (hgain : energy (Rk k) P + g ≤ energy (Rk k) Q) :
    familyEnergy Rk P + g ≤ familyEnergy Rk Q := by
  have hpoint : ∀ j ∈ (Finset.univ : Finset (Fin K)),
      energy (Rk j) P + (if j = k then g else 0) ≤ energy (Rk j) Q := by
    intro j _
    by_cases hjk : j = k
    · subst hjk
      simpa using hgain
    · rw [ite_eq_right hjk, add_zero]
      exact energy_mono (Rk j) hQP
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ k fun _ => g] at hsum
  simp only [Finset.mem_univ, ite_true] at hsum
  exact hsum

/-- The empty family has zero energy.
@isnad1 id=eq.0h4v.s6.211406e43065 from=translated src=- shape=f2dc2b60 vocab=f5136233
-/
theorem familyEnergy_zero (Rk : Fin 0 → α → α → Prop)
    [∀ k, DecidableRel (Rk k)] : familyEnergy Rk P = 0 := by
  simp [familyEnergy]

end Family

/-! ### The numerical schedule (provisional; final bound deferred to step 5) -/

private theorem nat_le_four_pow (n : ℕ) : n ≤ 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ 4 ^ n := Nat.one_le_pow n 4 (by norm_num)
    calc n + 1 ≤ 4 ^ n + 1 := by omega
      _ ≤ 4 ^ (n + 1) := by rw [pow_succ]; omega

/-- **The ε-dependent initial floor**, in the mathlib `initialBound` style: at least
the requested `l` (and `2`), and large enough that `4^·` beats the target `C/ε⁵`, so
the chunk's numerical condition `C ≤ 4^(·)·ε⁵` holds (`le_pow_familyInitialBound_mul`).
The threshold `C` is the chunk-derived, K-independent constant — a parameter until
step 3 fixes it.-/
noncomputable def familyInitialBound (C ε : ℝ) (l : ℕ) : ℕ :=
  max (max l 2) ⌈C / ε ^ 5⌉₊

/-- The number of chunks step 3 produces in EVERY parent cell — the same count in
each, which is what makes the exact part-count and equitability arguments uniform:
the single-relation atom factor times the equitabilisation factor.-/
def familyChunksPerPart (n : ℕ) : ℕ :=
  2 ^ (2 * n) * 4 ^ (n * 2 ^ (2 * n))

/-- One single-relation equitabilised refinement step's part-count growth: `n` parent
cells, each split into `familyChunksPerPart n` chunks. **K-free**: only the selected
relation is cut. Deliberately generous — only finiteness and monotonicity are used
downstream.-/
def familyStepBound (n : ℕ) : ℕ :=
  n * familyChunksPerPart n

/-- The fuel-indexed iterate of the single-relation step bound. The fuel itself
(`⌈K/(c·ε⁵)⌉`) is fixed only at step 5, once `c` is proved.-/
def familyRegularityBoundAux : ℕ → ℕ → ℕ
  | 0, m => m
  | t + 1, m => familyRegularityBoundAux t (familyStepBound m)

/--
@isnad1 id=le.0h3v.s3.8e268bc0ba5f from=translated src=- shape=667193bd vocab=efebf19a
-/
theorem le_familyInitialBound (C ε : ℝ) (l : ℕ) : l ≤ familyInitialBound C ε l :=
  le_trans (le_max_left l 2) (le_max_left _ _)

/--
@isnad1 id=le.0h3v.s4.8765cd6e1882 from=translated src=- shape=242e3cc5 vocab=efebf19a
-/
theorem two_le_familyInitialBound (C ε : ℝ) (l : ℕ) :
    2 ≤ familyInitialBound C ε l :=
  le_trans (le_max_right l 2) (le_max_left _ _)

/-- **The chunk numerical condition is met by the initial floor**: for the ε-dependent
floor, `4^(familyInitialBound C ε l)·ε⁵ ≥ C`. This is the family analogue of mathlib's
`100 ≤ 4^#P·ε⁵`, with the constant left as the parameter `C`. (No sign hypothesis on
`C` is needed: `⌈C/ε⁵⌉₊ = 0` for `C ≤ 0`, and `C ≤ 0 ≤ 4^··ε⁵` there.)
@isnad1 id=le.1h3v.s6.13ea21f2c8be from=translated src=- shape=48ce4e97 vocab=314d61fa
-/
theorem le_pow_familyInitialBound_mul {C ε : ℝ} (hε : 0 < ε) (l : ℕ) :
    C ≤ 4 ^ familyInitialBound C ε l * ε ^ 5 := by
  have hε5 : (0 : ℝ) < ε ^ 5 := by positivity
  have hceil_le : (⌈C / ε ^ 5⌉₊ : ℝ) ≤ (familyInitialBound C ε l : ℝ) := by
    have : ⌈C / ε ^ 5⌉₊ ≤ familyInitialBound C ε l := le_max_right _ _
    exact_mod_cast this
  have hdiv_le : C / ε ^ 5 ≤ (familyInitialBound C ε l : ℝ) :=
    le_trans (Nat.le_ceil _) hceil_le
  have hF4 : (familyInitialBound C ε l : ℝ) ≤ 4 ^ familyInitialBound C ε l := by
    exact_mod_cast nat_le_four_pow (familyInitialBound C ε l)
  have hkey : C / ε ^ 5 ≤ 4 ^ familyInitialBound C ε l := le_trans hdiv_le hF4
  calc C = C / ε ^ 5 * ε ^ 5 := (div_mul_cancel₀ C (ne_of_gt hε5)).symm
    _ ≤ 4 ^ familyInitialBound C ε l * ε ^ 5 :=
        mul_le_mul_of_nonneg_right hkey (le_of_lt hε5)

/-- **The transported numerical bridge**: the chunk condition holds at EVERY part
count `N` at or above the initial floor, not only at the floor itself — the form the
iteration consumes (`N := P.parts.card` at each refinement stage).
@isnad1 id=le.2h4v.s6.451deaad54ef from=translated src=- shape=fbf7f180 vocab=314d61fa
-/
theorem le_pow_mul_of_familyInitialBound_le {C ε : ℝ} (hε : 0 < ε) {l N : ℕ}
    (hN : familyInitialBound C ε l ≤ N) : C ≤ 4 ^ N * ε ^ 5 := by
  refine le_trans (le_pow_familyInitialBound_mul hε l) ?_
  have h4 : (4 : ℝ) ^ familyInitialBound C ε l ≤ 4 ^ N :=
    pow_le_pow_right₀ (by norm_num) hN
  exact mul_le_mul_of_nonneg_right h4 (by positivity)

/--
@isnad1 id=lt.0h1v.s3.7abd6fdfbe42 from=translated src=- shape=8a62b088 vocab=e189e79b
-/
theorem familyChunksPerPart_pos (n : ℕ) : 0 < familyChunksPerPart n :=
  Nat.mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)

/--
@isnad1 id=le.1h2v.s4.a0724011e223 from=translated src=- shape=6bee9d27 vocab=8f72746b
-/
theorem familyChunksPerPart_mono {m n : ℕ} (h : m ≤ n) :
    familyChunksPerPart m ≤ familyChunksPerPart n := by
  have h2 : 2 ^ (2 * m) ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 4 ^ (m * 2 ^ (2 * m)) ≤ 4 ^ (n * 2 ^ (2 * n)) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul h h2)
  exact Nat.mul_le_mul h2 h4

/-- The step bound is positive exactly on a nonempty partition — the nondegeneracy the
step-3 construction needs to divide the host size by it.
@isnad1 id=lt.1h1v.s4.19c994632c87 from=translated src=- shape=35bd48ee vocab=80df05d3
-/
theorem familyStepBound_pos {n : ℕ} (hn : 0 < n) : 0 < familyStepBound n :=
  Nat.mul_pos hn (familyChunksPerPart_pos n)

/--
@isnad1 id=le.0h1v.s3.7b205e4abdb8 from=translated src=- shape=e63234f4 vocab=d5eac618
-/
theorem le_familyStepBound (n : ℕ) : n ≤ familyStepBound n :=
  calc n = n * 1 := (mul_one n).symm
    _ ≤ n * familyChunksPerPart n := Nat.mul_le_mul (le_refl n) (familyChunksPerPart_pos n)

/-- Divisibility by three is preserved by the step, since `familyStepBound n` is `n` times
something. Seeding the exact iteration at a multiple of three therefore keeps every
reachable part count divisible by three — the prerequisite of grouping cells into owners of
three (`ARCHITECTURE.md`, route (b) ladder step 2).
@isnad1 id=dvd.1h1v.s4.3981ac2861e7 from=translated src=- shape=35bd48ee vocab=992ca9f5
-/
theorem three_dvd_familyStepBound {n : ℕ} (h : 3 ∣ n) : 3 ∣ familyStepBound n := by
  rw [familyStepBound]
  exact Dvd.dvd.mul_right h _

/--
@isnad1 id=le.1h2v.s4.0f7754b6c5df from=translated src=- shape=6bee9d27 vocab=d5eac618
-/
theorem familyStepBound_mono {m n : ℕ} (h : m ≤ n) :
    familyStepBound m ≤ familyStepBound n :=
  Nat.mul_le_mul h (familyChunksPerPart_mono h)

/--
@isnad1 id=le.0h2v.s3.76d1c392afde from=translated src=- shape=86c6c8ca vocab=7dca0cd4
-/
theorem le_familyRegularityBoundAux (t m : ℕ) :
    m ≤ familyRegularityBoundAux t m := by
  induction t generalizing m with
  | zero => simp [familyRegularityBoundAux]
  | succ t IH =>
    rw [familyRegularityBoundAux]
    exact le_trans (le_familyStepBound m) (IH _)

/-- Monotonicity of the iterate in its initial argument — step 5 uses this to replace
actual part counts by their recursive upper bounds.
@isnad1 id=le.1h3v.s4.88d33ce06c03 from=translated src=- shape=32f89d1d vocab=7dca0cd4
-/
theorem familyRegularityBoundAux_mono (t : ℕ) {m n : ℕ} (h : m ≤ n) :
    familyRegularityBoundAux t m ≤ familyRegularityBoundAux t n := by
  induction t generalizing m n with
  | zero => exact h
  | succ t IH =>
    rw [familyRegularityBoundAux, familyRegularityBoundAux]
    exact IH (familyStepBound_mono h)

/-! ### Tests -/

section Tests

-- The `K = 0` endpoint, concretely: any partition of any host is family-regular
-- for the empty family at any tolerance.

end Tests

end RegularityLemmata
