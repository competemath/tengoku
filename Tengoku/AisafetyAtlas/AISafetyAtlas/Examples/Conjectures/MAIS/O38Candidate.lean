module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Analysis.MaximalMinor
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Analysis.NullImage
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Conjectures.MAIS.O38
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Conjectures.MAIS.O38

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# MAIS-O38: the submitted candidate, proved

`AISafetyAtlas.Conjectures.MAIS.o38PolynomialSampleCandidate` transcribes the
theorem submitted as MAIS issue #30 by `26david26`, and
`o38PolynomialSampleCandidate_holds` **proves it**. The theorem
`maisO38_polynomialSamplesSuffice_holds` then resolves MAIS-O38 at every
`2 ≤ m`, `1 ≤ k < m`, while retaining print's growth hypotheses.

**The mathematics is not the atlas's.** The construction and the argument are the
issue's: `N = m³ + 2m` codes — `m` blocks of `L = m² + 1` codes carried on the
**cyclic windows** `Sₜ = {t, …, t+k-1}` of `[m]`, plus the `m` standard basis
vectors as anchors. The issue stated that it had been produced and checked
entirely by AI systems with no human verification; what this module adds is that
verification, and it found no gap.

## The route

| the note's step | here |
|---|---|
| Lemma 7, the window combinatorics | `cyclicWindow_injective`, `card_windows_containing`, `card_windows_containing_pair` |
| Lemma 6, the dimension count | `exists_subset_windowSpan_le_of_not_badBlock`, `volume_badBlock_eq_zero`, `forcing_of_windowSpan_le` |
| Lemma 8, fixing the codes first | `ae_ae_not_badBlock` |
| Theorem 3, Steps 1/3/4 | `col_mem_span_of_anchors`, `colDegree_eq`, `exists_perm_smul_col`, packaged as `uniquelyCoded_of_forcing` |

Lemma 7 is where `k < m` is spent, and it is false at `k = m` — the note's own
control, and the same boundary the atlas records at
`not_uniquelyCoded_of_full_sparsity_spark`.

Four facts Mathlib does not carry were written for this and are domain-neutral:
`AISafetyAtlas.Analysis.ae_eval_ne_zero_fintype`,
`AISafetyAtlas.Analysis.exists_det_ne_zero_of_linearIndependent`,
`AISafetyAtlas.Analysis.volume_setOf_exists_forall_dotProduct_eq_zero` — which
replaces the semialgebraic dimension count the note phrases the argument in,
since Mathlib has no semialgebraic sets — and
`AISafetyAtlas.Analysis.measurableSet_exists_of_isClosed`, which is what makes
Lemma 8's Tonelli step legitimate without the universal measurability of analytic
sets.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open Finset

/-! ## Cyclic windows -/

/-- The cyclic window of length `k` starting at `t`: print's `Sₜ`, read through
the characterisation `p ∈ Sₜ ↔ (p - t) < k` in `Fin m`, which is the form every
proof below uses.-/
@[expose] public def cyclicWindow {m : ℕ} [NeZero m] (k : ℕ) (t : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun p => ((p - t : Fin m) : ℕ) < k

@[simp]
public theorem mem_cyclicWindow {m : ℕ} [NeZero m] {k : ℕ} {t p : Fin m} :
    p ∈ cyclicWindow k t ↔ ((p - t : Fin m) : ℕ) < k := by
  simp [cyclicWindow]

/-- The `k` residues below `k` are `k` of them, once `k ≤ m`.-/
private theorem card_filter_val_lt (m k : ℕ) [NeZero m] (hk : k ≤ m) :
    (Finset.univ.filter fun s : Fin m => (s : ℕ) < k).card = k := by
  classical
  rw [show (Finset.univ.filter fun s : Fin m => (s : ℕ) < k)
      = (Finset.range k).attachFin (fun i hi => lt_of_lt_of_le (Finset.mem_range.1 hi) hk) by
    ext s
    simp [Finset.mem_attachFin]]
  simp

/-- **Lemma 7(b).** Every index lies in exactly `k` of the windows.

This is the equality half of the incidence count: it is what makes the classical
binomial factor disappear, since it bounds the count by `mk` from below at every
column of a rival dictionary that sits on a single atom.-/
public theorem card_windows_containing {m k : ℕ} [NeZero m] (hk : k ≤ m) (p : Fin m) :
    (Finset.univ.filter fun t : Fin m => p ∈ cyclicWindow k t).card = k := by
  classical
  have hbij : (Finset.univ.filter fun t : Fin m => p ∈ cyclicWindow k t).card
      = (Finset.univ.filter fun s : Fin m => (s : ℕ) < k).card := by
    refine Finset.card_bij' (fun t _ => p - t) (fun s _ => p - s) ?_ ?_ ?_ ?_ <;>
      intro a ha <;> simp_all
  rw [hbij, card_filter_val_lt m k hk]

/-- The predecessor of `0` in `Fin m` is `m - 1`. This is what makes `t - 1` land
*outside* a window of length `k < m`, which is the whole of Lemma 7(a).-/
private theorem val_neg_one (m : ℕ) [NeZero m] : ((-1 : Fin m) : ℕ) = m - 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne m) with ⟨n, rfl⟩
  simp [Fin.coe_neg_one]

/-- **Lemma 7(c).** Two distinct indices lie together in at most `k - 1` windows.

This is the strict half of the incidence count, and the reason a rival column
supported on two or more atoms is *cheaper* than one supported on a single atom.
The witness is print's: some window containing `p` omits `q`.-/
public theorem card_windows_containing_pair {m k : ℕ} [NeZero m] (hk1 : 1 ≤ k) (hkm : k < m)
    {p q : Fin m} (hpq : p ≠ q) :
    (Finset.univ.filter fun t : Fin m => p ∈ cyclicWindow k t ∧ q ∈ cyclicWindow k t).card < k := by
  classical
  have hd0 : ((q - p : Fin m) : ℕ) ≠ 0 := by
    simp only [ne_eq, Fin.val_eq_zero_iff, sub_eq_zero]
    exact fun hc => hpq hc.symm
  -- print's witness: some window catches `p` and misses `q`
  obtain ⟨t₀, hp₀, hq₀⟩ :
      ∃ t₀ : Fin m, p ∈ cyclicWindow k t₀ ∧ q ∉ cyclicWindow k t₀ := by
    by_cases hcase : k ≤ ((q - p : Fin m) : ℕ)
    · refine ⟨p, by simp; omega, ?_⟩
      simp only [mem_cyclicWindow, not_lt]
      exact hcase
    · rw [not_le] at hcase
      have hlt : k - ((q - p : Fin m) : ℕ) < m := by omega
      refine ⟨p - ⟨k - ((q - p : Fin m) : ℕ), hlt⟩, ?_, ?_⟩
      · simp only [mem_cyclicWindow,
          show (p - (p - ⟨k - ((q - p : Fin m) : ℕ), hlt⟩) : Fin m)
            = ⟨k - ((q - p : Fin m) : ℕ), hlt⟩ from by abel]
        show k - ((q - p : Fin m) : ℕ) < k
        omega
      · simp only [mem_cyclicWindow, not_lt,
          show (q - (p - ⟨k - ((q - p : Fin m) : ℕ), hlt⟩) : Fin m)
            = (q - p) + ⟨k - ((q - p : Fin m) : ℕ), hlt⟩ from by abel]
        rw [Fin.val_add]
        show k ≤ (((q - p : Fin m) : ℕ) + (k - ((q - p : Fin m) : ℕ))) % m
        rw [show ((q - p : Fin m) : ℕ) + (k - ((q - p : Fin m) : ℕ)) = k by omega,
          Nat.mod_eq_of_lt hkm]
  have hsub : (Finset.univ.filter
        fun t : Fin m => p ∈ cyclicWindow k t ∧ q ∈ cyclicWindow k t)
      ⊆ Finset.univ.filter fun t : Fin m => p ∈ cyclicWindow k t := by
    intro t ht
    simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.1⟩
  have hne : (Finset.univ.filter
        fun t : Fin m => p ∈ cyclicWindow k t ∧ q ∈ cyclicWindow k t)
      ≠ Finset.univ.filter fun t : Fin m => p ∈ cyclicWindow k t := by
    intro heq
    have h0 : t₀ ∈ Finset.univ.filter fun t : Fin m => p ∈ cyclicWindow k t :=
      Finset.mem_filter.2 ⟨Finset.mem_univ t₀, hp₀⟩
    rw [← heq] at h0
    exact hq₀ (Finset.mem_filter.1 h0).2.2
  exact lt_of_lt_of_le (Finset.card_lt_card (lt_of_le_of_ne hsub hne))
    (le_of_eq (card_windows_containing hkm.le p))

/-! ## Sparse vectors are determined by their image

The note's *"one consequence used repeatedly"* of the spark condition, and the
only property of `A` that Steps 3 and 4 of its Theorem 3 use besides the window
construction. The atlas already carries the special case `m ≤ 2k`
(`SparkCondition.mulVec_injective`); this is the version that bites at every `m`,
because the two vectors are separately `k`-sparse rather than unconstrained. -/

/-- `A *ᵥ v` as a combination of the columns `A` actually uses.-/
private theorem mulVec_eq_sum_of_support {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (v : Fin m → ℝ) (S : Finset (Fin m)) (hv : ∀ j, j ∉ S → v j = 0) :
    A.mulVec v = ∑ j ∈ S, v j • A.col j := by
  rw [Matrix.mulVec_eq_sum,
    ← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by simp [hv j hj])]
  simp [Matrix.col]

/-! ## Column spans and their coefficient vectors -/

/-! ## Window subspaces -/

open AISafetyAtlas.Conjectures.MAIS in
/-- Print's **window subspace** `Uₜ`: the span of the atoms indexed by the cyclic
window at `t`.-/
@[expose] public def windowSpan {n m : ℕ} [NeZero m] (k : ℕ) (A : Matrix (Fin n) (Fin m) ℝ)
    (t : Fin m) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (Set.range fun j : (cyclicWindow k t) => A.col (j : Fin m))

/-! ## The incidence count

Print's Step 3. Each nonzero rival column that meets a window subspace has a
*degree*: the number of windows containing it. Lemma 7(b) caps that degree at
`k`, with equality only when the column sits on a single atom, and Lemma 7(c) is
what makes a column spread over two or more atoms strictly cheaper. Since the
forcing lemma supplies `k` incidences per window, the total is `mk` from below
and `mk` from above, so every column is on a single atom. -/

/-- Membership in a window subspace is not decidable, so the incidence count runs
on `Set.ncard`; these bridge the two Lemma 7 bounds across.-/
private theorem ncard_setOf_eq_card_filter {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] : {a | P a}.ncard = (Finset.univ.filter P).card := by
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext a
  simp

private theorem ncard_windows_containing {m k : ℕ} [NeZero m] (hk : k ≤ m) (p : Fin m) :
    {t : Fin m | p ∈ cyclicWindow k t}.ncard = k := by
  classical
  rw [ncard_setOf_eq_card_filter]
  exact card_windows_containing hk p

private theorem ncard_windows_containing_pair {m k : ℕ} [NeZero m] (hk1 : 1 ≤ k) (hkm : k < m)
    {p q : Fin m} (hpq : p ≠ q) :
    {t : Fin m | p ∈ cyclicWindow k t ∧ q ∈ cyclicWindow k t}.ncard < k := by
  classical
  rw [ncard_setOf_eq_card_filter]
  exact card_windows_containing_pair hk1 hkm hpq

open AISafetyAtlas.Conjectures.MAIS in
/-- The number of window subspaces containing the `j`-th rival column.-/
@[expose] public noncomputable def colDegree {n m : ℕ} [NeZero m] (k : ℕ)
    (A B : Matrix (Fin n) (Fin m) ℝ) (j : Fin m) : ℕ :=
  {t : Fin m | B.col j ≠ 0 ∧ B.col j ∈ windowSpan k A t}.ncard

/-! ## Step 4: the permutation and the rescaling -/

open AISafetyAtlas.Conjectures.MAIS in
/-- **What the forcing lemma delivers**, and all of it that Steps 3 and 4 use: at
every window, `k` linearly independent rival columns lying in that window's
subspace. Isolating it this way is deliberate — everything below is independent
of *how* the forcing lemma is proved.-/
@[expose] public def ForcingData {n m : ℕ} [NeZero m] (k : ℕ)
    (A B : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  ∀ t : Fin m, ∃ T : Finset (Fin m), T.card = k ∧
    (∀ j ∈ T, B.col j ∈ windowSpan k A t) ∧ LinearIndependent ℝ fun j : T => B.col j

open AISafetyAtlas.Conjectures.MAIS in
/-- A one-index coefficient vector realises a rescaled atom.-/
private theorem mulVec_single {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (p : Fin m) (c : ℝ) :
    A.mulVec (fun q => if q = p then c else 0) = c • A.col p := by
  rw [mulVec_eq_sum_of_support A _ ({p} : Finset (Fin m)) (by
    intro q hq; simp only [Finset.mem_singleton] at hq; simp [hq])]
  simp

/-! ## From the column identity to print's conclusion -/

private theorem permMatrix_mul_diagonal_apply {m : ℕ} (σ : Equiv.Perm (Fin m)) (d : Fin m → ℝ)
    (a b : Fin m) : (σ.permMatrix ℝ * Matrix.diagonal d) a b = if σ a = b then d b else 0 := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Finset.sum_ite_eq']

private theorem mul_permMatrix_diagonal_apply {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (σ : Equiv.Perm (Fin m)) (d : Fin m → ℝ) (i : Fin n) (b : Fin m) :
    (A * σ.permMatrix ℝ * Matrix.diagonal d) i b = A i (σ.symm b) * d b := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [permMatrix_mul_diagonal_apply, ← Equiv.eq_symm_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

open AISafetyAtlas.Conjectures.MAIS in
/-- A permuted rescaling preserves `k`-sparsity: this is what lets the final step
compare `x i` with `P D *ᵥ x' i` under the spark condition.-/
private theorem isKSparse_permScale {k m : ℕ} (π : Equiv.Perm (Fin m)) (μ : Fin m → ℝ)
    {v : Fin m → ℝ} (hv : IsKSparse k v) :
    IsKSparse k (fun a => μ (π.symm a) * v (π.symm a)) := by
  classical
  have hsub : Function.support (fun a => μ (π.symm a) * v (π.symm a))
      ⊆ (fun a => π a) '' Function.support v := by
    intro a ha
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at ha
    exact ⟨π.symm a, by simpa using ha.2, by simp⟩
  calc (Function.support (fun a => μ (π.symm a) * v (π.symm a))).ncard
      ≤ ((fun a => π a) '' Function.support v).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (Function.support v).ncard := Set.ncard_image_of_injective _ π.injective
    _ ≤ k := hv

/-! ## The design

Print's construction: `m` blocks of `L = m² + 1` codes carried on the cyclic
windows, together with the `m` standard basis vectors as anchors. The count is
`m·(m² + 1) + m = m³ + 2m`, which is the candidate's `N`. -/

/-- Place a coefficient vector on the window at `t`, and zero elsewhere: print's
`ιₜ`. Supported on `cyclicWindow k t` by construction.-/
@[expose] public def windowPlace {m : ℕ} [NeZero m] {k : ℕ} (t : Fin m) (c : Fin k → ℝ) :
    Fin m → ℝ :=
  fun p => if h : ((p - t : Fin m) : ℕ) < k then c ⟨_, h⟩ else 0

/-- The design's index set: `m × L` window codes and `m` anchors.-/
public noncomputable def designEquiv (m : ℕ) :
    ((Fin m × Fin (m ^ 2 + 1)) ⊕ Fin m) ≃ Fin (m ^ 3 + 2 * m) :=
  Fintype.equivFinOfCardEq (by simp [Fintype.card_sum, Fintype.card_prod]; ring)

open AISafetyAtlas.Conjectures.MAIS in
/-- **Print's design**, at a given coefficient array.-/
@[expose] public noncomputable def o38Design {m : ℕ} [NeZero m] (k : ℕ)
    (c : Fin m → Fin (m ^ 2 + 1) → (Fin k → ℝ)) : Fin (m ^ 3 + 2 * m) → (Fin m → ℝ) :=
  fun i =>
    match (designEquiv m).symm i with
    | .inl tl => windowPlace tl.1 (c tl.1 tl.2)
    | .inr j => Pi.single j (1 : ℝ)

/-! ## The window in coordinates

The forcing lemma runs in the `k` coordinates of a window subspace, so the datum
a block of codes produces has to be written as an explicit combination of the `k`
atoms the window names. -/

/-- The `j`-th atom of the window at `t`.-/
@[expose] public def windowAtom {m k : ℕ} [NeZero m] (hkm : k ≤ m) (t : Fin m) (j : Fin k) :
    Fin m :=
  t + ⟨(j : ℕ), lt_of_lt_of_le j.isLt hkm⟩

/-! ## Step 1: the anchors put the rival inside `im A`

Print's Step 1, and the only role the `m` anchors play. It is what makes the
forcing lemma applicable at all, because the dimension count there is against
`im A` — of dimension at most `m`, however large `n` is — and not against `ℝⁿ`. -/

/-- Any image of `A` lies in the span of its columns.-/
private theorem mulVec_mem_span_col {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (v : Fin m → ℝ) :
    A.mulVec v ∈ Submodule.span ℝ (Set.range A.col) := by
  rw [← Matrix.range_mulVecLin]
  exact ⟨v, rfl⟩

/-! ## Lemma 6: the parameters of a rival, and the minors that cut it down

A rival whose columns lie in `im A` is `A · C`, so the rivals form an
`m²`-parameter family — and `L = m² + 1` clears that by exactly one. That is the
whole reason the count works, and it is why no basis of `im A` is ever needed. -/

/-- The discrete data one minor witness needs: how many rival columns to use,
which ones, and which rows to read. Finitely many, so a union over them is a
finite union.-/
@[expose] public def MinorChoice (k m n : ℕ) : Type :=
  Σ r : Fin (k + 1), (Fin (r : ℕ) → Fin m) × (Option (Fin (r : ℕ)) → Fin n)

public instance instFintypeMinorChoice (k m n : ℕ) : Fintype (MinorChoice k m n) := by
  unfold MinorChoice
  infer_instance

open AISafetyAtlas.Analysis in
/-- The normal vector a single choice contributes: the minor of the chosen rival
columns bordered by the window's `j`-th atom. Polynomial in `C`.-/
@[expose] public noncomputable def choiceNormal {n m k : ℕ} [NeZero m] (hkm : k ≤ m)
    (A : Matrix (Fin n) (Fin m) ℝ) (t : Fin m) (d : MinorChoice k m n)
    (C : Matrix (Fin m) (Fin m) ℝ) (j : Fin k) : ℝ :=
  borderedMinor (fun i : Fin (d.1 : ℕ) => ((A * C).col (d.2.1 i))) d.2.2
    (A.col (windowAtom hkm t j))

/-- **The coefficient blocks the forcing lemma has to exclude.** A block is bad
when some rival, with some choice of witnessing minors, makes every one of the
`L` linear conditions vanish while all the minors are alive.-/
@[expose] public noncomputable def BadBlock {n m k : ℕ} [NeZero m] (hkm : k ≤ m)
    (A : Matrix (Fin n) (Fin m) ℝ) (t : Fin m) (c : Fin (m ^ 2 + 1) → Fin k → ℝ) : Prop :=
  ∃ (D : Fin (m ^ 2 + 1) → MinorChoice k m n) (C : Matrix (Fin m) (Fin m) ℝ),
    (∀ ℓ, ∃ j, choiceNormal hkm A t (D ℓ) C j ≠ 0) ∧
      ∀ ℓ, ∑ j, c ℓ j * choiceNormal hkm A t (D ℓ) C j = 0

/-! ## Lemma 8: fixing the codes before the dictionary

Print's Lemma 8. For each dictionary the bad blocks are null; Tonelli turns that
into *for almost every array of blocks, the bad dictionaries are null*, which is
the quantifier order the printed question demands. The step that needs care is
measurability of the bad set in the product, since it is stated with an
existential over rivals; `AISafetyAtlas.Analysis.measurableSet_exists_of_isClosed`
is what discharges it. -/

/-! ## What is left

Everything above is Steps 1, 3 and 4 of the note's Theorem 3, and none of it
depends on how the forcing lemma is proved. The reduction below makes the
remaining gap a single statement: a design of `m³ + 2m` `k`-sparse codes for
which, at every `n ≥ 2k` and almost every spark-condition dictionary, every rival
admitting the data satisfies `ForcingData`. That is exactly the note's Lemma 6
(the dimension count) together with its Lemma 8 (the Tonelli argument fixing the
codes before the dictionary), and nothing else. -/

/-! ## Theorem 3 -/

end AISafetyAtlas.Examples.Conjectures.MAIS
