/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.RingTheory.PowerSeries.Evaluation
import Tengoku.Seed.RingTheory.AdicCompletion.Topology
import Tengoku.Seed.Topology.Algebra.OpenSubgroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `I`-adic evaluation of a power series

Let `A` be a commutative ring that is `I`-adically complete (`IsAdicComplete I A`; the case of a
complete DVR with maximal ideal `𝔪` is `I = 𝔪`).  Substituting an element `x ∈ I` into a power
series `f : A⟦X⟧` converges `I`-adically to a well-defined element `f(x) ∈ A`.  Mathlib already
provides the topological evaluation machinery (`PowerSeries.eval₂Hom` under a complete, separated,
linear ring topology with a topologically nilpotent point); this file *assembles the instance chain*
from `IsAdicComplete I A` and `x ∈ I`, packages the resulting substitution as a genuine ring
homomorphism `PowerSeries.adicEval`, and proves that it lands in `I` on series with vanishing
constant coefficient.

This is the reusable analytic brick behind the group `Ê(𝔪)` of a formal group over a complete
local ring (Silverman AEC IV.3, VII.2.2): the operation `x ⊕ y = F(x, y)` and the endomorphisms
`[m]` are `I`-adic substitutions of this kind, and torsion-freeness of `Ê(𝔪)` away from the
residue characteristic rests on these evaluations being well defined and staying inside `𝔪`.

## Main definitions / results

* `PowerSeries.adicEval I hx : PowerSeries A →+* A` — the `I`-adic evaluation ring homomorphism at
  `x ∈ I`, for `A` `I`-adically complete.
* `PowerSeries.adicEval_X`, `adicEval_C`, `adicEval_one` — computation on the generators.
* `PowerSeries.adicEval_mem` — `f(x) ∈ I` whenever `constantCoeff f = 0`.

## Implementation notes

The completeness / separatedness / linear-topology instances live in the `I`-adic topology, which
is *not* a global instance on `A` (it would clash with any other topology and cannot be inferred).
They are therefore introduced locally, via `letI : WithIdeal A := ⟨I⟩` together with
`IsAdic.isAdicComplete_iff`, both in the definition and in every lemma that reasons about it.

## References

Silverman, *The Arithmetic of Elliptic Curves*, IV.3, VII.2; Bourbaki, *Algebra*, IV §4.3.
-/

open scoped Topology

namespace PowerSeries

variable {A : Type*} [CommRing A] (I : Ideal A) [IsAdicComplete I A]

/-- The `I`-adic evaluation of a power series at a point `x ∈ I`, as a ring homomorphism
`PowerSeries A →+* A`, for `A` that is `I`-adically complete.

Concretely `f ↦ f(x) = ∑ₙ (coeff n f) · xⁿ`, the sum converging in the `I`-adic topology.  It is the
specialisation of `PowerSeries.eval₂Hom` to the identity coefficient map and the `I`-adic topology,
in which every element of `I` is topologically nilpotent and `A` is complete and separated. -/
noncomputable def adicEval {x : A} (hx : x ∈ I) : PowerSeries A →+* A :=
  letI : WithIdeal A := ⟨I⟩
  haveI : CompleteSpace A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).1
  haveI : T2Space A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).2
  eval₂Hom (φ := RingHom.id A) (a := x) continuous_id
    (WithIdeal.isTopologicallyNilpotent_of_mem hx)

variable {I}

/-- The underlying function of `adicEval` is `PowerSeries.eval₂` at the identity coefficient map. -/
theorem coe_adicEval {x : A} (hx : x ∈ I) :
    letI : WithIdeal A := ⟨I⟩
    ⇑(adicEval I hx) = eval₂ (RingHom.id A) x := by
  letI : WithIdeal A := ⟨I⟩
  haveI : CompleteSpace A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).1
  haveI : T2Space A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).2
  exact coe_eval₂Hom continuous_id (WithIdeal.isTopologicallyNilpotent_of_mem hx)

@[simp]
theorem adicEval_X {x : A} (hx : x ∈ I) : adicEval I hx (X : PowerSeries A) = x := by
  rw [coe_adicEval hx, eval₂_X]

@[simp]
theorem adicEval_C {x : A} (hx : x ∈ I) (a : A) : adicEval I hx (C a) = a := by
  rw [coe_adicEval hx, eval₂_C, RingHom.id_apply]

@[simp]
theorem adicEval_one {x : A} (hx : x ∈ I) : adicEval I hx (1 : PowerSeries A) = 1 :=
  map_one _

/-- Series form of the `I`-adic evaluation: `f(x) = ∑ₙ (coeff n f) · xⁿ`. -/
theorem adicEval_eq_tsum {x : A} (hx : x ∈ I) (f : PowerSeries A) :
    letI : WithIdeal A := ⟨I⟩
    adicEval I hx f = ∑' n : ℕ, coeff n f * x ^ n := by
  letI : WithIdeal A := ⟨I⟩
  haveI : CompleteSpace A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).1
  haveI : T2Space A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).2
  have := eval₂_eq_tsum (φ := RingHom.id A) (a := x) continuous_id
    (WithIdeal.isTopologicallyNilpotent_of_mem hx) f
  simpa only [coe_adicEval hx, RingHom.id_apply] using this

/-- The `I`-adic evaluation of a power series with vanishing constant coefficient lands in `I`.

This is the key statement for the formal group `Ê(𝔪)`: substituting elements of `𝔪` into the
formal group law (which has zero constant coefficient) keeps us inside `𝔪`.  The proof avoids all
topology: `constantCoeff f = 0` means `X ∣ f`, so `f = X * g` and `f(x) = x · g(x) ∈ I`. -/
theorem adicEval_mem {x : A} (hx : x ∈ I) {f : PowerSeries A}
    (hf : constantCoeff f = 0) : adicEval I hx f ∈ I := by
  obtain ⟨g, rfl⟩ := X_dvd_iff.mpr hf
  rw [map_mul, adicEval_X]
  exact Ideal.mul_mem_right _ _ hx

/-! ### Multivariate version

The multivariate `I`-adic evaluation, at a finite family `a : σ → A` of elements of `I`.  This is
the shape consumed by the formal group `Ê(𝔪)`: the operation `x ⊕ y = F(x, y)` is
`adicEvalMv I ![x, y] F` for the (two-variable, zero-constant-coefficient) formal group law `F`, and
`adicEvalMv_mem` is exactly the statement that this stays inside `𝔪`. -/

variable {σ : Type*} [Finite σ]

/-- The `I`-adic evaluation of a multivariate power series at a finite family `a : σ → A` of
elements of `I`, as a ring homomorphism `MvPowerSeries σ A →+* A`, for `A` `I`-adically complete. -/
noncomputable def adicEvalMv (I : Ideal A) [IsAdicComplete I A] {a : σ → A}
    (ha : ∀ s, a s ∈ I) : MvPowerSeries σ A →+* A :=
  letI : WithIdeal A := ⟨I⟩
  haveI : CompleteSpace A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).1
  haveI : T2Space A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).2
  MvPowerSeries.eval₂Hom (φ := RingHom.id A) (a := a) continuous_id
    ⟨fun s ↦ WithIdeal.isTopologicallyNilpotent_of_mem (ha s), by
      rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩

/-- The underlying function of `adicEvalMv` is `MvPowerSeries.eval₂` at the identity coefficient
map. -/
theorem coe_adicEvalMv (I : Ideal A) [IsAdicComplete I A] {a : σ → A} (ha : ∀ s, a s ∈ I) :
    letI : WithIdeal A := ⟨I⟩
    ⇑(adicEvalMv I ha) = MvPowerSeries.eval₂ (RingHom.id A) a := by
  letI : WithIdeal A := ⟨I⟩
  haveI : CompleteSpace A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).1
  haveI : T2Space A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).2
  exact MvPowerSeries.coe_eval₂Hom continuous_id
    ⟨fun s ↦ WithIdeal.isTopologicallyNilpotent_of_mem (ha s), by
      rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩

@[simp]
theorem adicEvalMv_X (I : Ideal A) [IsAdicComplete I A] {a : σ → A} (ha : ∀ s, a s ∈ I) (s : σ) :
    adicEvalMv I ha (MvPowerSeries.X s) = a s := by
  letI : WithIdeal A := ⟨I⟩
  rw [coe_adicEvalMv I ha, MvPowerSeries.eval₂_X]

@[simp]
theorem adicEvalMv_C (I : Ideal A) [IsAdicComplete I A] {a : σ → A} (ha : ∀ s, a s ∈ I) (r : A) :
    adicEvalMv I ha (MvPowerSeries.C r : MvPowerSeries σ A) = r := by
  letI : WithIdeal A := ⟨I⟩
  rw [coe_adicEvalMv I ha, MvPowerSeries.eval₂_C, RingHom.id_apply]

/-- The multivariate `I`-adic evaluation of a power series with vanishing constant coefficient lands
in `I`.  This is the group-law closure statement for `Ê(𝔪)`: with `a = ![x, y]` and `F` the formal
group law (which has zero constant coefficient), `F(x, y) ∈ I`. -/
theorem adicEvalMv_mem (I : Ideal A) [IsAdicComplete I A] {a : σ → A} (ha : ∀ s, a s ∈ I)
    {f : MvPowerSeries σ A} (hf : MvPowerSeries.constantCoeff f = 0) :
    adicEvalMv I ha f ∈ I := by
  letI : WithIdeal A := ⟨I⟩
  haveI : CompleteSpace A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).1
  haveI : T2Space A := ((IsAdic.isAdicComplete_iff (I := I) rfl).mp ‹_›).2
  have hev : MvPowerSeries.HasEval a :=
    ⟨fun s ↦ WithIdeal.isTopologicallyNilpotent_of_mem (ha s), by
      rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
  -- `I` is a closed additive subgroup in the `I`-adic topology.
  have hIclosed : IsClosed (I : Set A) := by
    have hopen : IsOpen (((I ^ 1).toAddSubgroup) : Set A) := (I.openAddSubgroup 1).isOpen'
    have := AddSubgroup.isClosed_of_isOpen ((I ^ 1).toAddSubgroup) hopen
    simpa [pow_one] using this
  -- Power membership: `b ∈ I`, `0 < k ⇒ b ^ k ∈ I`.
  have pow_mem : ∀ (b : A) (k : ℕ), b ∈ I → 0 < k → b ^ k ∈ I := by
    intro b k hb hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [pow_succ]
    exact I.mul_mem_left _ hb
  -- Each monomial term of the evaluation lies in `I`.
  have term_mem : ∀ d : σ →₀ ℕ,
      (RingHom.id A) (MvPowerSeries.coeff d f) * (d.prod fun s e ↦ a s ^ e) ∈ I := by
    intro d
    by_cases hd : d = 0
    · subst hd
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, map_zero, zero_mul]
      exact I.zero_mem
    · have hprod : (d.prod fun s e ↦ a s ^ e) ∈ I := by
        obtain ⟨s0, hs0⟩ := Finsupp.support_nonempty_iff.mpr hd
        rw [← Finsupp.mul_prod_erase d s0 (fun s e ↦ a s ^ e) hs0]
        exact I.mul_mem_right _
          (pow_mem (a s0) (d s0) (ha s0) (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hs0)))
      exact I.mul_mem_left _ hprod
  -- The evaluation is the (adic) limit of the partial sums of these terms, so it lands in `I`.
  have hsum := MvPowerSeries.hasSum_eval₂ (φ := RingHom.id A) (a := a) continuous_id hev f
  have key : MvPowerSeries.eval₂ (RingHom.id A) a f ∈ (I : Set A) := by
    refine hIclosed.mem_of_tendsto hsum (Filter.Eventually.of_forall fun s ↦ ?_)
    simpa only [SetLike.mem_coe] using Ideal.sum_mem I fun d _ ↦ term_mem d
  have hcoe : adicEvalMv I ha f = MvPowerSeries.eval₂ (RingHom.id A) a f :=
    congrFun (coe_adicEvalMv I ha) f
  rw [hcoe]
  exact key

end PowerSeries
