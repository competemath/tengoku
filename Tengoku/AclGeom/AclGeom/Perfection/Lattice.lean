/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Geometry.FrobeniusPowers
import Tengoku.AclGeom.AclGeom.Perfection.Subfield
import Tengoku.AclGeom.AclGeom.Geometry.Points
import Tengoku.Seed.FieldTheory.Perfect

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The perfected base and the pullback equation

Toward the perfection order isomorphism
`𝒢(K/k) ≃o 𝒢(K^perf/k^perf)` (blueprint Prop `perf-lattice`), this file
provides:

* `Perfection.basePerf`: the compatible perfected base `k^i` inside the
  perfection of `K` (blueprint eq. 20.1);
* `Perfection.perfIF`: `M^perf` as an intermediate field of the perfection
  over the perfected base, for a closed `M ∈ 𝒢(K/k)`;
* `Perfection.incl_mem_perfIF_iff`: the pullback equation (5.1) —
  intersecting `M^perf` with (the image of) `K` recovers `M`;
* `Perfection.isRAC_perfIF` / `Perfection.perfClosed`: `M^perf` is
  relatively algebraically closed in the perfection;
* `Perfection.comapClosed` and equation (5.2)
  (`perfClosed_comapClosed`): every closed subextension of the perfection
  is the perfection of its pullback;
* `Perfection.latticeIso`: the perfection order isomorphism
  `𝒢(K/k) ≃o 𝒢(K^perf/k^perf)` — checklist item P2.

The integral Frobenius action fixes every closed perfected subextension and hence every atom
(`frobZPow_mem_iff`, `frobZPow_image_closed`; P3).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** the perfection lattice isomorphism and its Frobenius invariance are proved (M2, P2–P3).
-/

namespace AclGeom

noncomputable section

namespace Perfection

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]
variable (π : Perfection K)

variable (k) in
/-- The compatible perfected base `k^i` (blueprint eq. 20.1): elements of the
perfection of `K` some `p`-power of which lies in the image of `k`.-/
def basePerf : Subfield π.carrier :=
  π.perfSubfield (algebraMap k K).fieldRange

/--
@isnad1 id=iff.0h4v.s8.310f516864d2 from=translated src=- shape=861d545b vocab=b0d223a3
-/
theorem mem_basePerf_iff {x : π.carrier} :
    x ∈ π.basePerf k ↔ ∃ n : ℕ, ∃ c : k, x ^ π.p ^ n = π.incl (algebraMap k K c) := by
  rw [basePerf, mem_perfSubfield_iff]
  constructor
  · rintro ⟨n, m, ⟨c, rfl⟩, h⟩
    exact ⟨n, c, h⟩
  · rintro ⟨n, c, h⟩
    exact ⟨n, algebraMap k K c, ⟨c, rfl⟩, h⟩

variable (k) in
/-- The perfected subfield of a closed intermediate field contains the
perfected base.
@isnad1 id=le.0h4v.s7.cdecc9b30019 from=translated src=- shape=a5c39ba4 vocab=69c90e15
-/
theorem basePerf_le_perfSubfield (M : ClosedIF k K) :
    π.basePerf k ≤ π.perfSubfield M.1.toSubfield :=
  π.perfSubfield_mono fun _ hy ↦ by
    obtain ⟨c, rfl⟩ := hy
    exact M.1.algebraMap_mem c

variable (k) in
/-- `M^perf`, as an intermediate field of the perfection over the perfected
base (blueprint §Foundation III).-/
def perfIF (M : ClosedIF k K) : IntermediateField (π.basePerf k) π.carrier :=
  (π.perfSubfield M.1.toSubfield).toIntermediateField fun x ↦
    π.basePerf_le_perfSubfield k M x.2

/--
@isnad1 id=iff.0h5v.s9.eab1f3ce9a66 from=translated src=- shape=831cbdf9 vocab=c486a626
-/
theorem mem_perfIF_iff {M : ClosedIF k K} {x : π.carrier} :
    x ∈ π.perfIF k M ↔ ∃ n : ℕ, ∃ m ∈ M, x ^ π.p ^ n = π.incl m :=
  Iff.rfl

/--
@isnad1 id=le.1h5v.s9.ce771dfd7588 from=translated src=- shape=48f0e178 vocab=f7ecc2bb
-/
theorem perfIF_mono {M N : ClosedIF k K} (h : M ≤ N) :
    π.perfIF k M ≤ π.perfIF k N := fun _ hx ↦ by
  obtain ⟨n, m, hm, hxm⟩ := hx
  exact ⟨n, m, ClosedIF.le_iff.1 h hm, hxm⟩

/-- Equation (5.1) of the blueprint: pulling `M^perf` back along the
inclusion of `K` recovers exactly `M`, for closed `M`. This is the inverse
direction of the perfection order isomorphism.
@isnad1 id=iff.0h5v.s8.2497bab60535 from=translated src=- shape=0de78415 vocab=8308eabf
-/
theorem incl_mem_perfIF_iff {M : ClosedIF k K} {x : K} :
    π.incl x ∈ π.perfIF k M ↔ x ∈ M := by
  rw [mem_perfIF_iff]
  constructor
  · rintro ⟨n, m, hm, hx⟩
    rw [← map_pow] at hx
    have hxm : x ^ π.p ^ n ∈ M.1 := by
      rw [π.incl_injective hx]
      exact hm
    exact M.2.mem_of_pow_mem (expChar_pow_pos K π.p n).ne' hxm
  · intro hx
    exact ⟨0, x, hx, by simp⟩

/-- The perfected subfield of a closed intermediate field is relatively
algebraically closed in the perfection (blueprint Prop `perf-lattice`,
first part). The proof raises an annihilating polynomial by a common
Frobenius power to land its coefficients in `ι M`, raises once more to land
the point in `ι K`, and descends the resulting polynomial identity to `K`
along the injective inclusion.
@isnad1 id=israc.0h4v.s7.e665dc9fe892 from=translated src=- shape=83c84d9b vocab=b9507283
-/
theorem isRAC_perfIF (M : ClosedIF k K) : IsRAC (π.perfIF k M) := by
  classical
  intro x hx
  -- An annihilating polynomial with coefficients in `M^perf`.
  obtain ⟨q, hq0, hqx, hqc⟩ := exists_poly_of_isAlgebraic hx
  -- Choose exponents and preimages for the coefficients, then pass to the
  -- common exponent `s`.
  choose e m hm hqm using fun n ↦ π.mem_perfIF_iff.1 (hqc n)
  set s := q.support.sup e with hs
  have key : ∀ n, ∃ c ∈ M, q.coeff n ^ π.p ^ s = π.incl c := by
    intro n
    by_cases hn : n ∈ q.support
    · refine ⟨m n ^ π.p ^ (s - e n),
        ClosedIF.mem_val.1 (pow_mem (ClosedIF.mem_val.2 (hm n)) _), ?_⟩
      have hsplit : π.p ^ s = π.p ^ e n * π.p ^ (s - e n) := by
        rw [← pow_add, Nat.add_sub_cancel' (Finset.le_sup hn)]
      rw [hsplit, pow_mul, hqm n, ← map_pow]
    · refine ⟨0, zero_mem M.1, ?_⟩
      rw [Polynomial.notMem_support_iff.1 hn, map_zero,
        zero_pow (expChar_pow_pos π.carrier π.p s).ne']
  choose c hc hcq using key
  -- A power of `x` descends to `K`.
  obtain ⟨r, y, hy⟩ := π.exists_pow_incl x
  set z : K := y ^ π.p ^ s with hz
  -- The descended annihilating polynomial over `K`.
  set Q : Polynomial K := ∑ n ∈ q.support, Polynomial.monomial n (c n ^ π.p ^ r) with hQ
  have hQcoeff : ∀ j, Q.coeff j ∈ M.1 := by
    intro j
    rw [hQ, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' q.support j fun n ↦ c n ^ π.p ^ r]
    split_ifs with hj
    · exact pow_mem (ClosedIF.mem_val.2 (hc j)) _
    · exact zero_mem _
  have hcne : ∀ n ∈ q.support, c n ≠ 0 := by
    intro n hn h0
    refine Polynomial.mem_support_iff.1 hn ?_
    have := hcq n
    rw [h0, map_zero, pow_eq_zero_iff (expChar_pow_pos π.carrier π.p s).ne'] at this
    exact this
  have hQ0 : Q ≠ 0 := by
    intro h0
    have hd : q.natDegree ∈ q.support := q.natDegree_mem_support_of_nonzero hq0
    have : Q.coeff q.natDegree = c q.natDegree ^ π.p ^ r := by
      rw [hQ, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_monomial]
      rw [Finset.sum_ite_eq' q.support _ fun n ↦ c n ^ π.p ^ r, ite_eq_left hd]
    rw [h0, Polynomial.coeff_zero] at this
    exact pow_ne_zero _ (hcne _ hd) this.symm
  -- The evaluation identity, via the `p^(s+r)`-th Frobenius.
  have hQz : Q.eval z = 0 := by
    refine π.incl_injective ?_
    have hev : π.incl (Q.eval z) =
        Polynomial.eval₂ (iterateFrobenius π.carrier π.p (s + r))
          (iterateFrobenius π.carrier π.p (s + r) x) q := by
      rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, hQ]
      rw [Polynomial.eval_finsetSum, map_sum]
      refine Finset.sum_congr rfl fun n hn ↦ ?_
      rw [Polynomial.eval_monomial, map_mul, map_pow, map_pow]
      congr 1
      · -- coefficient side: ι(c n)^(p^r) = (q.coeff n)^(p^(s+r))
        rw [← hcq n, iterateFrobenius_def, ← pow_mul, ← pow_add]
      · -- point side: ι(z)^n = (x^(p^(s+r)))^n
        rw [hz, map_pow, hy, iterateFrobenius_def,
          ← pow_mul x (π.p ^ r) (π.p ^ s), ← pow_add, Nat.add_comm r s]
    rw [hev, Polynomial.eval₂_at_apply, hqx, map_zero, map_zero]
  -- Descend: `z` is algebraic over the closed `M`, hence in `M`.
  have hzM : z ∈ M.1 := M.2 z (isAlgebraic_of_coeff_mem hQ0 hQz hQcoeff)
  refine π.mem_perfIF_iff.2 ⟨r + s, z, ClosedIF.mem_val.1 hzM, ?_⟩
  rw [hz, map_pow, hy, ← pow_mul, ← pow_add]

variable (k) in
/-- `M^perf` as a member of the closed lattice of the perfection over the
perfected base.-/
def perfClosed (M : ClosedIF k K) : ClosedIF (π.basePerf k) π.carrier :=
  ⟨π.perfIF k M, π.isRAC_perfIF M⟩

/-- The perfected intermediate field determines the closed field: `perfIF` is
injective.
@isnad1 id=injectiv.0h3v.s7.dcdd62779fba from=translated src=- shape=bc6ef67b vocab=3be0437c
-/
theorem perfIF_injective : Function.Injective (π.perfIF k (K := K)) := by
  intro M N h
  refine SetLike.ext fun x ↦ ?_
  rw [← π.incl_mem_perfIF_iff (M := M), ← π.incl_mem_perfIF_iff (M := N), h]

/-- `perfIF` reflects the order (via the pullback equation).
@isnad1 id=iff.0h5v.s9.892b3e7d3b7f from=translated src=- shape=6ae68c54 vocab=f7ecc2bb
-/
theorem perfIF_le_iff {M N : ClosedIF k K} :
    π.perfIF k M ≤ π.perfIF k N ↔ M ≤ N := by
  constructor
  · intro h x hx
    exact (π.incl_mem_perfIF_iff).1 (h ((π.incl_mem_perfIF_iff).2 hx))
  · exact π.perfIF_mono

section Comap

/-- Every element of `k` lands in the perfected base under the inclusion.
@isnad1 id=mem.0h4v.s7.ff600721c434 from=translated src=- shape=edf8f552 vocab=ae6882c8
-/
theorem incl_algebraMap_mem_basePerf (c : k) :
    π.incl (algebraMap k K c) ∈ π.basePerf k :=
  π.mem_basePerf_iff.2 ⟨0, c, by simp⟩

variable (k) in
/-- The pullback to `K` of a closed subextension of the perfection
(the inverse of the perfection order isomorphism; blueprint Prop
`perf-lattice`).-/
def comapIF (N : ClosedIF (π.basePerf k) π.carrier) : IntermediateField k K :=
  (N.1.toSubfield.comap π.incl).toIntermediateField fun c ↦ by
    change π.incl (algebraMap k K c) ∈ N.1.toSubfield
    exact N.1.algebraMap_mem (⟨_, π.incl_algebraMap_mem_basePerf c⟩ : π.basePerf k)

/--
@isnad1 id=iff.0h5v.s9.972862c5946c from=translated src=- shape=f27c04b4 vocab=0231b572
-/
theorem mem_comapIF_iff {N : ClosedIF (π.basePerf k) π.carrier} {x : K} :
    x ∈ π.comapIF k N ↔ π.incl x ∈ N :=
  Iff.rfl

/-- The pullback of a closed subextension of the perfection is closed in `K`
(second half of blueprint Prop `perf-lattice`).
@isnad1 id=israc.0h4v.s7.06fb40c875d1 from=translated src=- shape=5ffd71ca vocab=52006abc
-/
theorem isRAC_comapIF (N : ClosedIF (π.basePerf k) π.carrier) :
    IsRAC (π.comapIF k N) := by
  intro y hy
  obtain ⟨P, hP0, hPy, hPc⟩ := exists_poly_of_isAlgebraic hy
  rw [mem_comapIF_iff]
  refine ClosedIF.mem_val.1 <| N.2 (π.incl y) (isAlgebraic_of_coeff_mem
    (p := P.map π.incl)
    ((Polynomial.map_ne_zero_iff π.incl_injective).2 hP0) ?_ fun n ↦ ?_)
  · rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hPy, map_zero]
  · rw [Polynomial.coeff_map]
    exact ClosedIF.mem_val.2 ((π.mem_comapIF_iff (N := N)).1 (hPc n))

variable (k) in
/-- The pullback, as a member of the closed lattice of `K/k`.-/
def comapClosed (N : ClosedIF (π.basePerf k) π.carrier) : ClosedIF k K :=
  ⟨π.comapIF k N, π.isRAC_comapIF N⟩

/-- Equation (5.2) of the blueprint: every closed subextension of the
perfection is the perfection of its pullback.
@isnad1 id=eq.0h4v.s8.9c885c5d36e1 from=translated src=- shape=c7fd17bb vocab=97627940
-/
theorem perfClosed_comapClosed (N : ClosedIF (π.basePerf k) π.carrier) :
    π.perfClosed k (π.comapClosed k N) = N := by
  refine Subtype.ext (SetLike.ext fun x ↦ ?_)
  constructor
  · rintro ⟨n, m, hm, hx⟩
    -- `x ^ p ^ n = ι m ∈ N`, so `x ∈ N` since `N` is closed.
    have h1 : π.incl m ∈ N.1 := ClosedIF.mem_val.2 ((π.mem_comapIF_iff).1 hm)
    have h2 : x ^ π.p ^ n ∈ N.1 := hx ▸ h1
    exact N.2.mem_of_pow_mem (expChar_pow_pos π.carrier π.p n).ne' h2
  · intro hx
    -- Some `p`-power of `x` comes from `K`, and lies in `N`.
    obtain ⟨r, y, hy⟩ := π.exists_pow_incl x
    have h1 : π.incl y ∈ N.1 := by
      rw [hy]
      exact pow_mem hx _
    exact ⟨r, y, (π.mem_comapIF_iff).2 (ClosedIF.mem_val.1 h1), hy.symm⟩

/-- The reverse round trip: pulling the perfection of a closed `M` back to
`K` recovers `M` (restatement of equation 5.1).
@isnad1 id=eq.0h4v.s5.ed2cd33546b8 from=translated src=- shape=b4be77c1 vocab=7bb17111
-/
theorem comapClosed_perfClosed (M : ClosedIF k K) :
    π.comapClosed k (π.perfClosed k M) = M := by
  refine Subtype.ext (SetLike.ext fun x ↦ ?_)
  constructor
  · intro h
    exact ClosedIF.mem_val.2 (π.incl_mem_perfIF_iff.1 ((π.mem_comapIF_iff).1 h))
  · intro h
    exact (π.mem_comapIF_iff).2
      (ClosedIF.mem_val.1 (π.incl_mem_perfIF_iff.2 (ClosedIF.mem_val.1 h)))

variable (k) in
/-- The perfection order isomorphism (blueprint Prop `perf-lattice`):
`𝒢(K/k) ≃o 𝒢(K^perf/k^perf)`, with `M ↦ M^perf` and inverse the pullback
along the inclusion.-/
def latticeIso : ClosedIF k K ≃o ClosedIF (π.basePerf k) π.carrier where
  toFun := π.perfClosed k
  invFun := π.comapClosed k
  left_inv := π.comapClosed_perfClosed
  right_inv := π.perfClosed_comapClosed
  map_rel_iff' {M N} := by
    rw [ClosedIF.le_iff, ClosedIF.le_iff]
    exact π.perfIF_le_iff

end Comap

section Frobenius

/-- The integral Frobenius action on the perfection (blueprint checklist P3):
`n ↦ Frob^n` through the shared `frobeniusZPow` definition in the automorphism group.
The group-power laws supply `Frob^(m+n) = Frob^m * Frob^n` and the negative
iterates for free; in characteristic zero (`p = 1`), Frobenius is the
identity map on elements.-/
def frobZPow (n : ℤ) : RingAut π.carrier :=
  frobeniusZPow π.carrier π.p n

/--
@isnad1 id=eq.0h2v.s9.36d16488a005 from=translated src=- shape=c22f328c vocab=9033e9e9
-/
@[simp] theorem frobZPow_zero : π.frobZPow 0 = 1 := rfl

/--
@isnad1 id=eq.0h4v.s9.2802dde23a6e from=translated src=- shape=6d779d23 vocab=088e73e3
-/
theorem frobZPow_add (m n : ℤ) :
    π.frobZPow (m + n) = π.frobZPow m * π.frobZPow n :=
  zpow_add _ m n

/--
@isnad1 id=eq.0h3v.s8.5f2fd8a41e51 from=translated src=- shape=d7d9cf9f vocab=3a6f06f8
-/
theorem frobZPow_neg (n : ℤ) : π.frobZPow (-n) = (π.frobZPow n)⁻¹ :=
  zpow_neg _ n

/-- Every closed subextension of the perfection is stable, elementwise, under
every integral Frobenius power: closed subextensions are perfect, so both
Frobenius and its inverse preserve them (blueprint P3). In particular every
atom of the perfected geometry is fixed.
@isnad1 id=iff.0h6v.s10.eb28b39f56c4 from=translated src=- shape=988443d2 vocab=7f834710
-/
theorem frobZPow_mem_iff (n : ℤ) {N : ClosedIF (π.basePerf k) π.carrier}
    (x : π.carrier) : π.frobZPow n x ∈ N.1 ↔ x ∈ N.1 := by
  set F : RingAut π.carrier := (frobeniusEquiv π.carrier π.p : RingAut π.carrier)
    with hF
  have h1 : ∀ y : π.carrier, F y ∈ N.1 ↔ y ∈ N.1 := by
    intro y
    have hy : F y = y ^ π.p := by
      rw [hF]
      change frobeniusEquiv π.carrier π.p y = y ^ π.p
      rw [frobeniusEquiv_apply, frobenius_def]
    rw [hy]
    exact ⟨fun h ↦ N.2.mem_of_pow_mem (expChar_pos π.carrier π.p).ne' h,
      fun h ↦ pow_mem h _⟩
  have h2 : ∀ y : π.carrier, F⁻¹ y ∈ N.1 ↔ y ∈ N.1 := by
    intro y
    have hFy : F (F⁻¹ y) = y := RingEquiv.apply_symm_apply F y
    constructor
    · intro h
      have := (h1 (F⁻¹ y)).2 h
      rwa [hFy] at this
    · intro h
      refine (h1 (F⁻¹ y)).1 ?_
      rwa [hFy]
  induction n using Int.induction_on generalizing x with
  | zero => simp [frobZPow, frobeniusZPow]
  | succ i ih =>
    rw [frobZPow, frobeniusZPow, zpow_add_one]
    exact (ih (F x)).trans (h1 x)
  | pred i ih =>
    rw [frobZPow, frobeniusZPow, zpow_sub_one]
    exact (ih (F⁻¹ x)).trans (h2 x)

/-- The setwise form: integral Frobenius powers fix every closed
subextension of the perfection.
@isnad1 id=eq.0h5v.s10.33c720a4ffdd from=translated src=- shape=f5ddaa67 vocab=33188ca0
-/
theorem frobZPow_image_closed (n : ℤ) (N : ClosedIF (π.basePerf k) π.carrier) :
    π.frobZPow n '' (N.1 : Set π.carrier) = (N.1 : Set π.carrier) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (π.frobZPow_mem_iff n z).2 hz
  · intro hy
    refine ⟨π.frobZPow (-n) y, (π.frobZPow_mem_iff (-n) y).2 hy, ?_⟩
    rw [frobZPow_neg]
    exact (π.frobZPow n).apply_symm_apply y

end Frobenius

end Perfection

end

end AclGeom
