import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AdjoinRoot_isUnit_one_sub_root_pow_of_isUnit_of_not_dvd.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AdjoinRoot_isUnit_one_sub_root_pow_of_isUnit_of_not_dvd

set_option autoImplicit false

open Polynomial

universe u

namespace CycStrong29

abbrev S0 (m : ℕ) : Type := AdjoinRoot (cyclotomic m ℤ)

/--
@isnad1 id=isdomain.1h1v.s4.cdfbb623cf6b from=translated src=- shape=c1538fc1 vocab=0025855c
-/
theorem isDomain_S0 (m : ℕ) (hm : 0 < m) : IsDomain (S0 m) :=
  AdjoinRoot.isDomain_of_prime (cyclotomic.irreducible hm).prime

/--
@isnad1 id=ne.2h2v.s6.fd3c7c2783ed from=translated src=- shape=adb0c915 vocab=db02f520
-/
theorem natCast_ne_zero_S0 (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : n ≠ 0) : ((n : ℕ) : S0 m) ≠ 0 := by
  intro h
  have h' : AdjoinRoot.mk (cyclotomic m ℤ) (C (n : ℤ)) = 0 := by
    rw [← map_natCast (AdjoinRoot.of (cyclotomic m ℤ)) n] at h
    rw [← h, AdjoinRoot.mk_C]
  rw [AdjoinRoot.mk_eq_zero] at h'
  have hdeg := Polynomial.natDegree_le_of_dvd h' (by simp [hn])
  rw [natDegree_C, natDegree_cyclotomic] at hdeg
  exact absurd hdeg (not_le.mpr (Nat.totient_pos.mpr hm))

/--
@isnad1 id=dvd.3h3v.s6.26a3c8a30db8 from=translated src=- shape=51533694 vocab=252335a9
-/
theorem one_sub_dvd_of_isPrimitiveRoot {R : Type} [CommRing R] [IsDomain R] {ω : R} {d : ℕ} (hd : 0 < d)
    (hω : IsPrimitiveRoot ω d) (hω1 : ω ≠ 1) : (1 - ω) ∣ (d : R) := by
  classical
  have hprod := X_pow_sub_one_eq_prod hd hω
  have h1mem : (1 : R) ∈ nthRootsFinset d (1 : R) := (mem_nthRootsFinset hd (1 : R)).mpr (one_pow d)
  have hωmem : ω ∈ (nthRootsFinset d (1 : R)).erase 1 :=
    Finset.mem_erase.mpr ⟨hω1, (mem_nthRootsFinset hd (1 : R)).mpr hω.pow_eq_one⟩

  have hsplit : (X - C (1 : R)) * ∏ μ ∈ (nthRootsFinset d (1 : R)).erase 1, (X - C μ) =
      (X - C 1) * ∑ i ∈ Finset.range d, X ^ i := by
    rw [Finset.mul_prod_erase _ (fun μ => X - C μ) h1mem, ← hprod, C_1, mul_comm, geom_sum_mul]
  have hX1 : (X - C (1 : R)) ≠ 0 := X_sub_C_ne_zero 1
  have hq := mul_left_cancel₀ hX1 hsplit

  have hev := congrArg (eval (1 : R)) hq
  rw [eval_prod, eval_geom_sum] at hev
  simp only [eval_sub, eval_X, eval_C, one_pow, Finset.sum_const, Finset.card_range] at hev
  have hev' : ∏ μ ∈ (nthRootsFinset d (1 : R)).erase 1, ((1 : R) - μ) = (d : R) := by
    rw [hev, nsmul_eq_mul, mul_one]
  rw [← hev']
  exact Finset.dvd_prod_of_mem (fun μ => (1 : R) - μ) hωmem

/--
@isnad1 id=dvd.2h2v.s8.428d80b1b467 from=translated src=- shape=32d57419 vocab=f1a8962e
-/
theorem one_sub_pow_dvd_S0 (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : ¬ m ∣ j) :
    (1 - AdjoinRoot.root (cyclotomic m ℤ) ^ j) ∣ ((m : ℕ) : S0 m) := by
  haveI := isDomain_S0 m hm
  haveI : NeZero ((m : ℕ) : S0 m) := ⟨natCast_ne_zero_S0 m hm m hm.ne'⟩
  have hζ : IsPrimitiveRoot (AdjoinRoot.root (cyclotomic m ℤ)) m := by
    refine (isRoot_cyclotomic_iff (R := S0 m)).mp ?_
    have := AdjoinRoot.isRoot_root (cyclotomic m ℤ)
    rwa [map_cyclotomic] at this
  set ω := AdjoinRoot.root (cyclotomic m ℤ) ^ j with hω
  have hω1 : ω ≠ 1 := fun h => hj ((hζ.pow_eq_one_iff_dvd j).mp h)
  have hωd : IsPrimitiveRoot ω (orderOf ω) := IsPrimitiveRoot.orderOf ω
  have hωm : ω ^ m = 1 := by rw [hω, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hdpos : 0 < orderOf ω := (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hωm⟩).orderOf_pos
  have hdvd : orderOf ω ∣ m := orderOf_dvd_of_pow_eq_one hωm
  exact (one_sub_dvd_of_isPrimitiveRoot hdpos hωd hω1).trans (Nat.cast_dvd_cast hdvd)

end CycStrong29

open CycStrong29 in
/--
@isnad1 id=isunit.2h3v.s8.2fbbe40e8e2f from=translated src=- shape=b6b4141f vocab=301af526
-/
theorem solution
    (𝒪 : Type u) [CommRing 𝒪] (m : ℕ) (hm : IsUnit ((m : ℕ) : 𝒪)) (j : ℕ) (hj : ¬ m ∣ j) :
    IsUnit (1 - AdjoinRoot.root (cyclotomic m 𝒪) ^ j) := by
  rcases subsingleton_or_nontrivial 𝒪 with h𝒪 | h𝒪
  · haveI : Subsingleton (AdjoinRoot (cyclotomic m 𝒪)) := (algebraMap 𝒪 (AdjoinRoot (cyclotomic m 𝒪))).codomain_trivial
    exact isUnit_of_subsingleton _
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hm
    · exact h

  set 𝒪' := AdjoinRoot (cyclotomic m 𝒪) with h𝒪'
  have hroot : eval₂ (Int.castRingHom 𝒪') (AdjoinRoot.root (cyclotomic m 𝒪)) (cyclotomic m ℤ) = 0 := by
    rw [eval₂_eq_eval_map, map_cyclotomic, ← map_cyclotomic m (algebraMap 𝒪 𝒪'), eval_map,
      ← aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  let φ : S0 m →+* 𝒪' := AdjoinRoot.lift (Int.castRingHom 𝒪') (AdjoinRoot.root (cyclotomic m 𝒪)) hroot
  obtain ⟨α, hα⟩ := one_sub_pow_dvd_S0 m hm0 j hj
  have h := congrArg φ hα
  rw [map_natCast, map_mul, map_sub, map_one, map_pow, AdjoinRoot.lift_root] at h
  have hm' : IsUnit ((m : ℕ) : 𝒪') := by simpa using hm.map (algebraMap 𝒪 𝒪')
  rw [h] at hm'
  exact isUnit_of_mul_isUnit_left hm'
