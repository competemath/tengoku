import Tengoku.OpenaiMath.OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

/-! Orbit polynomials and exponentiation of locally nilpotent derivations. -/
namespace ComplexCancellation.LND
open Polynomial

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- Local nilpotence, allowing the bound zero for the zero element. -/
def LocallyNilpotent (D : Derivation k R R) : Prop :=
  ∀ r : R, ∃ n : ℕ, (D : R → R)^[n] r = 0

/--
@isnad1 id=eq.0h4v.s7.f86c3c392ff9 from=translated src=- shape=65139bd4 vocab=1b26a7ea
-/
lemma iterate_zero (D : Derivation k R R) (n : ℕ) : (D : R → R)^[n] 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]

/--
@isnad1 id=eq.2h6v.s8.c429b78efade from=translated src=- shape=fb96fcf9 vocab=39d6a5a4
-/
lemma iterate_eq_zero_of_le (D : Derivation k R R) {r : R} {n m : ℕ}
    (h : (D : R → R)^[n] r = 0) (hnm : n ≤ m) : (D : R → R)^[m] r = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [Nat.add_comm, Function.iterate_add_apply, h, iterate_zero]

/--
@isnad1 id=eq.0h6v.s8.75137521e8f2 from=translated src=- shape=938c2ee4 vocab=5d83a4d2
-/
lemma iterate_add (D : Derivation k R R) (n : ℕ) (r s : R) :
    (D : R → R)^[n] (r + s) = (D : R → R)^[n] r + (D : R → R)^[n] s := by
  simpa only [Module.End.pow_apply, Derivation.coeFn_coe] using
    (D.toLinearMap ^ n).map_add r s

/--
@isnad1 id=eq.0h6v.s8.425c578afde6 from=translated src=- shape=9086fa70 vocab=3d30ad00
-/
lemma iterate_smul (D : Derivation k R R) (n : ℕ) (c : k) (r : R) :
    (D : R → R)^[n] (c • r) = c • (D : R → R)^[n] r := by
  simpa only [Module.End.pow_apply, Derivation.coeFn_coe] using
    (D.toLinearMap ^ n).map_smul c r

/--
@isnad1 id=eq.0h6v.s8.e8b68551f073 from=translated src=- shape=19511a91 vocab=91ba33bf
-/
lemma iterate_leibniz (D : Derivation k R R) (n : ℕ) (r s : R) :
    (D : R → R)^[n] (r * s) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        n.choose ij.1 • ((D : R → R)^[ij.1] r * (D : R → R)^[ij.2] s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_sum,
      Finset.sum_antidiagonal_choose_succ_nsmul
        (fun i j => (D : R → R)^[i] r * (D : R → R)^[j] s) n]
    simp only [map_nsmul, Derivation.leibniz, smul_eq_mul, nsmul_add,
      Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro ij hij
      rw [Function.iterate_succ_apply']
    · apply Finset.sum_congr rfl
      rintro ⟨i,j⟩ hij
      have hij' : i + j = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have hchoose : n.choose i = n.choose j := by
        exact Nat.choose_symm_of_eq_add hij'.symm
      rw [Function.iterate_succ_apply', hchoose, mul_comm]

/--
@isnad1 id=finite.1h4v.s7.0934828678a9 from=translated src=- shape=d504351e vocab=9ed8d7f4
-/
lemma orbit_support_finite (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    (Function.support (fun n : ℕ => ((n.factorial : k)⁻¹) • (D : R → R)^[n] r)).Finite := by
  obtain ⟨m, hm⟩ := hD r
  apply (Set.finite_Iio m).subset
  intro n hn
  change n < m
  by_contra h
  have he := iterate_eq_zero_of_le D hm (by omega : m ≤ n)
  exact hn (by simp [he])

noncomputable def orbit (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) : R[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (Finsupp.ofSupportFinite (fun n : ℕ => ((n.factorial : k)⁻¹) • (D : R → R)^[n] r)
      (orbit_support_finite D hD r)))

/--
@isnad1 id=eq.1h5v.s7.3f3caa0f055f from=translated src=- shape=dcb30551 vocab=d9b906ab
-/
@[simp] lemma orbit_coeff (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) (n : ℕ) :
    (orbit D hD r).coeff n = ((n.factorial : k)⁻¹) • (D : R → R)^[n] r := by
  rfl

/--
@isnad1 id=eq.1h4v.s6.c31a34fe64a1 from=translated src=- shape=3b03a75e vocab=d7df9dba
-/
@[simp] lemma orbit_coeff_zero (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    (orbit D hD r).coeff 0 = r := by simp

/--
@isnad1 id=eq.1h4v.s7.64b12b9f5975 from=translated src=- shape=7ebd6666 vocab=5f39e297
-/
@[simp] lemma orbit_coeff_one (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    (orbit D hD r).coeff 1 = D r := by simp

/--
@isnad1 id=eq.1h4v.s7.131f709f6be9 from=translated src=- shape=f172cce0 vocab=63f48c26
-/
lemma inv_factorial_choose [CharZero k] {n i j : ℕ} (h : i + j = n) :
    ((n.factorial : k)⁻¹) * (n.choose i : k) =
      ((i.factorial : k)⁻¹) * ((j.factorial : k)⁻¹) := by
  have hi : i ≤ n := by omega
  rw [Nat.cast_choose k hi, show n - i = j by omega]
  have hn : (n.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp

/--
@isnad1 id=eq.1h5v.s7.517bfab9ffab from=translated src=- shape=b4dd1671 vocab=a73ce7d4
-/
lemma orbit_mul [CharZero k] (D : Derivation k R R) (hD : LocallyNilpotent D) (r s : R) :
    orbit D hD (r * s) = orbit D hD r * orbit D hD s := by
  ext n
  rw [orbit_coeff, Polynomial.coeff_mul, iterate_leibniz, Finset.smul_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ hij
  rw [orbit_coeff, orbit_coeff]
  have hij' : i + j = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, inv_factorial_choose hij',
    smul_mul_smul_comm]

/--
@isnad1 id=eq.1h5v.s7.187ac44c33f0 from=translated src=- shape=d64c4eac vocab=c1b2c3a6
-/
lemma orbit_add (D : Derivation k R R) (hD : LocallyNilpotent D) (r s : R) :
    orbit D hD (r + s) = orbit D hD r + orbit D hD s := by
  ext n
  simp [smul_add]

/--
@isnad1 id=eq.1h4v.s8.3c9b019458bd from=translated src=- shape=07fb7b77 vocab=d3bccb96
-/
lemma orbit_algebraMap (D : Derivation k R R) (hD : LocallyNilpotent D) (c : k) :
    orbit D hD (algebraMap k R c) = C (algebraMap k R c) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp [Function.iterate_succ_apply, D.map_algebraMap]

noncomputable def orbitHom [CharZero k] (D : Derivation k R R) (hD : LocallyNilpotent D) : R →ₐ[k] R[X] where
  toFun := orbit D hD
  map_zero' := by ext; simp
  map_one' := by simpa using orbit_algebraMap D hD 1
  map_add' := orbit_add D hD
  map_mul' := orbit_mul D hD
  commutes' := orbit_algebraMap D hD

/--
@isnad1 id=injectiv.1h3v.s6.8142651ca781 from=translated src=- shape=6d4d407b vocab=0677b041
-/
lemma orbit_injective (D : Derivation k R R) (hD : LocallyNilpotent D) :
    Function.Injective (orbit D hD) := by
  intro r s hes
  simpa using congrArg (fun p : R[X] => p.coeff 0) hes

/--
@isnad1 id=le.2h4v.s8.dccb0d290d57 from=translated src=- shape=7862c391 vocab=8fab3048
-/
lemma orbit_degree_le_one (D : Derivation k R R) (hD : LocallyNilpotent D) {r : R}
    (hr : D (D r) = 0) : (orbit D hD r).natDegree ≤ 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [orbit_coeff, iterate_eq_zero_of_le D (n := 2) hr (by omega), smul_zero]

/--
@isnad1 id=iff.1h4v.s8.fe3a4e7704fc from=translated src=- shape=a5c49b4d vocab=8bb756d1
-/
lemma orbit_constant_iff (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    orbit D hD r = C r ↔ D r = 0 := by
  constructor
  · intro h
    simpa using congrArg (fun p : R[X] => p.coeff 1) h
  · intro h
    ext n
    cases n with
    | zero => simp
    | succ n => simp [Function.iterate_succ_apply, h]

end ComplexCancellation.LND

end

end OAI
