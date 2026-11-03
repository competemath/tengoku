/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_1.Notation_2_18

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 — real/imaginary decomposition of `R[i] = Ri R`

`Ri R = R[X]/(X²+1)` is a free `R`-module on `{1, i}`. We extract the `R`-linear coordinate maps
`Ri.reL`, `Ri.imL : Ri R →ₗ[R] R` (via the degree-`<2` remainder `AdjoinRoot.modByMonicHom`) and
record `re (a + b·i) = a`, `im (a + b·i) = b`, and the decomposition `z = re z + (im z)·i`. This is
the coefficientwise ingredient of the commutation isomorphism `R[i]⟨⟨ε⟩⟩ ≅ R⟨⟨ε⟩⟩[i]`. -/

namespace Azurite.BPR

open Polynomial AdjoinRoot

variable {R : Type*} [CommRing R]

/-- `X² + 1` is monic.
@isnad1 id=monic.0h1v.s7.73cbbd0459b5 from=translated src=- shape=b1137392 vocab=8f1ad163
-/
theorem riMonic : (X ^ 2 + 1 : R[X]).Monic := by
  have h := monic_X_pow_add_C (a := (1 : R)) (n := 2) (by norm_num)
  rwa [C_1] at h

/-- `of c = mk (C c)` (definitionally).
@isnad1 id=eq.0h2v.s11.a39320e35d4c from=translated src=- shape=f3d9cb29 vocab=43991a3a
-/
theorem Ri.mk_C_eq_of (c : R) : AdjoinRoot.mk (X ^ 2 + 1) (C c) = AdjoinRoot.of (X ^ 2 + 1) c := rfl

/-- The real part `Ri R →ₗ[R] R`.-/
noncomputable def Ri.reL : Ri R →ₗ[R] R := (lcoeff R 0).comp (modByMonicHom riMonic)

/-- The imaginary part `Ri R →ₗ[R] R`.-/
noncomputable def Ri.imL : Ri R →ₗ[R] R := (lcoeff R 1).comp (modByMonicHom riMonic)

variable [Nontrivial R]

/--
@isnad1 id=eq.0h1v.s7.ff747f42af01 from=translated src=- shape=ae82c796 vocab=818de7ad
-/
theorem riDegree : (X ^ 2 + 1 : R[X]).degree = 2 := by
  rw [show (X ^ 2 + 1 : R[X]) = X ^ 2 + C 1 by rw [C_1], degree_X_pow_add_C (by norm_num)]; rfl

/--
@isnad1 id=eq.0h1v.s7.909d4256ef5b from=translated src=- shape=b2abef8c vocab=f9ae81c3
-/
theorem riNatDegree : (X ^ 2 + 1 : R[X]).natDegree = 2 := natDegree_eq_of_degree_eq_some riDegree

/--
@isnad1 id=eq.1h2v.s11.85185c9e3b27 from=translated src=- shape=f86a923c vocab=1159a339
-/
theorem Ri.reL_mk (p : R[X]) (hp : p.natDegree ≤ 1) :
    Ri.reL (AdjoinRoot.mk (X ^ 2 + 1) p) = p.coeff 0 := by
  have hself : p %ₘ (X ^ 2 + 1) = p := (modByMonic_eq_self_iff riMonic).mpr (by
    rw [riDegree]; exact lt_of_le_of_lt (degree_le_of_natDegree_le hp) (by norm_num))
  rw [Ri.reL, LinearMap.comp_apply, modByMonicHom_mk, hself, lcoeff_apply]

/--
@isnad1 id=eq.1h2v.s11.cfdb4e57499d from=translated src=- shape=f86a923c vocab=b2e24bb8
-/
theorem Ri.imL_mk (p : R[X]) (hp : p.natDegree ≤ 1) :
    Ri.imL (AdjoinRoot.mk (X ^ 2 + 1) p) = p.coeff 1 := by
  have hself : p %ₘ (X ^ 2 + 1) = p := (modByMonic_eq_self_iff riMonic).mpr (by
    rw [riDegree]; exact lt_of_le_of_lt (degree_le_of_natDegree_le hp) (by norm_num))
  rw [Ri.imL, LinearMap.comp_apply, modByMonicHom_mk, hself, lcoeff_apply]

/--
@isnad1 id=eq.0h2v.s11.96f66b12c0af from=translated src=- shape=b18f81d3 vocab=5b73b24a
-/
@[simp] theorem Ri.reL_of (a : R) : Ri.reL (AdjoinRoot.of (X ^ 2 + 1) a) = a := by
  rw [← Ri.mk_C_eq_of, Ri.reL_mk _ (by simp), coeff_C_zero]

/--
@isnad1 id=eq.0h2v.s11.77f89e1ce82c from=translated src=- shape=ba46dce3 vocab=d21ba6b6
-/
@[simp] theorem Ri.imL_of (a : R) : Ri.imL (AdjoinRoot.of (X ^ 2 + 1) a) = 0 := by
  rw [← Ri.mk_C_eq_of, Ri.imL_mk _ (by simp)]; simp

/--
@isnad1 id=eq.0h1v.s9.51f0754fa2d9 from=translated src=- shape=6d9f31df vocab=bda421b8
-/
@[simp] theorem Ri.reL_i : Ri.reL (Ri.i R) = 0 := by
  rw [Ri.i, ← AdjoinRoot.mk_X, Ri.reL_mk _ (by simp [natDegree_X])]; simp

/--
@isnad1 id=eq.0h1v.s9.e537e97d9053 from=translated src=- shape=6d9f31df vocab=0ef0d369
-/
@[simp] theorem Ri.imL_i : Ri.imL (Ri.i R) = 1 := by
  rw [Ri.i, ← AdjoinRoot.mk_X, Ri.imL_mk _ (by simp [natDegree_X])]; simp

omit [Nontrivial R] in
/--
@isnad1 id=eq.0h2v.s11.030f286f66ef from=translated src=- shape=5e76a724 vocab=09c46c39
-/
theorem Ri.of_mul_i_eq_smul (b : R) : AdjoinRoot.of (X ^ 2 + 1) b * Ri.i R = b • Ri.i R := by
  rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq]

/--
@isnad1 id=eq.0h3v.s12.1f9c6e595dc6 from=translated src=- shape=34ebea64 vocab=955ec127
-/
@[simp] theorem Ri.reL_lin (a b : R) :
    Ri.reL (AdjoinRoot.of (X ^ 2 + 1) a + AdjoinRoot.of (X ^ 2 + 1) b * Ri.i R) = a := by
  rw [Ri.of_mul_i_eq_smul, map_add, map_smul, Ri.reL_of, Ri.reL_i, smul_zero, add_zero]

/--
@isnad1 id=eq.0h3v.s12.6ab750be51bf from=translated src=- shape=fe02dee8 vocab=29a442e8
-/
@[simp] theorem Ri.imL_lin (a b : R) :
    Ri.imL (AdjoinRoot.of (X ^ 2 + 1) a + AdjoinRoot.of (X ^ 2 + 1) b * Ri.i R) = b := by
  rw [Ri.of_mul_i_eq_smul, map_add, map_smul, Ri.imL_of, Ri.imL_i, smul_eq_mul, mul_one, zero_add]

/-- **Decomposition** `z = re z + (im z)·i`.
@isnad1 id=eq.0h2v.s12.7a017ee313e1 from=translated src=- shape=bfa096ac vocab=c9d9e915
-/
theorem Ri.of_reL_add_of_imL_mul_i (z : Ri R) :
    AdjoinRoot.of (X ^ 2 + 1) (Ri.reL z) + AdjoinRoot.of (X ^ 2 + 1) (Ri.imL z) * Ri.i R = z := by
  induction z using AdjoinRoot.induction_on with
  | _ p =>
    have hqdeg : (p %ₘ (X ^ 2 + 1)).natDegree ≤ 1 := by
      have hne : (X ^ 2 + 1 : R[X]) ≠ 1 := fun h => by simpa [riNatDegree] using congrArg natDegree h
      have h := natDegree_modByMonic_lt p (riMonic (R := R)) hne
      rw [riNatDegree] at h; omega
    have hmkp : AdjoinRoot.mk (X ^ 2 + 1) p = AdjoinRoot.mk (X ^ 2 + 1) (p %ₘ (X ^ 2 + 1)) := by
      rw [← modByMonicHom_mk (riMonic (R := R)) p, mk_leftInverse (riMonic (R := R))]
    have hi : Ri.i R = AdjoinRoot.mk (X ^ 2 + 1) X := (AdjoinRoot.mk_X).symm
    rw [hmkp, Ri.reL_mk _ hqdeg, Ri.imL_mk _ hqdeg, hi]
    conv_rhs => rw [eq_X_add_C_of_natDegree_le_one hqdeg]
    rw [map_add, map_mul, Ri.mk_C_eq_of, Ri.mk_C_eq_of]
    ring

end Azurite.BPR
