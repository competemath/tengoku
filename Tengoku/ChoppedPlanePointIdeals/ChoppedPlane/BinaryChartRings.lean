module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.LaurentPairing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Actual rings for the two binary Laurent charts

The `u` chart allows arbitrary integral powers of `u` and nonnegative powers
of `v`; the `v` chart has the opposite convention.  Their injective algebra
maps into the binary Laurent ring have precisely the chart subspaces used by
the coefficient residue complex.
-/

noncomputable section
namespace ChoppedPlane.BinaryChartRings

open LaurentPairing

variable {K : Type*} [Field K]

abbrev URing (K : Type*) [Field K] := AddMonoidAlgebra K (ℤ × ℕ)
abbrev VRing (K : Type*) [Field K] := AddMonoidAlgebra K (ℕ × ℤ)

def uIndex : ℤ × ℕ →+ ℤ × ℤ where
  toFun e := (e.1, e.2)
  map_zero' := rfl
  map_add' e f := by simp

def vIndex : ℕ × ℤ →+ ℤ × ℤ where
  toFun e := (e.1, e.2)
  map_zero' := rfl
  map_add' e f := by simp

/--
@isnad1 id=injectiv.0h0v.s6.e9d662a6c515 from=translated src=- shape=1aa26a01 vocab=540fa3f3
-/
theorem uIndex_injective : Function.Injective uIndex := by
  intro e f h
  apply Prod.ext
  · simpa [uIndex] using congrArg (fun e : ℤ × ℤ => e.1) h
  · simpa [uIndex] using congrArg (fun e : ℤ × ℤ => e.2) h

/--
@isnad1 id=injectiv.0h0v.s6.5008f9ef0246 from=translated src=- shape=d3593e92 vocab=e2aebe8d
-/
theorem vIndex_injective : Function.Injective vIndex := by
  intro e f h
  apply Prod.ext
  · simpa [vIndex] using congrArg (fun e : ℤ × ℤ => e.1) h
  · simpa [vIndex] using congrArg (fun e : ℤ × ℤ => e.2) h

def uEmbedding : URing K →ₐ[K] BinaryLaurent K :=
  AddMonoidAlgebra.mapDomainAlgHom K K uIndex

def vEmbedding : VRing K →ₐ[K] BinaryLaurent K :=
  AddMonoidAlgebra.mapDomainAlgHom K K vIndex

/--
@isnad1 id=injectiv.0h1v.s7.16daa8d39a64 from=translated src=- shape=8ba1c623 vocab=b0fd2ff2
-/
theorem uEmbedding_injective : Function.Injective (uEmbedding (K := K)) :=
  AddMonoidAlgebra.mapDomain_injective uIndex_injective

/--
@isnad1 id=injectiv.0h1v.s7.6baac33bb04e from=translated src=- shape=8ba1c623 vocab=e890f87f
-/
theorem vEmbedding_injective : Function.Injective (vEmbedding (K := K)) :=
  AddMonoidAlgebra.mapDomain_injective vIndex_injective

/--
@isnad1 id=eq.0h0v.s6.3a2f703c0150 from=translated src=- shape=9db4b4a5 vocab=206da42b
-/
theorem range_uIndex : Set.range uIndex = {e : ℤ × ℤ | 0 ≤ e.2} := by
  ext e
  constructor
  · rintro ⟨p, rfl⟩
    exact Int.natCast_nonneg p.2
  · intro he
    exact ⟨(e.1, e.2.toNat), Prod.ext rfl (Int.toNat_of_nonneg he)⟩

/--
@isnad1 id=eq.0h0v.s6.1d04a9bf5d70 from=translated src=- shape=78b7da90 vocab=f73205a8
-/
theorem range_vIndex : Set.range vIndex = {e : ℤ × ℤ | 0 ≤ e.1} := by
  ext e
  constructor
  · rintro ⟨p, rfl⟩
    exact Int.natCast_nonneg p.1
  · intro he
    exact ⟨(e.1.toNat, e.2), Prod.ext (Int.toNat_of_nonneg he) rfl⟩

/--
@isnad1 id=eq.0h1v.s8.099bef2462da from=translated src=- shape=9137c913 vocab=a6881777
-/
theorem range_uEmbedding : LinearMap.range (uEmbedding (K := K)).toLinearMap = chartU := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    apply AddMonoidAlgebra.mem_supported'.mpr
    intro e he
    change q.coeff.mapDomain uIndex e = 0
    exact Finsupp.mapDomain_of_notMem_range q.coeff e (by simpa [range_uIndex] using he)
  · intro hp
    have hs : (p.coeff.support : Set (ℤ × ℤ)) ⊆ Set.range uIndex := by
      intro e he
      rw [range_uIndex]
      by_contra hn
      have hz := AddMonoidAlgebra.mem_supported'.mp hp e hn
      exact (Finsupp.mem_support_iff.mp he) hz
    refine ⟨AddMonoidAlgebra.comapDomain uIndex uIndex_injective p, ?_⟩
    exact AddMonoidAlgebra.mapDomain_comapDomain hs uIndex_injective

/--
@isnad1 id=eq.0h1v.s8.b8f79142e9b8 from=translated src=- shape=9137c913 vocab=e872cad9
-/
theorem range_vEmbedding : LinearMap.range (vEmbedding (K := K)).toLinearMap = chartV := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    apply AddMonoidAlgebra.mem_supported'.mpr
    intro e he
    change q.coeff.mapDomain vIndex e = 0
    exact Finsupp.mapDomain_of_notMem_range q.coeff e (by simpa [range_vIndex] using he)
  · intro hp
    have hs : (p.coeff.support : Set (ℤ × ℤ)) ⊆ Set.range vIndex := by
      intro e he
      rw [range_vIndex]
      by_contra hn
      have hz := AddMonoidAlgebra.mem_supported'.mp hp e hn
      exact (Finsupp.mem_support_iff.mp he) hz
    refine ⟨AddMonoidAlgebra.comapDomain vIndex vIndex_injective p, ?_⟩
    exact AddMonoidAlgebra.mapDomain_comapDomain hs vIndex_injective

def uU : URing K := AddMonoidAlgebra.single (1, 0) 1
def vU : URing K := AddMonoidAlgebra.single (0, 1) 1
def uUInv : URing K := AddMonoidAlgebra.single (-1, 0) 1

def uV : VRing K := AddMonoidAlgebra.single (1, 0) 1
def vV : VRing K := AddMonoidAlgebra.single (0, 1) 1
def vVInv : VRing K := AddMonoidAlgebra.single (0, -1) 1

/--
@isnad1 id=eq.0h1v.s6.52516ffeaed3 from=translated src=- shape=e94b03c3 vocab=f8fab94a
-/
@[simp] theorem uU_mul_inv : uU (K := K) * uUInv = 1 := by
  simp [uU, uUInv, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]
  rfl

/--
@isnad1 id=eq.0h1v.s6.762151bde808 from=translated src=- shape=e94b03c3 vocab=9ac8cc5e
-/
@[simp] theorem vV_mul_inv : vV (K := K) * vVInv = 1 := by
  simp [vV, vVInv, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]
  rfl

/--
@isnad1 id=eq.0h1v.s7.550e2b69d5fd from=translated src=- shape=d0481623 vocab=4ef80998
-/
@[simp] theorem uEmbedding_u : uEmbedding (uU (K := K)) = U := by
  simp [uEmbedding, uU, U, uIndex]

/--
@isnad1 id=eq.0h1v.s7.f7f5d38a75dd from=translated src=- shape=d0481623 vocab=5217a7b4
-/
@[simp] theorem uEmbedding_v : uEmbedding (vU (K := K)) = V := by
  simp [uEmbedding, vU, V, uIndex]

/--
@isnad1 id=eq.0h1v.s7.1ede9f1d091b from=translated src=- shape=d0481623 vocab=cf33a283
-/
@[simp] theorem vEmbedding_u : vEmbedding (uV (K := K)) = U := by
  simp [vEmbedding, uV, U, vIndex]

/--
@isnad1 id=eq.0h1v.s7.9027d44bf77c from=translated src=- shape=d0481623 vocab=12acdd85
-/
@[simp] theorem vEmbedding_v : vEmbedding (vV (K := K)) = V := by
  simp [vEmbedding, vV, V, vIndex]

end ChoppedPlane.BinaryChartRings
