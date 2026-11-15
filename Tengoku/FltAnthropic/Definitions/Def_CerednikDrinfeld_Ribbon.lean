import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ComponentGroup
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin
import Tengoku.Seed.Data.Nat.Prime.Defs
import Tengoku.Seed.Data.PNat.Defs
import Tengoku.Seed.Algebra.Module.Submodule.LinearMap
import Tengoku.Seed.LinearAlgebra.Quotient.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace CerednikDrinfeld

open ModularCurve

variable {E V : Type*}

structure DegeneracyData (E V : Type*) where
  a : E → V
  b : E → V
  w : E → ℕ+

def degeneracyMatrix [DecidableEq V] (f : E → V) : Matrix V E ℤ :=
  Matrix.of fun v e => if f e = v then 1 else 0

def pushforward [Fintype E] [DecidableEq V] (f : E → V) : (E → ℤ) →ₗ[ℤ] (V → ℤ) :=
  (degeneracyMatrix f).mulVecLin

def jointDelta [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    Fin 2 → ((E → ℤ) →ₗ[ℤ] (V → ℤ)) :=
  ![pushforward D.a, pushforward D.b]

def ribbonKernel [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    Submodule ℤ (E → ℤ) :=
  ⨅ i, LinearMap.ker (jointDelta D i)

/--
@isnad1 id=iff.0h4v.s8.e79aea7a3e60 from=translated src=- shape=dd711f42 vocab=bf6935e4
-/
theorem mem_ribbonKernel [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {x : E → ℤ} : x ∈ ribbonKernel D ↔ ∀ i, jointDelta D i x = 0 := by
  simp [ribbonKernel, Submodule.mem_iInf, LinearMap.mem_ker]

/--
@isnad1 id=eq.0h4v.s8.b40db7cd7f1d from=translated src=- shape=e7545f0c vocab=f36f747b
-/
theorem degreeOn_pushforward [Fintype E] [Fintype V] [DecidableEq V] (f : E → V)
    (x : E → ℤ) : degreeOn V (pushforward f x) = degreeOn E x := by
  classical
  simp only [degreeOn_apply, pushforward, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, degeneracyMatrix, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp

/--
@isnad1 id=le.0h3v.s7.1f47ebf22349 from=translated src=- shape=51d9d170 vocab=53957041
-/
theorem ribbonKernel_le_characterLattice [Fintype E] [Fintype V] [DecidableEq V]
    (D : DegeneracyData E V) : ribbonKernel D ≤ characterLattice E := by
  intro x hx
  rw [mem_ribbonKernel] at hx
  have h0 : pushforward D.a x = 0 := by
    simpa [jointDelta] using hx 0
  have hdeg : degreeOn E x = 0 := by
    rw [← degreeOn_pushforward D.a x, h0, map_zero]
  simpa [characterLattice, LinearMap.mem_ker] using hdeg

def ribbonGram [Fintype E] [DecidableEq V] (D : DegeneracyData E V) :
    ribbonKernel D →ₗ[ℤ] Module.Dual ℤ (ribbonKernel D) :=
  (widthPairing (fun e => (D.w e : ℕ))).domRestrict₁₂ (ribbonKernel D) (ribbonKernel D)

/--
@isnad1 id=eq.0h5v.s12.fe0aaab7c37a from=translated src=- shape=d1d1e4e3 vocab=f774b21f
-/
@[simp] theorem ribbonGram_apply [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) (x y : ribbonKernel D) :
    ribbonGram D x y = ∑ e : E, (D.w e : ℤ) * (x.1 e * y.1 e) :=
  rfl

abbrev ribbonComponentGroup [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) :=
  Module.Dual ℤ ↥(ribbonKernel D) ⧸ LinearMap.range (ribbonGram D)

abbrev ribbonComponentGroupProj [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) :
    Module.Dual ℤ ↥(ribbonKernel D) →ₗ[ℤ] ribbonComponentGroup D :=
  (LinearMap.range (ribbonGram D)).mkQ

/--
@isnad1 id=le.1h5v.s14.1aeb5a2998a0 from=translated src=- shape=89b38c00 vocab=63774a46
-/
theorem ribbonGram_range_map_dualMap_le [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) (A B : ribbonKernel D →ₗ[ℤ] ribbonKernel D)
    (hadj : ∀ x y : ribbonKernel D, ribbonGram D (A x) y = ribbonGram D x (B y)) :
    (LinearMap.range (ribbonGram D)).map B.dualMap ≤ LinearMap.range (ribbonGram D) := by
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hf
  refine LinearMap.mem_range.mpr ⟨A x, ?_⟩
  ext y
  rw [LinearMap.dualMap_apply]
  exact hadj x y

def ribbonComponentGroupMap [Fintype E] [DecidableEq V]
    (D : DegeneracyData E V) (A B : ribbonKernel D →ₗ[ℤ] ribbonKernel D)
    (hadj : ∀ x y : ribbonKernel D, ribbonGram D (A x) y = ribbonGram D x (B y)) :
    ribbonComponentGroup D →ₗ[ℤ] ribbonComponentGroup D :=
  (LinearMap.range (ribbonGram D)).mapQ (LinearMap.range (ribbonGram D)) B.dualMap
    (fun _ hf => ribbonGram_range_map_dualMap_le D A B hadj (Submodule.mem_map_of_mem hf))

structure HeckeData [Fintype E] [Fintype V] [DecidableEq V] (D : DegeneracyData E V) where
  T : Nat.Primes → Matrix E E ℤ
  Tv : Nat.Primes → Matrix V V ℤ
  comm : ∀ ℓ ℓ' : Nat.Primes, Commute (T ℓ) (T ℓ')
  commv : ∀ ℓ ℓ' : Nat.Primes, Commute (Tv ℓ) (Tv ℓ')
  S : Finset Nat.Primes
  good_equivariant : ∀ ℓ : Nat.Primes, ℓ ∉ S → ∀ i : Fin 2, ∀ x : E → ℤ,
    jointDelta D i ((T ℓ).mulVecLin x) = (Tv ℓ).mulVecLin (jointDelta D i x)
  kernel_stable : ∀ ℓ : Nat.Primes, ∀ x : E → ℤ, (∀ i, jointDelta D i x = 0) →
    ∀ i, jointDelta D i ((T ℓ).mulVecLin x) = 0

/--
@isnad1 id=mem.1h6v.s8.62040d28c7b8 from=translated src=- shape=df7aac54 vocab=e0266bf9
-/
theorem ribbonKernel_stable [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} (H : HeckeData D) (ℓ : Nat.Primes) :
    ∀ x ∈ ribbonKernel D, (H.T ℓ).mulVecLin x ∈ ribbonKernel D := by
  intro x hx
  rw [mem_ribbonKernel] at hx ⊢
  exact H.kernel_stable ℓ x hx

def heckeKernelMap [Fintype E] [Fintype V] [DecidableEq V]
    {D : DegeneracyData E V} (H : HeckeData D) (ℓ : Nat.Primes) :
    ribbonKernel D →ₗ[ℤ] ribbonKernel D :=
  ((H.T ℓ).mulVecLin).restrict (ribbonKernel_stable H ℓ)

variable {E₁ V₁ E₂ V₂ : Type*}

structure Matching [Fintype E₁] [Fintype V₁] [DecidableEq V₁]
    [Fintype E₂] [Fintype V₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {D₂ : DegeneracyData E₂ V₂}
    (H₁ : HeckeData D₁) (H₂ : HeckeData D₂) where
  eE : E₁ ≃ E₂
  eV : V₁ ≃ V₂
  map_a : ∀ e, D₂.a (eE e) = eV (D₁.a e)
  map_b : ∀ e, D₂.b (eE e) = eV (D₁.b e)
  map_w : ∀ e, D₂.w (eE e) = D₁.w e
  bad : Finset Nat.Primes
  away_intertwine : ∀ ℓ : Nat.Primes, ℓ ∉ bad → ∀ x : E₁ → ℤ,
    (H₂.T ℓ).mulVecLin (x ∘ eE.symm) = ((H₁.T ℓ).mulVecLin x) ∘ eE.symm
  bad_kernel_intertwine : ∀ ℓ : Nat.Primes, ℓ ∈ bad → ∀ x ∈ ribbonKernel D₁,
    (H₂.T ℓ).mulVecLin (x ∘ eE.symm) = ((H₁.T ℓ).mulVecLin x) ∘ eE.symm

end CerednikDrinfeld
