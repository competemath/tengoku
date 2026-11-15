import Tengoku.Seed.Algebra.Module.LocalizedModule.Basic
import Tengoku.Seed.Algebra.MvPolynomial.CommRing
import Tengoku.Seed.RingTheory.Ideal.Maps
import Tengoku.Seed.Algebra.Algebra.Subalgebra.Lattice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace CohCarrier

universe u v w

structure HeckeData (𝒪 : Type u) [CommRing 𝒪] (V : Type v) [AddCommGroup V] [Module 𝒪 V]
    (k : Type w) [Field k] [Algebra 𝒪 k] where

  Gen : Type

  op : Gen → Module.End 𝒪 V

  comm : ∀ g h : Gen, op g * op h = op h * op g

  θbar : Gen → k

namespace HeckeData

variable {𝒪 : Type u} [CommRing 𝒪] {V : Type v} [AddCommGroup V] [Module 𝒪 V]
  {k : Type w} [Field k] [Algebra 𝒪 k] (D : HeckeData 𝒪 V k)

abbrev FreeAlg : Type u := MvPolynomial D.Gen 𝒪

noncomputable def thetaTilde : D.FreeAlg →ₐ[𝒪] k := MvPolynomial.aeval D.θbar

def mTheta : Ideal D.FreeAlg := RingHom.ker D.thetaTilde.toRingHom

/--
@isnad1 id=isprime.0h4v.s6.8ab5bfb61db7 from=translated src=- shape=3b420bde vocab=c6a70fe9
-/
instance mTheta_isPrime : D.mTheta.IsPrime := RingHom.ker_isPrime _

noncomputable def opSubalgebra : Subalgebra 𝒪 (Module.End 𝒪 V) := Algebra.adjoin 𝒪 (Set.range D.op)

/--
@isnad1 id=eq.2h6v.s8.56f51b6d1973 from=translated src=- shape=818c5bea vocab=868276c2
-/
theorem op_comm_of_mem : ∀ a ∈ Set.range D.op, ∀ b ∈ Set.range D.op, a * b = b * a := by
  rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
  exact D.comm g h

/--
@isnad1 id=ismulcom.0h4v.s9.564b2d7b7239 from=translated src=- shape=931aa305 vocab=beb0c700
-/
instance opSubalgebra_isMulCommutative : IsMulCommutative ↥D.opSubalgebra :=
  Algebra.isMulCommutative_adjoin 𝒪 D.op_comm_of_mem

open scoped IsMulCommutative

noncomputable def opAlgHom : D.FreeAlg →ₐ[𝒪] Module.End 𝒪 V :=
  (D.opSubalgebra.val).comp
    (MvPolynomial.aeval fun g => (⟨D.op g, Algebra.subset_adjoin (Set.mem_range_self g)⟩ :
      ↥D.opSubalgebra))

/--
@isnad1 id=eq.0h5v.s8.034526c9ec35 from=translated src=- shape=34a16e64 vocab=4ba4dc52
-/
@[simp] theorem opAlgHom_X (g : D.Gen) : D.opAlgHom (MvPolynomial.X g) = D.op g := by
  simp [opAlgHom]

@[reducible] noncomputable def moduleFreeAlg : Module D.FreeAlg V :=
  Module.compHom V D.opAlgHom.toRingHom

attribute [local instance] moduleFreeAlg

noncomputable abbrev ML : Type (max u v) := LocalizedModule D.mTheta.primeCompl V

noncomputable def toML : V →ₗ[D.FreeAlg] D.ML := LocalizedModule.mkLinearMap D.mTheta.primeCompl V

/--
@isnad1 id=eq.0h6v.s9.c280bb290fcd from=translated src=- shape=12bf9a33 vocab=9073ac15
-/
theorem algebraMap_freeAlg_smul (r : 𝒪) (v : V) : (algebraMap 𝒪 D.FreeAlg r) • v = r • v := by
  show D.opAlgHom (algebraMap 𝒪 D.FreeAlg r) v = r • v
  rw [AlgHom.commutes]
  rfl

/--
@isnad1 id=isscalar.0h4v.s8.88edf16e103f from=translated src=- shape=8036aa36 vocab=b0564cb6
-/
instance V_isScalarTower : IsScalarTower 𝒪 D.FreeAlg V :=
  ⟨fun r a v => by rw [Algebra.smul_def, mul_smul, algebraMap_freeAlg_smul]⟩

noncomputable def toMLₒ : V →ₗ[𝒪] D.ML := D.toML.restrictScalars 𝒪

/--
@isnad1 id=eq.0h5v.s11.d5ec4ae2c5aa from=translated src=- shape=56993506 vocab=22a274ae
-/
@[simp] theorem toMLₒ_apply (v : V) : D.toMLₒ v = D.toML v := rfl

end HeckeData

end CohCarrier

end
