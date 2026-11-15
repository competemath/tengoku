import Tengoku.FltAnthropic.Definitions.Def_HeckeModule_IharaRungDatum
import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace IharaTower

variable {𝒪 : Type} [CommRing 𝒪]
  {T : Type} [CommRing T] [Algebra 𝒪 T]
  {T' : Type} [CommRing T'] [Algebra 𝒪 T']
  {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
  {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}

structure IsIharaDataAt (D : RungDatum T T' M M' P P')
    (πT : T →ₐ[𝒪] 𝒪) (πT' : T' →ₐ[𝒪] 𝒪) : Prop where
  cotorsion_comap_eq :
    Submodule.comap D.j (((RingHom.ker πT) • (⊤ : Submodule T M)).restrictScalars 𝒪) =
      ((RingHom.ker πT') • (⊤ : Submodule T' M')).restrictScalars 𝒪

section CornerRung

open IharaLemma

variable {𝒪 : Type} [CommRing 𝒪]
  {V V' : Type} [AddCommGroup V] [Module 𝒪 V] [AddCommGroup V'] [Module 𝒪 V']
  {𝕋 𝕋' : Type} [CommRing 𝕋] [CommRing 𝕋'] [Algebra 𝒪 𝕋] [Algebra 𝒪 𝕋']
  [Module 𝕋 V] [Module 𝕋' V'] [IsScalarTower 𝒪 𝕋 V] [IsScalarTower 𝒪 𝕋' V']
  (S : IdempotentSplitting 𝕋) (S' : IdempotentSplitting 𝕋') (i₀ : Fin S.n) (i₀' : Fin S'.n)
  (P : LevelPairing (𝒪 := 𝒪) (S.CornerRing i₀) ↥(cornerSubmodule (M := V) (S.e i₀)))
  (P' : LevelPairing (𝒪 := 𝒪) (S'.CornerRing i₀') ↥(cornerSubmodule (M := V') (S'.e i₀')))
  {n : ℕ}
  (L : RungAssembly.LegDatum (T := S.CornerRing i₀) (T' := S'.CornerRing i₀')
    (M := ↥(cornerSubmodule (M := V) (S.e i₀)))
    (M' := ↥(cornerSubmodule (M := V') (S'.e i₀')))
    (𝒪 := 𝒪) P P' n)
  (c : Fin n → S.CornerRing i₀) (res : S'.CornerRing i₀' →ₐ[𝒪] S.CornerRing i₀)

noncomputable def cornerRung :
    RungDatum (𝒪 := 𝒪) (S.CornerRing i₀) (S'.CornerRing i₀')
      ↥(cornerSubmodule (M := V) (S.e i₀)) ↥(cornerSubmodule (M := V') (S'.e i₀')) P P' :=
  RungAssembly.rungDatumOfLegs L c res

/--
@isnad1 id=eq.0h15v.s10.92ad647b4fbb from=translated src=- shape=e2852e1b vocab=ab6cfac0
-/
theorem cornerRung_res : (cornerRung S S' i₀ i₀' P P' L c res).res = res := rfl

/--
@isnad1 id=eq.0h15v.s11.2ce5c1f3d01d from=translated src=- shape=c07f3e25 vocab=9f23961f
-/
theorem cornerRung_i :
    (cornerRung S S' i₀ i₀' P P' L c res).i = RungAssembly.iComb L c := rfl

/--
@isnad1 id=eq.0h15v.s11.5c65d32870d6 from=translated src=- shape=0cba2cfc vocab=4db6cc55
-/
theorem cornerRung_j :
    (cornerRung S S' i₀ i₀' P P' L c res).j = RungAssembly.jComb L c := rfl

/--
@isnad1 id=eq.0h15v.s10.7dd7714df6dd from=translated src=- shape=5259c2cc vocab=5568f184
-/
theorem cornerRung_delta :
    (cornerRung S S' i₀ i₀' P P' L c res).Δ = RungAssembly.deltaComb L c := rfl

end CornerRung

end IharaTower
