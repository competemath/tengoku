import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

namespace ModularCurve

noncomputable section

abbrev uvCrossingIdeal (W : Type u) [CommRing W] (π : W) : Ideal (MvPowerSeries (Fin 2) W) :=
  Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
    MvPowerSeries.C π}

abbrev UVCrossingModel (W : Type u) [CommRing W] (π : W) : Type u :=
  MvPowerSeries (Fin 2) W ⧸ uvCrossingIdeal W π

namespace UVCrossingModel

variable {W : Type u} [CommRing W]

def mk (π : W) : MvPowerSeries (Fin 2) W →+* UVCrossingModel W π :=
  Ideal.Quotient.mk _

def U (π : W) : UVCrossingModel W π := mk π (MvPowerSeries.X 0)

def V (π : W) : UVCrossingModel W π := mk π (MvPowerSeries.X 1)

def const (π : W) (w : W) : UVCrossingModel W π := mk π (MvPowerSeries.C w)

def constHom (π : W) : W →+* UVCrossingModel W π :=
  (mk π).comp (MvPowerSeries.C : W →+* MvPowerSeries (Fin 2) W)

/--
@isnad1 id=eq.0h3v.s6.e4820f84420d from=translated src=- shape=15238020 vocab=25d07618
-/
theorem constHom_apply (π : W) (w : W) : constHom π w = const π w := rfl

/--
@isnad1 id=surjecti.0h2v.s7.5099e245a43d from=translated src=- shape=9c81019b vocab=488bfa3d
-/
theorem mk_surjective (π : W) : Function.Surjective (mk (W := W) π) :=
  Ideal.Quotient.mk_surjective

end UVCrossingModel

abbrev wittCrossingModel (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] : Type u :=
  UVCrossingModel (WittVector p k) (p : WittVector p k)

section VariableSwap

variable {W : Type u} [CommRing W]

def uvSwapEquiv : MvPowerSeries (Fin 2) W ≃+* MvPowerSeries (Fin 2) W :=
  (MvPowerSeries.renameEquiv W (Equiv.swap (0 : Fin 2) 1)).toRingEquiv

/--
@isnad1 id=eq.0h2v.s9.8b831edeb647 from=translated src=- shape=4c563058 vocab=980033c2
-/
theorem uvSwapEquiv_apply (f : MvPowerSeries (Fin 2) W) :
    uvSwapEquiv f = MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) f := rfl

/--
@isnad1 id=eq.0h1v.s8.94ae124a7aee from=translated src=- shape=0178ea28 vocab=6b6da1c5
-/
theorem uvSwapEquiv_X_zero :
    uvSwapEquiv (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) W) =
      MvPowerSeries.X 1 := by
  rw [uvSwapEquiv_apply, MvPowerSeries.rename_X, Equiv.swap_apply_left]

/--
@isnad1 id=eq.0h1v.s8.464a7f872aeb from=translated src=- shape=0178ea28 vocab=6b6da1c5
-/
theorem uvSwapEquiv_X_one :
    uvSwapEquiv (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) W) =
      MvPowerSeries.X 0 := by
  rw [uvSwapEquiv_apply, MvPowerSeries.rename_X, Equiv.swap_apply_right]

/--
@isnad1 id=eq.0h2v.s9.69d035453b4b from=translated src=- shape=b372f2dd vocab=6f4ea58b
-/
theorem uvSwapEquiv_C (w : W) :
    uvSwapEquiv (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) = MvPowerSeries.C w := by
  rw [uvSwapEquiv_apply, MvPowerSeries.rename_C]

/--
@isnad1 id=eq.0h2v.s9.126db31c5992 from=translated src=- shape=f7e23f37 vocab=73602300
-/
theorem uvSwapEquiv_crossing (π : W) :
    uvSwapEquiv ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
        MvPowerSeries.C π) =
      (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
        MvPowerSeries.C π := by
  rw [map_sub, map_mul, uvSwapEquiv_X_zero, uvSwapEquiv_X_one, uvSwapEquiv_C, mul_comm]

/--
@isnad1 id=eq.0h2v.s8.af9c16c44f19 from=translated src=- shape=4b5ac899 vocab=9ad90c09
-/
theorem map_uvSwapEquiv_uvCrossingIdeal (π : W) :
    Ideal.map (uvSwapEquiv (W := W)) (uvCrossingIdeal W π) = uvCrossingIdeal W π := by
  rw [show uvCrossingIdeal W π = Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) *
    MvPowerSeries.X 1 - MvPowerSeries.C π} from rfl, Ideal.map_span, Set.image_singleton,
    uvSwapEquiv_crossing]

end VariableSwap

namespace UVCrossingModel

variable {W : Type u} [CommRing W]

def crossingSwap (π : W) : UVCrossingModel W π ≃+* UVCrossingModel W π :=
  Ideal.quotientEquiv (uvCrossingIdeal W π) (uvCrossingIdeal W π) uvSwapEquiv
    (map_uvSwapEquiv_uvCrossingIdeal π).symm

/--
@isnad1 id=eq.0h3v.s10.c393ad519dba from=translated src=- shape=6ba8290a vocab=31a2b9d6
-/
theorem crossingSwap_mk (π : W) (f : MvPowerSeries (Fin 2) W) :
    crossingSwap π (UVCrossingModel.mk π f) = UVCrossingModel.mk π (uvSwapEquiv f) := rfl

def S (π : W) : UVCrossingModel W π := U π + V π

def D (π : W) : UVCrossingModel W π := U π - V π

/--
@isnad1 id=eq.0h2v.s6.f046efccb186 from=translated src=- shape=a7249be7 vocab=f4340022
-/
theorem S_def (π : W) : S π = U π + V π := rfl

/--
@isnad1 id=eq.0h2v.s6.cf6fa3e05ce9 from=translated src=- shape=a7249be7 vocab=461b0e08
-/
theorem D_def (π : W) : D π = U π - V π := rfl

def fixedSubring (π : W) : Subring (UVCrossingModel W π) :=
  RingHom.eqLocus
    (crossingSwap π : UVCrossingModel W π →+* UVCrossingModel W π) (RingHom.id _)

/--
@isnad1 id=iff.0h3v.s9.0020fc0f6696 from=translated src=- shape=641955d5 vocab=df76303e
-/
theorem mem_fixedSubring_iff {π : W} {x : UVCrossingModel W π} :
    x ∈ fixedSubring π ↔ crossingSwap π x = x :=
  Iff.rfl

end UVCrossingModel

end

end ModularCurve
