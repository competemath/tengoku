import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.AbhyankarSathaye.LiftingIdentities

namespace OAI

/-!
# Mutually inverse polynomial formulas

The parameter `T = α * U + β * (V + U * W)` and the formulas `inverseU`,
`inverseV`, and `inverseW` reconstruct each other over arbitrary commutative rings.
-/

namespace AbhyankarSathaye
section
variable {B : Type*} [CommRing B]

def inverseU (h x β T : B) : B := h*T-β*x
def inverseG (x y α T : B) : B := y*T+α*x
def inverseW (h y s α β U G : B) : B :=
  α*(1+β*y)*(y+U^2)+β^2*(s-h*G^2+2*U*y*G)
def inverseV (U G W : B) : B := G-U*W
def parameter (α β U V W : B) : B := α*U+β*(V+U*W)

/--
@isnad1 id=other.2h8v.s8.559f6fe704f8 from=translated src=- shape=0adb1a5e vocab=3774b61e
-/
theorem inverse_relations (h x y s α β T : B)
    (hc : x^2+y^3 = h*s) (hb : α*h+β*y = 1) :
    let U := inverseU h x β T
    let G := inverseG x y α T
    let W := inverseW h y s α β U G
    U^3+h*inverseV U G W = x ∧ -U^2+h*W = y ∧ S h U (inverseV U G W) W = s := by
  dsimp only
  have hl := linear_parameter_relation h x y α β T hb
  have hcompat := compatibility h x y s (inverseU h x β T) (inverseG x y α T) hc hl
  have hb2 := squared_bezout h y α β hb
  have hw := solve_h h (y^2) (y+(inverseU h x β T)^2)
    (s-h*(inverseG x y α T)^2+2*(inverseU h x β T)*y*(inverseG x y α T))
    (α*(1+β*y)) (β^2) hcompat hb2
  have hs := solve_c h (y^2) (y+(inverseU h x β T)^2)
    (s-h*(inverseG x y α T)^2+2*(inverseU h x β T)*y*(inverseG x y α T))
    (α*(1+β*y)) (β^2) hcompat hb2
  exact linear_to_original h x y s _ _ _ hl hw hs

/--
@isnad1 id=other.1h8v.s7.928184000ef5 from=translated src=- shape=c9fcfcf5 vocab=e4278755
-/
theorem inverse_parameter (h x y s α β T : B) (hb : α*h+β*y = 1) :
    let U := inverseU h x β T
    let G := inverseG x y α T
    let W := inverseW h y s α β U G
    parameter α β U (inverseV U G W) W = T := by
  dsimp only [parameter, inverseV]
  have he := linear_parameter_inverse h x y α β T hb
  dsimp [inverseU, inverseG]
  convert he using 1
  ring

/--
@isnad1 id=other.4h10v.s8.0bd461bf0529 from=translated src=- shape=09e35416 vocab=d602a349
-/
theorem original_reconstruction (h x y s α β U V W : B)
    (hb : α*h+β*y = 1) (hx : U^3+h*V = x)
    (hy : -U^2+h*W = y) (hs : S h U V W = s) :
    let T := parameter α β U V W
    let U' := inverseU h x β T
    let G' := inverseG x y α T
    let W' := inverseW h y s α β U' G'
    U' = U ∧ inverseV U' G' W' = V ∧ W' = W := by
  dsimp only
  obtain ⟨hl, hw, hs'⟩ := original_to_linear h x y s U V W hx hy hs
  have hu : inverseU h x β (parameter α β U V W) = U :=
    recover_U h x y α β U (V+U*W) hb hl
  have hg : inverseG x y α (parameter α β U V W) = V+U*W :=
    recover_G h x y α β U (V+U*W) hb hl
  rw [hu, hg]
  have hww : inverseW h y s α β U (V+U*W) = W :=
    (solve_unique h (y^2) (y+U^2) (s-h*(V+U*W)^2+2*U*y*(V+U*W))
      (α*(1+β*y)) (β^2) W (squared_bezout h y α β hb) hw hs').symm
  rw [hww]
  refine ⟨rfl, ?_, rfl⟩
  unfold inverseV
  ring

end

section Maps
variable {B D H : Type*} [CommRing B] [CommRing D]
variable [FunLike H B D] [RingHomClass H B D]

/--
@isnad1 id=eq.0h8v.s6.c2a468985bd7 from=translated src=- shape=8766dc8a vocab=5226db14
-/
@[simp] theorem map_inverseU (f : H) (h x β T : B) :
    f (inverseU h x β T) = inverseU (f h) (f x) (f β) (f T) := by simp [inverseU]
/--
@isnad1 id=eq.0h8v.s6.3a4ad4dad178 from=translated src=- shape=8766dc8a vocab=efcffb62
-/
@[simp] theorem map_inverseG (f : H) (x y α T : B) :
    f (inverseG x y α T) = inverseG (f x) (f y) (f α) (f T) := by simp [inverseG]
/--
@isnad1 id=eq.0h11v.s7.ac09a04e9ddb from=translated src=- shape=a433d351 vocab=c0361254
-/
@[simp] theorem map_inverseW (f : H) (h y s α β U G : B) :
    f (inverseW h y s α β U G) =
      inverseW (f h) (f y) (f s) (f α) (f β) (f U) (f G) := by simp [inverseW, map_ofNat]
/--
@isnad1 id=eq.0h7v.s6.325919938cb3 from=translated src=- shape=e50a39ff vocab=3861ac3b
-/
@[simp] theorem map_inverseV (f : H) (U G W : B) :
    f (inverseV U G W) = inverseV (f U) (f G) (f W) := by simp [inverseV]
/--
@isnad1 id=eq.0h9v.s6.7abdf0de34a5 from=translated src=- shape=6d6416b7 vocab=32f68fdf
-/
@[simp] theorem map_parameter (f : H) (α β U V W : B) :
    f (parameter α β U V W) = parameter (f α) (f β) (f U) (f V) (f W) := by
  simp [parameter]

end Maps
end AbhyankarSathaye

end OAI
