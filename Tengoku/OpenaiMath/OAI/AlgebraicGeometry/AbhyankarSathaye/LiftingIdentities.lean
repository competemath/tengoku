import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.AbhyankarSathaye.Identities

namespace OAI

/-!
# Linear equations for the lifting construction

The substitution `G = V + U * W` makes the equations linear in `W`.
A Bézout relation gives existence and uniqueness without cancellation.
-/

namespace AbhyankarSathaye
section
variable {B : Type*} [CommRing B]

/--
@isnad1 id=eq.0h5v.s8.0e441759ce30 from=translated src=- shape=82862447 vocab=b9deb524
-/
theorem substitute_S (h U G W : B) :
    S h U (G-U*W) W =
      h*G^2 - 2*U*(h*W-U^2)*G + (h*W-U^2)^2*W := by
  unfold S
  ring

/--
@isnad1 id=eq.0h6v.s8.dcc36632887f from=translated src=- shape=adfd5615 vocab=9c1cdc1d
-/
theorem compatibility_identity (h y s U G : B) :
    y^2*(y+U^2) - h*(s-h*G^2+2*U*y*G) =
      (h*G-y*U)^2 + y^3 - h*s := by ring

/--
@isnad1 id=eq.2h7v.s8.10b9a03022ed from=translated src=- shape=f4b74dba vocab=9c1cdc1d
-/
theorem compatibility (h x y s U G : B)
    (hc : x^2+y^3 = h*s) (hl : h*G-y*U = x) :
    y^2*(y+U^2) = h*(s-h*G^2+2*U*y*G) := by
  apply sub_eq_zero.mp
  rw [compatibility_identity, hl, hc, sub_self]

/--
@isnad1 id=eq.1h5v.s7.bb4b66f32fc6 from=translated src=- shape=3800977d vocab=a1216c81
-/
theorem squared_bezout (h y α β : B) (hb : α*h+β*y = 1) :
    α*(1+β*y)*h + β^2*y^2 = 1 := by
  calc
    _ = (α*h+β*y-1)*(1+β*y)+1 := by ring
    _ = 1 := by rw [hb]; ring

/--
@isnad1 id=eq.2h7v.s7.b589e194b117 from=translated src=- shape=09a8d77a vocab=7bb0ab33
-/
theorem solve_h (h c a b r q : B) (hc : c*a = h*b) (hb : r*h+q*c = 1) :
    h*(r*a+q*b) = a := by
  calc
    _ = r*h*a+q*(h*b) := by ring
    _ = (r*h+q*c)*a := by rw [← hc]; ring
    _ = a := by rw [hb, one_mul]

/--
@isnad1 id=eq.2h7v.s7.c2b6edec6bf1 from=translated src=- shape=8c25e276 vocab=7bb0ab33
-/
theorem solve_c (h c a b r q : B) (hc : c*a = h*b) (hb : r*h+q*c = 1) :
    c*(r*a+q*b) = b := by
  calc
    _ = r*(c*a)+q*c*b := by ring
    _ = (r*h+q*c)*b := by rw [hc]; ring
    _ = b := by rw [hb, one_mul]

/--
@isnad1 id=eq.3h8v.s7.d45ac6328ff8 from=translated src=- shape=de9a3b19 vocab=7bb0ab33
-/
theorem solve_unique (h c a b r q W : B) (hb : r*h+q*c = 1)
    (hh : h*W = a) (hy : c*W = b) : W = r*a+q*b := by
  calc
    W = (r*h+q*c)*W := by rw [hb, one_mul]
    _ = r*(h*W)+q*(c*W) := by ring
    _ = r*a+q*b := by rw [hh, hy]

/--
@isnad1 id=eq.1h7v.s7.385cfd5bf085 from=translated src=- shape=ca33f8c9 vocab=26b25aee
-/
theorem linear_parameter_relation (h x y α β T : B) (hb : α*h+β*y = 1) :
    h*(y*T+α*x)-y*(h*T-β*x) = x := by
  calc
    _ = (α*h+β*y)*x := by ring
    _ = x := by rw [hb, one_mul]

/--
@isnad1 id=eq.1h7v.s7.37e1a9ada879 from=translated src=- shape=22436791 vocab=26b25aee
-/
theorem linear_parameter_inverse (h x y α β T : B) (hb : α*h+β*y = 1) :
    α*(h*T-β*x)+β*(y*T+α*x) = T := by
  calc
    _ = (α*h+β*y)*T := by ring
    _ = T := by rw [hb, one_mul]

/--
@isnad1 id=eq.2h8v.s7.58f711d1631c from=translated src=- shape=15b8c487 vocab=26b25aee
-/
theorem recover_U (h x y α β U G : B)
    (hb : α*h+β*y = 1) (hl : h*G-y*U = x) :
    h*(α*U+β*G)-β*x = U := by
  calc
    _ = (α*h+β*y)*U+β*(h*G-y*U-x) := by ring
    _ = U := by rw [hb, hl]; ring

/--
@isnad1 id=eq.2h8v.s7.27f266ecc703 from=translated src=- shape=51d1876f vocab=26b25aee
-/
theorem recover_G (h x y α β U G : B)
    (hb : α*h+β*y = 1) (hl : h*G-y*U = x) :
    y*(α*U+β*G)+α*x = G := by
  calc
    _ = (α*h+β*y)*G-α*(h*G-y*U-x) := by ring
    _ = G := by rw [hb, hl]; ring

/--
@isnad1 id=and.3h8v.s9.551f20a3bd2b from=translated src=- shape=c9e60add vocab=6a703304
-/
theorem original_to_linear (h x y s U V W : B)
    (hx : U^3+h*V = x) (hy : -U^2+h*W = y) (hs : S h U V W = s) :
    h*(V+U*W)-y*U = x ∧ h*W = y+U^2 ∧
      y^2*W = s-h*(V+U*W)^2+2*U*y*(V+U*W) := by
  have hw : h*W-U^2 = y := by rw [← hy]; ring
  have hS : S h U V W =
      h*(V+U*W)^2-2*U*y*(V+U*W)+y^2*W := by
    have hh := substitute_S h U (V+U*W) W
    have hv : V+U*W-U*W = V := by ring
    rw [hv, hw] at hh
    exact hh
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = U^3+h*V+U*(h*W-U^2-y) := by ring
      _ = x := by rw [hw, hx]; ring
  · rw [← hw]; ring
  · rw [← hs, hS]; ring

/--
@isnad1 id=and.3h8v.s9.a40762de1cf9 from=translated src=- shape=83f7e984 vocab=6a703304
-/
theorem linear_to_original (h x y s U G W : B)
    (hl : h*G-y*U = x) (hw : h*W = y+U^2)
    (hs : y^2*W = s-h*G^2+2*U*y*G) :
    U^3+h*(G-U*W) = x ∧ -U^2+h*W = y ∧ S h U (G-U*W) W = s := by
  have hh : h*W-U^2 = y := by rw [hw]; ring
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = h*G-y*U-U*(h*W-U^2-y) := by ring
      _ = x := by rw [hl, hh]; ring
  · rw [hw]; ring
  · rw [substitute_S, hh, hs]; ring

end
end AbhyankarSathaye

end OAI
