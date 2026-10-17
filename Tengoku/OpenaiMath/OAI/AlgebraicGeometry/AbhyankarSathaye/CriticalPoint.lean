import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.AbhyankarSathaye.Identities
import Tengoku

namespace OAI

/-!
# An explicit critical point away from the zero fiber

At `(h,u,v,w) = (2,0,-1/2,1/2)`, the value of `F` is `-1` and every
partial derivative vanishes. Differentiating the ambient polynomial identity
proves the latter without expanding `F`.
-/

noncomputable section
namespace AbhyankarSathaye
open MvPolynomial

def criticalPoint (i : Fin 4) : ℂ :=
  if i = 0 then 2 else if i = 1 then 0 else if i = 2 then -1/2 else 1/2

/--
@isnad1 id=eq.0h0v.s4.e6b3d7396266 from=translated src=- shape=012516b9 vocab=b87c1447
-/
@[simp] theorem criticalPoint_h : criticalPoint 0 = 2 := rfl
/--
@isnad1 id=eq.0h0v.s4.87bed545256a from=translated src=- shape=012516b9 vocab=b87c1447
-/
@[simp] theorem criticalPoint_u : criticalPoint 1 = 0 := rfl
/--
@isnad1 id=eq.0h0v.s5.9bd1e3b2471e from=translated src=- shape=c86bec04 vocab=32e2cde8
-/
@[simp] theorem criticalPoint_v : criticalPoint 2 = -1/2 := rfl
/--
@isnad1 id=eq.0h0v.s5.12b2570aa1e2 from=translated src=- shape=f0c008b7 vocab=36b86364
-/
@[simp] theorem criticalPoint_w : criticalPoint 3 = 1/2 := rfl

/--
@isnad1 id=eq.0h0v.s7.974c1bf03715 from=translated src=- shape=1c77612e vocab=f28d96df
-/
theorem eval_x : eval criticalPoint x = -1 := by
  norm_num [x, u, h, v]

/--
@isnad1 id=eq.0h0v.s6.e89f8ad8bf2f from=translated src=- shape=451fb593 vocab=a3a3c16e
-/
theorem eval_y : eval criticalPoint y = 1 := by
  norm_num [y, u, h, w]

/--
@isnad1 id=eq.0h0v.s6.55b5e58999bd from=translated src=- shape=451fb593 vocab=fe54be73
-/
theorem eval_s : eval criticalPoint s = 1 := by
  norm_num [s, S, u, h, v, w]

/--
@isnad1 id=eq.0h0v.s7.5ddc8a3be636 from=translated src=- shape=451fb593 vocab=dabd6977
-/
theorem eval_p : eval criticalPoint p = 2 := by
  norm_num [p, P, eval_x, eval_y, eval_s]

/--
@isnad1 id=eq.0h0v.s7.fd8aeb4b55c0 from=translated src=- shape=1c77612e vocab=4fe00101
-/
theorem eval_F : eval criticalPoint F = -1 := by
  norm_num [F, h, eval_p]

/--
@isnad1 id=eq.0h0v.s6.c79aa5d7f37c from=translated src=- shape=451fb593 vocab=d4731a46
-/
theorem eval_shiftX : eval criticalPoint shiftX = 0 := by
  norm_num [shiftX, eval_x, eval_s]

/--
@isnad1 id=eq.0h0v.s6.ab1d07d090e6 from=translated src=- shape=451fb593 vocab=f840c521
-/
theorem eval_shiftY : eval criticalPoint shiftY = 0 := by
  norm_num [shiftY, eval_y, eval_s]

/--
@isnad1 id=eq.5h8v.s10.cd8dd8a5c243 from=translated src=- shape=795ed5b7 vocab=366783c7
-/
theorem critical_of_ambient_identity {σ B : Type*} [CommRing B]
    (A D E f : MvPolynomial σ B) (point : σ → B)
    (hid : A^2 + D^3 = E*(1+f))
    (hA : eval point A = 0) (hD : eval point D = 0)
    (hE : eval point E = 1) (hf : eval point f = -1) (i : σ) :
    eval point (pderiv i f) = 0 := by
  have hd := congrArg (fun z => eval point (pderiv i z)) hid
  simpa [pderiv_pow, pderiv_mul, hA, hD, hE, hf] using hd.symm

/--
@isnad1 id=eq.0h1v.s9.9186941cb559 from=translated src=- shape=a6a7257c vocab=187ad897
-/
theorem critical_derivatives (i : Fin 4) : eval criticalPoint (pderiv i F) = 0 :=
  critical_of_ambient_identity shiftX shiftY s F criticalPoint ambient
    eval_shiftX eval_shiftY eval_s eval_F i

end AbhyankarSathaye

end

end OAI
