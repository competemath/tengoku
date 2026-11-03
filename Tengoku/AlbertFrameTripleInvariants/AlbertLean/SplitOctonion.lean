import Tengoku.Seed.Data.Rat.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Split octonions in the Zorn matrix model

This file fixes one explicit convention for the split octonions over `ℚ`.
An element `Zorn.mk a u v b` represents the vector matrix
`(a,u;v,b)`.  All signs are visible in `Zorn.mul` and `Zorn.norm`.  Relative
to Fields §3.8 after identifying the three-vector coordinates by
`(e1,e2,e3)`, this definition uses the opposite three-volume convention, so
both cross-product signs are reversed.  The later coordinate map is derived
with this orientation throughout.
-/

namespace AlbertLean

-- PALOMAR_MODEL_STATEMENT_BEGIN

/-- Three-dimensional rational column vectors used in the Zorn model.-/
structure Vec3 where
  x : ℚ
  y : ℚ
  z : ℚ
  deriving DecidableEq

namespace Vec3

def dot (u v : Vec3) : ℚ := u.x * v.x + u.y * v.y + u.z * v.z

def cross (u v : Vec3) : Vec3 :=
  ⟨u.y * v.z - u.z * v.y,
   u.z * v.x - u.x * v.z,
   u.x * v.y - u.y * v.x⟩

def neg (u : Vec3) : Vec3 := ⟨-u.x, -u.y, -u.z⟩

def add (u v : Vec3) : Vec3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

def sub (u v : Vec3) : Vec3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩

def smul (a : ℚ) (u : Vec3) : Vec3 := ⟨a * u.x, a * u.y, a * u.z⟩

end Vec3

/-- A Zorn vector matrix `(a,u;v,b)`, the standard split-octonion carrier.-/
structure Zorn where
  upperLeft : ℚ
  upperRight : Vec3
  lowerLeft : Vec3
  lowerRight : ℚ
  deriving DecidableEq

namespace Zorn

def zero : Zorn := ⟨0, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, 0⟩

def one : Zorn := ⟨1, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, 1⟩

def add (x y : Zorn) : Zorn :=
  ⟨x.upperLeft + y.upperLeft,
   Vec3.add x.upperRight y.upperRight,
   Vec3.add x.lowerLeft y.lowerLeft,
   x.lowerRight + y.lowerRight⟩

def sub (x y : Zorn) : Zorn :=
  ⟨x.upperLeft - y.upperLeft,
   Vec3.sub x.upperRight y.upperRight,
   Vec3.sub x.lowerLeft y.lowerLeft,
   x.lowerRight - y.lowerRight⟩

def smul (a : ℚ) (x : Zorn) : Zorn :=
  ⟨a * x.upperLeft, Vec3.smul a x.upperRight,
   Vec3.smul a x.lowerLeft, a * x.lowerRight⟩

def conj (x : Zorn) : Zorn :=
  ⟨x.lowerRight, Vec3.neg x.upperRight, Vec3.neg x.lowerLeft, x.upperLeft⟩

/-- The split quadratic norm `a*b - u·v`.-/
def norm (x : Zorn) : ℚ :=
  x.upperLeft * x.lowerRight - Vec3.dot x.upperRight x.lowerLeft

/-- The scalar trace, equal to twice the scalar (real) part.-/
def scalarTrace (x : Zorn) : ℚ := x.upperLeft + x.lowerRight

/-- Zorn multiplication.  The displayed signs fix the convention used later.-/
def mul (x y : Zorn) : Zorn :=
  ⟨x.upperLeft * y.upperLeft + Vec3.dot x.upperRight y.lowerLeft,
   ⟨x.upperLeft * y.upperRight.x + y.lowerRight * x.upperRight.x -
       (Vec3.cross x.lowerLeft y.lowerLeft).x,
    x.upperLeft * y.upperRight.y + y.lowerRight * x.upperRight.y -
       (Vec3.cross x.lowerLeft y.lowerLeft).y,
    x.upperLeft * y.upperRight.z + y.lowerRight * x.upperRight.z -
       (Vec3.cross x.lowerLeft y.lowerLeft).z⟩,
   ⟨y.upperLeft * x.lowerLeft.x + x.lowerRight * y.lowerLeft.x +
       (Vec3.cross x.upperRight y.upperRight).x,
    y.upperLeft * x.lowerLeft.y + x.lowerRight * y.lowerLeft.y +
       (Vec3.cross x.upperRight y.upperRight).y,
    y.upperLeft * x.lowerLeft.z + x.lowerRight * y.lowerLeft.z +
       (Vec3.cross x.upperRight y.upperRight).z⟩,
   Vec3.dot x.lowerLeft y.upperRight + x.lowerRight * y.lowerRight⟩

end Zorn

-- PALOMAR_MODEL_STATEMENT_END

namespace Vec3

/--
@isnad1 id=eq.3h2v.s4.daef97e601b0 from=translated src=- shape=966c8f3f vocab=ed8a39ca
-/
theorem ext {u v : Vec3}
    (hx : u.x = v.x) (hy : u.y = v.y) (hz : u.z = v.z) : u = v := by
  cases u
  cases v
  simp_all

end Vec3

namespace Zorn

/--
@isnad1 id=eq.4h2v.s5.0058ee887228 from=translated src=- shape=4e05324f vocab=6e155567
-/
theorem ext {x y : Zorn}
    (hul : x.upperLeft = y.upperLeft)
    (hur : x.upperRight = y.upperRight)
    (hll : x.lowerLeft = y.lowerLeft)
    (hlr : x.lowerRight = y.lowerRight) : x = y := by
  cases x
  cases y
  simp_all

end Zorn

end AlbertLean
