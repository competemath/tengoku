import Tengoku.AlbertFrameTripleInvariants.AlbertLean.SplitOctonion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The split Albert cubic on Hermitian `3 × 3` Zorn matrices

`Hermitian3.mk d1 d2 d3 x23 x31 x12` denotes
`[[d1,x12,conj x31],[conj x12,d2,x23],[x31,conj x23,d3]]`.
The cubic below is the conventional Hermitian determinant formula.  Its
triple-product term is written in a cyclic order chosen to match the frozen
C0 triality coordinates.
-/

namespace AlbertLean

-- PALOMAR_MODEL_STATEMENT_BEGIN

/-- A Hermitian `3 × 3` matrix over the split octonions.-/
structure Hermitian3 where
  diag1 : ℚ
  diag2 : ℚ
  diag3 : ℚ
  off23 : Zorn
  off31 : Zorn
  off12 : Zorn
  deriving DecidableEq

namespace Hermitian3

def one : Hermitian3 := ⟨1, 1, 1, Zorn.zero, Zorn.zero, Zorn.zero⟩

def add (x y : Hermitian3) : Hermitian3 :=
  ⟨x.diag1 + y.diag1, x.diag2 + y.diag2, x.diag3 + y.diag3,
   Zorn.add x.off23 y.off23, Zorn.add x.off31 y.off31,
   Zorn.add x.off12 y.off12⟩

def sub (x y : Hermitian3) : Hermitian3 :=
  ⟨x.diag1 - y.diag1, x.diag2 - y.diag2, x.diag3 - y.diag3,
   Zorn.sub x.off23 y.off23, Zorn.sub x.off31 y.off31,
   Zorn.sub x.off12 y.off12⟩

def smul (a : ℚ) (x : Hermitian3) : Hermitian3 :=
  ⟨a * x.diag1, a * x.diag2, a * x.diag3,
   Zorn.smul a x.off23, Zorn.smul a x.off31, Zorn.smul a x.off12⟩

/-- The square obtained by multiplying the represented Hermitian matrix by itself.-/
def square (x : Hermitian3) : Hermitian3 :=
  ⟨x.diag1 ^ 2 + Zorn.norm x.off31 + Zorn.norm x.off12,
   x.diag2 ^ 2 + Zorn.norm x.off12 + Zorn.norm x.off23,
   x.diag3 ^ 2 + Zorn.norm x.off23 + Zorn.norm x.off31,
   Zorn.add (Zorn.smul (x.diag2 + x.diag3) x.off23)
     (Zorn.conj (Zorn.mul x.off31 x.off12)),
   Zorn.add (Zorn.smul (x.diag3 + x.diag1) x.off31)
     (Zorn.conj (Zorn.mul x.off12 x.off23)),
   Zorn.add (Zorn.smul (x.diag1 + x.diag2) x.off12)
     (Zorn.conj (Zorn.mul x.off23 x.off31))⟩

/-- The symmetrized Hermitian matrix product, recovered by polarizing `square`.-/
def jordan (x y : Hermitian3) : Hermitian3 :=
  smul (2 : ℚ)⁻¹
    (sub (square (add x y)) (add (square x) (square y)))

/-- The scalar triple coupling `2 Re ((x31*x12)*x23)`.-/
def tripleCoupling (x : Hermitian3) : ℚ :=
  Zorn.scalarTrace (Zorn.mul (Zorn.mul x.off31 x.off12) x.off23)

/-- The conventional cubic norm (Hermitian determinant).-/
def cubicNorm (x : Hermitian3) : ℚ :=
  x.diag1 * x.diag2 * x.diag3 -
  x.diag1 * Zorn.norm x.off23 -
  x.diag2 * Zorn.norm x.off31 -
  x.diag3 * Zorn.norm x.off12 +
  tripleCoupling x

end Hermitian3

-- PALOMAR_MODEL_STATEMENT_END

namespace Hermitian3

theorem ext {x y : Hermitian3}
    (hd1 : x.diag1 = y.diag1)
    (hd2 : x.diag2 = y.diag2)
    (hd3 : x.diag3 = y.diag3)
    (h23 : x.off23 = y.off23)
    (h31 : x.off31 = y.off31)
    (h12 : x.off12 = y.off12) : x = y := by
  cases x
  cases y
  simp_all

end Hermitian3

end AlbertLean
