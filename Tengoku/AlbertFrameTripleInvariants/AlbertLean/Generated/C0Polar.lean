import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Challenge
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

open AlbertLean

def δ (i j : Fin 27) : ℚ := basisVec i j

/-- Explicit trilinear polarization of the 45 imported C0 norm monomials.-/
def polarForm (x y z : Coord) : ℚ :=
    q (1) 1 * (v x 0 * v y 1 * v z 2 + v x 0 * v y 2 * v z 1 + v x 1 * v y 0 * v z 2 + v x 1 * v y 2 * v z 0 + v x 2 * v y 0 * v z 1 + v x 2 * v y 1 * v z 0) +
    q (-1) 1 * (v x 0 * v y 3 * v z 4 + v x 0 * v y 4 * v z 3 + v x 3 * v y 0 * v z 4 + v x 3 * v y 4 * v z 0 + v x 4 * v y 0 * v z 3 + v x 4 * v y 3 * v z 0) +
    q (-1) 1 * (v x 0 * v y 5 * v z 10 + v x 0 * v y 10 * v z 5 + v x 5 * v y 0 * v z 10 + v x 5 * v y 10 * v z 0 + v x 10 * v y 0 * v z 5 + v x 10 * v y 5 * v z 0) +
    q (1) 1 * (v x 0 * v y 6 * v z 9 + v x 0 * v y 9 * v z 6 + v x 6 * v y 0 * v z 9 + v x 6 * v y 9 * v z 0 + v x 9 * v y 0 * v z 6 + v x 9 * v y 6 * v z 0) +
    q (-1) 1 * (v x 0 * v y 7 * v z 8 + v x 0 * v y 8 * v z 7 + v x 7 * v y 0 * v z 8 + v x 7 * v y 8 * v z 0 + v x 8 * v y 0 * v z 7 + v x 8 * v y 7 * v z 0) +
    q (-1) 1 * (v x 1 * v y 11 * v z 15 + v x 1 * v y 15 * v z 11 + v x 11 * v y 1 * v z 15 + v x 11 * v y 15 * v z 1 + v x 15 * v y 1 * v z 11 + v x 15 * v y 11 * v z 1) +
    q (-1) 1 * (v x 1 * v y 12 * v z 16 + v x 1 * v y 16 * v z 12 + v x 12 * v y 1 * v z 16 + v x 12 * v y 16 * v z 1 + v x 16 * v y 1 * v z 12 + v x 16 * v y 12 * v z 1) +
    q (-1) 1 * (v x 1 * v y 13 * v z 17 + v x 1 * v y 17 * v z 13 + v x 13 * v y 1 * v z 17 + v x 13 * v y 17 * v z 1 + v x 17 * v y 1 * v z 13 + v x 17 * v y 13 * v z 1) +
    q (-1) 1 * (v x 1 * v y 14 * v z 18 + v x 1 * v y 18 * v z 14 + v x 14 * v y 1 * v z 18 + v x 14 * v y 18 * v z 1 + v x 18 * v y 1 * v z 14 + v x 18 * v y 14 * v z 1) +
    q (-1) 1 * (v x 2 * v y 19 * v z 23 + v x 2 * v y 23 * v z 19 + v x 19 * v y 2 * v z 23 + v x 19 * v y 23 * v z 2 + v x 23 * v y 2 * v z 19 + v x 23 * v y 19 * v z 2) +
    q (-1) 1 * (v x 2 * v y 20 * v z 24 + v x 2 * v y 24 * v z 20 + v x 20 * v y 2 * v z 24 + v x 20 * v y 24 * v z 2 + v x 24 * v y 2 * v z 20 + v x 24 * v y 20 * v z 2) +
    q (-1) 1 * (v x 2 * v y 21 * v z 25 + v x 2 * v y 25 * v z 21 + v x 21 * v y 2 * v z 25 + v x 21 * v y 25 * v z 2 + v x 25 * v y 2 * v z 21 + v x 25 * v y 21 * v z 2) +
    q (-1) 1 * (v x 2 * v y 22 * v z 26 + v x 2 * v y 26 * v z 22 + v x 22 * v y 2 * v z 26 + v x 22 * v y 26 * v z 2 + v x 26 * v y 2 * v z 22 + v x 26 * v y 22 * v z 2) +
    q (1) 1 * (v x 3 * v y 15 * v z 19 + v x 3 * v y 19 * v z 15 + v x 15 * v y 3 * v z 19 + v x 15 * v y 19 * v z 3 + v x 19 * v y 3 * v z 15 + v x 19 * v y 15 * v z 3) +
    q (1) 1 * (v x 3 * v y 16 * v z 20 + v x 3 * v y 20 * v z 16 + v x 16 * v y 3 * v z 20 + v x 16 * v y 20 * v z 3 + v x 20 * v y 3 * v z 16 + v x 20 * v y 16 * v z 3) +
    q (1) 1 * (v x 3 * v y 17 * v z 21 + v x 3 * v y 21 * v z 17 + v x 17 * v y 3 * v z 21 + v x 17 * v y 21 * v z 3 + v x 21 * v y 3 * v z 17 + v x 21 * v y 17 * v z 3) +
    q (1) 1 * (v x 3 * v y 18 * v z 22 + v x 3 * v y 22 * v z 18 + v x 18 * v y 3 * v z 22 + v x 18 * v y 22 * v z 3 + v x 22 * v y 3 * v z 18 + v x 22 * v y 18 * v z 3) +
    q (1) 1 * (v x 4 * v y 11 * v z 23 + v x 4 * v y 23 * v z 11 + v x 11 * v y 4 * v z 23 + v x 11 * v y 23 * v z 4 + v x 23 * v y 4 * v z 11 + v x 23 * v y 11 * v z 4) +
    q (1) 1 * (v x 4 * v y 12 * v z 24 + v x 4 * v y 24 * v z 12 + v x 12 * v y 4 * v z 24 + v x 12 * v y 24 * v z 4 + v x 24 * v y 4 * v z 12 + v x 24 * v y 12 * v z 4) +
    q (1) 1 * (v x 4 * v y 13 * v z 25 + v x 4 * v y 25 * v z 13 + v x 13 * v y 4 * v z 25 + v x 13 * v y 25 * v z 4 + v x 25 * v y 4 * v z 13 + v x 25 * v y 13 * v z 4) +
    q (1) 1 * (v x 4 * v y 14 * v z 26 + v x 4 * v y 26 * v z 14 + v x 14 * v y 4 * v z 26 + v x 14 * v y 26 * v z 4 + v x 26 * v y 4 * v z 14 + v x 26 * v y 14 * v z 4) +
    q (1) 1 * (v x 5 * v y 13 * v z 22 + v x 5 * v y 22 * v z 13 + v x 13 * v y 5 * v z 22 + v x 13 * v y 22 * v z 5 + v x 22 * v y 5 * v z 13 + v x 22 * v y 13 * v z 5) +
    q (-1) 1 * (v x 5 * v y 14 * v z 21 + v x 5 * v y 21 * v z 14 + v x 14 * v y 5 * v z 21 + v x 14 * v y 21 * v z 5 + v x 21 * v y 5 * v z 14 + v x 21 * v y 14 * v z 5) +
    q (1) 1 * (v x 5 * v y 15 * v z 24 + v x 5 * v y 24 * v z 15 + v x 15 * v y 5 * v z 24 + v x 15 * v y 24 * v z 5 + v x 24 * v y 5 * v z 15 + v x 24 * v y 15 * v z 5) +
    q (-1) 1 * (v x 5 * v y 16 * v z 23 + v x 5 * v y 23 * v z 16 + v x 16 * v y 5 * v z 23 + v x 16 * v y 23 * v z 5 + v x 23 * v y 5 * v z 16 + v x 23 * v y 16 * v z 5) +
    q (-1) 1 * (v x 6 * v y 12 * v z 22 + v x 6 * v y 22 * v z 12 + v x 12 * v y 6 * v z 22 + v x 12 * v y 22 * v z 6 + v x 22 * v y 6 * v z 12 + v x 22 * v y 12 * v z 6) +
    q (1) 1 * (v x 6 * v y 14 * v z 20 + v x 6 * v y 20 * v z 14 + v x 14 * v y 6 * v z 20 + v x 14 * v y 20 * v z 6 + v x 20 * v y 6 * v z 14 + v x 20 * v y 14 * v z 6) +
    q (1) 1 * (v x 6 * v y 15 * v z 25 + v x 6 * v y 25 * v z 15 + v x 15 * v y 6 * v z 25 + v x 15 * v y 25 * v z 6 + v x 25 * v y 6 * v z 15 + v x 25 * v y 15 * v z 6) +
    q (-1) 1 * (v x 6 * v y 17 * v z 23 + v x 6 * v y 23 * v z 17 + v x 17 * v y 6 * v z 23 + v x 17 * v y 23 * v z 6 + v x 23 * v y 6 * v z 17 + v x 23 * v y 17 * v z 6) +
    q (1) 1 * (v x 7 * v y 12 * v z 21 + v x 7 * v y 21 * v z 12 + v x 12 * v y 7 * v z 21 + v x 12 * v y 21 * v z 7 + v x 21 * v y 7 * v z 12 + v x 21 * v y 12 * v z 7) +
    q (-1) 1 * (v x 7 * v y 13 * v z 20 + v x 7 * v y 20 * v z 13 + v x 13 * v y 7 * v z 20 + v x 13 * v y 20 * v z 7 + v x 20 * v y 7 * v z 13 + v x 20 * v y 13 * v z 7) +
    q (1) 1 * (v x 7 * v y 15 * v z 26 + v x 7 * v y 26 * v z 15 + v x 15 * v y 7 * v z 26 + v x 15 * v y 26 * v z 7 + v x 26 * v y 7 * v z 15 + v x 26 * v y 15 * v z 7) +
    q (-1) 1 * (v x 7 * v y 18 * v z 23 + v x 7 * v y 23 * v z 18 + v x 18 * v y 7 * v z 23 + v x 18 * v y 23 * v z 7 + v x 23 * v y 7 * v z 18 + v x 23 * v y 18 * v z 7) +
    q (1) 1 * (v x 8 * v y 11 * v z 22 + v x 8 * v y 22 * v z 11 + v x 11 * v y 8 * v z 22 + v x 11 * v y 22 * v z 8 + v x 22 * v y 8 * v z 11 + v x 22 * v y 11 * v z 8) +
    q (-1) 1 * (v x 8 * v y 14 * v z 19 + v x 8 * v y 19 * v z 14 + v x 14 * v y 8 * v z 19 + v x 14 * v y 19 * v z 8 + v x 19 * v y 8 * v z 14 + v x 19 * v y 14 * v z 8) +
    q (1) 1 * (v x 8 * v y 16 * v z 25 + v x 8 * v y 25 * v z 16 + v x 16 * v y 8 * v z 25 + v x 16 * v y 25 * v z 8 + v x 25 * v y 8 * v z 16 + v x 25 * v y 16 * v z 8) +
    q (-1) 1 * (v x 8 * v y 17 * v z 24 + v x 8 * v y 24 * v z 17 + v x 17 * v y 8 * v z 24 + v x 17 * v y 24 * v z 8 + v x 24 * v y 8 * v z 17 + v x 24 * v y 17 * v z 8) +
    q (-1) 1 * (v x 9 * v y 11 * v z 21 + v x 9 * v y 21 * v z 11 + v x 11 * v y 9 * v z 21 + v x 11 * v y 21 * v z 9 + v x 21 * v y 9 * v z 11 + v x 21 * v y 11 * v z 9) +
    q (1) 1 * (v x 9 * v y 13 * v z 19 + v x 9 * v y 19 * v z 13 + v x 13 * v y 9 * v z 19 + v x 13 * v y 19 * v z 9 + v x 19 * v y 9 * v z 13 + v x 19 * v y 13 * v z 9) +
    q (1) 1 * (v x 9 * v y 16 * v z 26 + v x 9 * v y 26 * v z 16 + v x 16 * v y 9 * v z 26 + v x 16 * v y 26 * v z 9 + v x 26 * v y 9 * v z 16 + v x 26 * v y 16 * v z 9) +
    q (-1) 1 * (v x 9 * v y 18 * v z 24 + v x 9 * v y 24 * v z 18 + v x 18 * v y 9 * v z 24 + v x 18 * v y 24 * v z 9 + v x 24 * v y 9 * v z 18 + v x 24 * v y 18 * v z 9) +
    q (1) 1 * (v x 10 * v y 11 * v z 20 + v x 10 * v y 20 * v z 11 + v x 11 * v y 10 * v z 20 + v x 11 * v y 20 * v z 10 + v x 20 * v y 10 * v z 11 + v x 20 * v y 11 * v z 10) +
    q (-1) 1 * (v x 10 * v y 12 * v z 19 + v x 10 * v y 19 * v z 12 + v x 12 * v y 10 * v z 19 + v x 12 * v y 19 * v z 10 + v x 19 * v y 10 * v z 12 + v x 19 * v y 12 * v z 10) +
    q (1) 1 * (v x 10 * v y 17 * v z 26 + v x 10 * v y 26 * v z 17 + v x 17 * v y 10 * v z 26 + v x 17 * v y 26 * v z 10 + v x 26 * v y 10 * v z 17 + v x 26 * v y 17 * v z 10) +
    q (-1) 1 * (v x 10 * v y 18 * v z 25 + v x 10 * v y 25 * v z 18 + v x 18 * v y 10 * v z 25 + v x 18 * v y 25 * v z 10 + v x 25 * v y 10 * v z 18 + v x 25 * v y 18 * v z 10)

/-- Ordered coefficient of the full cubic polarization, derived from the 45 C0 norm monomials.-/
def polarCoeff (a b c : Fin 27) : ℚ :=
    q (1) 1 * (δ a 0 * δ b 1 * δ c 2 + δ a 0 * δ b 2 * δ c 1 + δ a 1 * δ b 0 * δ c 2 + δ a 1 * δ b 2 * δ c 0 + δ a 2 * δ b 0 * δ c 1 + δ a 2 * δ b 1 * δ c 0) +
    q (-1) 1 * (δ a 0 * δ b 3 * δ c 4 + δ a 0 * δ b 4 * δ c 3 + δ a 3 * δ b 0 * δ c 4 + δ a 3 * δ b 4 * δ c 0 + δ a 4 * δ b 0 * δ c 3 + δ a 4 * δ b 3 * δ c 0) +
    q (-1) 1 * (δ a 0 * δ b 5 * δ c 10 + δ a 0 * δ b 10 * δ c 5 + δ a 5 * δ b 0 * δ c 10 + δ a 5 * δ b 10 * δ c 0 + δ a 10 * δ b 0 * δ c 5 + δ a 10 * δ b 5 * δ c 0) +
    q (1) 1 * (δ a 0 * δ b 6 * δ c 9 + δ a 0 * δ b 9 * δ c 6 + δ a 6 * δ b 0 * δ c 9 + δ a 6 * δ b 9 * δ c 0 + δ a 9 * δ b 0 * δ c 6 + δ a 9 * δ b 6 * δ c 0) +
    q (-1) 1 * (δ a 0 * δ b 7 * δ c 8 + δ a 0 * δ b 8 * δ c 7 + δ a 7 * δ b 0 * δ c 8 + δ a 7 * δ b 8 * δ c 0 + δ a 8 * δ b 0 * δ c 7 + δ a 8 * δ b 7 * δ c 0) +
    q (-1) 1 * (δ a 1 * δ b 11 * δ c 15 + δ a 1 * δ b 15 * δ c 11 + δ a 11 * δ b 1 * δ c 15 + δ a 11 * δ b 15 * δ c 1 + δ a 15 * δ b 1 * δ c 11 + δ a 15 * δ b 11 * δ c 1) +
    q (-1) 1 * (δ a 1 * δ b 12 * δ c 16 + δ a 1 * δ b 16 * δ c 12 + δ a 12 * δ b 1 * δ c 16 + δ a 12 * δ b 16 * δ c 1 + δ a 16 * δ b 1 * δ c 12 + δ a 16 * δ b 12 * δ c 1) +
    q (-1) 1 * (δ a 1 * δ b 13 * δ c 17 + δ a 1 * δ b 17 * δ c 13 + δ a 13 * δ b 1 * δ c 17 + δ a 13 * δ b 17 * δ c 1 + δ a 17 * δ b 1 * δ c 13 + δ a 17 * δ b 13 * δ c 1) +
    q (-1) 1 * (δ a 1 * δ b 14 * δ c 18 + δ a 1 * δ b 18 * δ c 14 + δ a 14 * δ b 1 * δ c 18 + δ a 14 * δ b 18 * δ c 1 + δ a 18 * δ b 1 * δ c 14 + δ a 18 * δ b 14 * δ c 1) +
    q (-1) 1 * (δ a 2 * δ b 19 * δ c 23 + δ a 2 * δ b 23 * δ c 19 + δ a 19 * δ b 2 * δ c 23 + δ a 19 * δ b 23 * δ c 2 + δ a 23 * δ b 2 * δ c 19 + δ a 23 * δ b 19 * δ c 2) +
    q (-1) 1 * (δ a 2 * δ b 20 * δ c 24 + δ a 2 * δ b 24 * δ c 20 + δ a 20 * δ b 2 * δ c 24 + δ a 20 * δ b 24 * δ c 2 + δ a 24 * δ b 2 * δ c 20 + δ a 24 * δ b 20 * δ c 2) +
    q (-1) 1 * (δ a 2 * δ b 21 * δ c 25 + δ a 2 * δ b 25 * δ c 21 + δ a 21 * δ b 2 * δ c 25 + δ a 21 * δ b 25 * δ c 2 + δ a 25 * δ b 2 * δ c 21 + δ a 25 * δ b 21 * δ c 2) +
    q (-1) 1 * (δ a 2 * δ b 22 * δ c 26 + δ a 2 * δ b 26 * δ c 22 + δ a 22 * δ b 2 * δ c 26 + δ a 22 * δ b 26 * δ c 2 + δ a 26 * δ b 2 * δ c 22 + δ a 26 * δ b 22 * δ c 2) +
    q (1) 1 * (δ a 3 * δ b 15 * δ c 19 + δ a 3 * δ b 19 * δ c 15 + δ a 15 * δ b 3 * δ c 19 + δ a 15 * δ b 19 * δ c 3 + δ a 19 * δ b 3 * δ c 15 + δ a 19 * δ b 15 * δ c 3) +
    q (1) 1 * (δ a 3 * δ b 16 * δ c 20 + δ a 3 * δ b 20 * δ c 16 + δ a 16 * δ b 3 * δ c 20 + δ a 16 * δ b 20 * δ c 3 + δ a 20 * δ b 3 * δ c 16 + δ a 20 * δ b 16 * δ c 3) +
    q (1) 1 * (δ a 3 * δ b 17 * δ c 21 + δ a 3 * δ b 21 * δ c 17 + δ a 17 * δ b 3 * δ c 21 + δ a 17 * δ b 21 * δ c 3 + δ a 21 * δ b 3 * δ c 17 + δ a 21 * δ b 17 * δ c 3) +
    q (1) 1 * (δ a 3 * δ b 18 * δ c 22 + δ a 3 * δ b 22 * δ c 18 + δ a 18 * δ b 3 * δ c 22 + δ a 18 * δ b 22 * δ c 3 + δ a 22 * δ b 3 * δ c 18 + δ a 22 * δ b 18 * δ c 3) +
    q (1) 1 * (δ a 4 * δ b 11 * δ c 23 + δ a 4 * δ b 23 * δ c 11 + δ a 11 * δ b 4 * δ c 23 + δ a 11 * δ b 23 * δ c 4 + δ a 23 * δ b 4 * δ c 11 + δ a 23 * δ b 11 * δ c 4) +
    q (1) 1 * (δ a 4 * δ b 12 * δ c 24 + δ a 4 * δ b 24 * δ c 12 + δ a 12 * δ b 4 * δ c 24 + δ a 12 * δ b 24 * δ c 4 + δ a 24 * δ b 4 * δ c 12 + δ a 24 * δ b 12 * δ c 4) +
    q (1) 1 * (δ a 4 * δ b 13 * δ c 25 + δ a 4 * δ b 25 * δ c 13 + δ a 13 * δ b 4 * δ c 25 + δ a 13 * δ b 25 * δ c 4 + δ a 25 * δ b 4 * δ c 13 + δ a 25 * δ b 13 * δ c 4) +
    q (1) 1 * (δ a 4 * δ b 14 * δ c 26 + δ a 4 * δ b 26 * δ c 14 + δ a 14 * δ b 4 * δ c 26 + δ a 14 * δ b 26 * δ c 4 + δ a 26 * δ b 4 * δ c 14 + δ a 26 * δ b 14 * δ c 4) +
    q (1) 1 * (δ a 5 * δ b 13 * δ c 22 + δ a 5 * δ b 22 * δ c 13 + δ a 13 * δ b 5 * δ c 22 + δ a 13 * δ b 22 * δ c 5 + δ a 22 * δ b 5 * δ c 13 + δ a 22 * δ b 13 * δ c 5) +
    q (-1) 1 * (δ a 5 * δ b 14 * δ c 21 + δ a 5 * δ b 21 * δ c 14 + δ a 14 * δ b 5 * δ c 21 + δ a 14 * δ b 21 * δ c 5 + δ a 21 * δ b 5 * δ c 14 + δ a 21 * δ b 14 * δ c 5) +
    q (1) 1 * (δ a 5 * δ b 15 * δ c 24 + δ a 5 * δ b 24 * δ c 15 + δ a 15 * δ b 5 * δ c 24 + δ a 15 * δ b 24 * δ c 5 + δ a 24 * δ b 5 * δ c 15 + δ a 24 * δ b 15 * δ c 5) +
    q (-1) 1 * (δ a 5 * δ b 16 * δ c 23 + δ a 5 * δ b 23 * δ c 16 + δ a 16 * δ b 5 * δ c 23 + δ a 16 * δ b 23 * δ c 5 + δ a 23 * δ b 5 * δ c 16 + δ a 23 * δ b 16 * δ c 5) +
    q (-1) 1 * (δ a 6 * δ b 12 * δ c 22 + δ a 6 * δ b 22 * δ c 12 + δ a 12 * δ b 6 * δ c 22 + δ a 12 * δ b 22 * δ c 6 + δ a 22 * δ b 6 * δ c 12 + δ a 22 * δ b 12 * δ c 6) +
    q (1) 1 * (δ a 6 * δ b 14 * δ c 20 + δ a 6 * δ b 20 * δ c 14 + δ a 14 * δ b 6 * δ c 20 + δ a 14 * δ b 20 * δ c 6 + δ a 20 * δ b 6 * δ c 14 + δ a 20 * δ b 14 * δ c 6) +
    q (1) 1 * (δ a 6 * δ b 15 * δ c 25 + δ a 6 * δ b 25 * δ c 15 + δ a 15 * δ b 6 * δ c 25 + δ a 15 * δ b 25 * δ c 6 + δ a 25 * δ b 6 * δ c 15 + δ a 25 * δ b 15 * δ c 6) +
    q (-1) 1 * (δ a 6 * δ b 17 * δ c 23 + δ a 6 * δ b 23 * δ c 17 + δ a 17 * δ b 6 * δ c 23 + δ a 17 * δ b 23 * δ c 6 + δ a 23 * δ b 6 * δ c 17 + δ a 23 * δ b 17 * δ c 6) +
    q (1) 1 * (δ a 7 * δ b 12 * δ c 21 + δ a 7 * δ b 21 * δ c 12 + δ a 12 * δ b 7 * δ c 21 + δ a 12 * δ b 21 * δ c 7 + δ a 21 * δ b 7 * δ c 12 + δ a 21 * δ b 12 * δ c 7) +
    q (-1) 1 * (δ a 7 * δ b 13 * δ c 20 + δ a 7 * δ b 20 * δ c 13 + δ a 13 * δ b 7 * δ c 20 + δ a 13 * δ b 20 * δ c 7 + δ a 20 * δ b 7 * δ c 13 + δ a 20 * δ b 13 * δ c 7) +
    q (1) 1 * (δ a 7 * δ b 15 * δ c 26 + δ a 7 * δ b 26 * δ c 15 + δ a 15 * δ b 7 * δ c 26 + δ a 15 * δ b 26 * δ c 7 + δ a 26 * δ b 7 * δ c 15 + δ a 26 * δ b 15 * δ c 7) +
    q (-1) 1 * (δ a 7 * δ b 18 * δ c 23 + δ a 7 * δ b 23 * δ c 18 + δ a 18 * δ b 7 * δ c 23 + δ a 18 * δ b 23 * δ c 7 + δ a 23 * δ b 7 * δ c 18 + δ a 23 * δ b 18 * δ c 7) +
    q (1) 1 * (δ a 8 * δ b 11 * δ c 22 + δ a 8 * δ b 22 * δ c 11 + δ a 11 * δ b 8 * δ c 22 + δ a 11 * δ b 22 * δ c 8 + δ a 22 * δ b 8 * δ c 11 + δ a 22 * δ b 11 * δ c 8) +
    q (-1) 1 * (δ a 8 * δ b 14 * δ c 19 + δ a 8 * δ b 19 * δ c 14 + δ a 14 * δ b 8 * δ c 19 + δ a 14 * δ b 19 * δ c 8 + δ a 19 * δ b 8 * δ c 14 + δ a 19 * δ b 14 * δ c 8) +
    q (1) 1 * (δ a 8 * δ b 16 * δ c 25 + δ a 8 * δ b 25 * δ c 16 + δ a 16 * δ b 8 * δ c 25 + δ a 16 * δ b 25 * δ c 8 + δ a 25 * δ b 8 * δ c 16 + δ a 25 * δ b 16 * δ c 8) +
    q (-1) 1 * (δ a 8 * δ b 17 * δ c 24 + δ a 8 * δ b 24 * δ c 17 + δ a 17 * δ b 8 * δ c 24 + δ a 17 * δ b 24 * δ c 8 + δ a 24 * δ b 8 * δ c 17 + δ a 24 * δ b 17 * δ c 8) +
    q (-1) 1 * (δ a 9 * δ b 11 * δ c 21 + δ a 9 * δ b 21 * δ c 11 + δ a 11 * δ b 9 * δ c 21 + δ a 11 * δ b 21 * δ c 9 + δ a 21 * δ b 9 * δ c 11 + δ a 21 * δ b 11 * δ c 9) +
    q (1) 1 * (δ a 9 * δ b 13 * δ c 19 + δ a 9 * δ b 19 * δ c 13 + δ a 13 * δ b 9 * δ c 19 + δ a 13 * δ b 19 * δ c 9 + δ a 19 * δ b 9 * δ c 13 + δ a 19 * δ b 13 * δ c 9) +
    q (1) 1 * (δ a 9 * δ b 16 * δ c 26 + δ a 9 * δ b 26 * δ c 16 + δ a 16 * δ b 9 * δ c 26 + δ a 16 * δ b 26 * δ c 9 + δ a 26 * δ b 9 * δ c 16 + δ a 26 * δ b 16 * δ c 9) +
    q (-1) 1 * (δ a 9 * δ b 18 * δ c 24 + δ a 9 * δ b 24 * δ c 18 + δ a 18 * δ b 9 * δ c 24 + δ a 18 * δ b 24 * δ c 9 + δ a 24 * δ b 9 * δ c 18 + δ a 24 * δ b 18 * δ c 9) +
    q (1) 1 * (δ a 10 * δ b 11 * δ c 20 + δ a 10 * δ b 20 * δ c 11 + δ a 11 * δ b 10 * δ c 20 + δ a 11 * δ b 20 * δ c 10 + δ a 20 * δ b 10 * δ c 11 + δ a 20 * δ b 11 * δ c 10) +
    q (-1) 1 * (δ a 10 * δ b 12 * δ c 19 + δ a 10 * δ b 19 * δ c 12 + δ a 12 * δ b 10 * δ c 19 + δ a 12 * δ b 19 * δ c 10 + δ a 19 * δ b 10 * δ c 12 + δ a 19 * δ b 12 * δ c 10) +
    q (1) 1 * (δ a 10 * δ b 17 * δ c 26 + δ a 10 * δ b 26 * δ c 17 + δ a 17 * δ b 10 * δ c 26 + δ a 17 * δ b 26 * δ c 10 + δ a 26 * δ b 10 * δ c 17 + δ a 26 * δ b 17 * δ c 10) +
    q (-1) 1 * (δ a 10 * δ b 18 * δ c 25 + δ a 10 * δ b 25 * δ c 18 + δ a 18 * δ b 10 * δ c 25 + δ a 18 * δ b 25 * δ c 10 + δ a 25 * δ b 10 * δ c 18 + δ a 25 * δ b 18 * δ c 10)

/-- Coordinate trace, unit, spur, and Springer coefficients derived from polarization.-/
def traceCoeff (a : Fin 27) : ℚ := δ a 0 + δ a 1 + δ a 2
def oneCoeff (k : Fin 27) : ℚ := δ 0 k + δ 1 k + δ 2 k
def spurCoeff (a b : Fin 27) : ℚ :=
  polarCoeff 0 a b + polarCoeff 1 a b + polarCoeff 2 a b
def crossCoeff (a b k : Fin 27) : ℚ :=
  ∑ j : Fin 27, polarCoeff a b j * traceDualCoeff j k
def springerCoeff (a b k : Fin 27) : ℚ :=
  (2 : ℚ)⁻¹ * (crossCoeff a b k + traceCoeff a * δ b k +
    traceCoeff b * δ a k - spurCoeff a b * oneCoeff k)

/-- Sparse coordinate product form transcribed from all 339 C0 tensor entries.-/
def productForm (x y : Coord) : Coord := fun k =>
  match k.val with
  | 0 => q (1) 1 * v x 0 * v y 0 + q (1) 2 * v x 11 * v y 15 + q (1) 2 * v x 12 * v y 16 + q (1) 2 * v x 13 * v y 17 + q (1) 2 * v x 14 * v y 18 + q (1) 2 * v x 15 * v y 11 + q (1) 2 * v x 16 * v y 12 + q (1) 2 * v x 17 * v y 13 + q (1) 2 * v x 18 * v y 14 + q (1) 2 * v x 19 * v y 23 + q (1) 2 * v x 20 * v y 24 + q (1) 2 * v x 21 * v y 25 + q (1) 2 * v x 22 * v y 26 + q (1) 2 * v x 23 * v y 19 + q (1) 2 * v x 24 * v y 20 + q (1) 2 * v x 25 * v y 21 + q (1) 2 * v x 26 * v y 22
  | 1 => q (1) 1 * v x 1 * v y 1 + q (1) 2 * v x 3 * v y 4 + q (1) 2 * v x 4 * v y 3 + q (1) 2 * v x 5 * v y 10 + q (-1) 2 * v x 6 * v y 9 + q (1) 2 * v x 7 * v y 8 + q (1) 2 * v x 8 * v y 7 + q (-1) 2 * v x 9 * v y 6 + q (1) 2 * v x 10 * v y 5 + q (1) 2 * v x 19 * v y 23 + q (1) 2 * v x 20 * v y 24 + q (1) 2 * v x 21 * v y 25 + q (1) 2 * v x 22 * v y 26 + q (1) 2 * v x 23 * v y 19 + q (1) 2 * v x 24 * v y 20 + q (1) 2 * v x 25 * v y 21 + q (1) 2 * v x 26 * v y 22
  | 2 => q (1) 1 * v x 2 * v y 2 + q (1) 2 * v x 3 * v y 4 + q (1) 2 * v x 4 * v y 3 + q (1) 2 * v x 5 * v y 10 + q (-1) 2 * v x 6 * v y 9 + q (1) 2 * v x 7 * v y 8 + q (1) 2 * v x 8 * v y 7 + q (-1) 2 * v x 9 * v y 6 + q (1) 2 * v x 10 * v y 5 + q (1) 2 * v x 11 * v y 15 + q (1) 2 * v x 12 * v y 16 + q (1) 2 * v x 13 * v y 17 + q (1) 2 * v x 14 * v y 18 + q (1) 2 * v x 15 * v y 11 + q (1) 2 * v x 16 * v y 12 + q (1) 2 * v x 17 * v y 13 + q (1) 2 * v x 18 * v y 14
  | 3 => q (1) 2 * v x 1 * v y 3 + q (1) 2 * v x 2 * v y 3 + q (1) 2 * v x 3 * v y 1 + q (1) 2 * v x 3 * v y 2 + q (1) 2 * v x 11 * v y 23 + q (1) 2 * v x 12 * v y 24 + q (1) 2 * v x 13 * v y 25 + q (1) 2 * v x 14 * v y 26 + q (1) 2 * v x 23 * v y 11 + q (1) 2 * v x 24 * v y 12 + q (1) 2 * v x 25 * v y 13 + q (1) 2 * v x 26 * v y 14
  | 4 => q (1) 2 * v x 1 * v y 4 + q (1) 2 * v x 2 * v y 4 + q (1) 2 * v x 4 * v y 1 + q (1) 2 * v x 4 * v y 2 + q (1) 2 * v x 15 * v y 19 + q (1) 2 * v x 16 * v y 20 + q (1) 2 * v x 17 * v y 21 + q (1) 2 * v x 18 * v y 22 + q (1) 2 * v x 19 * v y 15 + q (1) 2 * v x 20 * v y 16 + q (1) 2 * v x 21 * v y 17 + q (1) 2 * v x 22 * v y 18
  | 5 => q (1) 2 * v x 1 * v y 5 + q (1) 2 * v x 2 * v y 5 + q (1) 2 * v x 5 * v y 1 + q (1) 2 * v x 5 * v y 2 + q (1) 2 * v x 11 * v y 20 + q (-1) 2 * v x 12 * v y 19 + q (1) 2 * v x 17 * v y 26 + q (-1) 2 * v x 18 * v y 25 + q (-1) 2 * v x 19 * v y 12 + q (1) 2 * v x 20 * v y 11 + q (-1) 2 * v x 25 * v y 18 + q (1) 2 * v x 26 * v y 17
  | 6 => q (1) 2 * v x 1 * v y 6 + q (1) 2 * v x 2 * v y 6 + q (1) 2 * v x 6 * v y 1 + q (1) 2 * v x 6 * v y 2 + q (1) 2 * v x 11 * v y 21 + q (-1) 2 * v x 13 * v y 19 + q (-1) 2 * v x 16 * v y 26 + q (1) 2 * v x 18 * v y 24 + q (-1) 2 * v x 19 * v y 13 + q (1) 2 * v x 21 * v y 11 + q (1) 2 * v x 24 * v y 18 + q (-1) 2 * v x 26 * v y 16
  | 7 => q (1) 2 * v x 1 * v y 7 + q (1) 2 * v x 2 * v y 7 + q (1) 2 * v x 7 * v y 1 + q (1) 2 * v x 7 * v y 2 + q (1) 2 * v x 11 * v y 22 + q (-1) 2 * v x 14 * v y 19 + q (1) 2 * v x 16 * v y 25 + q (-1) 2 * v x 17 * v y 24 + q (-1) 2 * v x 19 * v y 14 + q (1) 2 * v x 22 * v y 11 + q (-1) 2 * v x 24 * v y 17 + q (1) 2 * v x 25 * v y 16
  | 8 => q (1) 2 * v x 1 * v y 8 + q (1) 2 * v x 2 * v y 8 + q (1) 2 * v x 8 * v y 1 + q (1) 2 * v x 8 * v y 2 + q (1) 2 * v x 12 * v y 21 + q (-1) 2 * v x 13 * v y 20 + q (1) 2 * v x 15 * v y 26 + q (-1) 2 * v x 18 * v y 23 + q (-1) 2 * v x 20 * v y 13 + q (1) 2 * v x 21 * v y 12 + q (-1) 2 * v x 23 * v y 18 + q (1) 2 * v x 26 * v y 15
  | 9 => q (1) 2 * v x 1 * v y 9 + q (1) 2 * v x 2 * v y 9 + q (1) 2 * v x 9 * v y 1 + q (1) 2 * v x 9 * v y 2 + q (1) 2 * v x 12 * v y 22 + q (-1) 2 * v x 14 * v y 20 + q (-1) 2 * v x 15 * v y 25 + q (1) 2 * v x 17 * v y 23 + q (-1) 2 * v x 20 * v y 14 + q (1) 2 * v x 22 * v y 12 + q (1) 2 * v x 23 * v y 17 + q (-1) 2 * v x 25 * v y 15
  | 10 => q (1) 2 * v x 1 * v y 10 + q (1) 2 * v x 2 * v y 10 + q (1) 2 * v x 10 * v y 1 + q (1) 2 * v x 10 * v y 2 + q (1) 2 * v x 13 * v y 22 + q (-1) 2 * v x 14 * v y 21 + q (1) 2 * v x 15 * v y 24 + q (-1) 2 * v x 16 * v y 23 + q (-1) 2 * v x 21 * v y 14 + q (1) 2 * v x 22 * v y 13 + q (-1) 2 * v x 23 * v y 16 + q (1) 2 * v x 24 * v y 15
  | 11 => q (1) 2 * v x 0 * v y 11 + q (1) 2 * v x 2 * v y 11 + q (1) 2 * v x 3 * v y 19 + q (1) 2 * v x 5 * v y 24 + q (1) 2 * v x 6 * v y 25 + q (1) 2 * v x 7 * v y 26 + q (1) 2 * v x 11 * v y 0 + q (1) 2 * v x 11 * v y 2 + q (1) 2 * v x 19 * v y 3 + q (1) 2 * v x 24 * v y 5 + q (1) 2 * v x 25 * v y 6 + q (1) 2 * v x 26 * v y 7
  | 12 => q (1) 2 * v x 0 * v y 12 + q (1) 2 * v x 2 * v y 12 + q (1) 2 * v x 3 * v y 20 + q (-1) 2 * v x 5 * v y 23 + q (1) 2 * v x 8 * v y 25 + q (1) 2 * v x 9 * v y 26 + q (1) 2 * v x 12 * v y 0 + q (1) 2 * v x 12 * v y 2 + q (1) 2 * v x 20 * v y 3 + q (-1) 2 * v x 23 * v y 5 + q (1) 2 * v x 25 * v y 8 + q (1) 2 * v x 26 * v y 9
  | 13 => q (1) 2 * v x 0 * v y 13 + q (1) 2 * v x 2 * v y 13 + q (1) 2 * v x 3 * v y 21 + q (-1) 2 * v x 6 * v y 23 + q (-1) 2 * v x 8 * v y 24 + q (1) 2 * v x 10 * v y 26 + q (1) 2 * v x 13 * v y 0 + q (1) 2 * v x 13 * v y 2 + q (1) 2 * v x 21 * v y 3 + q (-1) 2 * v x 23 * v y 6 + q (-1) 2 * v x 24 * v y 8 + q (1) 2 * v x 26 * v y 10
  | 14 => q (1) 2 * v x 0 * v y 14 + q (1) 2 * v x 2 * v y 14 + q (1) 2 * v x 3 * v y 22 + q (-1) 2 * v x 7 * v y 23 + q (-1) 2 * v x 9 * v y 24 + q (-1) 2 * v x 10 * v y 25 + q (1) 2 * v x 14 * v y 0 + q (1) 2 * v x 14 * v y 2 + q (1) 2 * v x 22 * v y 3 + q (-1) 2 * v x 23 * v y 7 + q (-1) 2 * v x 24 * v y 9 + q (-1) 2 * v x 25 * v y 10
  | 15 => q (1) 2 * v x 0 * v y 15 + q (1) 2 * v x 2 * v y 15 + q (1) 2 * v x 4 * v y 23 + q (1) 2 * v x 8 * v y 22 + q (-1) 2 * v x 9 * v y 21 + q (1) 2 * v x 10 * v y 20 + q (1) 2 * v x 15 * v y 0 + q (1) 2 * v x 15 * v y 2 + q (1) 2 * v x 20 * v y 10 + q (-1) 2 * v x 21 * v y 9 + q (1) 2 * v x 22 * v y 8 + q (1) 2 * v x 23 * v y 4
  | 16 => q (1) 2 * v x 0 * v y 16 + q (1) 2 * v x 2 * v y 16 + q (1) 2 * v x 4 * v y 24 + q (-1) 2 * v x 6 * v y 22 + q (1) 2 * v x 7 * v y 21 + q (-1) 2 * v x 10 * v y 19 + q (1) 2 * v x 16 * v y 0 + q (1) 2 * v x 16 * v y 2 + q (-1) 2 * v x 19 * v y 10 + q (1) 2 * v x 21 * v y 7 + q (-1) 2 * v x 22 * v y 6 + q (1) 2 * v x 24 * v y 4
  | 17 => q (1) 2 * v x 0 * v y 17 + q (1) 2 * v x 2 * v y 17 + q (1) 2 * v x 4 * v y 25 + q (1) 2 * v x 5 * v y 22 + q (-1) 2 * v x 7 * v y 20 + q (1) 2 * v x 9 * v y 19 + q (1) 2 * v x 17 * v y 0 + q (1) 2 * v x 17 * v y 2 + q (1) 2 * v x 19 * v y 9 + q (-1) 2 * v x 20 * v y 7 + q (1) 2 * v x 22 * v y 5 + q (1) 2 * v x 25 * v y 4
  | 18 => q (1) 2 * v x 0 * v y 18 + q (1) 2 * v x 2 * v y 18 + q (1) 2 * v x 4 * v y 26 + q (-1) 2 * v x 5 * v y 21 + q (1) 2 * v x 6 * v y 20 + q (-1) 2 * v x 8 * v y 19 + q (1) 2 * v x 18 * v y 0 + q (1) 2 * v x 18 * v y 2 + q (-1) 2 * v x 19 * v y 8 + q (1) 2 * v x 20 * v y 6 + q (-1) 2 * v x 21 * v y 5 + q (1) 2 * v x 26 * v y 4
  | 19 => q (1) 2 * v x 0 * v y 19 + q (1) 2 * v x 1 * v y 19 + q (1) 2 * v x 4 * v y 11 + q (-1) 2 * v x 5 * v y 16 + q (-1) 2 * v x 6 * v y 17 + q (-1) 2 * v x 7 * v y 18 + q (1) 2 * v x 11 * v y 4 + q (-1) 2 * v x 16 * v y 5 + q (-1) 2 * v x 17 * v y 6 + q (-1) 2 * v x 18 * v y 7 + q (1) 2 * v x 19 * v y 0 + q (1) 2 * v x 19 * v y 1
  | 20 => q (1) 2 * v x 0 * v y 20 + q (1) 2 * v x 1 * v y 20 + q (1) 2 * v x 4 * v y 12 + q (1) 2 * v x 5 * v y 15 + q (-1) 2 * v x 8 * v y 17 + q (-1) 2 * v x 9 * v y 18 + q (1) 2 * v x 12 * v y 4 + q (1) 2 * v x 15 * v y 5 + q (-1) 2 * v x 17 * v y 8 + q (-1) 2 * v x 18 * v y 9 + q (1) 2 * v x 20 * v y 0 + q (1) 2 * v x 20 * v y 1
  | 21 => q (1) 2 * v x 0 * v y 21 + q (1) 2 * v x 1 * v y 21 + q (1) 2 * v x 4 * v y 13 + q (1) 2 * v x 6 * v y 15 + q (1) 2 * v x 8 * v y 16 + q (-1) 2 * v x 10 * v y 18 + q (1) 2 * v x 13 * v y 4 + q (1) 2 * v x 15 * v y 6 + q (1) 2 * v x 16 * v y 8 + q (-1) 2 * v x 18 * v y 10 + q (1) 2 * v x 21 * v y 0 + q (1) 2 * v x 21 * v y 1
  | 22 => q (1) 2 * v x 0 * v y 22 + q (1) 2 * v x 1 * v y 22 + q (1) 2 * v x 4 * v y 14 + q (1) 2 * v x 7 * v y 15 + q (1) 2 * v x 9 * v y 16 + q (1) 2 * v x 10 * v y 17 + q (1) 2 * v x 14 * v y 4 + q (1) 2 * v x 15 * v y 7 + q (1) 2 * v x 16 * v y 9 + q (1) 2 * v x 17 * v y 10 + q (1) 2 * v x 22 * v y 0 + q (1) 2 * v x 22 * v y 1
  | 23 => q (1) 2 * v x 0 * v y 23 + q (1) 2 * v x 1 * v y 23 + q (1) 2 * v x 3 * v y 15 + q (-1) 2 * v x 8 * v y 14 + q (1) 2 * v x 9 * v y 13 + q (-1) 2 * v x 10 * v y 12 + q (-1) 2 * v x 12 * v y 10 + q (1) 2 * v x 13 * v y 9 + q (-1) 2 * v x 14 * v y 8 + q (1) 2 * v x 15 * v y 3 + q (1) 2 * v x 23 * v y 0 + q (1) 2 * v x 23 * v y 1
  | 24 => q (1) 2 * v x 0 * v y 24 + q (1) 2 * v x 1 * v y 24 + q (1) 2 * v x 3 * v y 16 + q (1) 2 * v x 6 * v y 14 + q (-1) 2 * v x 7 * v y 13 + q (1) 2 * v x 10 * v y 11 + q (1) 2 * v x 11 * v y 10 + q (-1) 2 * v x 13 * v y 7 + q (1) 2 * v x 14 * v y 6 + q (1) 2 * v x 16 * v y 3 + q (1) 2 * v x 24 * v y 0 + q (1) 2 * v x 24 * v y 1
  | 25 => q (1) 2 * v x 0 * v y 25 + q (1) 2 * v x 1 * v y 25 + q (1) 2 * v x 3 * v y 17 + q (-1) 2 * v x 5 * v y 14 + q (1) 2 * v x 7 * v y 12 + q (-1) 2 * v x 9 * v y 11 + q (-1) 2 * v x 11 * v y 9 + q (1) 2 * v x 12 * v y 7 + q (-1) 2 * v x 14 * v y 5 + q (1) 2 * v x 17 * v y 3 + q (1) 2 * v x 25 * v y 0 + q (1) 2 * v x 25 * v y 1
  | 26 => q (1) 2 * v x 0 * v y 26 + q (1) 2 * v x 1 * v y 26 + q (1) 2 * v x 3 * v y 18 + q (1) 2 * v x 5 * v y 13 + q (-1) 2 * v x 6 * v y 12 + q (1) 2 * v x 8 * v y 11 + q (1) 2 * v x 11 * v y 8 + q (-1) 2 * v x 12 * v y 6 + q (1) 2 * v x 13 * v y 5 + q (1) 2 * v x 18 * v y 3 + q (1) 2 * v x 26 * v y 0 + q (1) 2 * v x 26 * v y 1
  | _ => 0

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h3v.s4.0dbd3d1fbeb1 from=translated src=- shape=ea9ef4de vocab=5a2c6cec
-/
theorem cubicPolar_eq_polarForm (x y z : Coord) :
    cubicPolar x y z = polarForm x y z := by
  simp [cubicPolar, cubicNorm, polarForm, v, q]
  ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.2e3ac4fda591 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_0 (x : Coord) :
    sharp x (0 : Fin 27) = cubicPolar x x (basisVec (0 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.d851a3f84573 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_1 (x : Coord) :
    sharp x (1 : Fin 27) = cubicPolar x x (basisVec (1 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.e98ef359aed3 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_2 (x : Coord) :
    sharp x (2 : Fin 27) = cubicPolar x x (basisVec (2 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.4e279459df53 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_3 (x : Coord) :
    sharp x (3 : Fin 27) = cubicPolar x x (basisVec (4 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.33e7863a4178 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_4 (x : Coord) :
    sharp x (4 : Fin 27) = cubicPolar x x (basisVec (3 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.36f36634c5be from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_5 (x : Coord) :
    sharp x (5 : Fin 27) = cubicPolar x x (basisVec (10 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.b6626a00ec09 from=translated src=- shape=90045ff2 vocab=0ce8344b
-/
theorem sharp_coord_6 (x : Coord) :
    sharp x (6 : Fin 27) = -(cubicPolar x x (basisVec (9 : Fin 27)) / 2) := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.ab9e92225f17 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_7 (x : Coord) :
    sharp x (7 : Fin 27) = cubicPolar x x (basisVec (8 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.259a2ad0e52a from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_8 (x : Coord) :
    sharp x (8 : Fin 27) = cubicPolar x x (basisVec (7 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.412b80cc414c from=translated src=- shape=90045ff2 vocab=0ce8344b
-/
theorem sharp_coord_9 (x : Coord) :
    sharp x (9 : Fin 27) = -(cubicPolar x x (basisVec (6 : Fin 27)) / 2) := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.0905b0bea781 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_10 (x : Coord) :
    sharp x (10 : Fin 27) = cubicPolar x x (basisVec (5 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.ca4a3872e8ff from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_11 (x : Coord) :
    sharp x (11 : Fin 27) = cubicPolar x x (basisVec (15 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.b480358913b4 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_12 (x : Coord) :
    sharp x (12 : Fin 27) = cubicPolar x x (basisVec (16 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.9129af93ef13 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_13 (x : Coord) :
    sharp x (13 : Fin 27) = cubicPolar x x (basisVec (17 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.b53dac8bfe43 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_14 (x : Coord) :
    sharp x (14 : Fin 27) = cubicPolar x x (basisVec (18 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.cfd6824f4116 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_15 (x : Coord) :
    sharp x (15 : Fin 27) = cubicPolar x x (basisVec (11 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.26868eb165c0 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_16 (x : Coord) :
    sharp x (16 : Fin 27) = cubicPolar x x (basisVec (12 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.509f3003c10a from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_17 (x : Coord) :
    sharp x (17 : Fin 27) = cubicPolar x x (basisVec (13 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.7f7c9ef163fb from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_18 (x : Coord) :
    sharp x (18 : Fin 27) = cubicPolar x x (basisVec (14 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.6ea426640d78 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_19 (x : Coord) :
    sharp x (19 : Fin 27) = cubicPolar x x (basisVec (23 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.311808ab9c38 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_20 (x : Coord) :
    sharp x (20 : Fin 27) = cubicPolar x x (basisVec (24 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.b6d9feff619e from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_21 (x : Coord) :
    sharp x (21 : Fin 27) = cubicPolar x x (basisVec (25 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.0a9155b0f972 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_22 (x : Coord) :
    sharp x (22 : Fin 27) = cubicPolar x x (basisVec (26 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.e5a6a11e1c6e from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_23 (x : Coord) :
    sharp x (23 : Fin 27) = cubicPolar x x (basisVec (19 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.c75c7ffd6709 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_24 (x : Coord) :
    sharp x (24 : Fin 27) = cubicPolar x x (basisVec (20 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.57801a8ba3ed from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_25 (x : Coord) :
    sharp x (25 : Fin 27) = cubicPolar x x (basisVec (21 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h1v.s5.68f17fb5d988 from=translated src=- shape=70e2961f vocab=4645f71c
-/
theorem sharp_coord_26 (x : Coord) :
    sharp x (26 : Fin 27) = cubicPolar x x (basisVec (22 : Fin 27)) / 2 := by
  simp [sharp, traceDualCoeff, traceDualCoeffNat, Fin.sum_univ_succ, q] <;> ring

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
/--
@isnad1 id=eq.0h2v.s3.8deaffe2ba2c from=translated src=- shape=6c8684e5 vocab=f2dcc738
-/
theorem structuredProduct_eq_productForm (x y : Coord) :
    structuredProduct x y = productForm x y := by
  funext k
  fin_cases k <;>
    simp [structuredProduct, cross, traceN, spurBilinear,
      cubicPolar_eq_polarForm, polarForm, productForm, one, basisVec, v, q,
      sharp_coord_0, sharp_coord_1, sharp_coord_2, sharp_coord_3, sharp_coord_4, sharp_coord_5, sharp_coord_6, sharp_coord_7, sharp_coord_8, sharp_coord_9, sharp_coord_10, sharp_coord_11, sharp_coord_12, sharp_coord_13, sharp_coord_14, sharp_coord_15, sharp_coord_16, sharp_coord_17, sharp_coord_18, sharp_coord_19, sharp_coord_20, sharp_coord_21, sharp_coord_22, sharp_coord_23, sharp_coord_24, sharp_coord_25, sharp_coord_26] <;> ring

end AlbertLean.Generated
