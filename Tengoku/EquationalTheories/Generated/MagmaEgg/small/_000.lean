-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._000: verified translations of equational_theories/Generated/MagmaEgg/small/_000.lean (11 theorems)
import Tengoku.EquationalTheories.Deps.Magma
import Tengoku.EquationalTheories.Deps

set_option linter.all false

namespace EquationalTheories

private def congr_op {G: Type _} [Magma G] {a b c d: G} (h1: a = b) (h2: c = d): a ◇ c = b ◇ d := by
  rw [h1, h2]
private abbrev T := @Eq.trans
private abbrev S := @Eq.symm
private abbrev R := @Eq.refl
private abbrev M := @Magma.op
private abbrev C := @congr_op

theorem Equation3715_implies_Equation4470 (G: Type _) [Magma G] (h: Equation3715 G) : Equation4470 G
:= fun x y =>
  T (T (h x (M y y)) (C (h x x) (S (h y y)))) (S (h (M x x) y))

theorem Equation692_implies_Equation1358 (G: Type _) [Magma G] (h: Equation692 G) : Equation1358 G
:= fun x y z =>
  let v0 := M (M z x) z
  T (h x y v0) (C (R y) (S (h (M v0 y) x z)))

theorem Equation1855_implies_Equation4318 (G: Type _) [Magma G] (h: Equation1855 G) : Equation4318 G
:= fun x y z =>
  let v0 := M x (M y x)
  T (h v0 v0 z) (C (S (h x y v0)) (R (M z z)))

theorem Equation3266_implies_Equation310 (G: Type _) [Magma G] (h: Equation3266 G) : Equation310 G
:= fun x y =>
  let v0 := M y y
  T (h x y v0) (C (R x) (S (h y v0 y)))

theorem Equation4096_implies_Equation367 (G: Type _) [Magma G] (h: Equation4096 G) : Equation367 G
:= fun x y =>
  let v0 := M y y
  T (h x v0 y) (C (S (h y y v0)) (R x))

theorem Equation2550_implies_Equation28 (G: Type _) [Magma G] (h: Equation2550 G) : Equation28 G
:= fun x y =>
  T (h x y (M (M y x) x)) (C (C (R y) (S (h x y x))) (R x))

theorem Equation1452_implies_Equation209 (G: Type _) [Magma G] (h: Equation1452 G) : Equation209 G
:= fun x y =>
  let v0 := M y x
  T (h x v0) (C (R (M x v0)) (S (h y x)))

theorem Equation1481_implies_Equation3955 (G: Type _) [Magma G] (h: Equation1481 G) : Equation3955 G
:= fun x y =>
  let v0 := M x y
  T (h v0 y) (C (R (M y v0)) (S (h y x)))

theorem Equation1630_implies_Equation23 (G: Type _) [Magma G] (h: Equation1630 G) : Equation23 G
:= fun x =>
  let v0 := M x x
  T (h x (M v0 x)) (C (R v0) (S (h x x)))

theorem Equation1884_implies_Equation8 (G: Type _) [Magma G] (h: Equation1884 G) : Equation8 G
:= fun x =>
  let v0 := M x x
  T (h x (M x v0)) (C (S (h x x)) (R v0))

theorem Equation2051_implies_Equation3511 (G: Type _) [Magma G] (h: Equation2051 G) : Equation3511 G
:= fun x y =>
  let v0 := M x y
  T (h v0 x) (C (S (h x y)) (R (M v0 x)))

end EquationalTheories
