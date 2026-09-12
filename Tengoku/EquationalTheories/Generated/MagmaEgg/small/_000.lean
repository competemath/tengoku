-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._000: verified translations of equational_theories/Generated/MagmaEgg/small/_000.lean (23 theorems)
import Tengoku.EquationalTheories.Deps.Magma
import Tengoku.EquationalTheories.Deps.Equations

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

theorem Equation2100_implies_Equation117 (G: Type _) [Magma G] (h: Equation2100 G) : Equation117 G
:= fun x y =>
  let v0 := M x y
  T (h x v0) (C (S (h y x)) (R (M v0 x)))

theorem Equation3167_implies_Equation31 (G: Type _) [Magma G] (h: Equation3167 G) : Equation31 G
:= fun x y =>
  let v0 := M y y
  T (h x v0 v0) (C (S (h v0 y v0)) (R x))

theorem Equation3689_implies_Equation3693 (G: Type _) [Magma G] (h: Equation3689 G) : Equation3693 G
:= fun x y z w =>
  T (h x z w) (C (T (h z x x) (S (h y x x))) (R (M z w)))

theorem Equation3691_implies_Equation3693 (G: Type _) [Magma G] (h: Equation3691 G) : Equation3693 G
:= fun x y z w =>
  T (h x w z) (C (T (h w x x) (S (h y x x))) (R (M z w)))

theorem Equation3699_implies_Equation3709 (G: Type _) [Magma G] (h: Equation3699 G) : Equation3709 G
:= fun x y z w =>
  T (h x y z) (C (R (M y z)) (T (h y x x) (S (h w x x))))

theorem Equation3704_implies_Equation3709 (G: Type _) [Magma G] (h: Equation3704 G) : Equation3709 G
:= fun x y z w =>
  T (h x y z) (C (R (M y z)) (T (h z x x) (S (h w x x))))

theorem Equation1224_implies_Equation99 (G: Type _) [Magma G] (h: Equation1224 G) : Equation99 G
:= fun x =>
  let v0 := M (M x x) x
  T (h x (M (M (M v0 v0) v0) x)) (C (R x) (S (h v0 x)))

theorem Equation820_implies_Equation8 (G: Type _) [Magma G] (h: Equation820 G) : Equation8 G
:= fun x =>
  let v0 := M x x
  T (h x (M v0 v0)) (C (R x) (S (h v0 v0)))

theorem Equation2243_implies_Equation203 (G: Type _) [Magma G] (h: Equation2243 G) : Equation203 G
:= fun x =>
  have h0 := R x
  T (h x (M x (M x (M x x)))) (C (C h0 (C h0 (S (h x x)))) h0)

theorem Equation2592_implies_Equation3201 (G: Type _) [Magma G] (h: Equation2592 G) : Equation3201 G
:= fun x y z =>
  let v0 := M (M y z) y
  T (h x v0 z) (C (C (R v0) (S (h z z y))) (R x))

theorem Equation2733_implies_Equation23 (G: Type _) [Magma G] (h: Equation2733 G) : Equation23 G
:= fun x =>
  let v0 := M x x
  T (h x (M v0 v0)) (C (S (h v0 v0)) (R x))

theorem Equation3751_implies_Equation3722 (G: Type _) [Magma G] (h: Equation3751 G) : Equation3722 G
:= fun x y =>
  let v0 := M x y
  have h1 := h y x
  T (T (h x y) (C h1 h1)) (S (h v0 v0))

end EquationalTheories
