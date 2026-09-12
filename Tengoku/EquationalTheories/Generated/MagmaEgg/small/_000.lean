-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._000: verified translations of equational_theories/Generated/MagmaEgg/small/_000.lean (48 theorems)
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

theorem Equation1025_implies_Equation8 (G: Type _) [Magma G] (h: Equation1025 G) : Equation8 G
:= fun x =>
  have h0 := R x
  T (h x (M x (M x x))) (C h0 (C (S (h x x)) h0))

theorem Equation2679_implies_Equation260 (G: Type _) [Magma G] (h: Equation2679 G) : Equation260 G
:= fun x y =>
  let v0 := M x x
  T (h x y (M v0 v0)) (C (C (R (M x y)) (S (h x x x))) (R x))

theorem Equation3727_implies_Equation3726 (G: Type _) [Magma G] (h: Equation3727 G) : Equation3726 G
:= fun x y z =>
  have h0 := h x y x
  T (T h0 (h (M x y) (M x x) (M y z))) (C (S h0) (S (h y z x)))

theorem Equation1250_implies_Equation107 (G: Type _) [Magma G] (h: Equation1250 G) : Equation107 G
:= fun x y =>
  let v0 := M (M y y) x
  T (h x y (M (M (M x x) v0) x)) (C (R x) (S (h v0 x x)))

theorem Equation1458_implies_Equation215 (G: Type _) [Magma G] (h: Equation1458 G) : Equation215 G
:= fun x y z =>
  let v0 := M y z
  T (h x v0 z) (C (R (M x v0)) (S (h y z y)))

theorem Equation2161_implies_Equation166 (G: Type _) [Magma G] (h: Equation2161 G) : Equation166 G
:= fun x y =>
  T (h x (M (M y x) y) (M y y)) (C (C (S (h y y x)) (R x)) (R (M x x)))

theorem Equation2182_implies_Equation138 (G: Type _) [Magma G] (h: Equation2182 G) : Equation138 G
:= fun x y z =>
  let v0 := M z y
  T (h x v0 z) (C (S (h y z y)) (R (M v0 x)))

theorem Equation3282_implies_Equation3286 (G: Type _) [Magma G] (h: Equation3282 G) : Equation3286 G
:= fun x y z =>
  have h0 := R y
  T (h x y) (C h0 (C h0 (T (h y x) (S (h z x)))))

theorem Equation4196_implies_Equation39 (G: Type _) [Magma G] (h: Equation4196 G) : Equation39 G
:= fun x y =>
  let v0 := M x y
  T (T (h x x (M x v0)) (C (S (h v0 x x)) (R x))) (S (h y x x))

theorem Equation1230_implies_Equation101 (G: Type _) [Magma G] (h: Equation1230 G) : Equation101 G
:= fun x y =>
  let v0 := M (M x y) x
  T (h x y (M (M (M v0 x) v0) x)) (C (R x) (S (h v0 x x)))

theorem Equation1442_implies_Equation3511 (G: Type _) [Magma G] (h: Equation1442 G) : Equation3511 G
:= fun x y =>
  have h0 := S (h x y)
  let v1 := M x y
  T (h v1 (M x v1)) (C h0 (C (R v1) h0))

theorem Equation1867_implies_Equation156 (G: Type _) [Magma G] (h: Equation1867 G) : Equation156 G
:= fun x y =>
  T (h x (M y (M x y)) (M y y)) (C (C (R x) (S (h y x y))) (R (M x x)))

theorem Equation2090_implies_Equation3955 (G: Type _) [Magma G] (h: Equation2090 G) : Equation3955 G
:= fun x y =>
  have h0 := S (h y x)
  let v1 := M x y
  T (h v1 (M v1 y)) (C (C h0 (R v1)) h0)

theorem Equation2180_implies_Equation14 (G: Type _) [Magma G] (h: Equation2180 G) : Equation14 G
:= fun x y =>
  let v0 := M x y
  T (h x (M y v0) y) (C (S (h y y v0)) (R v0))

theorem Equation2476_implies_Equation208 (G: Type _) [Magma G] (h: Equation2476 G) : Equation208 G
:= fun x y =>
  have h0 := R x
  T (h x (M y (M (M x x) y)) y) (C (C h0 (C (S (h y x x)) h0)) h0)

theorem Equation2503_implies_Equation3050 (G: Type _) [Magma G] (h: Equation2503 G) : Equation3050 G
:= fun x =>
  let v0 := M (M x x) x
  T (h x v0) (C (C (R v0) (S (h x x))) (R x))

theorem Equation2696_implies_Equation203 (G: Type _) [Magma G] (h: Equation2696 G) : Equation203 G
:= fun x =>
  let v0 := M x x
  T (h x (M v0 v0)) (C (C (S (h x x)) (R v0)) (R x))

theorem Equation1227_implies_Equation100 (G: Type _) [Magma G] (h: Equation1227 G) : Equation100 G
:= fun x y =>
  let v0 := M x x
  T (h x (M (M (M v0 v0) x) x) y) (C (R x) (C (S (h v0 x x)) (R y)))

theorem Equation1558_implies_Equation14 (G: Type _) [Magma G] (h: Equation1558 G) : Equation14 G
:= fun x y =>
  have h0 := S (h y x y)
  let v1 := M x y
  T (h x v1 (M y v1)) (C h0 (C (R x) h0))

theorem Equation1571_implies_Equation2685 (G: Type _) [Magma G] (h: Equation1571 G) : Equation2685 G
:= fun x y z =>
  let v0 := M z y
  let v1 := M x y
  T (h x v1 v0) (C (R (M v1 v0)) (S (h z x y)))

theorem Equation1587_implies_Equation2805 (G: Type _) [Magma G] (h: Equation1587 G) : Equation2805 G
:= fun x y z =>
  let v0 := M z x
  let v1 := M y z
  T (h x v1 v0) (C (R (M v1 v0)) (S (h y z x)))

theorem Equation1660_implies_Equation1871 (G: Type _) [Magma G] (h: Equation1660 G) : Equation1871 G
:= fun x y z =>
  let v0 := M y z
  T (h x v0 (M (M z x) y)) (C (R (M x v0)) (C (S (h y z x)) (R x)))

theorem Equation1682_implies_Equation3050 (G: Type _) [Magma G] (h: Equation1682 G) : Equation3050 G
:= fun x =>
  let v0 := M (M x x) x
  T (h x v0) (C (R (M v0 x)) (S (h x x)))

theorem Equation1885_implies_Equation411 (G: Type _) [Magma G] (h: Equation1885 G) : Equation411 G
:= fun x =>
  let v0 := M x (M x x)
  T (h x v0) (C (S (h x x)) (R (M x v0)))

theorem Equation2706_implies_Equation23 (G: Type _) [Magma G] (h: Equation2706 G) : Equation23 G
:= fun x =>
  have h0 := S (h x x)
  let v1 := M x x
  T (h x (M v1 v1)) (C (C h0 h0) (R x))

end EquationalTheories
