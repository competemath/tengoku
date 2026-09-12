-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._006: verified translations of equational_theories/Generated/MagmaEgg/small/_006.lean (19 theorems)
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

theorem Equation1790_implies_Equation3607 (G: Type _) [Magma G] (h: Equation1790 G) : Equation3607 G
:= fun x y z =>
  let v0 := M x y
  let v1 := M y z
  let v2 := M v1 x
  let v3 := M v2 v0
  let v4 := M v0 v1
  let v5 := M z v2
  have h6 := h z x y
  have h7 := S h6
  have h8 := h y v2 x
  have h9 := R (M v2 x)
  have h10 := R v5
  have h11 := h x z v2
  T (T (h v0 v5 y) (C (T (T (C h10 (T h8 (C h9 h7))) (S h11)) (h x v0 v1)) (T (T (T (C (R (M y v0)) (T (h v5 v0 y) (C (R (M v0 y)) (T (C (R (M y v5)) (C (T h11 (C h10 (T (C h9 h6) (S h8)))) (R y))) (S (h y y v5)))))) (S (h y y v0))) (h y v1 x)) (C (T (h v2 v2 v0) (C (R v3) (C h7 (R v2)))) (R v4))))) (S (h v5 v4 v3))

theorem Equation1333_implies_Equation2 (G: Type _) [Magma G] (h: Equation1333 G) : Equation2 G
:= fun x y =>
  let v0 := M (M x y) x
  let v1 := M v0 x
  have h2 := R x
  have h3 := h x x y
  let v4 := M x x
  let v5 := M (M v4 v4) x
  have h6 := h v4 x x
  let v7 := M v4 x
  let v8 := M v7 x
  let v9 := M (M v4 v0) x
  have h10 := h x x x
  have h11 := S h10
  let v12 := M (M v4 v7) x
  T (T (h x x v1) (C h2 (T (T (T (T (T (C (C (S h3) h2) h2) (h v7 x v5)) (C h2 (T (T (T (C (C (S h6) (R v7)) h2) (h v12 x v8)) (C h2 (C (T (C h11 (R v12)) (S (h v7 x x))) h2))) h11))) (C h2 (T (T (T h3 (C h2 (C (T (h v0 x x) (C h10 (R v9))) h2))) (S (h v9 x v8))) (C (C h6 (R v0)) h2)))) (S (h v0 x v5))) (C (C h3 (R y)) h2)))) (S (h y x v1))

theorem Equation2135_implies_Equation1492 (G: Type _) [Magma G] (h: Equation2135 G) : Equation1492 G
:= fun x y =>
  let v0 := M y y
  let v1 := M y v0
  let v2 := M y x
  let v3 := M v2 v1
  let v4 := M v3 v3
  let v5 := M v4 v3
  let v6 := M (M v1 v1) v1
  let v7 := M (M v0 v0) v0
  have h8 := h y y
  let v9 := M v0 y
  have h10 := R v9
  have h11 := R (M (M v2 v2) v2)
  let v12 := M x x
  have h13 := T (T (T (h (M v12 x) v2) (C h11 (S (h y x)))) (C h11 (T (T (T (T h8 (C h10 (T (T (T (T (h v0 y) (C h10 (T (h v9 v0) (C (R v7) (S h8))))) (S (h v7 y))) (h v7 v1)) (C (R v6) (S (h y v0)))))) (S (h v6 y))) (h v6 v3)) (C (R v5) (S (h v2 v1)))))) (S (h v5 v2))
  T (T (h x x) (C h13 (T (T (h v12 x) (C h13 h13)) (S (h v4 v3))))) (S (h v3 v3))

theorem Equation1776_implies_Equation19 (G: Type _) [Magma G] (h: Equation1776 G) : Equation19 G
:= fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  have h2 := h v0 v1 v1
  have h3 := S h2
  let v4 := M v1 v1
  have h5 := h (M v4 v0) v1 (M v1 x)
  have h6 := h x y y
  have h7 := R v1
  let v8 := M y y
  have h9 := h (M v8 x) y v0
  have h10 := h x y v0
  have h11 := R v4
  have h12 := h x v1 v1
  T (T (T (T (T h12 (C h11 (T (h (M v4 x) v1 (M v8 z)) (C (S (h z y v0)) (S h12))))) h5) (C (T (C h7 (T (C h7 h6) (S h9))) (S h10)) h3)) (h (M x v0) v1 (M v1 y))) (C (T (C h7 (T (C h7 (h y y y)) (S (h (M v8 y) y v0)))) (S (h y y v0))) (T (C h11 (T (C (T h10 (C h7 (T h9 (C h7 (S h6))))) h2) (S h5))) h3))

theorem Equation1293_implies_Equation684 (G: Type _) [Magma G] (h: Equation1293 G) : Equation684 G
:= fun x y z =>
  let v0 := M (M y z) z
  let v1 := M x v0
  have h2 := R v1
  let v3 := M y v1
  let v4 := M (M (M v3 v3) x) x
  have h5 := h y v1 v4
  have h6 := R v4
  have h7 := h v3 v3 x
  have h8 := R v0
  have h9 := S h7
  have h10 := R z
  let v11 := M (M v3 v0) v0
  have h12 := S (h v1 v1 x)
  let v13 := M (M (M v1 v1) x) x
  T (T (T (T (h x v0 v13) (C h8 (T (C h12 (R v13)) h12))) (C h8 (T (T (h v1 v11 z) (C (R v11) (C (C (S (h y v1 v0)) h10) h10))) (C (C (C (C (T h5 (C h2 (T (C h9 h6) h9))) h2) h8) h8) h8)))) (S (h (M (M v1 v3) v1) v0 v0))) (C (T (C h2 (T h7 (C h7 h6))) (S h5)) h2)

theorem Equation3755_implies_Equation3798 (G: Type _) [Magma G] (h: Equation3755 G) : Equation3798 G
:= fun x y z w =>
  let v0 := M w y
  let v1 := M z x
  let v2 := M x v0
  let v3 := M v0 v1
  have h4 := h v0 x z
  let v5 := M x y
  let v6 := M y x
  let v7 := M x v5
  have h8 := R (M x v6)
  have h9 := h x y w
  T (T (T (T (T h9 (h v6 v0 x)) (h (M v0 v6) v2 v0)) (C (T (T (T (T (C (R v2) (T (T (T (T (h v0 v6 x) (C (S h9) h8)) (C (T (T (h x y x) (h v6 v5 x)) (C (S (h y x y)) (R v7))) h8)) (S (h v7 v6 x))) (S (h v5 x y)))) (S (h v0 x v5))) h4) (h v2 v1 v0)) (C (T (T (T (h v1 v2 x) (C (T (S h4) (h v0 x v0)) (R (M x v2)))) (S (h (M v0 x) v2 x))) (S (h x v0 x))) (R v3))) (R (M v0 v2)))) (S (h v3 v2 v0))) (S (h v1 v0 x))

theorem Equation2714_implies_Equation1761 (G: Type _) [Magma G] (h: Equation2714 G) : Equation1761 G
:= fun x y z =>
  let v0 := M x y
  let v1 := M v0 z
  let v2 := M y z
  have h3 := h y x v2
  have h4 := R y
  have h5 := h x x y
  have h6 := R v0
  have h7 := h x x v0
  have h8 := S h7
  let v9 := M x x
  have h10 := h v0 (M v9 (M x v0)) v0
  have h11 := T (C (T h10 (C (C h8 h8) h6)) h4) (S h5)
  T (T (T h5 (C (T (C (C h7 h7) h6) (S h10)) h4)) (h (M v0 y) x v1)) (C (T (T (C (T (T (C (R x) h11) (h v9 v0 y)) (C (T (C (R (M v0 v9)) h11) (S (h y x x))) h4)) (T (h (M x v1) v0 z) (C (S (h y x v1)) (R z)))) (C (C h3 h3) (R v2))) (S (h v2 (M v0 (M x v2)) v2))) (R v1))

theorem Equation1537_implies_Equation1384 (G: Type _) [Magma G] (h: Equation1537 G) : Equation1384 G
:= fun x y z =>
  let v0 := M z z
  let v1 := M v0 x
  let v2 := M y (M v1 y)
  have h3 := h v0 x z
  have h4 := h z z z
  have h5 := S h4
  have h6 := R v0
  have h7 := h z z v0
  have h8 := R z
  let v9 := M v2 v2
  let v10 := M x x
  have h11 := R v10
  T (T (T (T (h x z v0) (C h6 (T (C h6 (C (R x) (T (T h3 (C h11 (T (C h8 (T (C h6 h4) (S h7))) (C h8 (T (h z x v0) (C h11 h5)))))) (S (h v10 x z))))) (S (h x z x))))) (h v1 v1 y)) (C (R (M v1 v1)) (T (h v2 z v2) (C h6 (C (R v2) (T (T (h v9 x z) (C h11 (T (C h8 (T (C (R v9) h4) (S (h z v2 v0)))) (C h8 (T h7 (C h6 h5)))))) (S h3))))))) (S (h v2 v1 v0))

theorem Equation2104_implies_Equation2 (G: Type _) [Magma G] (h: Equation2104 G) : Equation2 G
:= fun x y =>
  have h0 := h y x x
  have h1 := S h0
  have h2 := h x x x
  have h3 := S h2
  have h4 := C h3 h3
  let v5 := M x x
  have h6 := h x v5 (M v5 x)
  have h7 := h x v5 (M (M x y) x)
  have h8 := S h7
  have h9 := C h2 h0
  have h10 := R x
  have h11 := S h6
  have h12 := C h2 h2
  have h13 := S (h v5 x y)
  let v14 := M y x
  have h15 := R v14
  have h16 := C h10 (T h6 h4)
  T (T (h x y x) (C (T (T (T (T (T (C (T (T (T (T (h v14 x y) (C (C (T (T (C (T (T (T h6 h4) h16) (C (T (T h6 h4) h16) (T h12 h11))) h15) h13) h16) h10) h15)) h13) h12) h11) (R y)) h9) h8) h6) h4) (C (T h7 (C h3 h1)) h10)) (T (T (T h9 h8) h6) h4))) h1

theorem Equation3959_implies_Equation3331 (G: Type _) [Magma G] (h: Equation3959 G) : Equation3331 G
:= fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  have h2 := R v1
  let v3 := M x v1
  have h4 := R z
  let v5 := M y v3
  have h6 := h z v5 v0
  have h7 := S h6
  have h8 := R v0
  have h9 := h x y v1
  let v10 := M x y
  have h11 := h y v10 z
  have h12 := h x y y
  have h13 := S h12
  have h14 := R y
  let v15 := M y v10
  T (T (T h12 (h v15 y v1)) (C (T (T (T (T (C h14 (T (T (h v15 v1 y) (C (T (T (T (T (C h2 h13) (h v1 v10 z)) (C (T (C h9 (S (h y z z))) h7) h4)) (C (T h6 (C (S h9) h8)) h4)) (S h11)) h14)) h13)) h11) (C (T (C h9 h8) h7) h4)) (h (M z v5) z v3)) (C (C h4 (S (h y z v3))) (R v3))) h2)) (S (h x v1 v1))

theorem Equation909_implies_Equation703 (G: Type _) [Magma G] (h: Equation909 G) : Equation703 G
:= fun x y =>
  let v0 := M x x
  let v1 := M v0 x
  let v2 := M y v1
  let v3 := M y v2
  have h4 := h v3 v1
  let v5 := M v1 v3
  have h6 := h v2 y
  have h7 := R v1
  have h8 := S (h v1 v1)
  let v9 := M v1 v1
  have h10 := h v9 v0
  have h11 := h x v0
  have h12 := R v0
  have h13 := T (C h12 (C h11 h11)) (S h10)
  let v14 := M v0 v0
  have h15 := h v0 v0
  have h16 := S h11
  T (T (T (T (T (T h11 (C h12 (T (T h10 (C h12 (C h16 h16))) (C h15 h15)))) (S (h (M v14 v14) v0))) (C h13 h13)) (h (M v9 v9) v1)) (C h7 (T (T (C h8 h8) (C h7 (T (T (T (h v1 y) (C (R y) (C h6 h6))) (S (h (M v3 v3) y))) (C h4 h4)))) (S (h (M v5 v5) v1))))) (S h4)

theorem Equation1891_implies_Equation2 (G: Type _) [Magma G] (h: Equation1891 G) : Equation2 G
:= fun x y =>
  let v0 := M x x
  let v1 := M y x
  let v2 := M x v0
  have h3 := h x v2 v2
  have h4 := R (M v2 v2)
  have h5 := h x x x
  have h6 := T (C h5 h4) (S h3)
  let v7 := M y y
  let v8 := M x v7
  have h9 := h x v8 v8
  have h10 := R (M v8 v8)
  have h11 := h y x x
  have h12 := T (T (T (C h11 h10) (S h9)) h3) (C (S h5) h4)
  have h13 := h x v0 v0
  have h14 := S h13
  have h15 := T (T h14 h9) (C (S h11) h10)
  let v16 := M v0 v0
  T (T h13 (C (T (h v16 y y) (C (C (R y) h14) (R v7))) (T (h v16 x y) (C (T (T (T (C h13 (R (M v16 v16))) (C h15 h15)) (C h12 h12)) (C h6 h6)) (R v1))))) (S (h y v1 v0))

theorem Equation2718_implies_Equation2 (G: Type _) [Magma G] (h: Equation2718 G) : Equation2 G
:= fun x y =>
  have h0 := h y x x
  have h1 := S h0
  have h2 := R x
  let v3 := M x y
  let v4 := M v3 v3
  have h5 := h v4 x x
  let v6 := M y x
  let v7 := M x x
  let v8 := M v7 v6
  have h9 := C (T (C (S (h v8 x x)) h1) (S (h x x y))) (R v4)
  let v10 := M x v8
  have h11 := h x (M v10 v10) v4
  let v12 := M v6 v7
  let v13 := M v7 v7
  let v14 := M x v13
  have h15 := R v12
  have h16 := h x y x
  let v17 := M x v4
  T (T h16 (C (T (T (h v12 y x) (C (C (T (T (T (C (T h0 (C h5 h16)) h15) (S (h x (M v17 v17) v12))) h11) h9) (T (T (T (C (T (h x x x) (C (h v13 x x) h16)) h15) (S (h x (M v14 v14) v12))) h11) h9)) h2)) (S h5)) h2)) h1

theorem Equation3566_implies_Equation333 (G: Type _) [Magma G] (h: Equation3566 G) : Equation333 G
:= fun x y =>
  let v0 := M x y
  have h1 := h x y v0
  have h2 := R y
  have h3 := h v0 x y
  have h4 := S h3
  have h5 := R x
  have h6 := h y v0 v0
  have h7 := h (M v0 y) v0 y
  have h8 := R v0
  have h9 := h y y x
  have h10 := h y v0 y
  have h11 := C (T (C h8 (T (T h10 (C h8 (C h9 h8))) (S h7))) (S h6)) h5
  have h12 := C h5 h11
  have h13 := C (T h6 (C h8 (T (T h7 (C h8 (C (S h9) h8))) (S h10)))) h5
  have h14 := h (M y v0) x v0
  have h15 := C h5 h13
  have h16 := C (T (T (C h5 (T (T (T h3 h15) (S h14)) h13)) h12) h4) h2
  T (T h1 (C h2 (C (T (T h3 h15) (C h5 (T (T (T h11 h14) h12) h4))) h2))) (C h2 (T (T (T h16 (h (M v0 x) y x)) (C h2 h16)) (S h1)))

theorem Equation3940_implies_Equation3331 (G: Type _) [Magma G] (h: Equation3940 G) : Equation3331 G
:= fun x y z =>
  let v0 := M y z
  let v1 := M z v0
  let v2 := M x v1
  let v3 := M x y
  let v4 := M v3 v2
  have h5 := R z
  let v6 := M z v1
  have h7 := R v6
  have h8 := h z v0 z
  have h9 := R x
  let v10 := M x (M v1 y)
  let v11 := M v3 v3
  T (T (T (T (h x y v3) (h (M x (M v3 y)) v3 v3)) (C (T (T (T (C (C h9 (h v3 y x)) (R v11)) (S (h x x v11))) (h x x v4)) (C (C h9 (T (T (T (S (h v3 v1 x)) (h v3 v1 z)) (C (T (T (T (T (T (C (T (h x y v1) (C (R v10) h8)) h7) (S (h v10 z v6))) (C (C h9 (S (h z z y))) h5)) (S (h x z z))) (h x z v6)) (C (C h9 (S h8)) h7)) h5)) (S (h v2 v1 z)))) (R v4))) (R v3))) (S (h (M x (M v2 v1)) v2 v3))) (S (h x v1 v2))

theorem Equation1359_implies_Equation2 (G: Type _) [Magma G] (h: Equation1359 G) : Equation2 G
:= fun x y =>
  have h0 := R x
  have h1 := h y x x
  have h2 := C h1 h0
  let v3 := M y x
  have h4 := h v3 x y
  let v5 := M (M (M x v3) x) x
  have h6 := R y
  have h7 := h x x y
  let v8 := M (M v3 y) y
  T (T (h x y y) (C h6 (T (T (h v8 y y) (C h6 (T (T (T (h (M (M (M y v8) y) y) x x) (C h0 (C (C (T (T (S (h v8 x y)) (h v8 x x)) (C h0 (C (C (S h7) h0) h0))) h0) h0))) (S (h (M (M x x) x) x x))) (C (T (T (C h0 (T (T (T (T (T h7 (C h0 (C (C (h v3 y x) h6) h6))) (S (h v5 x y))) (h v5 x x)) (C h0 (C (T (C (T (S (h v3 x x)) h2) h0) (C (T (C (S h1) h0) h4) h0)) h0))) (S (h (M (M (M y v3) y) y) x x)))) (S h4)) h2) h0)))) (S (h (M (M (M x y) x) x) y x))))) (S (h y y x))

theorem Equation1492_implies_Equation2135 (G: Type _) [Magma G] (h: Equation1492 G) : Equation2135 G
:= fun x y =>
  let v0 := M x y
  let v1 := M y y
  let v2 := M v1 y
  let v3 := M v2 v0
  let v4 := M v3 v3
  let v5 := M v3 v4
  have h6 := R (M v0 (M v0 v0))
  let v7 := M v2 (M v2 v2)
  let v8 := M y v1
  have h9 := R v8
  let v10 := M v1 (M v1 v1)
  have h11 := h y y
  let v12 := M x x
  have h13 := T (T (T (h (M x v12) v0) (C (S (h y x)) h6)) (C (T (T (T (T h11 (C (T (h v1 v2) (C (T (C (R v2) (T (T (h v1 y) (C (T (h v8 v1) (C (S h11) (R v10))) h9)) (S (h v10 y)))) (S (h y v1))) (R v7))) h9)) (S (h v7 y))) (h v7 v3)) (C (S (h v0 v2)) (R v5))) h6)) (S (h v5 v0))
  T (T (h x x) (C (T (T (h v12 x) (C h13 h13)) (S (h v4 v3))) h13)) (S (h v3 v3))

theorem Equation3591_implies_Equation4200 (G: Type _) [Magma G] (h: Equation3591 G) : Equation4200 G
:= fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  let v2 := M v1 y
  let v3 := M x y
  have h4 := R y
  have h5 := h v0 z z
  let v6 := M v1 z
  have h7 := R v6
  have h8 := R z
  let v9 := M (M x v1) y
  let v10 := M v2 v3
  let v11 := M v3 v3
  T (T (T (T (h x y v3) (h v3 (M (M x v3) y) v3)) (C (R v3) (T (T (T (C (R v11) (C (h x v3 y) h4)) (S (h y y v11))) (h y y v10)) (C (R v10) (C (T (T (T (S (h v1 v3 y)) (h v1 v3 z)) (C h8 (T (T (T (T (T (C h7 (T (h x y v1) (C h5 (R v9)))) (S (h z v9 v6))) (C h8 (C (S (h z z x)) h4))) (S (h z y z))) (h z y v6)) (C h7 (C (S h5) h4))))) (S (h v1 v2 z))) h4))))) (S (h v2 (M (M v1 v2) y) v3))) (S (h v1 y v2))

theorem Equation3159_implies_Equation2290 (G: Type _) [Magma G] (h: Equation3159 G) : Equation2290 G
:= fun x y =>
  let v0 := M x x
  have h1 := h x v0 x
  have h2 := S h1
  have h3 := R x
  have h4 := h x x v0
  have h5 := T (C h4 h3) h2
  let v6 := M x v0
  have h7 := R v6
  let v8 := M y v6
  let v9 := M v8 x
  have h10 := R y
  have h11 := R v9
  have h12 := R v8
  have h13 := T (C (T (h y v9 v9) (C (C (C (T (C (T (h v9 v8 v8) (C (C (C (T (C (T (h v8 v6 v6) (C (C (C (T (C (T (h v6 x x) (C (T (C (C h5 h3) h7) (R (M v0 v6))) h7)) h7) (S (h v6 x v6))) h7) h12) h12)) h12) (S (h v8 v6 v8))) h12) h11) h11)) h11) (S (h v9 v8 v9))) h11) h10) h10)) h10) (S (h y v9 y))
  have h14 := S h4
  T (T (T (T h1 (C h14 (T h1 (C h14 h3)))) (h v6 y y)) (C (C (C h13 h10) h7) h7)) (C (C h13 h7) (T (C h4 h5) h2))

end EquationalTheories
