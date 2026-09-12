-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._007: verified translations of equational_theories/Generated/MagmaEgg/small/_007.lean (7 theorems)
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

theorem Equation711_implies_Equation725 (G: Type _) [Magma G] (h: Equation711 G) : Equation725 G
:= fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  have h2 := S (h v1 v1 x)
  let v3 := M v1 (M (M v1 x) x)
  have h4 := R y
  let v5 := M z (M v0 x)
  have h6 := h z v0 v5
  have h7 := S h6
  have h8 := R v5
  have h9 := h z z x
  have h10 := R v0
  have h11 := C h10 (C h10 (T h9 (C h9 h8)))
  have h12 := R x
  have h13 := S h9
  have h14 := C h10 (C (C (T h6 (C h10 (C h10 (T (C h13 h8) h13)))) h12) h12)
  have h15 := S (h x x x)
  let v16 := M x (M (M x x) x)
  have h17 := C h10 (C h10 (T (C h15 (R v16)) h15))
  have h18 := h x v0 v16
  T (T (T (T (T h18 h17) h14) (C h10 (T (T (T (C (C (T h11 h7) h12) (T (T h18 h17) h14)) (S (h (M v0 v1) v0 x))) h11) h7))) (h v1 y v3)) (C h4 (C h4 (T (C h2 (R v3)) h2)))

theorem Equation3789_implies_Equation41 (G: Type _) [Magma G] (h: Equation3789 G) : Equation41 G
:= fun x y z =>
  let v0 := M y z
  have h1 := h y x x
  have h2 := h x y x
  have h3 := S h2
  let v4 := M x x
  let v5 := M y x
  have h6 := h v4 v5 v4
  have h7 := S h6
  have h8 := h x x y
  have h9 := h x x x
  have h10 := C h9 h8
  have h11 := h x x z
  have h12 := S h11
  have h13 := S h9
  let v14 := M z x
  have h15 := h v4 v14 v4
  have h16 := T (T (T (T h15 (C h13 h12)) h10) h7) h3
  have h17 := h v14 v4 v4
  have h18 := C h13 (S h8)
  have h19 := T (T (T (T h2 h6) h18) (C h9 h11)) (S h15)
  T (T (T (T h8 (h v5 v4 v0)) (C (C (R v0) (T (T (T (T (T (T (T h1 (C h19 h19)) (S h17)) h12) h9) h10) h7) h3)) (T (T (T (T (T (T (T h6 h18) h13) h11) h17) (C h16 h16)) (S h1)) (h y x z)))) (S (h (M x y) (M z y) v0))) (S (h y z x))

theorem Equation3930_implies_Equation4510 (G: Type _) [Magma G] (h: Equation3930 G) : Equation4510 G
:= fun x y z =>
  let v0 := M x y
  have h1 := R x
  let v2 := M y z
  let v3 := M y v2
  have h4 := T (T (h x v3 y) (C (C h1 (S (h y y z))) h1)) (S (h x y y))
  have h5 := S (h x y z)
  have h6 := h y z y
  have h7 := C (C h1 (S h6)) h1
  let v8 := M z y
  have h9 := h x (M y v8) y
  let v10 := M v0 x
  have h11 := R y
  have h12 := h z y z
  have h13 := R z
  let v14 := M z v2
  have h15 := S (h y v14 z)
  have h16 := C (C h11 h12) h11
  have h17 := C h1 (T (T (T (T (T h6 h16) h15) (h y v14 v10)) (C (C h11 (C (T (T (h z v2 y) (C (C h13 (T (C (T (T h6 h16) h15) h11) (S (h y z v2)))) h13)) (S h12)) (R v10))) h11)) (S (h y v8 v10)))
  T (T (T (T (T (T (T h17 h9) h7) h5) (h x y v2)) (h (M x v3) x v2)) (C (C h4 (T (T (T h17 h9) h7) h5)) h4)) (S (h v0 x y))

theorem Equation928_implies_Equation543 (G: Type _) [Magma G] (h: Equation928 G) : Equation543 G
:= fun x y z =>
  let v0 := M y z
  let v1 := M x v0
  let v2 := M z v1
  let v3 := M y v2
  let v4 := M v0 x
  have h5 := h z v0 x
  let v6 := M v1 v1
  have h7 := S (h v1 v2 x)
  have h8 := R v2
  let v9 := M v1 x
  have h10 := R z
  have h11 := R v1
  have h12 := h v1 v1 (M v9 v4)
  have h13 := h v0 v1 x
  have h14 := S h13
  T (T (h x v2 v0) (C h8 (C (R (M v2 v0)) (T (T (T h12 (C h11 (C h14 h14))) (h (M v1 (M v0 v0)) v3 v1)) (C (R v3) (T (T (C (T (h (M v3 v1) y v2) (C (R y) (S (h z v3 v1)))) (T (T (C (T (C h11 (C h13 h13)) (S h12)) h11) (h v6 z v2)) (C h10 (T (C (T (C h10 (T (h v2 v2 (M (M v2 x) v9)) (C h8 (C h7 h7)))) (S (h v1 z v1))) (R (M v6 v2))) (S (h z v1 v1)))))) (C (R v0) (C h5 h5))) (S (h v0 v0 (M v4 (M z x)))))))))) (S (h v3 v2 v0))

theorem Equation1283_implies_Equation2 (G: Type _) [Magma G] (h: Equation1283 G) : Equation2 G
:= fun x y =>
  let v0 := M x x
  let v1 := M (M v0 x) x
  let v2 := M v1 v1
  let v3 := M v2 y
  let v4 := M (M v3 v3) x
  let v5 := M (M (M y y) y) y
  have h6 := R x
  have h7 := h x v1 x
  have h8 := S h7
  have h9 := R v2
  let v10 := M (M v0 y) y
  have h11 := h x v10 y
  have h12 := S h11
  have h13 := T (C (T (C (C (T h12 h7) h12) h6) (C (C h9 h7) h6)) h6) (C (C (C h8 h8) h6) h6)
  let v14 := M v10 v10
  have h15 := h v14 x x
  have h16 := R v4
  have h17 := R y
  have h18 := S h15
  have h19 := T (C (C (C h7 h7) h6) h6) (C (T (C (C h9 h8) h6) (C (C (T h8 h11) h11) h6)) h6)
  T (T (T (h x y x) (C h17 (T (h v1 v4 v1) (C h16 (T (T (C (T (T (C h8 h19) h18) h12) h19) h18) h12))))) (C h17 (T (C h16 (T (T h11 h15) (C (T (T h11 (h v14 y x)) (C (h y v5 y) h13)) h13))) (S (h v5 v4 v1))))) (S (h y y y))

theorem Equation4176_implies_Equation3959 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3959 G
:= fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  have h2 := R v0
  have h3 := R v1
  have h4 := h v1 x z
  let v5 := M x y
  have h6 := R x
  have h7 := h x y v0
  have h8 := R y
  let v9 := M v1 z
  let v10 := M z v9
  have h11 := R z
  T (T h7 (C (T (T (T (T (T (T (T h4 (C (T (T (h v0 v1 y) (C (S (h y y v0)) h8)) (C (T (T (T (h y y x) (C (T (C (h y x z) h8) (S (h z v0 y))) h6)) (C (T (h z v0 z) (C (S (h z x z)) h11)) h6)) (S (h z z x))) h8)) h11)) (S (h y z z))) (h y z v0)) (C (T (C (T (h z v0 x) (C (T (T (T (C (T (C (h x z v9) h6) (S (h v9 v10 x))) h11) (S (h v10 v1 z))) (C (T (h z v9 y) (C (S (h y v1 z)) h8)) h3)) (S (h y y v1))) h6)) h8) (S (h x y y))) h2)) (h v5 v0 v1)) (C (T (C (T (T (h v0 v1 x) (C (S h7) h6)) (h v5 x y)) (R v5)) (S (h y v5 v5))) h3)) (C (T (T (h y v5 v1) (C (T (S (h v1 x y)) h4) h3)) (S (h z v0 v1))) h3)) h2)) (S (h v1 z v0))

theorem Equation2105_implies_Equation2592 (G: Type _) [Magma G] (h: Equation2105 G) : Equation2592 G
:= fun x y z =>
  let v0 := M z y
  let v1 := M v0 z
  let v2 := M y v1
  let v3 := M v2 x
  have h4 := R v1
  have h5 := h y z x
  have h6 := S h5
  let v7 := M x x
  have h8 := R v7
  have h9 := h v1 v1 x
  have h10 := h (M v1 v1) v1 x
  have h11 := S h10
  have h12 := h y z v1
  have h13 := C (T (C h6 h4) (C h12 h4)) h8
  have h14 := h v7 v1 x
  have h15 := h v1 v7 x
  have h16 := C (T (T h15 (C (T (C (C (T (T h14 h13) h11) h4) h8) (S h9)) h8)) h6) h4
  T (T (h x x v0) (C (T (T (C (T (T (T h14 h13) h11) h16) (R x)) (h v3 v3 v1)) (C (C (T (T (T (T (h (M v3 v3) v1 x) (C (C (S (h y z v3)) h4) h8)) (C (C (h y z y) h4) h8)) (S (h (M y y) v1 x))) (C (R y) (T (T h5 (C (T h9 (C (C (T (T h10 (C (T (C (S h12) h4) (C h5 h4)) h8)) (S h14)) h4) h8)) h8)) (S h15)))) (R v3)) h16)) (R (M v0 v0)))) (S (h v3 v2 v0))

end EquationalTheories
