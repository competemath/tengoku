-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._006: verified translations of equational_theories/Generated/MagmaEgg/small/_006.lean (7 theorems)
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

end EquationalTheories
