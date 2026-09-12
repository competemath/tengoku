-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._010: verified translations of equational_theories/Generated/MagmaEgg/small/_010.lean (6 theorems)
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

theorem Equation522_implies_Equation2925 (G: Type _) [Magma G] (h: Equation522 G) : Equation2925 G
:= fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M v1 y
  let v3 := M v2 z
  have h4 := h y v1 v0
  have h5 := S h4
  have h6 := R v1
  have h7 := C h6 h5
  have h8 := h v0 v1 v1
  have h9 := h v0 y y
  have h10 := S h9
  have h11 := h y v0 v2
  have h12 := S h11
  have h13 := R (M v2 (M y v2))
  have h14 := S h8
  have h15 := C h6 h4
  have h16 := T h15 h14
  have h17 := h v1 v2 y
  have h18 := R v0
  have h19 := C h18 (T h17 (C h16 h13))
  have h20 := T h19 h12
  have h21 := C h16 h20
  have h22 := T h8 h7
  have h23 := C h18 (T (C h22 h13) (S h17))
  have h24 := T h11 h23
  have h25 := C h6 h24
  have h26 := C h6 (T (T h8 h7) h25)
  have h27 := C h22 (T (T (T h26 h5) h11) h23)
  have h28 := R y
  have h29 := h v1 y v0
  have h30 := h v1 v2 v0
  have h31 := C h6 h20
  have h32 := C h6 (T (T h31 h15) h14)
  have h33 := C h16 (T (T (T h19 h12) h4) h32)
  have h34 := R v2
  have h35 := h y v2 v0
  have h36 := C h22 h24
  have h37 := C h28 (T (T (T (T (T h36 h33) (C h22 (T (T (T h26 h5) h35) (C h34 h33)))) (S h30)) h29) (C h28 (C h28 (T h27 h21))))
  have h38 := R v3
  have h39 := R z
  have h40 := h v0 v0 x
  have h41 := h x v0 z
  have h42 := h z v0 v0
  have h43 := R x
  T (T (h x v3 z) (C h38 (C h38 (T (T (T (C h39 (T (T h40 (C h18 (C h18 (C h43 (T (C h18 h41) (S h42)))))) (C h22 (C h18 h22)))) (C h39 (T (T (T (T (T (C h16 (C h18 h16)) (C h18 (C h18 (C h43 (T h42 (C h18 (S h41))))))) (S h40)) h8) h7) h25))) (C h39 (T (T (T (T h31 h15) h14) h9) (C h28 (T (T (T (T (T (C h28 (C h28 (T h36 h33))) (S h29)) h30) (C h16 (T (T (T (C h34 h27) (S h35)) h4) h32))) h27) h21))))) (C h39 (T (T (T h37 h10) (h v0 v3 y)) (C h38 (T (C h38 (T (T (T (T h37 h10) h8) h7) (h v2 v3 z))) (S (h z v3 v3)))))))))) (S (h v3 v3 z))

theorem Equation895_implies_Equation3804 (G: Type _) [Magma G] (h: Equation895 G) : Equation3804 G
:= fun x y z =>
  let v0 := M x z
  let v1 := M z y
  let v2 := M v1 v0
  let v3 := M y x
  have h4 := h x z y
  let v5 := M x y
  let v6 := M v5 v1
  have h7 := R v2
  have h8 := h y v1 v5
  have h9 := S h8
  let v10 := M v1 v5
  have h11 := R v10
  have h12 := h v5 v5 (M v3 (M v5 x))
  have h13 := h y v5 x
  have h14 := R v5
  have h15 := R y
  have h16 := h x y y
  have h17 := h z x y
  have h18 := T h17 (C (T h16 (C h15 (T (C h14 (C h13 h13)) (S h12)))) h11)
  have h19 := R v1
  have h20 := C h19 h18
  let v21 := M v1 z
  have h22 := S (h v21 v5 v1)
  have h23 := R v6
  have h24 := S h17
  have h25 := S h13
  have h26 := C (T (C h15 (T h12 (C h14 (C h25 h25)))) (S h16)) h11
  have h27 := h v1 v1 (M v3 (M v1 x))
  have h28 := h y v1 x
  have h29 := h z y y
  have h30 := C h14 (T (T h4 (C (T h29 (C h15 (T (C h19 (C h28 h28)) (S h27)))) h23)) (C (C (T h8 (C h19 (T h26 h24))) h19) h23))
  have h31 := R v0
  let v32 := M v0 x
  have h33 := h v0 v0 (M (M z x) v32)
  have h34 := h z v0 x
  have h35 := T (C h31 (C h34 h34)) (S h33)
  have h36 := S h34
  have h37 := h v0 v2 x
  have h38 := S h28
  T (T (h v5 y x) (C h15 (C (T (T (T h30 h22) (h v21 v2 v1)) (C h7 (T (C (T (C (T h20 h9) (T h27 (C h19 (C h38 h38)))) (S h29)) (T (C h7 (T (h v1 v1 v0) (C (T (T (T (h v1 v0 v0) (C h31 (T (C h7 (C h37 h37)) (S (h v2 v2 (M v32 (M v2 x))))))) (C (T h33 (C h31 (C h36 h36))) h7)) (C (T (h (M v0 (M z z)) v5 x) (C h14 (C (T (T (T (C h35 (T (h x x z) (C (T (T (h x z z) (C (R z) h35)) (C h18 h31)) (R (M v0 v0))))) (S (h (M (M y v5) v10) v0 v0))) h26) h24) (T (T (T h30 h22) h20) h9)))) h7)) (R (M v2 v2))))) (S (h v6 v2 v2)))) (S h4)))) (R v3)))) (S (h v2 y x))

theorem Equation1090_implies_Equation4210 (G: Type _) [Magma G] (h: Equation1090 G) : Equation4210 G
:= fun x y z =>
  let v0 := M z y
  let v1 := M v0 x
  let v2 := M (M y v1) x
  have h3 := h z v0 v2
  have h4 := S h3
  have h5 := R v2
  have h6 := h y v0 x
  have h7 := R z
  have h8 := R v0
  have h9 := C h8 (T h6 (C (C h7 h6) h5))
  have h10 := T h9 h4
  have h11 := R v1
  have h12 := R y
  let v13 := M v1 z
  have h14 := h v0 v13 y
  let v15 := M (M z (M v13 x)) x
  have h16 := h v1 v13 v15
  have h17 := S h16
  have h18 := R v15
  have h19 := h z v13 x
  have h20 := R v13
  have h21 := C h20 (T h19 (C (C h11 h19) h18))
  let v22 := M x y
  have h23 := h (M v13 z) v22 y
  have h24 := S h23
  have h25 := h y v22 x
  have h26 := S h25
  let v27 := M (M y (M v22 x)) x
  have h28 := R v27
  have h29 := R x
  have h30 := R v22
  have h31 := h x v22 v27
  have h32 := T h31 (C h30 (T (C (C h29 h26) h28) h26))
  have h33 := S h19
  have h34 := C h20 (T (C (C h11 h33) h18) h33)
  have h35 := h x v1 x
  have h36 := S h35
  let v37 := M (M x (M v1 x)) x
  have h38 := R v37
  have h39 := h v0 v1 v37
  have h40 := S h6
  have h41 := C h8 (T (C (C h7 h40) h5) h40)
  have h42 := C h30 (T (T h3 h41) (C (T (T h39 (C h11 (T (C (C h8 h36) h38) h36))) (C (T h16 h34) h32)) h12))
  have h43 := h (M v22 z) v0 y
  have h44 := C h30 (T (T (C (T (T (C (T h21 h17) (T (C h30 (T h25 (C (C h29 h25) h28))) (S h31))) (C h11 (T h35 (C (C h8 h35) h38)))) (S h39)) h12) h9) h4)
  T (T (h v22 v1 y) (C h11 (C (T (T (T (C h30 (C (C (T h14 (C h20 (C (T (T (T (T (T (C h8 (C (C (T (T (T h16 h34) h23) h44) (T h3 h41)) h12)) (S h43)) h42) h24) h21) h17) h12))) h32) h12)) (S (h (M v13 (M v1 y)) v22 y))) (C h20 (C (T (T (T (T (T h16 h34) h23) h44) h43) (C h8 (C (C (T (T (T h42 h24) h21) h17) h10) h12))) h12))) (S h14)) h12))) (C h11 h10)

theorem Equation928_implies_Equation2482 (G: Type _) [Magma G] (h: Equation928 G) : Equation2482 G
:= fun x y z =>
  let v0 := M y z
  let v1 := M v0 y
  let v2 := M x v1
  let v3 := M v2 z
  let v4 := M v3 v0
  have h5 := S (h z v0 x)
  have h6 := R v0
  have h7 := h v0 v1 v1
  let v8 := M v1 x
  have h9 := h v1 v1 (M v8 (M y x))
  have h10 := h y v1 x
  have h11 := R v1
  have h12 := T (C h11 (C h10 h10)) (S h9)
  have h13 := h y v0 y
  have h14 := T h13 (C h6 h12)
  have h15 := C h12 h11
  have h16 := h (M v1 (M y y)) x v1
  have h17 := S h10
  have h18 := T h9 (C h11 (C h17 h17))
  have h19 := C h18 h11
  have h20 := R v2
  have h21 := h v1 v2 x
  have h22 := S h21
  have h23 := C h20 (C h22 h22)
  have h24 := h v2 v2 (M (M v2 x) v8)
  have h25 := R x
  have h26 := C (T (C h25 (T (T h24 h23) (C h20 h19))) (S h16)) h11
  have h27 := h v1 x v1
  let v28 := M x v2
  have h29 := R v28
  have h30 := C h29 (T (C h25 (T h24 h23)) (S h27))
  have h31 := h (M v28 v28) v0 y
  have h32 := S h24
  have h33 := C h20 (C h21 h21)
  have h34 := C h29 (T h27 (C h25 (T h33 h32)))
  have h35 := C (T h16 (C h25 (T (T (C h20 h15) h33) h32))) h11
  have h36 := T (C h6 h18) (S h13)
  let v37 := M v0 v1
  have h38 := R v37
  T (T (h x y v0) (C (R y) (C (R (M y v0)) (T (T (T (T (C h25 (h v0 v2 y)) (S (h (M v2 y) x v1))) (C h20 h14)) (C h20 (T (T (T (T (T (h v37 y z) (C h14 (T (T (T (C h6 (C h36 (R z))) (C h6 (T h7 (C h11 (C (T (T h19 h35) h34) h36))))) (S h31)) h30))) (C h38 h26)) (C h38 h15)) (h (M v37 (M v1 v1)) v3 v0)) (C (R v3) (C (R v4) (T (C (T (C h36 (T (T (T (T h19 h35) h34) h31) (C h6 (T (C h11 (C (T (T h30 h26) h15) h14)) (S h7))))) (S (h y y z))) (T (h v0 v0 (M (M v0 x) (M z x))) (C h6 (C h5 h5)))) (S (h z y z)))))))) (S (h v4 v2 z)))))) (S (h v3 y v0))

theorem Equation3591_implies_Equation3617 (G: Type _) [Magma G] (h: Equation3591 G) : Equation3617 G
:= fun x y z =>
  let v0 := M z x
  let v1 := M v0 y
  let v2 := M z v1
  have h3 := h z v1 v2
  have h4 := S h3
  let v5 := M (M z v2) v1
  have h6 := R v1
  let v7 := M v2 v2
  have h8 := h v0 y v2
  have h9 := S h8
  let v10 := M (M v0 v2) y
  have h11 := h v2 v10 v5
  have h12 := R v10
  have h13 := R v5
  have h14 := T (T (C h13 (T h8 (C h3 h12))) (S h11)) h9
  have h15 := T (T h8 h11) (C h13 (T (C h4 h12) h9))
  let v16 := M z v0
  let v17 := M v16 x
  have h18 := h v0 y v17
  have h19 := S h18
  have h20 := R y
  have h21 := h z x v0
  have h22 := R v17
  have h23 := C h22 (C h21 h20)
  have h24 := h v16 x v1
  have h25 := R x
  have h26 := h v16 v1 x
  have h27 := C h22 (C (S h21) h20)
  have h28 := h z y x
  have h29 := S h28
  have h30 := h x x v1
  let v31 := M z z
  let v32 := M v31 v1
  let v33 := M v31 x
  let v34 := M v0 x
  let v35 := M z y
  have h36 := h z x x
  let v37 := M v0 v0
  have h38 := R v34
  T (T (T (T (T (h x y v34) (C h38 (C (S h36) h20))) (h v34 v1 v2)) (C (R v2) (T (T (T (C (T (T (T (T (T (T (T (T (T (C h38 (T (T (T (h z v1 v0) (h v0 (M v16 v1) v0)) (C (R v0) (T (T (C (R v37) (C (h z v0 x) h6)) (S (h x v1 v37))) h29))) (C h36 (R v35)))) (S (h x v35 v34))) (C h25 (T (h z y v33) (C (R v33) (C (S (h z x z)) h20))))) (S (h v31 v1 x))) (h v31 v1 v1)) (C h6 (T (T (T (T (T (C (R v32) (T h8 (C (h z v1 z) h12))) (S (h z v10 v32))) (h z v10 v1)) (C h6 h9)) (C h6 h15)) (C (T (T h18 h27) (C (T (T h24 (C h6 (T (C (T (T h26 (C h25 (T h23 h19))) h29) h25) (C h28 h25)))) (S h30)) h6)) h14)))) (S (h (M x x) v1 v1))) (C (T (T h30 (C h6 (T (C h29 h25) (C (T (T h28 (C h25 (T h18 h27))) (S h26)) h25)))) (S h24)) h6)) h23) h19) h15) (C h6 h14)) (h v1 v1 v7)) (C (R v7) (C (S (h z v2 v1)) h6))))) (S (h v2 v5 v2))) h4

theorem Equation1130_implies_Equation2 (G: Type _) [Magma G] (h: Equation1130 G) : Equation2 G
:= fun x y =>
  let v0 := M y (M y x)
  have h1 := R y
  have h2 := h x y y
  let v3 := M x x
  let v4 := M x v3
  have h5 := h x x v4
  have h6 := S h5
  have h7 := R x
  have h8 := h x x x
  have h9 := C h7 (C h8 h7)
  have h10 := h v4 y y
  have h11 := S h10
  have h12 := C h7 (C (S h8) h7)
  have h13 := C h1 (T h5 h12)
  have h14 := C (C h1 h13) h1
  let v15 := M v0 y
  have h16 := h v15 y y
  have h17 := S h16
  have h18 := C h1 (T h9 h6)
  have h19 := C h1 (C (T h18 (C h1 h2)) h1)
  have h20 := h v3 y x
  have h21 := C h1 (T (T (T h20 h19) h17) h14)
  let v22 := M y v3
  have h23 := S h20
  have h24 := S h2
  have h25 := C h1 (C (T (C h1 h24) h13) h1)
  have h26 := h v4 x y
  have h27 := S h26
  have h28 := C h7 h13
  have h29 := h y x x
  have h30 := C h7 (C (S h29) h7)
  have h31 := h x x (M x (M x y))
  have h32 := T (T h31 h30) h28
  have h33 := h v15 x y
  have h34 := h x y x
  have h35 := h (M v22 y) x y
  have h36 := C h7 (T (T (T (T (T (T h35 (C h7 (C (T (C h7 (S h34)) (C h7 h2)) h7))) (S h33)) h16) h25) h23) (C h32 h7))
  have h37 := S h31
  have h38 := C h7 (C h29 h7)
  have h39 := C h7 h18
  have h40 := C (T (T h39 h38) h37) h7
  have h41 := C h7 (T (T (T (T (T (T h40 h20) h19) h17) h33) (C h7 (C (T (C h7 h24) (C h7 h34)) h7))) (S h35))
  have h42 := T (C h1 (T h26 h41)) (C h1 (T (T (T h36 h27) h10) (C h1 (T (T (T (C (C h1 h18) h1) h16) h25) h23))))
  T (T (T (T (T h2 (C h1 (T (T h16 h25) h23))) (h v22 y x)) (C h1 (C (T (T (T (T (T (C h1 (T (T (T (T (T (T (T (T (C (T (T (T h31 h30) h28) (C h7 h42)) (T (T (T h21 h11) h9) h6)) (C (T (T (T (C h7 (T (C h1 (T (T (T h21 h11) h26) h41)) (C h1 (T h36 h27)))) h39) h38) h37) (T (T (T h5 h12) h26) h41))) (C h32 (T (T (T h36 h27) h9) h6))) h40) h20) h19) h17) h14) (C (C h1 h42) h1))) (S (h v22 y y))) h21) h11) h9) h6) h1))) (C h1 (C h2 h1))) (S (h y y v0))

end EquationalTheories
