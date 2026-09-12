-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._011: verified translations of equational_theories/Generated/MagmaEgg/small/_011.lean (4 theorems)
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

theorem Equation4176_implies_Equation3404 (G: Type _) [Magma G] (h: Equation4176 G) : Equation3404 G
:= fun x y z =>
  let v0 := M z x
  let v1 := M y v0
  have h2 := R v0
  have h3 := R x
  have h4 := h v1 v0 v1
  have h5 := R v1
  have h6 := h v0 v1 v1
  have h7 := h v1 y v0
  have h8 := R y
  let v9 := M z v1
  have h10 := h y v0 v9
  have h11 := h v9 (M v0 v9) y
  have h12 := R v9
  have h13 := h z x x
  have h14 := S h13
  have h15 := R z
  have h16 := h x x z
  have h17 := h x z x
  have h18 := S h17
  have h19 := h x v0 x
  let v20 := M x v0
  have h21 := h v20 z x
  have h22 := h v0 v20 z
  have h23 := h z x v0
  have h24 := h z x y
  have h25 := S h24
  let v26 := M x y
  have h27 := h y v26 z
  have h28 := C (T (T (T (T (C (T (C h24 h15) (S h27)) h3) (C (T (T (T h27 (C h25 h15)) (C h23 h15)) (S h22)) h3)) (S h21)) (C (T h19 (C h18 h3)) h15)) (S h16)) h15
  have h29 := h x v0 z
  have h30 := S h19
  have h31 := h x z v1
  have h32 := h v1 v9 x
  have h33 := h x v1 v9
  have h34 := h (M x v1) z v1
  have h35 := h z x v1
  let v36 := M v0 v1
  have h37 := S h29
  have h38 := C (T (T (T h16 (C (T (C h17 h3) h30) h15)) h21) (C (T h22 (C (S h23) h15)) h3)) h15
  have h39 := C (T h38 h37) h3
  let v40 := M v26 z
  have h41 := T h4 (C (T (C (T (T (T h6 (C (S h7) h5)) (C (T (T (C h10 h8) (S h11)) (C h12 (T (C (T h13 (C (T (T (T (T h38 h37) h19) (C (T h18 h31) h3)) (S h32)) h3)) h12) (S h33)))) h5)) (S h34)) h5) (S h35)) h5)
  T (T (T (h x y v1) (h (M (M y v1) x) v1 v0)) (C (T (T (T (C h41 (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T (T (h y v1 v0) (C (T (T (C h41 h8) (C (C h24 h5) h8)) (S (h v1 v40 y))) h2)) (S (h v40 y v0))) h25) h13) h39) (C (h x v0 v1) h3)) (S (h v1 v36 x))) (h v1 v36 y)) (C (S (h y v0 v1)) h8)) (C (h y v0 v0) h8)) (S (h v0 (M v0 v0) y))) (C h2 (T (C (T h13 h39) h2) (S (h x x v0))))) h3) (S (h (M x x) z x))) h38) h37)) (h v36 v20 x)) (C (C (T (C (T h29 h28) h3) h14) (T (C (T h35 (C (T (T (T h34 (C (T (T (C h12 (T h33 (C (T (C (T (T (T (T h32 (C (T (S h31) h17) h3)) h30) h29) h28) h3) h14) h12))) h11) (C (S h10) h8)) h5)) (C h7 h5)) (S h6)) h5)) h5) (S h4))) h3)) (S (h (M v1 v0) z x))) h2)) (S (h z v1 v0))

theorem Equation3131_implies_Equation759 (G: Type _) [Magma G] (h: Equation3131 G) : Equation759 G
:= fun x y z =>
  let v0 := M y x
  let v1 := M v0 z
  let v2 := M z v1
  let v3 := M y v2
  have h4 := h v3 v2 v0
  have h5 := S h4
  have h6 := R v1
  have h7 := h z v0 v0
  have h8 := h v0 v1 v0
  have h9 := T h8 (C (S h7) h6)
  have h10 := T (C h7 h6) (S h8)
  have h11 := R v0
  have h12 := R v3
  have h13 := h v2 y y
  have h14 := C (S h13) h12
  have h15 := h y v3 y
  have h16 := C (T h15 h14) h11
  have h17 := C h16 h10
  have h18 := S h15
  have h19 := C h13 h12
  have h20 := C (T h19 h18) h11
  have h21 := h y v3 v3
  have h22 := S h21
  have h23 := R y
  have h24 := R v2
  have h25 := C h17 h24
  have h26 := C (T h25 h5) h23
  have h27 := h v0 y v2
  have h28 := C (T (T (T (C (C (C (T h27 h26) h12) h12) h12) h22) h15) h14) h11
  have h29 := h v3 v0 v3
  have h30 := C (T (T h29 h28) h20) h9
  have h31 := C (T (T (T (T (T (C h30 h9) h25) h5) h29) h28) h20) h9
  have h32 := S h29
  have h33 := S h27
  have h34 := C h20 h9
  have h35 := C h34 h24
  have h36 := C (T h4 h35) h23
  have h37 := C (T (T (T h19 h18) h21) (C (C (C (T h36 h33) h12) h12) h12)) h11
  have h38 := C (T (T h16 h37) h32) h10
  have h39 := C h38 h10
  have h40 := h v3 y v3
  have h41 := h v0 v3 v0
  have h42 := S h41
  have h43 := C (T h30 (C (T (T (T (T (T h16 h37) h32) h4) h35) h39) h10)) h12
  have h44 := C (C (T (T (T h43 h42) h27) h26) h12) h12
  have h45 := h v0 v3 v3
  have h46 := C (T (T (T h43 h42) h45) h44) h12
  have h47 := C (T h46 h22) h12
  have h48 := C (T h31 h38) h12
  have h49 := C (C (T (T (T h36 h33) h41) h48) h12) h12
  have h50 := C (T (T (T (T (C (T h45 (C (T h46 (C (T h49 h47) h12)) h12)) h23) (S h40)) h4) h35) h39) h10
  have h51 := S h45
  have h52 := C (T (T (T h49 h51) h41) h48) h12
  have h53 := C (T (C (T h21 h52) h12) h44) h12
  have h54 := R x
  T (T (h x v0 v3) (C (T (T (T (T (T (T (T (C (T (T (T (C (C (T (h v0 x v0) (C (T (T (C (C (T (T (T (C (h x y y) h11) (S (h y v0 y))) h15) h14) h11) h11) h34) h38) h54)) h54) h12) (S (h v0 v3 x))) h45) h47) h12) h53) h22) (h y v0 v2)) (C (T (T (T (T (C (T h50 h31) h24) h25) h5) h40) (C (T (C (T h53 h52) h12) h51) h23)) h9)) h50) h31) h17) h9)) h5

theorem Equation871_implies_Equation2 (G: Type _) [Magma G] (h: Equation871 G) : Equation2 G
:= fun x y =>
  let v0 := M x y
  let v1 := M x x
  let v2 := M v1 v0
  let v3 := M y y
  have h4 := R v3
  let v5 := M v1 v1
  have h6 := h x v5 x
  have h7 := S h6
  let v8 := M v3 v3
  have h9 := h x v5 (M v3 (M y x))
  have h10 := S h9
  have h11 := h y x x
  have h12 := R v1
  have h13 := R v5
  have h14 := C h13 (C h12 h11)
  have h15 := R y
  have h16 := C h13 (C h12 (S h11))
  have h17 := h x v5 v5
  have h18 := S h17
  have h19 := h x x x
  have h20 := C h13 (C h12 h19)
  have h21 := R x
  have h22 := h v1 y x
  have h23 := S h22
  have h24 := C h12 (S h19)
  have h25 := C h13 h24
  have h26 := T h17 h25
  have h27 := C h15 h26
  have h28 := T h27 h23
  have h29 := h x v2 y
  have h30 := S h29
  have h31 := C h30 h21
  have h32 := R (M v2 v2)
  have h33 := C h32 h30
  have h34 := C (T h7 h29) h29
  have h35 := R (M v5 v5)
  have h36 := C h35 h7
  have h37 := C (T (T h20 h18) h6) h6
  have h38 := T h20 h18
  have h39 := R (M v5 (M v1 x))
  have h40 := C h39 h38
  have h41 := T (T h7 h17) h25
  have h42 := C h41 h7
  have h43 := C h35 h6
  have h44 := T h30 h6
  have h45 := C h44 h30
  have h46 := C h32 h29
  have h47 := C h29 h21
  have h48 := C h39 h26
  have h49 := T (T (T (C (T (T (T (T (T (T (T h27 h23) h47) h46) h45) h43) h42) h48) (T (T (T (T (T (T h27 h23) h47) h46) h45) h43) h42)) (C (T h40 h37) (T h37 h36))) (C (T h36 h34) (T h34 h33))) (C (T h33 h31) h31)
  have h50 := C h15 h38
  have h51 := T h22 h50
  have h52 := C h51 h21
  have h53 := T (T (T (C (T h47 h46) h47) (C (T h45 h43) (T h46 h45))) (C (T h42 h48) (T h43 h42))) (C (T (T (T (T (T (T (T h40 h37) h36) h34) h33) h31) h22) h50) (T (T (T (T (T (T h37 h36) h34) h33) h31) h22) h50))
  T (T (h x v1 v5) (C h12 (T (T (T (T (T (T h24 h52) (C h28 h6)) (S (h v1 v1 v1))) (h v1 v0 v1)) (C (T (T (T (T (T (T (T (C h29 h15) (C h44 h15)) (C h41 h15)) (C (T (T (T (T h20 h18) h9) h16) (C h53 (C h51 h15))) h15)) (C (T (T (T (T (T (C h49 (C h28 h15)) h14) h10) h17) h25) (C h53 h52)) h15)) (C (T (T (T (T (C h49 (C h28 h21)) h20) h18) h9) h16) h15)) (C (T h14 h10) (T (h y v8 v5) (C (R v8) (C h4 (S (h x y x))))))) (S (h v3 x x))) h7)) (C h4 (h x y y))))) (S (h y v1 v2))

theorem Equation3552_implies_Equation355 (G: Type _) [Magma G] (h: Equation3552 G) : Equation355 G
:= fun x y z w =>
  let v0 := M x y
  let v1 := M w y
  have h2 := h z v1 v0
  let v3 := M z v0
  let v4 := M v3 v1
  let v5 := M z v1
  have h6 := h v1 y v5
  have h7 := S h6
  have h8 := R y
  have h9 := h z v1 v1
  have h10 := S h9
  have h11 := R v1
  have h12 := h z v1 x
  have h13 := h v1 v1 (M (M z x) v1)
  have h14 := C h11 (T (T h13 (C h11 (C (S h12) h11))) h10)
  have h15 := h w v1 y
  have h16 := h w v1 v1
  have h17 := S h16
  have h18 := h w y y
  have h19 := S h18
  have h20 := h w y x
  have h21 := C h8 (C (S h20) h8)
  have h22 := h y y (M (M w x) y)
  have h23 := h y y (M (M x x) y)
  have h24 := S h23
  have h25 := h x y x
  have h26 := C h8 (C h25 h8)
  have h27 := h x y y
  have h28 := T (T (T (T (T h27 h26) h24) h22) h21) h19
  have h29 := R (M w v1)
  have h30 := C h28 (C h29 h28)
  have h31 := h w v0 v1
  have h32 := C h8 (C (T (T (T (T h31 h30) h17) h15) h14) h8)
  have h33 := h w y v0
  have h34 := T (T h33 h32) h7
  let v35 := M v5 v1
  have h36 := h y (M v1 y) y
  have h37 := S h36
  have h38 := S h22
  have h39 := C h8 (C h20 h8)
  have h40 := C (T (T h18 h39) h38) h34
  have h41 := S h13
  have h42 := C h11 (C h12 h11)
  have h43 := S h27
  have h44 := C h8 (C (S h25) h8)
  have h45 := T (T (T (T (T h18 h39) h38) h23) h44) h43
  let v46 := M z y
  have h47 := S h33
  have h48 := S h15
  have h49 := C h8 (C (T (T (T (T (C h11 (T (T h9 h42) h41)) h48) h16) (C h45 (C h29 h45))) (S h31)) h8)
  have h50 := T (T h6 h49) h47
  have h51 := C h50 (C (T (T h22 h21) h19) h50)
  T (T (T (T (T (T (T (T (T (T h27 h26) h24) h22) h21) h36) h51) h14) (C (T (T (T (T (T (T h18 h36) h51) h48) (h w v1 v5)) (C h11 (C (T (h w v5 v5) (C (T (T (T (h z v1 y) (C h34 (R (M v46 v1)))) (C (T (T (T (T (T (T (T (T h6 h49) h47) h18) h39) h38) h23) h44) h43) (C (R v46) h45))) (S (h z v0 y))) (T (T (C (T (h w v5 v0) (C (R v5) (T (T (C (T (T (T (T (T (T (T (T (T h31 h30) h17) h15) (C h34 h40)) h37) h19) h33) h32) h7) (T (T (T h9 h42) h41) h40)) h37) h19))) (T h9 (C h34 (R v35)))) (S (h v1 v35 y))) h10))) h11))) (S (h v3 v1 v5))) (T h2 (C h34 (R v4))))) (S (h v1 v4 y))) (S h2)

end EquationalTheories
