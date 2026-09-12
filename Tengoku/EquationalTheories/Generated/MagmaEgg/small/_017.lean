-- Tengoku.EquationalTheories.Generated.MagmaEgg.small._017: verified translations of equational_theories/Generated/MagmaEgg/small/_017.lean (2 theorems)
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

theorem Equation4176_implies_Equation4640 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4640 G
:= fun x y z =>
  let v0 := M x y
  let v1 := M y z
  have h2 := R v0
  have h3 := R v1
  let v4 := M v0 x
  have h5 := R v4
  have h6 := R z
  have h7 := h x y v0
  have h8 := S h7
  let v9 := M y v0
  have h10 := h v9 x y
  have h11 := S h10
  have h12 := R y
  have h13 := h v0 v9 x
  have h14 := S h13
  have h15 := R x
  have h16 := C h7 h15
  have h17 := h y v0 v0
  have h18 := h v0 x y
  have h19 := T (C h18 h2) (S h17)
  have h20 := C h19 h15
  have h21 := h v0 v0 x
  have h22 := C (T h21 h20) h2
  let v23 := M v0 v0
  have h24 := h v23 v0 x
  have h25 := S h21
  have h26 := C (T h17 (C (S h18) h2)) h15
  have h27 := C (T h16 h14) h12
  have h28 := h x x y
  have h29 := h x x v4
  have h30 := S h29
  have h31 := h x v4 v0
  have h32 := S h31
  have h33 := C h21 h2
  let v34 := M v1 z
  have h35 := h v23 v0 v34
  have h36 := S h35
  have h37 := R v34
  have h38 := R (M v0 v34)
  have h39 := C (C h38 (T (T (T (T h28 h27) h11) h26) h25)) h37
  let v40 := M x x
  have h41 := h v40 v0 v34
  have h42 := C (T (T (T (T h41 h39) h36) h33) h32) h15
  let v43 := M v40 v0
  have h44 := h v43 x y
  have h45 := S h44
  have h46 := R v43
  have h47 := C h25 h2
  have h48 := T (T (T h31 h47) h22) h8
  have h49 := S h41
  have h50 := S h28
  have h51 := C h8 h15
  have h52 := C (T h13 h51) h12
  have h53 := C (C h38 (T (T (T (T h21 h20) h10) h52) h50)) h37
  have h54 := C (T h26 h25) h2
  have h55 := T (T (T h7 h54) h33) h32
  have h56 := h v0 x x
  have h57 := C (T (T (T (T (T (T (T (T (C (T h56 h42) h5) h30) h28) h27) h11) h26) h25) (C h55 (T (T (T (T h7 h54) h35) h53) h49))) (C h48 h46)) h12
  have h58 := h y v4 v4
  have h59 := h v4 (M y v4) x
  have h60 := h x y v4
  have h61 := C (T (T (T (C (T (T (C h60 h15) (S h59)) (C h5 (T (T (T (T (T (T (T h58 (C (T (T h57 h45) h42) h5)) h30) h28) h27) h11) h26) h25))) h15) (S h24)) h22) h8) h15
  have h62 := h x v0 x
  have h63 := C (T (T (T h62 h61) h16) h14) h12
  have h64 := C (T h63 h11) h2
  have h65 := h y x v0
  have h66 := T (T h65 h64) h8
  have h67 := S h56
  have h68 := h v43 x v34
  have h69 := R (M x v34)
  let v70 := M y x
  have h71 := h v70 x v34
  have h72 := S h65
  have h73 := S h62
  have h74 := C (T (T (T (T h31 h47) h35) h53) h49) h15
  have h75 := C (T (T h74 h44) (C (T (T (T (T (T (T (T (T (C h55 h46) (C h48 (T (T (T (T h41 h39) h36) h22) h8))) h21) h20) h10) h52) h50) h29) (C (T h74 h67) h5)) h12)) h5
  have h76 := C (T (T (C h5 (T (T (T (T (T (T (T h21 h20) h10) h52) h50) h29) h75) (S h58))) h59) (C (S h60) h15)) h15
  have h77 := C (T (T (T h7 h54) h24) h76) h15
  have h78 := C (T h10 (C (T (T (T h13 h51) h77) h73) h12)) h2
  have h79 := T (T (T h56 h68) (C (C h69 (T (T (T (T (T h41 h39) h36) h22) h78) h72)) h37)) (S h71)
  have h80 := T h62 h61
  let v81 := M x v0
  T (T (T (T (h v0 x v0) (C (C h80 h2) h2)) (C h19 h2)) (C (T (h y v0 v1) (C (T (T (T (T (S (h v1 x y)) (h v1 x v4)) (C (T (C (T (T (T (T h31 h47) h24) h76) (C (T (C (h x y z) h15) (S (h z v1 x))) h15)) h3) (S (h x z v1))) h5)) (C (T (h x z z) (C (T (T (T (T (T (C (T (T (T (T (T (T (T (h z z y) (C (T (C (T (h z y x) (C (C h66 h6) h15)) h6) (S (h x v0 z))) h12)) h63) h52) h50) h29) h75) (C (T (T h57 h45) h67) (T h77 h73))) h15) (S (h v81 v0 x))) (h v81 v0 v4)) (C (T (T (T (T (T (T (C (T (C (T (T h7 h78) h72) h5) (C (T (T (T (T h65 h64) h54) h33) h32) h79)) h80) (S (h (M v70 x) x v4))) (S (h x y x))) h7) h54) h33) h32) h79)) (C (T (T (T (T h31 h47) h22) h78) h72) (T (T (T h71 (C (C h69 (T (T (T (T (T h65 h64) h54) h35) h53) h49)) h37)) (S h68)) h67))) (C h66 h5)) h6)) h5)) (S (h z v0 v4))) h3)) h2)) (S (h v1 z v0))

theorem Equation2789_implies_Equation2319 (G: Type _) [Magma G] (h: Equation2789 G) : Equation2319 G
:= fun x y z =>
  have h0 := R y
  let v1 := M z z
  let v2 := M x v1
  let v3 := M x z
  have h4 := h v2 (M (M x v2) v3) v2
  have h5 := S h4
  have h6 := R v2
  have h7 := h z x v2
  have h8 := C (C h7 h7) h6
  let v9 := M v1 v2
  have h10 := h v9 v2 x
  have h11 := S h10
  have h12 := R x
  have h13 := T h8 h5
  have h14 := R v1
  have h15 := C h14 h13
  have h16 := C h13 h15
  have h17 := S h7
  have h18 := C (C h17 h17) h6
  have h19 := T h4 h18
  have h20 := C h14 h19
  have h21 := T (T h4 h18) h20
  have h22 := h v9 v1 v1
  have h23 := S h22
  have h24 := h v1 (M v2 v3) v1
  have h25 := S h24
  have h26 := h z x v1
  have h27 := C (C h26 h26) h14
  have h28 := T h27 h25
  have h29 := S h26
  have h30 := C (C h29 h29) h14
  have h31 := T h24 h30
  have h32 := C h31 h20
  have h33 := C (T h20 h32) h28
  have h34 := C (T h33 h23) h21
  have h35 := h v1 v1 v2
  have h36 := T (T h35 h34) h16
  have h37 := S h35
  have h38 := C h28 h15
  have h39 := C (T h38 h15) h31
  have h40 := C (T h22 h39) (T (T h15 h8) h5)
  have h41 := C h19 h20
  have h42 := T (T h41 h40) h37
  have h43 := C h6 h19
  have h44 := C (T (T (T h43 h41) h40) h37) h42
  let v45 := M v2 v2
  have h46 := R v45
  have h47 := C h46 h43
  let v48 := M (M y v2) y
  have h49 := h (M v45 v45) v2 v48
  have h50 := S h49
  have h51 := R v48
  have h52 := C h6 h13
  have h53 := C h46 h52
  have h54 := C (T (T (T h35 h34) h16) h52) h36
  have h55 := C (T (T (T h38 h15) h8) h5) (T (T (T h24 h30) h54) h53)
  have h56 := h v48 (M (M x v48) v3) v48
  have h57 := h z x v48
  have h58 := h v48 v1 v2
  have h59 := C (T h58 (C (C h13 (T (C (C h57 h57) h51) (S h56))) (T (T (T h4 h18) h22) h55))) h51
  let v60 := M v48 v48
  have h61 := h v60 v2 v1
  have h62 := S h61
  have h63 := C (T (T (T h4 h18) h20) h32) (T (T (T h47 h44) h27) h25)
  have h64 := S h57
  have h65 := C (T (C (C h19 (T h56 (C (C h64 h64) h51))) (T (T (T h63 h23) h8) h5)) (S h58)) h51
  have h66 := T (T (T (T h4 h18) h22) h55) (C h6 (T h49 h65))
  have h67 := h v9 v2 v2
  have h68 := C h6 (T h59 h50)
  have h69 := T (T (T (T h68 h63) h23) h8) h5
  have h70 := h v60 v2 v2
  have h71 := C (T (T (T (T (T (T (T h24 h30) h54) h53) h49) h65) h70) (C (T (T (T (T (C (T (T (T (T (T (T h43 h41) h40) h37) h24) h30) h54) h69) (S h67)) h22) h39) (C h13 h28)) h66)) (T (T (T (T (T h59 h50) h47) h44) h27) h25)
  have h72 := h x (M (M x x) v3) x
  have h73 := h z x x
  have h74 := T (C (C h73 h73) h12) (S h72)
  have h75 := C (C h74 (T (T (T (T (T (T (T h71 h62) h59) h50) h47) h44) h27) h25)) h12
  have h76 := h v60 v1 x
  have h77 := T h71 h62
  have h78 := C (T (T (T (T (C h28 h77) h71) h62) h76) h75) h36
  have h79 := h v60 v1 v1
  have h80 := C (T (T (T (T (T (T (T h24 h30) h54) h53) h49) h65) h79) h78) h12
  let v81 := M v1 x
  have h82 := C (T (T (T (T (T (T (T (C (T (T (T (T (C h19 h31) h33) h23) h67) (C (T (T (T (T (T (T h44 h27) h25) h35) h34) h16) h52) h66)) h69) (S h70)) h59) h50) h47) h44) h27) h25) (T (T (T (T (T h24 h30) h54) h53) h49) h65)
  have h83 := S h76
  have h84 := S h73
  have h85 := C (C h84 h84) h12
  have h86 := C (C (T h72 h85) (T (T (T (T (T (T (T h24 h30) h54) h53) h49) h65) h61) h82)) h12
  have h87 := C (T (T (T (T (T (T (T (C (T (T (T (T h86 h83) h61) h82) (C h31 (T h61 h82))) h42) (S h79)) h59) h50) h47) h44) h27) h25) h12
  have h88 := h z x y
  T (T (T h72 h85) (h v81 v1 y)) (C (C (T (C (C h88 h88) h0) (S (h y (M (M x y) v3) y))) (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T h24 h30) h54) h53) h49) h65) h79) h78) (C (T (T (T (T (T (T (T (T (T (T (T h86 h83) h59) h50) h47) h44) h27) h25) h35) h34) h16) h52) (T (T (T (T (T (T (T (T (T (T (T h41 h40) h37) h24) h30) h54) h53) h49) h65) (h v60 v1 v2)) (C (T (T (T (T (T (C h13 h77) h68) h63) h23) h10) h87) h21)) (C (T (T (T h80 h11) h8) h5) (T (T h15 h10) h87))))) (C (T (T (T (T (T (T (T (T (T (T (T h43 h41) h40) h37) h24) h30) h54) h53) h49) h65) h76) h75) (R (M v2 v81)))) h74) (S (h v81 v2 x))) h80) h11) h8) h5)) h0)

end EquationalTheories
