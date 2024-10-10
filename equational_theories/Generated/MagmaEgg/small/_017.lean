import equational_theories.Equations.All
import equational_theories.Magma

private def congr_op {G: Type _} [Magma G] {a b c d: G} (h1: a = b) (h2: c = d): a ◇ c = b ◇ d := by
  rw [h1, h2]
private abbrev T := @Eq.trans
private abbrev S := @Eq.symm
private abbrev R := @Eq.refl
private abbrev M := @Magma.op
private abbrev C := @congr_op

@[equational_result]
theorem Equation4176_implies_Equation4640 (G: Type _) [Magma G] (h: Equation4176 G) : Equation4640 G := fun x y z =>
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

@[equational_result]
theorem Equation2789_implies_Equation2319 (G: Type _) [Magma G] (h: Equation2789 G) : Equation2319 G := fun x y z =>
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

@[equational_result]
theorem Equation3599_implies_Equation41 (G: Type _) [Magma G] (h: Equation3599 G) : Equation41 G := fun x y z =>
  have h0 := h y z y
  have h1 := S h0
  let v2 := M y z
  let v3 := M z y
  let v4 := M v3 y
  have h5 := S (h y v4 v2)
  let v6 := M v4 y
  have h7 := S (h v6 y x)
  have h8 := R v6
  let v9 := M x x
  have h10 := h y v3 v9
  have h11 := S h10
  have h12 := R x
  have h13 := C h12 (C (T h11 (h y v3 y)) h8)
  have h14 := h v6 v9 x
  have h15 := h x x v9
  have h16 := S h15
  let v17 := M v9 x
  have h18 := R v17
  have h19 := h x x x
  have h20 := T (C (S h19) h18) h16
  have h21 := C h8 h20
  have h22 := h v17 x v6
  have h23 := R v2
  have h24 := h x x v2
  have h25 := C h12 (T (C (S h24) h18) h16)
  have h26 := h v17 v2 x
  have h27 := h y z v2
  have h28 := S h27
  have h29 := R v4
  have h30 := C h28 h29
  have h31 := T h30 h28
  let v32 := M v6 y
  have h33 := R z
  have h34 := h v17 x x
  have h35 := T h15 (C h19 h18)
  have h36 := C h12 h20
  have h37 := h v17 x v4
  have h38 := S h37
  have h39 := C h29 h35
  have h40 := h v4 v9 x
  have h41 := S h40
  have h42 := h y z v9
  have h43 := C h12 (T h30 (C h42 h29))
  have h44 := C h27 h29
  have h45 := h y z z
  have h46 := S h45
  have h47 := C h12 (T (C h46 h29) h44)
  have h48 := h v4 z x
  let v49 := M y v3
  have h50 := h z v4 v2
  have h51 := S h50
  have h52 := C h12 (T (C h1 h29) h44)
  have h53 := h v4 y x
  have h54 := h v6 z v6
  have h55 := h y v3 z
  have h56 := h y v3 x
  have h57 := C (T (S h56) h10) h8
  have h58 := C (T h11 h56) h8
  have h59 := C h8 h58
  have h60 := h v6 v9 v6
  have h61 := T (T (T (T (T (T (T (T (T (T (T (T h53 h52) h43) h41) h39) h38) h22) h21) h60) h59) (C h8 (T h57 (C (T h11 h55) h8)))) (S h54)) (C (T (T (T h53 h52) (C h12 (T h30 (C h45 h29)))) (S h48)) h33)
  have h62 := C h23 h61
  have h63 := h y v3 v2
  have h64 := T (T (T h63 h62) h51) h46
  have h65 := S h53
  have h66 := C h12 (T h30 (C h0 h29))
  have h67 := C h12 (T (C (S h42) h29) h44)
  have h68 := C h29 h20
  have h69 := S h22
  have h70 := C h8 h35
  have h71 := S h60
  have h72 := C h8 h57
  have h73 := T (T (T h45 h50) (C h23 (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T h48 h47) h66) h65) h33) h54) (C h8 (T (C (T (S h55) h10) h8) h58))) h72) h71) h70) h69) h37) h68) h40) h67) h66) h65))) (S h63)
  have h74 := h z y v2
  have h75 := h v2 (M v2 z) v2
  have h76 := C (T (T (T (T h11 h63) h62) h51) h46) h61
  have h77 := h v2 z v2
  have h78 := S h77
  have h79 := h y z x
  have h80 := C (S h79) h29
  have h81 := h v4 v2 z
  have h82 := h v4 v2 x
  have h83 := h v4 x v6
  have h84 := h v4 x x
  have h85 := C h79 h29
  have h86 := C h12 (T h80 h44)
  have h87 := C h23 (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T h84 h86) h66) h65) h12) (h v6 x v6)) h72) h71) h70) h69) h37) h68) h40) h67) (C h12 (T h30 h85))) (S h84)) h83) (C (T (T (T (T h53 h52) (S h82)) h81) (C h33 h31)) (T h80 h28)))
  have h88 := h x v4 v2
  have h89 := C h23 (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (C h33 (T h27 h44)) (S h81)) h82) h66) h65) (T h27 h85)) (S h83)) h84) h86) h43) h41) h39) h38) h22) h21) h60) h59) (C (T (T (T (T (T (T (T (T (T h53 h52) h43) h41) h39) h38) h22) h21) (h v6 v9 v2)) (C (T (T (T h79 h88) h87) h78) (T (T h76 h51) h46))) (T (T (T h57 h76) h51) h46)))
  have h90 := C h23 (C (C (T (T (T h77 h89) (S h75)) (S h74)) h73) h73)
  T (T (T (T (T (T (T (T (T (T (T (T (T (T h24 (h v2 v17 v9)) (C (R v9) (C (T (T (T h26 h25) (h x v9 z)) (C h33 (T h34 h36))) (T (T (T (T (T (T (T (T (T (T (T (T h79 h88) h87) h78) (C (T (T (T (T (T (T (T h79 h88) h87) h89) h90) (C h23 (C (C (T (T (T h74 h75) h90) (S (h v49 v3 v2))) h64) h64))) (S (h v2 (M v49 v3) v2))) (S (h v3 y v2))) h33)) h48) h47) h43) h41) h39) h38) h34) h36)))) (S (h (M x v9) z v9))) (C (T (T (T (T (T (T (C h12 h35) (S h34)) h22) h21) h14) h13) h7) h33)) (h v32 z v4)) (C h29 (T (T (C (T (S (h y v4 z)) h1) (R v32)) h5) h1))) (h v4 v2 v17)) (C h18 h31)) h26) h25) (h x v9 v2)) (C h23 (T (T (T (T h22 h21) h14) h13) h7))) h5) h1

@[equational_result]
theorem Equation3959_implies_Equation4200 (G: Type _) [Magma G] (h: Equation3959 G) : Equation4200 G := fun x y z =>
  let v0 := M z x
  let v1 := M v0 z
  have h2 := h v1 y z
  have h3 := S h2
  have h4 := S (h (M y (M v1 z)) z z)
  have h5 := R z
  have h6 := C h5 h2
  let v7 := M v1 y
  have h8 := R v7
  have h9 := h z x v7
  let v10 := M z v7
  have h11 := R x
  let v12 := M x v0
  have h13 := R v12
  have h14 := h v1 y v7
  let v15 := M y (M v1 v7)
  have h16 := R v1
  have h17 := h v1 y x
  have h18 := h y (M v1 x) v7
  let v19 := M y v7
  have h20 := R v19
  have h21 := h v0 z v1
  have h22 := S h21
  have h23 := h v0 z x
  let v24 := M v0 v1
  let v25 := M z v24
  have h26 := R v25
  have h27 := C (T (C h26 (S h23)) h22) h11
  let v28 := M v0 x
  have h29 := h (M z v28) v25 x
  have h30 := h z v28 x
  have h31 := R v0
  have h32 := h z x v0
  have h33 := S h32
  have h34 := h (M x (M z v0)) v0 v0
  let v35 := M v0 v0
  have h36 := h z v35 x
  have h37 := h (M z v35) v0 v0
  have h38 := S h37
  have h39 := h v0 z v0
  have h40 := C (C h31 h39) h31
  have h41 := h z v24 x
  have h42 := C (T (T h41 (C (T (T h40 h38) (C (T h36 (C (T (T (C (C h31 h32) h31) (S h34)) h33) h11)) h31)) h11)) (S h30)) h26
  have h43 := h v25 v25 v1
  have h44 := S h43
  have h45 := C (T h21 (C h26 h21)) h16
  have h46 := T (T (T (T h45 h44) h42) h29) h27
  have h47 := h y (M v1 v1) v7
  have h48 := T (T h47 (C (C h46 h20) h8)) (S h18)
  have h49 := C (T (C h26 h22) h22) h16
  have h50 := S h41
  have h51 := S h39
  have h52 := C (C h31 h51) h31
  have h53 := C (T (T h30 (C (T (T (C (T (C (T (T h32 h34) (C (C h31 h33) h31)) h11) (S h36)) h31) h37) h52) h11)) h50) h26
  have h54 := S h29
  have h55 := C (T h21 (C h26 h23)) h11
  have h56 := T (T h18 (C (C (T (T (T (T h55 h54) h53) h43) h49) h20) h8)) (S h47)
  have h57 := h v1 y v0
  have h58 := S h57
  have h59 := h (M y (M v1 v0)) v0 v0
  have h60 := R y
  let v61 := M x y
  let v62 := M v0 v61
  have h63 := h x y v0
  have h64 := R v61
  have h65 := h v1 y v1
  have h66 := h v1 y v61
  have h67 := S h66
  let v68 := M y (M v1 v61)
  have h69 := h v1 v61 y
  have h70 := h x y v7
  let v71 := M y (M x v7)
  let v72 := M z v61
  have h73 := h x y z
  have h74 := C h5 (S h73)
  have h75 := h (M y (M x z)) z z
  have h76 := h z x v61
  T (T (T (T (T (T (T (T (T (T h73 h75) (C (T (T (T (T h74 (h z v61 x)) (C (T (C h64 h76) (C h64 (T (S h76) (h z x x)))) h11)) (S (h v12 v61 x))) (C h13 (T (T h73 h75) (C h74 h5)))) h5)) (S (h v72 v12 z))) (h v72 v12 v7)) (C (C h13 (T (T (T (T (T (T (C (C h5 h70) h8) (S (h v71 z v7))) (h v71 z v1)) (C (C h5 (T (T (T (h v71 v1 v7) (C (C h16 (S h70)) h8)) (C (T (T (T (T (T (T (T (T (T (T h69 (C (C h64 h66) h60)) (h (M v61 (M v68 v61)) y y)) (C (C h60 (T (C (C h64 h67) h60) (S h69))) h60)) (h v68 y v61)) (C (C h60 h67) h64)) (h v19 v61 x)) (C (T (T (T (T (T (T (C h64 (T (T (T (T (T (T (T (h v19 x y) (C (T (C h11 (T (T (S (h v1 y y)) h65) (C h48 h16))) (C h11 (T (C h56 h16) (S h65)))) h60)) (S (h v1 x y))) h55) h54) h53) h43) h49)) (C h64 (T (T (T (T (T (T h45 h44) h42) h29) h27) (C (T (T h39 h37) h52) h11)) h50))) (h v61 v25 x)) (C (C h26 (T (T (h v61 x x) (C (T (T (T (T (T (C h11 (T (C (T (T h63 (h (M y v12) v0 v0)) (C (C h31 (S h63)) h31)) h11) (S (h z v62 x)))) (h x (M z v62) y)) (C (S (h v0 z v61)) h60)) h57) h59) (C (C h31 h58) h31)) h11)) (C (T (T (C (C h31 h57) h31) (S h59)) h58) h11))) h11)) (S (h v7 v25 x))) (C h8 (T (T (T (T (T (T h41 (C (T (T h40 h38) h51) h11)) h55) h54) h53) h43) h49))) (C h8 h46)) h11)) (S (h v1 v7 x))) (C h16 (T h17 (C h56 h11)))) (C h16 (T (T (C h48 h11) (S h17)) h14))) h8)) (S (h v15 v1 v7)))) h16)) (S (h v15 z v1))) (h v15 z v7)) (C (C h5 (S h14)) h8))) h8)) (S (h v10 v12 v7))) (h v10 v12 z)) (C (T (T (T (T (C h13 (T (T (C h6 h5) h4) h3)) (C (C h11 (T (T h9 (h (M x v10) v7 v7)) (C (C h8 (S h9)) h8))) h8)) (S (h (M v7 v0) x v7))) (S (h z v7 x))) h6) h5)) h4) h3

@[equational_result]
theorem Equation522_implies_Equation2279 (G: Type _) [Magma G] (h: Equation522 G) : Equation2279 G := fun x y z =>
  let v0 := M z y
  let v1 := M y v0
  let v2 := M x v1
  let v3 := M v2 z
  have h4 := R v3
  have h5 := R v2
  have h6 := C h5 (T (h z v3 v3) (C h4 (S (h v2 v3 z))))
  have h7 := h z v1 y
  have h8 := S h7
  have h9 := h v1 v0 v0
  have h10 := S h9
  have h11 := h v0 v0 z
  have h12 := S h11
  have h13 := R v0
  have h14 := h z v0 y
  have h15 := S h14
  have h16 := C h13 (T h15 h7)
  have h17 := h y v0 v0
  have h18 := R z
  have h19 := C h13 (C h13 (C h18 (T (T h17 h16) (C h13 h8))))
  have h20 := h v1 v3 y
  have h21 := S h20
  have h22 := h y v1 v0
  have h23 := S h22
  have h24 := R v1
  have h25 := C h24 h23
  have h26 := h v0 v1 v1
  have h27 := R y
  have h28 := C h27 (T h26 h25)
  have h29 := C h4 (C h4 h28)
  have h30 := h z v3 y
  have h31 := T (T h30 h29) h21
  have h32 := C h31 (T h19 h12)
  have h33 := S h17
  have h34 := C h13 (T h8 h14)
  have h35 := C h13 (C h13 (C h18 (T (T (C h13 h7) h34) h33)))
  have h36 := h v0 z v1
  have h37 := S h36
  let v38 := M v0 v1
  have h39 := R (M v1 v38)
  have h40 := S h30
  have h41 := S h26
  have h42 := C h24 h22
  have h43 := C h27 (T h42 h41)
  have h44 := C h4 (C h4 h43)
  have h45 := T (T h20 h44) h40
  have h46 := C h13 (T (T (T h20 h44) h40) h7)
  have h47 := C h45 (T (T (T (T h46 h34) h33) h22) (C h45 h39))
  have h48 := R v38
  have h49 := C h31 h48
  have h50 := C h18 (T (T (T (T h49 h47) h37) h11) h35)
  have h51 := h y z v0
  have h52 := h y y v0
  have h53 := S h52
  have h54 := C h13 (T (T (T h8 h30) h29) h21)
  have h55 := C h27 (C h27 (T (T h17 h16) h54))
  have h56 := C h13 (T (T (T (T h55 h53) h51) h50) h32)
  have h57 := h y v0 y
  have h58 := C h13 (T (T (T h55 h53) h57) (C h13 h56))
  have h59 := C h27 (C h27 (T (T h46 h34) h33))
  have h60 := S h51
  have h61 := C h45 h48
  have h62 := C h31 (T (T (T (T (C h31 h39) h23) h17) h16) h54)
  have h63 := C h18 (T (T (T (T h19 h12) h36) h62) h61)
  have h64 := C h45 (T h11 h35)
  have h65 := C h13 (T (T (T (T h64 h63) h60) h52) h59)
  have h66 := C h13 (T (T (T (C h13 h65) (S h57)) h52) h59)
  have h67 := h v1 v1 v1
  have h68 := S h67
  have h69 := C h31 (C h24 h7)
  have h70 := C h45 (C h24 h8)
  have h71 := h z z y
  have h72 := R (M z v1)
  have h73 := T (T (T (T (T (T (C h45 h72) (S h71)) h30) h29) h21) h67) h70
  have h74 := C h31 h72
  have h75 := h z v0 v1
  have h76 := h y v1 y
  have h77 := S h76
  have h78 := C h31 (T (T (T (T h46 h34) h33) h52) h59)
  have h79 := h v0 y v1
  have h80 := C h13 (T (T h51 h50) h32)
  have h81 := C h24 (T (T (T (T (T (C h27 (T (T (T (T (T h80 h65) h58) h10) h28) (C h27 (T (T (T h42 h41) h36) h62)))) (S h79)) h36) h62) h61) h78)
  have h82 := R (M y (M v0 y))
  have h83 := C h31 h82
  have h84 := C h13 (T (T h64 h63) h60)
  have h85 := C h18 (T (T (C h27 h7) (C h27 (T (T (T (T (T (T h8 h30) h29) h21) h9) h66) h56))) (C h27 h84))
  have h86 := h y v0 z
  have h87 := h y v1 z
  have h88 := C h18 (T (T (C h27 h80) (C h27 (T (T (T (T (T (T h65 h58) h10) h20) h44) h40) h7))) (C h27 h8))
  have h89 := C h45 h82
  have h90 := C h45 (T (T (T (T h55 h53) h17) h16) h54)
  have h91 := C h24 (T (T (T (T (T h90 h49) h47) h37) h79) (C h27 (T (T (T (T (T (C h27 (T (T (T h47 h37) h26) h25)) h43) h9) h66) h56) h84)))
  have h92 := R (M y (M y y))
  T (T (T (h x v3 v2) (C h4 (C h4 (T (T (T (T (T (T (C h5 (T (T (S (h z x y)) h75) (C h13 (T (T (T (T (C h13 h73) (C h13 (T (T (T (T (T (T h69 h68) h20) h44) h40) h14) (C h13 (T (T (T (T (T (T h46 h34) h33) h76) h91) h89) h88))))) (S h86)) h87) (C h45 (T (T (T (T (T (C h45 (T (T (T (T (T h85 h83) h81) h77) h52) h59)) (C h31 h92)) h90) h49) h47) h37)))))) (C h5 (T (T (T (C h13 (T (T (T (T (C h31 (T (T (T (T (T h36 h62) h61) h78) (C h45 h92)) (C h31 (T (T (T (T (T h55 h53) h76) h91) h89) h88)))) (S h87)) h86) (C h13 (T (T (T (T (T (T (C h13 (T (T (T (T (T (T h85 h83) h81) h77) h17) h16) h54)) h15) h30) h29) h21) h67) h70))) (C h13 (T (T (T (T (T (T h69 h68) h20) h44) h40) h71) h74)))) (S h75)) h71) h74))) (C h5 h73)) (C h5 (T (T (T (T h69 h68) h9) h66) h56))) (C h5 (T (T h65 h58) h10))) (C h5 (T (T (h v1 v2 v1) (C h5 (C h5 h8))) (C h5 h6)))) (S (h v3 v2 v2)))))) (C h4 (C h4 h6))) (S (h v3 v3 v2))

@[equational_result]
theorem Equation1517_implies_Equation2 (G: Type _) [Magma G] (h: Equation1517 G) : Equation2 G := fun x y =>
  have h0 := h y x x
  have h1 := S h0
  let v2 := M y (M y x)
  have h3 := h v2 y x
  have h4 := S h3
  let v5 := M v2 (M v2 x)
  let v6 := M y y
  have h7 := h v6 y v5
  have h8 := S h7
  have h9 := R v6
  have h10 := h y y x
  have h11 := C h9 (T h10 (C h9 h3))
  have h12 := h v2 x x
  let v13 := M x x
  have h14 := R v13
  have h15 := T (C h14 (S h12)) h1
  have h16 := C h9 h15
  have h17 := h v13 y v5
  have h18 := T (T (T h17 h16) h11) h8
  have h19 := S h17
  have h20 := T h0 (C h14 h12)
  have h21 := C h9 h20
  have h22 := R y
  let v23 := M x v13
  have h24 := h v13 y (M v23 (M v23 x))
  have h25 := S h24
  have h26 := h v23 x x
  have h27 := h x x x
  have h28 := C h18 (T h27 (C h14 h26))
  have h29 := R x
  have h30 := h v13 x v5
  have h31 := S h30
  have h32 := C h14 h20
  have h33 := T h32 h31
  have h34 := C h33 h29
  let v35 := M v13 y
  have h36 := h v35 x x
  have h37 := S h36
  have h38 := C h14 h15
  have h39 := T h30 h38
  have h40 := C h39 h29
  have h41 := C h9 (T (C h9 h4) (S h10))
  have h42 := T (T (T h7 h41) h21) h19
  have h43 := C h42 (T (C h14 (S h26)) (S h27))
  have h44 := h v13 y v2
  have h45 := C h33 h22
  have h46 := h v35 x y
  have h47 := C h14 (T h46 (C h39 (T (T (T (T (C (T (T (T (T (T h32 h31) h17) h16) h11) h8) (T h45 (C h14 h0))) (S h44)) h24) h43) h40)))
  have h48 := T h47 h37
  have h49 := C h48 h29
  have h50 := C h39 h22
  have h51 := C h14 (T (C h33 (T (T (T (T h34 h28) h25) h44) (C (T (T (T (T (T h7 h41) h21) h19) h30) h38) (T (C h14 h1) h50)))) (S h46))
  have h52 := T (T (T (T (T h28 h25) h30) h38) h36) h51
  have h53 := C h52 h29
  let v54 := M v13 x
  have h55 := h v54 x x
  have h56 := S h55
  have h57 := T (T (T (T (T h47 h37) h32) h31) h24) h43
  have h58 := C h57 h29
  have h59 := T h36 h51
  have h60 := C h59 h29
  have h61 := h v13 x y
  have h62 := T h28 h25
  have h63 := T h24 h43
  have h64 := h v54 x y
  have h65 := C h14 (T h64 (C h63 (T (T (T (T (T (T (C h62 (T (T (T (T (C h52 h22) (C h48 h22)) h45) h36) h51)) (S h61)) h24) h43) h40) h60) h58)))
  have h66 := C (T h65 h56) h29
  have h67 := C h14 (T (C h62 (T (T (T (T (T (T h53 h49) h34) h28) h25) h61) (C h63 (T (T (T (T h47 h37) h50) (C h59 h22)) (C h57 h22))))) (S h64))
  have h68 := h v13 y x
  have h69 := S h68
  have h70 := C h9 (T (T (T (T (T h21 h19) h24) h43) h55) h67)
  have h71 := C (T (T (T (T (T h70 h69) h24) h43) h55) h67) h29
  have h72 := C h9 (T (T (T (T (T h65 h56) h28) h25) h17) h16)
  have h73 := C (T (T (T (T (T h7 h41) h21) h19) h68) h72) h29
  let v74 := M v6 x
  have h75 := h v74 x x
  have h76 := S h75
  have h77 := C (T (T (T (T (T h70 h69) h17) h16) h11) h8) h29
  have h78 := C (T (T (T (T (T h65 h56) h28) h25) h68) h72) h29
  have h79 := C (T h55 h67) h29
  have h80 := T (T (T (T (T (T (T (T (T (T (T h7 h41) h21) h19) h24) h43) h40) h60) h58) h79) h78) h77
  have h81 := C h80 h29
  have h82 := h v6 x y
  have h83 := T (T (T (T (T (T (T (T (T (T (T h73 h71) h66) h53) h49) h34) h28) h25) h17) h16) h11) h8
  have h84 := T (T (T (T (T (T (T h73 h71) h66) h53) h49) h34) h28) h25
  have h85 := T (T (T (T (T (T (T h24 h43) h40) h60) h58) h79) h78) h77
  have h86 := h v74 x y
  have h87 := C h42 (T h86 (C h85 (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C h84 (T (T (T (T (C h83 h22) h21) h19) h68) h72)) (S h82)) h7) h41) h21) h19) h24) h43) h40) h60) h58) h79) h78) h77) h81)))
  have h88 := T (T (T (T (T (T (T (T (T (T (T h87 h76) h73) h71) h66) h53) h49) h34) h28) h25) h17) h16
  have h89 := C h80 h22
  have h90 := C h83 h29
  have h91 := C h18 (T (C h84 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h90 h73) h71) h66) h53) h49) h34) h28) h25) h17) h16) h11) h8) h82) (C h85 (T (T (T (T h70 h69) h17) h16) h89)))) (S h86))
  have h92 := T h75 h91
  have h93 := T h17 h16
  let v94 := M v23 (M v23 y)
  T (T (T (T (T (h x y x) (C h9 (T (h v23 y y) (C h42 (h v94 x x))))) (S (h v13 y (M v94 (M v94 x))))) (h v13 v13 (M v5 (M v5 y)))) (C (T (T (T (T (C h93 (T (T (T (T (T (T (T (T (T (T h24 h43) h40) h60) h58) h79) h78) h77) h81) (C h92 h29)) (C h88 h29))) (C (T h21 h19) (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (T (C (T (T (T (T (T (T (T (T (T (T (T h21 h19) h24) h43) h40) h60) h58) h79) h78) h77) h75) h91) h29) (C (T h87 h76) h29)) h90) h73) h71) h66) h53) h49) h34) h28) h25) h17) h16) h11) h8) (h v6 x x)) (C h93 (T (T (T (T (T (T (T (T (T (T (T (T (T (T h87 h76) h73) h71) h66) h53) h49) h34) h28) h25) h17) h16) h89) (C h92 h22)) (C h88 h22)))))) (S (h (M v6 y) x y))) h21) h19) (T (C h18 (S (h v5 x y))) h4))) h1

@[equational_result]
theorem Equation522_implies_Equation2335 (G: Type _) [Magma G] (h: Equation522 G) : Equation2335 G := fun x y z =>
  let v0 := M x z
  let v1 := M y v0
  let v2 := M y v1
  let v3 := M v2 z
  have h4 := h v0 y x
  have h5 := S h4
  have h6 := h x v0 z
  have h7 := R v0
  have h8 := h z v0 v0
  have h9 := R x
  have h10 := R y
  have h11 := C h10 (C h10 (C h9 (T h8 (C h7 (S h6)))))
  have h12 := h v2 v3 z
  have h13 := S h12
  have h14 := R v3
  have h15 := C h14 (T (T h13 h11) h5)
  have h16 := h z v3 v3
  have h17 := C h7 (T h16 h15)
  have h18 := R z
  have h19 := T h11 h5
  have h20 := C h19 h18
  have h21 := R (M v0 (M v3 v0))
  have h22 := C h10 (C h10 (C h9 (T (C h7 h6) (S h8))))
  have h23 := T h4 h22
  have h24 := C h23 h21
  have h25 := h v3 v0 z
  have h26 := S h16
  have h27 := C h14 (T (T h4 h22) h12)
  have h28 := h v2 v1 v1
  have h29 := S h28
  have h30 := R v1
  have h31 := C h23 h30
  have h32 := C h30 h31
  have h33 := C h30 h32
  have h34 := h y v1 v0
  have h35 := h y v0 v2
  have h36 := R v2
  have h37 := h v1 v2 y
  have h38 := C h19 h30
  have h39 := C h30 (T (T (T (T h38 (C h7 (T h37 (C h19 (C h36 (C h10 (T (C h30 (T h34 h33)) h29))))))) (S h35)) h34) h33)
  have h40 := C h14 (T (T (T h39 h29) h11) h5)
  have h41 := C h14 (T (T h40 h27) h26)
  have h42 := h v2 v3 v1
  have h43 := C h19 (T (T (T (C h19 (C h19 (C h18 (T h42 h41)))) (S h25)) h20) h17)
  have h44 := h z v2 v2
  have h45 := S h34
  have h46 := C h30 h38
  have h47 := C h30 h46
  have h48 := C h30 (T (T (T (T h47 h45) h35) (C h7 (T (C h23 (C h36 (C h10 (T h28 (C h30 (T h47 h45)))))) (S h37)))) h31)
  have h49 := S h42
  have h50 := C h14 (T (T (T h4 h22) h28) h48)
  have h51 := C h14 (T (T h16 h15) h50)
  have h52 := C h23 h18
  have h53 := C h7 (T h27 h26)
  have h54 := C h36 (T (C h14 h12) h26)
  have h55 := C h36 (T h16 (C h14 h13))
  have h56 := C h7 h55
  have h57 := C h14 (T (T (T (T (T (T (T h56 (C h23 (T (T h54 h20) h17))) (C h19 h21)) (C h23 (T (T (T h53 h52) h25) (C h23 (C h23 (C h18 (T h51 h49))))))) (S h44)) h16) h15) h50)
  have h58 := C h7 h54
  have h59 := h v3 v3 v2
  have h60 := S h59
  have h61 := C h14 (C h14 h55)
  have h62 := C h14 (C h14 h54)
  have h63 := C h14 (T (T (C h19 (T h59 h62)) (C h7 (T (T h61 h60) h55))) h58)
  have h64 := C h14 (T (T (T (T h63 h57) h49) h28) h48)
  have h65 := C h14 (T (T h56 (C h7 (T (T h54 h59) h62))) (C h23 (T h61 h60)))
  have h66 := C h14 (T (T (T (T (T (T (T h40 h27) h26) h44) h43) h24) (C h19 (T (T h53 h52) h55))) h58)
  have h67 := h v2 v2 v3
  have h68 := S h67
  have h69 := C h23 (C h23 (T (T (T (T h4 h22) h42) h66) h65))
  have h70 := C h19 (C h7 h19)
  have h71 := C h36 (C h19 h36)
  have h72 := C h14 (T (T (T (T (T (T h71 h70) h69) h68) h42) h66) h65)
  have h73 := C h36 (C h23 h36)
  have h74 := C h23 (C h7 h23)
  have h75 := C h19 (C h19 (T (T (T (T h63 h57) h49) h11) h5))
  have h76 := h v2 z v2
  have h77 := S h76
  have h78 := h v3 z z
  have h79 := C h18 (T (T (T h53 h52) h78) (C h18 (T (T (T (T (T (C h18 (C h18 (T (T (T (T (T h51 h49) h67) h75) h74) h73))) h77) h67) h75) h74) h73)))
  have h80 := C h18 h17
  have h81 := C h14 (T (T (T (T (T (T (T (C h18 h20) h80) h79) h77) h67) h75) h74) h73)
  have h82 := C h18 h53
  have h83 := C h18 (T (T (T (C h18 (T (T (T (T (T h71 h70) h69) h68) h76) (C h18 (C h18 (T (T (T (T (T h71 h70) h69) h68) h42) h41))))) (S h78)) h20) h17)
  have h84 := C h14 (T (T (T (T (T (T (T h71 h70) h69) h68) h76) h83) h82) (C h18 h52))
  have h85 := C h14 (T (T (T (T (T (T h63 h57) h49) h67) h75) h74) h73)
  have h86 := C h14 (T (T (T (T h39 h29) h42) h66) h65)
  have h87 := h z z v3
  have h88 := C h18 (C h18 (T (T (T (T (T h81 h72) h64) h40) h27) h26))
  T (T (h x v3 v2) (C h14 (C h14 (T (T (T (T (T (T (T (C h19 (T (T (T (T (T (T (T (T (C h9 (T (T h28 h48) h46)) (C h9 (T (T (T (T h32 h39) h29) h42) h66))) (C h9 (T (T (T h57 h49) h67) h75))) (C h9 h74)) (C h9 (T (T (T (T (T h70 h69) h68) h76) h83) h82))) (C h9 (T (T (T (T (T h80 h79) h77) h11) h5) (C h9 (T h87 h88))))) (S (h z x z))) h87) h88)) (C h23 (R (M z (M z z))))) (C h19 (T (T (T (T (T (T (T (C h18 (C h18 (T (T (T (T (T h16 h15) h50) h86) h85) h84))) (S h87)) h16) h15) h50) h86) h85) h84))) (C h23 (R (M v3 (M z v3))))) (C h36 (T (T (T (T (T (T (T (T h81 h72) h64) h40) h27) h26) h44) h43) h24))) (S (h v3 v2 v0))) h20) h17)))) (S (h v3 v3 v0))
