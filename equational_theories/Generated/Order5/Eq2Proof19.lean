import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation39103_implies_Equation2 (G : Type*) [Magma G] (h : Equation39103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ (X2 ◇ X2)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq22 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq45 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq11 eq22
  have eq54 (X0 X2 : G) : X0 = X2 := superpose eq11 eq45
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq106 eq54


@[equational_result]
theorem Equation39106_implies_Equation2 (G : Type*) [Magma G] (h : Equation39106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = X1 := superpose eq12 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq45 eq28


@[equational_result]
theorem Equation39108_implies_Equation2 (G : Type*) [Magma G] (h : Equation39108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X3) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ X1) := superpose eq7 eq11
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ X2) ◇ X0) := superpose eq11 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) := superpose eq12 eq14
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq16
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X3) ◇ X2) = X1 := superpose eq17 eq9
  have eq23 (X1 X2 X3 : G) : (X3 ◇ X2) = X1 := superpose eq17 eq18
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation39109_implies_Equation2 (G : Type*) [Magma G] (h : Equation39109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ (X2 ◇ X2)) ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq7 eq9
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq23 eq21


@[equational_result]
theorem Equation39110_implies_Equation2 (G : Type*) [Magma G] (h : Equation39110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation39113_implies_Equation2 (G : Type*) [Magma G] (h : Equation39113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X2 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0))) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq11 eq11
  have eq18 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq13 eq9
  have eq19 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq38 eq20


@[equational_result]
theorem Equation39116_implies_Equation2 (G : Type*) [Magma G] (h : Equation39116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ X2) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X2 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1)) ◇ X0)) ◇ X3) = X2 := superpose eq7 eq11
  have eq23 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq14
  have eq46 (X0 X3 : G) : X0 = X3 := superpose eq7 eq23
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq138 eq46


@[equational_result]
theorem Equation39118_implies_Equation2 (G : Type*) [Magma G] (h : Equation39118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) = ((((X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) ◇ X3) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X0) := superpose eq11 eq11
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) = ((((X1 ◇ X0) ◇ X0) ◇ X3) ◇ X1) := superpose eq12 eq10
  have eq21 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X3) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X2) := superpose eq13 eq17
  have eq23 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X0 := superpose eq13 eq7
  have eq24 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq23 eq21
  have eq25 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq24 eq23
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq25 eq24
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq25 eq28
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq30 eq30
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq36 eq31


@[equational_result]
theorem Equation39120_implies_Equation2 (G : Type*) [Magma G] (h : Equation39120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation39122_implies_Equation2 (G : Type*) [Magma G] (h : Equation39122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X3)) ◇ X1) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X0) = ((((X1 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X0)) ◇ X0) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X3))) := superpose eq11 eq11
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq11 eq11
  have eq16 (X0 X1 : G) : (X0 ◇ X0) = ((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq11 eq7
  have eq20 (X0 X1 X4 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X4)) ◇ X1)) := superpose eq11 eq9
  have eq23 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0))) := superpose eq11 eq9
  have eq30 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq11 eq9
  have eq33 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X0) = ((((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X0)) ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X0)) ◇ X1) := superpose eq9 eq7
  have eq38 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq16 eq16
  have eq44 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq16 eq7
  have eq54 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq9 eq10
  have eq112 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq44 eq7
  have eq143 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq112 eq11
  have eq146 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq112 eq15
  have eq157 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq112 eq16
  have eq159 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq112 eq146
  have eq160 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq112 eq157
  have eq172 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq7 eq20
  have eq173 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ X1)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq16 eq20
  have eq205 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq112 eq172
  have eq206 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq143 eq205
  have eq207 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq112 eq173
  have eq208 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq112 eq207
  have eq209 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq159 eq208
  have eq234 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq143 eq7
  have eq236 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq143 eq9
  have eq266 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq13 eq30
  have eq267 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) ◇ ((((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq15 eq30
  have eq269 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq30
  have eq293 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq160 eq266
  have eq294 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq44 eq293
  have eq368 (X0 X1 X4 : G) : (X0 ◇ X1) = ((((X4 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)) ◇ X4) := superpose eq7 eq33
  have eq426 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq159 eq9
  have eq459 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq159 eq54
  have eq463 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0))) := superpose eq143 eq54
  have eq506 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X0)) ◇ (((X1 ◇ (X0 ◇ X3)) ◇ X0) ◇ X4)) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X0)) = (((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X0)) ◇ (((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X0)) ◇ (((X1 ◇ (X0 ◇ X3)) ◇ X0) ◇ X4)) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) := superpose eq9 eq54
  have eq546 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq209 eq459
  have eq550 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0))) := superpose eq206 eq463
  have eq580 (X0 X1 X3 : G) : ((((X3 ◇ X0) ◇ X1) ◇ X0) ◇ X3) = X0 := superpose eq7 eq368
  have eq649 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) = (((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)))) ◇ (((((X0 ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) ◇ ((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)))) ◇ (((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) ◇ X2)) ◇ ((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq16 eq23
  have eq730 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq112 eq580
  have eq732 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq580
  have eq733 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := superpose eq9 eq580
  have eq750 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := superpose eq23 eq580
  have eq751 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq7 eq580
  have eq811 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq730 eq267
  have eq813 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq730 eq269
  have eq822 (X0 X1 X2 : G) : (((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ ((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)))) ◇ (((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) ◇ X2)) ◇ ((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose eq732 eq649
  have eq826 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq733 eq546
  have eq827 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq733 eq811
  have eq829 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq733 eq550
  have eq831 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq826 eq426
  have eq833 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq294 eq827
  have eq843 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq829 eq236
  have eq844 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq829 eq234
  have eq859 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq751 eq813
  have eq880 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq859 eq831
  have eq884 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq730 eq880
  have eq892 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq884 eq38
  have eq895 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq884 eq160
  have eq911 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq895 eq892
  have eq919 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq911 eq833
  have eq920 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq911 eq844
  have eq946 (X0 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq920 eq843
  have eq951 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq919 eq946
  have eq952 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq112 eq951
  have eq955 (X0 X1 X2 : G) : (((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) ◇ ((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ X2)) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq952 eq822
  have eq984 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq952 eq750
  have eq1086 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq952 eq730
  have eq1104 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq952 eq955
  have eq1118 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq1086 eq984
  have eq1141 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq1118 eq751
  have eq1163 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq952 eq1141
  have eq1165 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq1163 eq1104
  have eq1254 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X0)) = (((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) := superpose eq1163 eq506
  have eq1314 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X2))) = X0 := superpose eq1163 eq1165
  have eq1315 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq1163 eq1314
  have eq1316 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq1163 eq1315
  have eq1317 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq1163 eq1316
  have eq1318 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq1163 eq1317
  have eq1319 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq1163 eq1318
  have eq1557 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq1319 eq1254
  have eq1558 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X3))) ◇ (X1 ◇ (X0 ◇ X3))) := superpose eq1163 eq1557
  have eq1559 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) := superpose eq1163 eq1558
  have eq1560 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X1 := superpose eq1319 eq1559
  have eq1561 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq1163 eq1560
  have eq1562 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq1163 eq1561
  have eq1884 (X0 X1 : G) : X0 = X1 := superpose eq1319 eq1562
  have eq1903 (X0 : G) : sK0 ≠ X0 := superpose eq1884 eq8
  subsumption eq1903 eq1884


@[equational_result]
theorem Equation39123_implies_Equation2 (G : Type*) [Magma G] (h : Equation39123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ (X2 ◇ X3)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq20 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq31 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq20 eq7
  have eq50 (X0 X1 : G) : X0 = X1 := superpose eq31 eq20
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq58 eq50


@[equational_result]
theorem Equation39124_implies_Equation2 (G : Type*) [Magma G] (h : Equation39124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ (X3 ◇ X4)) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq22 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq7 eq9
  have eq34 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X0 := superpose eq22 eq7
  have eq85 (X0 X1 : G) : X0 = X1 := superpose eq34 eq22
  have eq97 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq97 eq85


@[equational_result]
theorem Equation39128_implies_Equation2 (G : Type*) [Magma G] (h : Equation39128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ X4) = X1 := superpose eq7 eq7
  have eq33 (X0 X1 X2 X3 X5 : G) : (((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X1) ◇ ((X3 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0)) ◇ X5) = X3 := superpose eq7 eq11
  have eq52 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq33
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq52
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq148 eq53


@[equational_result]
theorem Equation39131_implies_Equation2 (G : Type*) [Magma G] (h : Equation39131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ (X2 ◇ X3)) ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq7 eq9
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq133 eq38


@[equational_result]
theorem Equation39132_implies_Equation2 (G : Type*) [Magma G] (h : Equation39132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation39134_implies_Equation2 (G : Type*) [Magma G] (h : Equation39134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X3))) = X1 := superpose eq7 eq7
  have eq51 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq11 eq7
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq51
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq157 eq57


@[equational_result]
theorem Equation39135_implies_Equation2 (G : Type*) [Magma G] (h : Equation39135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation39136_implies_Equation2 (G : Type*) [Magma G] (h : Equation39136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ (X3 ◇ X4)) ◇ X5) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 X5 : G) : ((X0 ◇ X5) ◇ X5) = X3 := superpose eq7 eq9
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq48 eq31


@[equational_result]
theorem Equation39137_implies_Equation2 (G : Type*) [Magma G] (h : Equation39137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X3 := superpose eq7 eq7
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq54 eq17


@[equational_result]
theorem Equation39140_implies_Equation2 (G : Type*) [Magma G] (h : Equation39140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq10 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq21 eq13


@[equational_result]
theorem Equation39143_implies_Equation2 (G : Type*) [Magma G] (h : Equation39143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X2) := superpose eq7 eq10
  have eq19 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3) = X2 := superpose eq13 eq9
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq42 eq26


@[equational_result]
theorem Equation39145_implies_Equation2 (G : Type*) [Magma G] (h : Equation39145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X2)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq10
  have eq15 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ X2) = X1 := superpose eq11 eq9
  have eq18 (X1 X2 X3 : G) : (X3 ◇ X2) = X1 := superpose eq11 eq15
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq21 eq19


@[equational_result]
theorem Equation39146_implies_Equation2 (G : Type*) [Magma G] (h : Equation39146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq34 eq15


@[equational_result]
theorem Equation39147_implies_Equation2 (G : Type*) [Magma G] (h : Equation39147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq48 eq15


@[equational_result]
theorem Equation39150_implies_Equation2 (G : Type*) [Magma G] (h : Equation39150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0))) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq39 eq15


@[equational_result]
theorem Equation39153_implies_Equation2 (G : Type*) [Magma G] (h : Equation39153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1))) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq9
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq66 eq47


@[equational_result]
theorem Equation39155_implies_Equation2 (G : Type*) [Magma G] (h : Equation39155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = X2 := superpose eq10 eq7
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq7 eq19
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq103 eq48


@[equational_result]
theorem Equation39157_implies_Equation2 (G : Type*) [Magma G] (h : Equation39157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq55 eq18


@[equational_result]
theorem Equation39159_implies_Equation2 (G : Type*) [Magma G] (h : Equation39159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) ◇ X3)) ◇ X1) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) ◇ X0) ◇ X3) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0)) = X1 := superpose eq7 eq9
  have eq37 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X0) = (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ (((((X2 ◇ X2) ◇ X0) ◇ X1) ◇ X0) ◇ X1)) := superpose eq11 eq11
  have eq109 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (((((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq37
  have eq113 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) = ((((((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) ◇ X2)) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) ◇ X2))) := superpose eq37 eq37
  have eq134 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq109
  have eq171 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq134 eq7
  have eq173 (X0 X1 : G) : ((((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := superpose eq134 eq10
  have eq174 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq134 eq11
  have eq309 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq174 eq7
  have eq312 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq174 eq11
  have eq346 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq309 eq312
  have eq349 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq346 eq171
  have eq351 (X0 X1 : G) : (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq346 eq173
  have eq395 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq349 eq346
  have eq513 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq349 eq7
  have eq555 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq513 eq395
  have eq557 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) = (((((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1))) ◇ ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X1) ◇ X2))) := superpose eq555 eq113
  have eq574 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0)) = X1 := superpose eq555 eq11
  have eq622 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq555 eq351
  have eq660 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X1)) = ((((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2))) := superpose eq555 eq557
  have eq661 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X1)) = ((((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2))) := superpose eq555 eq660
  have eq662 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2))) := superpose eq555 eq661
  have eq801 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq555 eq7
  have eq903 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq801
  have eq949 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq555 eq903
  have eq1068 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq949 eq801
  have eq1093 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq949 eq1068
  have eq1094 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq555 eq1093
  have eq1224 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq574 eq1094
  have eq1313 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq1224 eq801
  have eq1327 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq1313 eq622
  have eq1334 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq555 eq1327
  have eq1335 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = (((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2))) := superpose eq1334 eq662
  have eq1507 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq1334 eq1335
  have eq1508 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq1334 eq1507
  have eq1509 (X0 X1 X2 : G) : ((((X0 ◇ X2) ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq1334 eq1508
  have eq1510 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq1334 eq1509
  have eq1511 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq1334 eq1510
  have eq1512 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq1334 eq1511
  have eq2275 (X0 X2 : G) : X0 = X2 := superpose eq1512 eq1512
  have eq2280 (X0 : G) : sK0 ≠ X0 := superpose eq2275 eq8
  subsumption eq2280 eq2275


@[equational_result]
theorem Equation39161_implies_Equation2 (G : Type*) [Magma G] (h : Equation39161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) ◇ X4)) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq11 (X0 X4 : G) : ((X0 ◇ X0) ◇ X4) = X0 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : (((X0 ◇ X0) ◇ X3) ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq11 eq12
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq39 eq15


@[equational_result]
theorem Equation39165_implies_Equation2 (G : Type*) [Magma G] (h : Equation39165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) ◇ X4)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1)) ◇ X5) = X3 := superpose eq7 eq9
  have eq47 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq66 eq47


@[equational_result]
theorem Equation39168_implies_Equation2 (G : Type*) [Magma G] (h : Equation39168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X2) ◇ X3)) ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) ◇ X0) ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ X2) = X2 := superpose eq7 eq9
  have eq26 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) ◇ X1) = X2 := superpose eq10 eq10
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq7 eq10
  have eq55 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq27 eq10
  have eq66 (X0 X1 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq55
  have eq67 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq66 eq27
  have eq68 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq67 eq66
  have eq81 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq68 eq26
  have eq130 (X0 X2 : G) : X0 = X2 := superpose eq81 eq81
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq130 eq8
  subsumption eq135 eq130


@[equational_result]
theorem Equation39169_implies_Equation2 (G : Type*) [Magma G] (h : Equation39169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq59 eq18


@[equational_result]
theorem Equation39171_implies_Equation2 (G : Type*) [Magma G] (h : Equation39171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X4)) = X0 := superpose eq7 eq11
  have eq15 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X4) := superpose eq7 eq11
  have eq29 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X0)) = X0 := superpose eq15 eq12
  have eq33 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = X0 := superpose eq29 eq7
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq33 eq33
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq50 eq40


@[equational_result]
theorem Equation39172_implies_Equation2 (G : Type*) [Magma G] (h : Equation39172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ X3) := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq11
  have eq58 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq152 eq58


@[equational_result]
theorem Equation39173_implies_Equation2 (G : Type*) [Magma G] (h : Equation39173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X4) ◇ X5)) = X0 := superpose eq7 eq12
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq12 eq12
  have eq79 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X4) = X0 := superpose eq7 eq22
  have eq125 (X0 X4 X5 : G) : (X4 ◇ (X0 ◇ X5)) = X0 := superpose eq79 eq13
  have eq136 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ X3) = X0 := superpose eq125 eq7
  have eq166 (X0 X3 : G) : X0 = X3 := superpose eq136 eq136
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq166 eq8
  subsumption eq182 eq166


@[equational_result]
theorem Equation39174_implies_Equation2 (G : Type*) [Magma G] (h : Equation39174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X3 := superpose eq7 eq7
  have eq18 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq55 eq18


@[equational_result]
theorem Equation39176_implies_Equation2 (G : Type*) [Magma G] (h : Equation39176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X0))) = X0 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq10
  have eq25 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq7 eq11
  have eq35 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq17 eq25
  have eq69 (X0 X1 : G) : X0 = X1 := superpose eq17 eq35
  have eq93 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq93 eq69


@[equational_result]
theorem Equation39177_implies_Equation2 (G : Type*) [Magma G] (h : Equation39177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ (X3 ◇ X2)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq11 eq7
  have eq20 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq9
  have eq32 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = X2 := superpose eq20 eq15
  have eq62 (X0 X2 : G) : X0 = X2 := superpose eq32 eq32
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq80 eq62


@[equational_result]
theorem Equation39178_implies_Equation2 (G : Type*) [Magma G] (h : Equation39178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X5) = X2 := superpose eq7 eq7
  have eq11 (X0 X4 : G) : ((X0 ◇ X0) ◇ X4) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq11 eq7
  have eq19 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq15 eq10
  have eq22 (X0 X2 : G) : X0 = X2 := superpose eq11 eq19
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation39180_implies_Equation2 (G : Type*) [Magma G] (h : Equation39180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X3 ◇ X1)) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1)) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) = X1 := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq10 eq10
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X3 ◇ X1)) ◇ X0))) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X3 ◇ X1)) ◇ X0)))) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X3 ◇ X1)) ◇ X0))) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X3 ◇ X1)) ◇ X0)))) ◇ X0)) = X0 := superpose eq9 eq9
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X3) ◇ X1) = (((X1 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X3) ◇ X1))) ◇ ((X0 ◇ (X4 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X3) ◇ X1))) ◇ ((X0 ◇ (X4 ◇ X1)) ◇ (((X1 ◇ X0) ◇ X3) ◇ X1))) := superpose eq10 eq9
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0)) = ((((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) ◇ (X3 ◇ ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0)))) ◇ ((X0 ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0))) ◇ ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0)))) ◇ ((X0 ◇ (X5 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0))) ◇ ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0)))) := superpose eq9 eq9
  have eq34 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = ((X1 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3)) := superpose eq10 eq14
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := superpose eq7 eq14
  have eq38 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X0) := superpose eq10 eq14
  have eq39 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X0)) = (((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) := superpose eq9 eq14
  have eq56 (X0 X1 X2 X4 : G) : ((X0 ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)))) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)))) ◇ X0)) = X0 := superpose eq37 eq22
  have eq58 (X0 X1 X3 X4 X5 : G) : ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = ((((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (X3 ◇ ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)))) ◇ ((X0 ◇ (X5 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)))) ◇ ((X0 ◇ (X5 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)))) := superpose eq37 eq25
  have eq65 (X0 X1 X2 : G) : ((X0 ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ X0)) = X0 := superpose eq37 eq56
  have eq66 (X0 X1 X4 X5 : G) : ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = ((((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X5 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)))) ◇ ((X0 ◇ (X5 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)))) := superpose eq38 eq58
  have eq68 (X0 X1 X4 X5 : G) : ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = ((((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X5 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)))) := superpose eq38 eq66
  have eq69 (X0 X1 X4 X5 : G) : ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ (X5 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)))) := superpose eq10 eq68
  have eq70 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ (X4 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := superpose eq38 eq69
  have eq72 (X0 X1 : G) : ((X0 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)) = X0 := superpose eq70 eq65
  have eq73 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := superpose eq14 eq72
  have eq75 (X0 X1 X3 : G) : (X1 ◇ X0) = (X1 ◇ (X3 ◇ X0)) := superpose eq10 eq39
  have eq79 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) = X1 := superpose eq75 eq12
  have eq81 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X3) ◇ X1) = (((X1 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X3) ◇ X1))) ◇ ((X0 ◇ (X4 ◇ X1)) ◇ X1)) ◇ ((X0 ◇ (X4 ◇ X1)) ◇ X1)) := superpose eq75 eq24
  have eq82 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = ((X1 ◇ X3) ◇ (X0 ◇ X3)) := superpose eq75 eq34
  have eq85 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq75 eq73
  have eq94 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ X1) = (((X1 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X3) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq75 eq81
  have eq95 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ X1) = (((X1 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X3) ◇ X1))) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq75 eq94
  have eq96 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ X1) = (((X1 ◇ (((X1 ◇ X0) ◇ X3) ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq75 eq95
  have eq97 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ X1) = (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq75 eq96
  have eq125 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq10 eq85
  have eq128 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X0 ◇ X2) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq85 eq10
  have eq130 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq125 eq97
  have eq132 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ X1) = (X1 ◇ X1) := superpose eq75 eq130
  have eq134 (X0 X1 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq132 eq79
  have eq137 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq75 eq128
  have eq138 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq134 eq137
  have eq140 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ X3)) = X1 := superpose eq138 eq82
  have eq159 (X1 X3 : G) : ((X1 ◇ X3) ◇ X3) = X1 := superpose eq138 eq140
  have eq160 (X1 X3 : G) : (X3 ◇ X3) = X1 := superpose eq138 eq159
  have eq170 (X0 X1 : G) : X0 = X1 := superpose eq138 eq160
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq170 eq8
  subsumption eq175 eq170


@[equational_result]
theorem Equation39182_implies_Equation2 (G : Type*) [Magma G] (h : Equation39182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X2 ◇ X0) = (X0 ◇ X3) := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq118 eq49


@[equational_result]
theorem Equation39185_implies_Equation2 (G : Type*) [Magma G] (h : Equation39185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ (X3 ◇ X2)) ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = X3 := superpose eq7 eq9
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq103 eq38


@[equational_result]
theorem Equation39186_implies_Equation2 (G : Type*) [Magma G] (h : Equation39186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation39188_implies_Equation2 (G : Type*) [Magma G] (h : Equation39188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ (X4 ◇ X1)) = X0 := superpose eq7 eq12
  have eq52 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq124 eq52


@[equational_result]
theorem Equation39189_implies_Equation2 (G : Type*) [Magma G] (h : Equation39189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ X2) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation39190_implies_Equation2 (G : Type*) [Magma G] (h : Equation39190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ (X4 ◇ X3)) ◇ X5) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X5) = X4 := superpose eq7 eq9
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq56 eq29


@[equational_result]
theorem Equation39191_implies_Equation2 (G : Type*) [Magma G] (h : Equation39191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation39193_implies_Equation2 (G : Type*) [Magma G] (h : Equation39193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X3 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0))) ◇ X1) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0)) = X1 := superpose eq7 eq10
  have eq15 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq10
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) := superpose eq7 eq15
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq10 eq15
  have eq33 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X1) ◇ X0) = ((X1 ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X1))) ◇ X0) := superpose eq9 eq15
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X2 := superpose eq15 eq10
  have eq42 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq31 eq7
  have eq44 (X0 X1 X3 : G) : (((X0 ◇ X3) ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq31 eq11
  have eq52 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X1 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq32 eq33
  have eq53 (X0 X1 X3 : G) : ((X1 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X0) = X1 := superpose eq42 eq52
  have eq67 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X0)) = X1 := superpose eq41 eq44
  have eq70 (X0 X1 X3 : G) : (X3 ◇ X0) = X1 := superpose eq67 eq53
  have eq73 (X0 X2 : G) : X0 = X2 := superpose eq15 eq70
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq107 eq73


@[equational_result]
theorem Equation39195_implies_Equation2 (G : Type*) [Magma G] (h : Equation39195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X4 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X0))) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq11 (X0 X4 : G) : ((X0 ◇ X0) ◇ X4) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq11 eq11
  have eq18 (X0 X3 X5 : G) : (((X0 ◇ X0) ◇ X3) ◇ X5) = X3 := superpose eq13 eq9
  have eq19 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq11 eq18
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq38 eq20


@[equational_result]
theorem Equation39197_implies_Equation2 (G : Type*) [Magma G] (h : Equation39197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X3 ◇ (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1))) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1)) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1)) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1)) = X1 := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq10 eq10
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) = ((((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ (X3 ◇ ((X0 ◇ (X5 ◇ ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)))) ◇ ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))))) ◇ ((X0 ◇ (X5 ◇ ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)))) ◇ ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X5 ◇ ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)))) ◇ ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)))) := superpose eq9 eq9
  have eq32 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) = (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ X4)) ◇ (X0 ◇ X4)) := superpose eq9 eq14
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X0) := superpose eq10 eq14
  have eq46 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) = ((((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X5 ◇ ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)))) ◇ ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)))) ◇ ((X0 ◇ (X5 ◇ ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)))) ◇ ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)))) := superpose eq35 eq22
  have eq47 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) = (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) ◇ (X0 ◇ X4)) := superpose eq35 eq32
  have eq48 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) = ((((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X5 ◇ ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)))) ◇ ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)))) := superpose eq35 eq46
  have eq49 (X0 X1 X2 X4 : G) : ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) = ((((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) ◇ X0) := superpose eq35 eq48
  have eq50 (X0 X1 X2 X4 : G) : ((X1 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) = ((X1 ◇ X0) ◇ X0) := superpose eq7 eq49
  have eq54 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) = (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) := superpose eq35 eq47
  have eq55 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X1 ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq7 eq54
  have eq56 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq55 eq50
  have eq59 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X2) := superpose eq56 eq35
  have eq62 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X1 := superpose eq59 eq11
  have eq64 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) := superpose eq59 eq55
  have eq76 (X0 X1 X3 : G) : (((X0 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq59 eq62
  have eq77 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ (X1 ◇ X0)) = X1 := superpose eq59 eq76
  have eq79 (X0 X1 X3 : G) : (X1 ◇ X0) = ((X1 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq59 eq64
  have eq80 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq77 eq79
  have eq84 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X0) = X1 := superpose eq80 eq77
  have eq86 (X0 X1 X3 : G) : (X3 ◇ X0) = X1 := superpose eq80 eq84
  have eq87 (X0 X3 : G) : X0 = X3 := superpose eq86 eq86
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq89 eq87


@[equational_result]
theorem Equation39199_implies_Equation2 (G : Type*) [Magma G] (h : Equation39199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X5) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq10 eq10
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq148 eq40


@[equational_result]
theorem Equation39203_implies_Equation2 (G : Type*) [Magma G] (h : Equation39203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq79 eq16


@[equational_result]
theorem Equation39205_implies_Equation2 (G : Type*) [Magma G] (h : Equation39205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ X4)) = X0 := superpose eq7 eq11
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq128 eq53


@[equational_result]
theorem Equation39206_implies_Equation2 (G : Type*) [Magma G] (h : Equation39206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X0 ◇ X3) := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq11
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq160 eq59


@[equational_result]
theorem Equation39207_implies_Equation2 (G : Type*) [Magma G] (h : Equation39207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X5) ◇ X5) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq10 eq10
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq157 eq52


@[equational_result]
theorem Equation39208_implies_Equation2 (G : Type*) [Magma G] (h : Equation39208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation39211_implies_Equation2 (G : Type*) [Magma G] (h : Equation39211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ (X3 ◇ X3)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq9
  have eq25 (X0 X2 : G) : ((X2 ◇ X2) ◇ X2) = X0 := superpose eq17 eq7
  have eq31 (X0 X1 : G) : X0 = X1 := superpose eq10 eq25
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq51 eq31


@[equational_result]
theorem Equation39212_implies_Equation2 (G : Type*) [Magma G] (h : Equation39212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 : G) : ((X0 ◇ X0) ◇ X4) = X0 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq28 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq12
  have eq43 (X0 X3 : G) : X0 = X3 := superpose eq7 eq28
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq102 eq43


@[equational_result]
theorem Equation39216_implies_Equation2 (G : Type*) [Magma G] (h : Equation39216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ X3) := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq116 eq47


@[equational_result]
theorem Equation39219_implies_Equation2 (G : Type*) [Magma G] (h : Equation39219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X2) ◇ X2) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq7 eq10
  have eq17 (X0 X2 : G) : ((X2 ◇ X2) ◇ X2) = X0 := superpose eq11 eq7
  have eq22 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq29 eq22


@[equational_result]
theorem Equation39220_implies_Equation2 (G : Type*) [Magma G] (h : Equation39220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation39222_implies_Equation2 (G : Type*) [Magma G] (h : Equation39222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X4 ◇ X4)) ◇ X5) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X3)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X4) ◇ X2) = X2 := superpose eq11 eq7
  have eq19 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X3) ◇ X2) = X2 := superpose eq11 eq7
  have eq24 (X2 X4 : G) : (X4 ◇ X2) = X2 := superpose eq19 eq17
  have eq25 (X0 X1 X3 X4 X5 : G) : (((X0 ◇ (X4 ◇ X4)) ◇ X5) ◇ X3) = X1 := superpose eq24 eq9
  have eq32 (X1 X3 X5 : G) : (X5 ◇ X3) = X1 := superpose eq24 eq25
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq32 eq32
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq35 eq33


@[equational_result]
theorem Equation39223_implies_Equation2 (G : Type*) [Magma G] (h : Equation39223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ X2) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation39224_implies_Equation2 (G : Type*) [Magma G] (h : Equation39224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X3 ◇ X3) = ((X0 ◇ X4) ◇ X4) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq51 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq125 eq51


@[equational_result]
theorem Equation39225_implies_Equation2 (G : Type*) [Magma G] (h : Equation39225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation39227_implies_Equation2 (G : Type*) [Magma G] (h : Equation39227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4))) = X0 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq10
  have eq40 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) := superpose eq7 eq18
  have eq44 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq11 eq18
  have eq60 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq44 eq40
  have eq70 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq60 eq18
  have eq98 (X0 X2 : G) : X0 = X2 := superpose eq70 eq70
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq98 eq8
  subsumption eq100 eq98


@[equational_result]
theorem Equation39228_implies_Equation2 (G : Type*) [Magma G] (h : Equation39228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ (X4 ◇ X5)) ◇ X2) ◇ X4) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq20 (X0 X2 X5 : G) : ((X0 ◇ X5) ◇ X2) = X5 := superpose eq7 eq9
  have eq31 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X0 := superpose eq20 eq7
  have eq40 (X0 X1 : G) : X0 = X1 := superpose eq11 eq31
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq60 eq40


@[equational_result]
theorem Equation39229_implies_Equation2 (G : Type*) [Magma G] (h : Equation39229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ (X4 ◇ X5)) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X5) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X4) = X5 := superpose eq7 eq9
  have eq30 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq17 eq10
  have eq31 (X0 X4 : G) : X0 = X4 := superpose eq9 eq30
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq72 eq31


@[equational_result]
theorem Equation39230_implies_Equation2 (G : Type*) [Magma G] (h : Equation39230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X6 : G) : ((X0 ◇ X0) ◇ X6) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq11 eq7
  have eq19 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = X0 := superpose eq16 eq7
  have eq25 (X0 X2 : G) : X0 = X2 := superpose eq11 eq19
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq32 eq25


@[equational_result]
theorem Equation39232_implies_Equation2 (G : Type*) [Magma G] (h : Equation39232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X4 ◇ X5)) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1)) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = ((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4))) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X4) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1)) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1)) = X1 := superpose eq7 eq10
  have eq67 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X1 ◇ (X6 ◇ X7)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0)) = ((((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) ◇ (X4 ◇ X5)) ◇ ((X0 ◇ (X8 ◇ X9)) ◇ ((X1 ◇ (X6 ◇ X7)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0)))) ◇ ((X0 ◇ (X8 ◇ X9)) ◇ ((X1 ◇ (X6 ◇ X7)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0)))) := superpose eq9 eq9
  have eq80 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq11 eq9
  have eq96 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1) = X0 := superpose eq80 eq7
  have eq98 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X4) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) = X1 := superpose eq80 eq12
  have eq101 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X1 ◇ (X6 ◇ X7)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) ◇ ((X0 ◇ (X8 ◇ X9)) ◇ ((X1 ◇ (X6 ◇ X7)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))))) ◇ ((X0 ◇ (X8 ◇ X9)) ◇ ((X1 ◇ (X6 ◇ X7)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))))) := superpose eq80 eq67
  have eq132 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq80 eq96
  have eq135 (X0 X1 X4 : G) : (((X0 ◇ X4) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq80 eq98
  have eq136 (X0 X1 X4 : G) : ((X0 ◇ X4) ◇ (X1 ◇ X0)) = X1 := superpose eq80 eq135
  have eq143 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X1 ◇ (X6 ◇ X7)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) ◇ (X0 ◇ (X8 ◇ X9))) ◇ (X0 ◇ (X8 ◇ X9))) := superpose eq80 eq101
  have eq144 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X1 ◇ (X6 ◇ X7)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) ◇ (X0 ◇ (X8 ◇ X9))) := superpose eq80 eq143
  have eq145 (X0 X1 X2 X3 X6 X7 X8 X9 : G) : ((X1 ◇ (X6 ◇ X7)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X8 ◇ X9))) := superpose eq80 eq144
  have eq146 (X0 X1 X2 X3 X6 X7 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = ((X1 ◇ (X6 ◇ X7)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) := superpose eq80 eq145
  have eq147 (X0 X1 X6 X7 : G) : (X0 ◇ X1) = ((X1 ◇ (X6 ◇ X7)) ◇ (X0 ◇ X1)) := superpose eq80 eq146
  have eq148 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq136 eq147
  have eq150 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq148 eq132
  have eq169 (X0 X2 : G) : X0 = X2 := superpose eq150 eq150
  have eq171 (X0 : G) : sK0 ≠ X0 := superpose eq169 eq8
  subsumption eq171 eq169


@[equational_result]
theorem Equation39233_implies_Equation2 (G : Type*) [Magma G] (h : Equation39233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X1 ◇ X2) ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X1) ◇ X2) = X0 := superpose eq12 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq15 eq15
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq25 eq21


@[equational_result]
theorem Equation39234_implies_Equation2 (G : Type*) [Magma G] (h : Equation39234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X4 ◇ X5)) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X0)) = (X0 ◇ X2) := superpose eq7 eq7
  have eq13 (X1 X2 X3 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X5) = X3 := superpose eq12 eq9
  have eq15 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq13 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq15 eq15
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39235_implies_Equation2 (G : Type*) [Magma G] (h : Equation39235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 X5 : G) : (X3 ◇ X4) = (X0 ◇ X5) := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq12
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq119 eq49


@[equational_result]
theorem Equation39237_implies_Equation2 (G : Type*) [Magma G] (h : Equation39237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (((X3 ◇ X0) ◇ (X4 ◇ X5)) ◇ X4)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq51 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq12 eq11
  have eq61 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X1) = X2 := superpose eq51 eq10
  have eq71 (X0 X4 : G) : X0 = X4 := superpose eq7 eq61
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq173 eq71


@[equational_result]
theorem Equation39238_implies_Equation2 (G : Type*) [Magma G] (h : Equation39238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ (X4 ◇ X5)) ◇ X4) ◇ X4) = X2 := superpose eq7 eq7
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq54 eq36


@[equational_result]
theorem Equation39239_implies_Equation2 (G : Type*) [Magma G] (h : Equation39239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation39240_implies_Equation2 (G : Type*) [Magma G] (h : Equation39240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 X6 : G) : ((X0 ◇ X4) ◇ X6) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation39242_implies_Equation2 (G : Type*) [Magma G] (h : Equation39242 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X1) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq10 eq10
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq136 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq136 eq59


@[equational_result]
theorem Equation39243_implies_Equation2 (G : Type*) [Magma G] (h : Equation39243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X2) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq55 eq16


@[equational_result]
theorem Equation39244_implies_Equation2 (G : Type*) [Magma G] (h : Equation39244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ (X4 ◇ X5)) ◇ X5) ◇ X5) = X3 := superpose eq7 eq7
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq62 eq42


@[equational_result]
theorem Equation39245_implies_Equation2 (G : Type*) [Magma G] (h : Equation39245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation39247_implies_Equation2 (G : Type*) [Magma G] (h : Equation39247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X5 ◇ (X6 ◇ X5)) = X0 := superpose eq7 eq12
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq153 eq55


@[equational_result]
theorem Equation39248_implies_Equation2 (G : Type*) [Magma G] (h : Equation39248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X5 X6 : G) : ((X0 ◇ X6) ◇ X2) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation39249_implies_Equation2 (G : Type*) [Magma G] (h : Equation39249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : ((X0 ◇ X6) ◇ X4) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation39250_implies_Equation2 (G : Type*) [Magma G] (h : Equation39250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X4 ◇ X5) = ((X0 ◇ X6) ◇ X6) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq63 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq152 eq63


@[equational_result]
theorem Equation39251_implies_Equation2 (G : Type*) [Magma G] (h : Equation39251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X7 X8 : G) : ((X0 ◇ X7) ◇ X8) = X4 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation39254_implies_Equation2 (G : Type*) [Magma G] (h : Equation39254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq13 eq16
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq24 eq17


@[equational_result]
theorem Equation39257_implies_Equation2 (G : Type*) [Magma G] (h : Equation39257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq11 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq20 eq18


@[equational_result]
theorem Equation39259_implies_Equation2 (G : Type*) [Magma G] (h : Equation39259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq42 eq12


@[equational_result]
theorem Equation39260_implies_Equation2 (G : Type*) [Magma G] (h : Equation39260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq10 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq9
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq12 eq10
  have eq14 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq13 eq11
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39261_implies_Equation2 (G : Type*) [Magma G] (h : Equation39261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39264_implies_Equation2 (G : Type*) [Magma G] (h : Equation39264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X2 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0))) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X2 ◇ (((X3 ◇ X3) ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0)))) ◇ X2) ◇ X4) = X2 := superpose eq7 eq9
  have eq21 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ X4) = X2 := superpose eq7 eq13
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq21 eq7
  have eq42 (X0 X1 : G) : X0 = X1 := superpose eq26 eq21
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq49 eq42


@[equational_result]
theorem Equation39267_implies_Equation2 (G : Type*) [Magma G] (h : Equation39267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2) = ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X3) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X3) ◇ ((X1 ◇ X4) ◇ X3)) ◇ X3) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X2) ◇ X5) := superpose eq10 eq10
  have eq23 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) = X0 := superpose eq7 eq10
  have eq28 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) ◇ (X3 ◇ (((X2 ◇ X2) ◇ X1) ◇ X2))) ◇ (((X2 ◇ X2) ◇ X1) ◇ X2)) ◇ X4) = X3 := superpose eq10 eq7
  have eq33 (X0 X1 X2 X5 : G) : (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X2) ◇ X5) = X1 := superpose eq23 eq22
  have eq35 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ X4) = X3 := superpose eq33 eq28
  have eq62 (X0 X3 : G) : X0 = X3 := superpose eq7 eq35
  have eq174 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq174 eq62


@[equational_result]
theorem Equation39269_implies_Equation2 (G : Type*) [Magma G] (h : Equation39269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation39271_implies_Equation2 (G : Type*) [Magma G] (h : Equation39271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39273_implies_Equation2 (G : Type*) [Magma G] (h : Equation39273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = ((((X1 ◇ X1) ◇ X0) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq9 eq9
  have eq13 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = ((((X1 ◇ X1) ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0)) ◇ X1) := superpose eq9 eq9
  have eq16 (X0 X1 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq7 eq13
  have eq18 (X0 : G) : (X0 ◇ X0) = (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq9 eq16
  have eq19 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq16
  have eq21 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq16 eq7
  have eq24 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq21 eq18
  have eq26 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq21 eq10
  have eq27 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq21 eq24
  have eq28 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq19 eq27
  have eq29 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) = X0 := superpose eq28 eq7
  have eq33 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq28 eq16
  have eq45 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) = ((X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0)) ◇ X0) := superpose eq28 eq26
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X0) := superpose eq28 eq45
  have eq56 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq29 eq29
  have eq74 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq56 eq56
  have eq78 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq28 eq74
  have eq79 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq78 eq46
  have eq81 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq79 eq29
  have eq94 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq81 eq33
  have eq108 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq81 eq94
  have eq124 (X0 X2 : G) : X0 = X2 := superpose eq108 eq108
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq124 eq8
  subsumption eq132 eq124


@[equational_result]
theorem Equation39275_implies_Equation2 (G : Type*) [Magma G] (h : Equation39275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ (X3 ◇ X4)) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq7 eq7
  have eq14 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq11 eq9
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq28 eq16


@[equational_result]
theorem Equation39277_implies_Equation2 (G : Type*) [Magma G] (h : Equation39277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X0 ◇ X3)) ◇ X2) = ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = ((((X4 ◇ X4) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X3)) ◇ X2)) ◇ X4) ◇ X4) := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X2) ◇ ((X1 ◇ X3) ◇ X4)) ◇ X2) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X0) ◇ X5) := superpose eq9 eq9
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X1) = X0 := superpose eq7 eq9
  have eq25 (X0 X1 X2 X4 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = ((X2 ◇ X2) ◇ X4) := superpose eq17 eq10
  have eq28 (X0 X1 X5 : G) : (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X0) ◇ X5) = X1 := superpose eq17 eq16
  have eq143 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X2) = X2 := superpose eq25 eq7
  have eq161 (X0 X1 X5 : G) : (X0 ◇ X5) = X1 := superpose eq143 eq28
  have eq163 (X0 X3 : G) : X0 = X3 := superpose eq7 eq161
  have eq257 (X0 : G) : sK0 ≠ X0 := superpose eq163 eq8
  subsumption eq257 eq163


@[equational_result]
theorem Equation39279_implies_Equation2 (G : Type*) [Magma G] (h : Equation39279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X3 ◇ X4)) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1)) ◇ X5) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X3 X4 X5 : G) : (((X0 ◇ (X3 ◇ X4)) ◇ (X1 ◇ X1)) ◇ X5) = X3 := superpose eq11 eq9
  have eq15 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq11 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation39282_implies_Equation2 (G : Type*) [Magma G] (h : Equation39282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X0 ◇ X3)) ◇ X3) = ((((X1 ◇ X1) ◇ X0) ◇ X3) ◇ X3) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X3 ◇ X3) ◇ (X2 ◇ X2)) ◇ X1) ◇ X1) = ((((X0 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1))) ◇ ((X2 ◇ X2) ◇ X1)) ◇ X1) := superpose eq9 eq9
  have eq17 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X1 ◇ X3)) ◇ X3) = ((((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X1) ◇ X3) ◇ X3) := superpose eq9 eq9
  have eq18 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq9
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2) = X0 := superpose eq7 eq9
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X2) = (((((X0 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1))) ◇ ((X2 ◇ X2) ◇ X1)) ◇ X1) ◇ X1) := superpose eq9 eq7
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X1) := superpose eq9 eq18
  have eq39 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq18 eq7
  have eq43 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq18 eq7
  have eq44 (X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X1 ◇ X3)) ◇ X3) = (((X1 ◇ X1) ◇ X3) ◇ X3) := superpose eq35 eq17
  have eq50 (X0 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq43
  have eq52 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1))) ◇ ((X2 ◇ X2) ◇ X1)) ◇ X1) = ((X2 ◇ X1) ◇ X1) := superpose eq50 eq13
  have eq54 (X1 X2 : G) : (X2 ◇ X2) = (((X2 ◇ X1) ◇ X1) ◇ X1) := superpose eq52 eq26
  have eq57 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1))) ◇ ((X2 ◇ X2) ◇ X1)) := superpose eq9 eq39
  have eq65 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (((X2 ◇ X2) ◇ X1) ◇ X1) := superpose eq57 eq52
  have eq67 (X1 X2 X3 : G) : (((X2 ◇ X2) ◇ (X1 ◇ X3)) ◇ X3) = ((X1 ◇ X3) ◇ X3) := superpose eq65 eq44
  have eq69 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X2) = X0 := superpose eq67 eq7
  have eq75 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq69 eq54
  have eq80 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2) = X0 := superpose eq75 eq21
  have eq84 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq75 eq50
  have eq96 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq75 eq84
  have eq98 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq96 eq80
  have eq102 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq96 eq98
  have eq114 (X0 X2 : G) : X0 = X2 := superpose eq102 eq102
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq114 eq8
  subsumption eq119 eq114


@[equational_result]
theorem Equation39283_implies_Equation2 (G : Type*) [Magma G] (h : Equation39283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ (X3 ◇ X4)) ◇ X4) ◇ X5) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq7 eq7
  have eq14 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq11 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation39285_implies_Equation2 (G : Type*) [Magma G] (h : Equation39285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation39286_implies_Equation2 (G : Type*) [Magma G] (h : Equation39286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation39287_implies_Equation2 (G : Type*) [Magma G] (h : Equation39287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : ((X0 ◇ X3) ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X1 : G) : X0 = X1 := superpose eq13 eq11
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq19 eq16


@[equational_result]
theorem Equation39288_implies_Equation2 (G : Type*) [Magma G] (h : Equation39288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39291_implies_Equation2 (G : Type*) [Magma G] (h : Equation39291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X0) ◇ X2)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq11 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq11
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq22 eq14


@[equational_result]
theorem Equation39294_implies_Equation2 (G : Type*) [Magma G] (h : Equation39294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1) ◇ X2)) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq9
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq36 eq25


@[equational_result]
theorem Equation39296_implies_Equation2 (G : Type*) [Magma G] (h : Equation39296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq37 eq12


@[equational_result]
theorem Equation39298_implies_Equation2 (G : Type*) [Magma G] (h : Equation39298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation39301_implies_Equation2 (G : Type*) [Magma G] (h : Equation39301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq9 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39303_implies_Equation2 (G : Type*) [Magma G] (h : Equation39303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation39304_implies_Equation2 (G : Type*) [Magma G] (h : Equation39304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation39306_implies_Equation2 (G : Type*) [Magma G] (h : Equation39306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation39307_implies_Equation2 (G : Type*) [Magma G] (h : Equation39307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation39308_implies_Equation2 (G : Type*) [Magma G] (h : Equation39308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39310_implies_Equation2 (G : Type*) [Magma G] (h : Equation39310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) = X2 := superpose eq10 eq7
  have eq30 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq13
  have eq57 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq10 eq30
  have eq90 (X0 X2 : G) : X0 = X2 := superpose eq57 eq57
  have eq186 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq186 eq90


@[equational_result]
theorem Equation39312_implies_Equation2 (G : Type*) [Magma G] (h : Equation39312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) ◇ X3)) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (((X0 ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X0 := superpose eq13 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39314_implies_Equation2 (G : Type*) [Magma G] (h : Equation39314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39315_implies_Equation2 (G : Type*) [Magma G] (h : Equation39315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39316_implies_Equation2 (G : Type*) [Magma G] (h : Equation39316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39318_implies_Equation2 (G : Type*) [Magma G] (h : Equation39318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39319_implies_Equation2 (G : Type*) [Magma G] (h : Equation39319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39320_implies_Equation2 (G : Type*) [Magma G] (h : Equation39320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39322_implies_Equation2 (G : Type*) [Magma G] (h : Equation39322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39323_implies_Equation2 (G : Type*) [Magma G] (h : Equation39323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39324_implies_Equation2 (G : Type*) [Magma G] (h : Equation39324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39325_implies_Equation2 (G : Type*) [Magma G] (h : Equation39325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39327_implies_Equation2 (G : Type*) [Magma G] (h : Equation39327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq9 eq9
  have eq22 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq47 eq22


@[equational_result]
theorem Equation39329_implies_Equation2 (G : Type*) [Magma G] (h : Equation39329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation39331_implies_Equation2 (G : Type*) [Magma G] (h : Equation39331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq23 eq13


@[equational_result]
theorem Equation39333_implies_Equation2 (G : Type*) [Magma G] (h : Equation39333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq7 eq7
  have eq14 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation39337_implies_Equation2 (G : Type*) [Magma G] (h : Equation39337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (((X2 ◇ X2) ◇ (X3 ◇ X0)) ◇ X3)) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X3 X4 X5 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X3 ◇ X0)) ◇ X5) = X4 := superpose eq11 eq10
  have eq15 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation39339_implies_Equation2 (G : Type*) [Magma G] (h : Equation39339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq50 eq13


@[equational_result]
theorem Equation39340_implies_Equation2 (G : Type*) [Magma G] (h : Equation39340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation39341_implies_Equation2 (G : Type*) [Magma G] (h : Equation39341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq10 (X0 X2 X3 : G) : (X2 ◇ X0) = ((X0 ◇ X3) ◇ X3) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : ((X0 ◇ X3) ◇ X3) = X0 := superpose eq11 eq7
  have eq13 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq12 eq10
  have eq14 (X4 X5 : G) : (X5 ◇ X5) = X4 := superpose eq13 eq9
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq13 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation39342_implies_Equation2 (G : Type*) [Magma G] (h : Equation39342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39344_implies_Equation2 (G : Type*) [Magma G] (h : Equation39344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq9
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq7 eq13
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq30 eq19


@[equational_result]
theorem Equation39346_implies_Equation2 (G : Type*) [Magma G] (h : Equation39346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq53 eq20


@[equational_result]
theorem Equation39348_implies_Equation2 (G : Type*) [Magma G] (h : Equation39348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39349_implies_Equation2 (G : Type*) [Magma G] (h : Equation39349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39350_implies_Equation2 (G : Type*) [Magma G] (h : Equation39350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39352_implies_Equation2 (G : Type*) [Magma G] (h : Equation39352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39353_implies_Equation2 (G : Type*) [Magma G] (h : Equation39353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39354_implies_Equation2 (G : Type*) [Magma G] (h : Equation39354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39356_implies_Equation2 (G : Type*) [Magma G] (h : Equation39356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39357_implies_Equation2 (G : Type*) [Magma G] (h : Equation39357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39358_implies_Equation2 (G : Type*) [Magma G] (h : Equation39358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39359_implies_Equation2 (G : Type*) [Magma G] (h : Equation39359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39361_implies_Equation2 (G : Type*) [Magma G] (h : Equation39361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq10 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq12 eq13
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq21 eq14


@[equational_result]
theorem Equation39362_implies_Equation2 (G : Type*) [Magma G] (h : Equation39362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq35 eq12


@[equational_result]
theorem Equation39363_implies_Equation2 (G : Type*) [Magma G] (h : Equation39363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq49 eq17


@[equational_result]
theorem Equation39365_implies_Equation2 (G : Type*) [Magma G] (h : Equation39365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation39366_implies_Equation2 (G : Type*) [Magma G] (h : Equation39366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation39367_implies_Equation2 (G : Type*) [Magma G] (h : Equation39367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39369_implies_Equation2 (G : Type*) [Magma G] (h : Equation39369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation39370_implies_Equation2 (G : Type*) [Magma G] (h : Equation39370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation39371_implies_Equation2 (G : Type*) [Magma G] (h : Equation39371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39373_implies_Equation2 (G : Type*) [Magma G] (h : Equation39373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39374_implies_Equation2 (G : Type*) [Magma G] (h : Equation39374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39375_implies_Equation2 (G : Type*) [Magma G] (h : Equation39375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39376_implies_Equation2 (G : Type*) [Magma G] (h : Equation39376 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39378_implies_Equation2 (G : Type*) [Magma G] (h : Equation39378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq34 eq15


@[equational_result]
theorem Equation39379_implies_Equation2 (G : Type*) [Magma G] (h : Equation39379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation39380_implies_Equation2 (G : Type*) [Magma G] (h : Equation39380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation39381_implies_Equation2 (G : Type*) [Magma G] (h : Equation39381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ X4) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation39383_implies_Equation2 (G : Type*) [Magma G] (h : Equation39383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39384_implies_Equation2 (G : Type*) [Magma G] (h : Equation39384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39385_implies_Equation2 (G : Type*) [Magma G] (h : Equation39385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39386_implies_Equation2 (G : Type*) [Magma G] (h : Equation39386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39388_implies_Equation2 (G : Type*) [Magma G] (h : Equation39388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39389_implies_Equation2 (G : Type*) [Magma G] (h : Equation39389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39390_implies_Equation2 (G : Type*) [Magma G] (h : Equation39390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39391_implies_Equation2 (G : Type*) [Magma G] (h : Equation39391 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39393_implies_Equation2 (G : Type*) [Magma G] (h : Equation39393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39394_implies_Equation2 (G : Type*) [Magma G] (h : Equation39394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39395_implies_Equation2 (G : Type*) [Magma G] (h : Equation39395 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39396_implies_Equation2 (G : Type*) [Magma G] (h : Equation39396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39398_implies_Equation2 (G : Type*) [Magma G] (h : Equation39398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39399_implies_Equation2 (G : Type*) [Magma G] (h : Equation39399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39400_implies_Equation2 (G : Type*) [Magma G] (h : Equation39400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39401_implies_Equation2 (G : Type*) [Magma G] (h : Equation39401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39402_implies_Equation2 (G : Type*) [Magma G] (h : Equation39402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39404_implies_Equation2 (G : Type*) [Magma G] (h : Equation39404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X3 ◇ X3)) ◇ X3) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq11 eq7
  have eq26 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq10
  have eq29 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq10 eq11
  have eq32 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq15 eq26
  have eq33 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq11 eq15
  have eq37 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq15 eq10
  have eq40 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq32 eq33
  have eq44 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq40 eq29
  have eq46 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq40 eq7
  have eq47 (X0 X1 X2 X3 : G) : (((X0 ◇ (X3 ◇ X3)) ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) = X3 := superpose eq40 eq9
  have eq67 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X0 := superpose eq44 eq46
  have eq69 (X0 X1 X2 X3 : G) : (((X0 ◇ (X3 ◇ X3)) ◇ X3) ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq44 eq47
  have eq70 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X3) ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq40 eq69
  have eq71 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq44 eq70
  have eq78 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq71 eq37
  have eq84 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq78 eq67
  have eq92 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq78 eq84
  have eq95 (X0 X2 : G) : X0 = X2 := superpose eq92 eq92
  have eq97 (X0 : G) : sK0 ≠ X0 := superpose eq95 eq8
  subsumption eq97 eq95


@[equational_result]
theorem Equation39405_implies_Equation2 (G : Type*) [Magma G] (h : Equation39405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ (X3 ◇ X3)) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq10
  have eq18 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq13 eq18
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq44 eq40


@[equational_result]
theorem Equation39406_implies_Equation2 (G : Type*) [Magma G] (h : Equation39406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq24 eq17


@[equational_result]
theorem Equation39408_implies_Equation2 (G : Type*) [Magma G] (h : Equation39408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X3 ◇ X3)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X1)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X1)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0))) ◇ (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq22 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq10 eq9
  have eq28 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq22
  have eq51 (X0 X2 : G) : X0 = X2 := superpose eq22 eq28
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq130 eq51


@[equational_result]
theorem Equation39410_implies_Equation2 (G : Type*) [Magma G] (h : Equation39410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation39413_implies_Equation2 (G : Type*) [Magma G] (h : Equation39413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ (X3 ◇ X3)) ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq7 eq9
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq41 eq30


@[equational_result]
theorem Equation39414_implies_Equation2 (G : Type*) [Magma G] (h : Equation39414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39416_implies_Equation2 (G : Type*) [Magma G] (h : Equation39416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq54 eq15


@[equational_result]
theorem Equation39417_implies_Equation2 (G : Type*) [Magma G] (h : Equation39417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation39418_implies_Equation2 (G : Type*) [Magma G] (h : Equation39418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X4) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation39419_implies_Equation2 (G : Type*) [Magma G] (h : Equation39419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X0)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39421_implies_Equation2 (G : Type*) [Magma G] (h : Equation39421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X3 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0))) ◇ X3) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (X0 ◇ X1)) ◇ X0) = ((((X1 ◇ X2) ◇ X0) ◇ (((X1 ◇ X3) ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = (((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := superpose eq11 eq11
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq11 eq7
  have eq44 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))) ◇ X1) = ((X0 ◇ (((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))) ◇ X1)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) := superpose eq7 eq10
  have eq48 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) = ((X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq14 eq10
  have eq62 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq9 eq10
  have eq69 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq62 eq48
  have eq99 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq62 eq11
  have eq109 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq69 eq13
  have eq112 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) := superpose eq13 eq7
  have eq119 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq13 eq62
  have eq123 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq109
  have eq162 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose eq123 eq7
  have eq212 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) := superpose eq13 eq162
  have eq217 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq123 eq162
  have eq240 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq217
  have eq260 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq13 eq12
  have eq299 (X0 X1 : G) : (X0 ◇ X0) = (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq240 eq7
  have eq307 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = ((((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq240 eq12
  have eq316 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq299 eq307
  have eq317 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq240 eq316
  have eq320 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq317 eq299
  have eq321 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq123 eq320
  have eq328 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq321 eq119
  have eq354 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) := superpose eq321 eq99
  have eq412 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq11 eq328
  have eq419 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq412 eq112
  have eq426 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq412 eq212
  have eq428 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) = (((((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq412 eq260
  have eq433 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq11 eq426
  have eq434 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq321 eq433
  have eq466 (X0 X2 : G) : ((((X0 ◇ X2) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq434 eq419
  have eq477 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X0) = (((((X0 ◇ X2) ◇ X0) ◇ X0) ◇ X0) ◇ X0) := superpose eq434 eq428
  have eq478 (X0 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq466 eq477
  have eq479 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq321 eq478
  have eq508 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq479 eq354
  have eq509 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq321 eq508
  have eq678 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq509 eq509
  have eq747 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq434 eq678
  have eq748 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))) = ((X0 ◇ ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))))) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) := superpose eq747 eq44
  have eq826 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (X1 ◇ X2)) := superpose eq747 eq748
  have eq827 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ (X1 ◇ X1)) = ((X0 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X1))) ◇ X1) := superpose eq747 eq826
  have eq828 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X1 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq747 eq827
  have eq829 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X1 ◇ X3) ◇ X1) := superpose eq321 eq828
  have eq830 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq747 eq829
  have eq831 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq321 eq830
  have eq848 (X0 X1 : G) : X0 = X1 := superpose eq831 eq747
  have eq850 (X0 : G) : sK0 ≠ X0 := superpose eq848 eq8
  subsumption eq850 eq848


@[equational_result]
theorem Equation39423_implies_Equation2 (G : Type*) [Magma G] (h : Equation39423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X0 := superpose eq11 eq7
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq15 eq11
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq22 eq19


@[equational_result]
theorem Equation39425_implies_Equation2 (G : Type*) [Magma G] (h : Equation39425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X3 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ (X0 ◇ X1)) ◇ X1) = ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X5) ◇ ((X0 ◇ X4) ◇ (X2 ◇ X0))) ◇ X0) ◇ X0) = (((X0 ◇ X3) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0)) ◇ X0) := superpose eq10 eq10
  have eq18 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) ◇ X3) ◇ (X4 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1)) = (((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq7 eq10
  have eq24 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ X0) := superpose eq10 eq10
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X0 := superpose eq7 eq10
  have eq33 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ X0) = X2 := superpose eq25 eq24
  have eq35 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X2)) ◇ X2))) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X2)) ◇ X2)) = (((X1 ◇ X0) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X2)) ◇ X2)) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq9 eq9
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : ((((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ X5) ◇ X4) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) = (((X2 ◇ ((((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ X3) ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq10 eq9
  have eq54 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) ◇ X3) ◇ (X4 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1)) = ((X0 ◇ (X4 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq35 eq18
  have eq56 (X0 X1 X2 X4 X5 : G) : ((((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ X5) ◇ X4) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) = (((X2 ◇ ((X2 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq54 eq37
  have eq57 (X0 X1 X2 X4 X5 : G) : (X2 ◇ (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0))) = ((((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0) ◇ X5) ◇ X4) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq9 eq56
  have eq58 (X0 X1 X2 X4 : G) : ((X0 ◇ (X4 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1)) = (X0 ◇ ((X4 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq57 eq54
  have eq60 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X3 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1))) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1)) = X3 := superpose eq58 eq9
  have eq88 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = ((((X1 ◇ X4) ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1) ◇ X1) := superpose eq25 eq10
  have eq113 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X2) ◇ (X1 ◇ X1)) := superpose eq60 eq7
  have eq216 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq113 eq7
  have eq217 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1)) = X1 := superpose eq113 eq25
  have eq218 (X0 X1 : G) : (X1 ◇ X1) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ X1) := superpose eq113 eq33
  have eq251 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq216 eq218
  have eq290 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X1 := superpose eq251 eq217
  have eq308 (X0 X2 X4 X5 : G) : ((((X0 ◇ X5) ◇ ((X0 ◇ X4) ◇ (X2 ◇ X0))) ◇ X0) ◇ X0) = X0 := superpose eq290 eq16
  have eq309 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X1 := superpose eq308 eq88
  have eq310 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq309 eq7
  have eq432 (X0 X2 : G) : X0 = X2 := superpose eq310 eq310
  have eq434 (X0 : G) : sK0 ≠ X0 := superpose eq432 eq8
  subsumption eq434 eq432


@[equational_result]
theorem Equation39427_implies_Equation2 (G : Type*) [Magma G] (h : Equation39427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) ◇ X4) = X3 := superpose eq7 eq7
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq82 eq24


@[equational_result]
theorem Equation39431_implies_Equation2 (G : Type*) [Magma G] (h : Equation39431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq62 eq15


@[equational_result]
theorem Equation39433_implies_Equation2 (G : Type*) [Magma G] (h : Equation39433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq79 eq15


@[equational_result]
theorem Equation39434_implies_Equation2 (G : Type*) [Magma G] (h : Equation39434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation39435_implies_Equation2 (G : Type*) [Magma G] (h : Equation39435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X4) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq48 eq17


@[equational_result]
theorem Equation39436_implies_Equation2 (G : Type*) [Magma G] (h : Equation39436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39439_implies_Equation2 (G : Type*) [Magma G] (h : Equation39439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ (X3 ◇ X2)) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X2) := superpose eq11 eq9
  have eq21 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq34 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq20 eq7
  have eq49 (X0 X1 : G) : X0 = X1 := superpose eq34 eq21
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq66 eq49


@[equational_result]
theorem Equation39440_implies_Equation2 (G : Type*) [Magma G] (h : Equation39440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X0 := superpose eq11 eq7
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq13 eq11
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq21 eq18


@[equational_result]
theorem Equation39442_implies_Equation2 (G : Type*) [Magma G] (h : Equation39442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X3 ◇ X1)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X1)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X1)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ (X0 ◇ X3)) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = ((((X4 ◇ X1) ◇ (((X2 ◇ X3) ◇ (X0 ◇ X3)) ◇ X2)) ◇ X4) ◇ X4) := superpose eq7 eq10
  have eq18 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) = ((((X4 ◇ X1) ◇ X2) ◇ X4) ◇ X4) := superpose eq10 eq10
  have eq25 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X3) = (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ X1) := superpose eq10 eq10
  have eq26 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = X0 := superpose eq7 eq10
  have eq35 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ X1) = X2 := superpose eq26 eq25
  have eq54 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X1) ◇ X4) ◇ ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X1) ◇ X4)) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X1)) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq9 eq10
  have eq70 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (((X1 ◇ X1) ◇ X0) ◇ X1) := superpose eq7 eq26
  have eq98 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X1) = X1 := superpose eq7 eq35
  have eq135 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X0 := superpose eq26 eq70
  have eq199 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X1 ◇ (X0 ◇ X2))) = ((((X4 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ X2)) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ X2)) ◇ X4) ◇ X4) := superpose eq9 eq18
  have eq304 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X2) = ((X3 ◇ X4) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) ◇ X4)) := superpose eq10 eq135
  have eq312 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X2 ◇ X2) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0)) := superpose eq10 eq135
  have eq343 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X0 ◇ X1))) = ((((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X1) ◇ X1) ◇ X3) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X1)) := superpose eq304 eq54
  have eq344 (X0 X1 X2 X3 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X0 ◇ X1))) = ((X3 ◇ X3) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X1)) := superpose eq7 eq343
  have eq359 (X0 X1 X3 : G) : (X3 ◇ X1) = ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq312 eq344
  have eq360 (X1 X2 X3 X4 : G) : (X1 ◇ X2) = ((((X4 ◇ (((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ X2)) ◇ (((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ X2)) ◇ X4) ◇ X4) := superpose eq359 eq199
  have eq362 (X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X1 := superpose eq359 eq98
  have eq367 (X1 X2 X4 : G) : (X1 ◇ X2) = (X4 ◇ X4) := superpose eq362 eq360
  have eq484 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = X3 := superpose eq367 eq7
  have eq514 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X1 := superpose eq484 eq14
  have eq713 (X0 X1 : G) : X0 = X1 := superpose eq26 eq514
  have eq726 (X0 : G) : sK0 ≠ X0 := superpose eq713 eq8
  subsumption eq726 eq713


@[equational_result]
theorem Equation39444_implies_Equation2 (G : Type*) [Magma G] (h : Equation39444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq60 eq13


@[equational_result]
theorem Equation39447_implies_Equation2 (G : Type*) [Magma G] (h : Equation39447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ (X3 ◇ X2)) ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq7 eq9
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq124 eq57


@[equational_result]
theorem Equation39448_implies_Equation2 (G : Type*) [Magma G] (h : Equation39448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation39450_implies_Equation2 (G : Type*) [Magma G] (h : Equation39450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation39451_implies_Equation2 (G : Type*) [Magma G] (h : Equation39451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation39452_implies_Equation2 (G : Type*) [Magma G] (h : Equation39452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq11
  have eq22 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq13 eq11
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq22 eq22
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq33 eq31


@[equational_result]
theorem Equation39453_implies_Equation2 (G : Type*) [Magma G] (h : Equation39453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39455_implies_Equation2 (G : Type*) [Magma G] (h : Equation39455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X4))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq36 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq12 eq11
  have eq49 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq36 eq7
  have eq83 (X0 X3 : G) : X0 = X3 := superpose eq49 eq49
  have eq91 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq91 eq83


@[equational_result]
theorem Equation39456_implies_Equation2 (G : Type*) [Magma G] (h : Equation39456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ (X4 ◇ X5)) ◇ X4) ◇ X2) = X4 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq22 (X0 X2 X5 : G) : ((X0 ◇ X2) ◇ X5) = X2 := superpose eq7 eq9
  have eq36 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X0 := superpose eq22 eq7
  have eq46 (X0 X1 : G) : X0 = X1 := superpose eq11 eq36
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq65 eq46


@[equational_result]
theorem Equation39457_implies_Equation2 (G : Type*) [Magma G] (h : Equation39457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : ((X0 ◇ X3) ◇ X3) = X0 := superpose eq11 eq7
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq14 eq11
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq21 eq18


@[equational_result]
theorem Equation39458_implies_Equation2 (G : Type*) [Magma G] (h : Equation39458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X6 : G) : ((X0 ◇ X4) ◇ X6) = X4 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X0 := superpose eq11 eq7
  have eq19 (X0 X1 : G) : X0 = X1 := superpose eq14 eq11
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq22 eq19


@[equational_result]
theorem Equation39460_implies_Equation2 (G : Type*) [Magma G] (h : Equation39460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ (X0 ◇ X5)) ◇ X3) = ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 X4 X5 X7 X8 : G) : ((((X7 ◇ X8) ◇ X3) ◇ X7) ◇ X7) = (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ ((X3 ◇ X4) ◇ X5)) := superpose eq10 eq10
  have eq28 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X3 ◇ X4) ◇ ((X2 ◇ X5) ◇ X6)) ◇ X3) = (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ X7) := superpose eq10 eq10
  have eq29 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X4)) ◇ X1) = X0 := superpose eq7 eq10
  have eq31 (X0 X1 X2 X3 X4 X5 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ ((X3 ◇ X4) ◇ X5)) ◇ ((X3 ◇ X4) ◇ X5)) = X3 := superpose eq10 eq7
  have eq42 (X0 X1 X2 X7 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0) ◇ X7) = X2 := superpose eq29 eq28
  have eq46 (X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ X4) ◇ X5)) = X3 := superpose eq42 eq31
  have eq47 (X3 X7 X8 : G) : ((((X7 ◇ X8) ◇ X3) ◇ X7) ◇ X7) = X3 := superpose eq46 eq20
  have eq56 (X0 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ (X0 ◇ X5)) ◇ X3) = X0 := superpose eq47 eq10
  have eq63 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq56 eq7
  have eq66 (X3 X7 X8 : G) : (((X7 ◇ X8) ◇ X3) ◇ X7) = X3 := superpose eq63 eq47
  have eq74 (X3 X7 X8 : G) : ((X7 ◇ X8) ◇ X7) = X3 := superpose eq63 eq66
  have eq75 (X3 X7 : G) : (X7 ◇ X7) = X3 := superpose eq63 eq74
  have eq84 (X0 X1 : G) : X0 = X1 := superpose eq63 eq75
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq84 eq8
  subsumption eq94 eq84


@[equational_result]
theorem Equation39461_implies_Equation2 (G : Type*) [Magma G] (h : Equation39461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4))) ◇ X1) = X2 := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = (X0 ◇ X2) := superpose eq11 eq7
  have eq56 (X0 X2 X5 : G) : (X2 ◇ X5) = X0 := superpose eq7 eq21
  have eq188 (X0 X4 : G) : X0 = X4 := superpose eq7 eq56
  have eq374 (X0 : G) : sK0 ≠ X0 := superpose eq188 eq8
  subsumption eq374 eq188


@[equational_result]
theorem Equation39462_implies_Equation2 (G : Type*) [Magma G] (h : Equation39462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq51 eq13


@[equational_result]
theorem Equation39463_implies_Equation2 (G : Type*) [Magma G] (h : Equation39463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X0 ◇ X5) = X1 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation39465_implies_Equation2 (G : Type*) [Magma G] (h : Equation39465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq12 eq12
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X4 ◇ X5)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ X1) = X4 := superpose eq12 eq7
  have eq22 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq14 eq20
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq138 eq44


@[equational_result]
theorem Equation39466_implies_Equation2 (G : Type*) [Magma G] (h : Equation39466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ (X0 ◇ X5)) ◇ X4) = ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X2) := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X2) = X0 := superpose eq12 eq7
  have eq18 (X0 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ (X0 ◇ X5)) ◇ X4) = X0 := superpose eq15 eq10
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq18 eq7
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq20 eq15
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq20 eq21
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq20 eq26
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq36 eq28


@[equational_result]
theorem Equation39467_implies_Equation2 (G : Type*) [Magma G] (h : Equation39467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation39468_implies_Equation2 (G : Type*) [Magma G] (h : Equation39468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39470_implies_Equation2 (G : Type*) [Magma G] (h : Equation39470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq56 eq16


@[equational_result]
theorem Equation39471_implies_Equation2 (G : Type*) [Magma G] (h : Equation39471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation39472_implies_Equation2 (G : Type*) [Magma G] (h : Equation39472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation39473_implies_Equation2 (G : Type*) [Magma G] (h : Equation39473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39475_implies_Equation2 (G : Type*) [Magma G] (h : Equation39475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ X2)) = X4 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation39476_implies_Equation2 (G : Type*) [Magma G] (h : Equation39476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X5 X6 : G) : ((X0 ◇ X6) ◇ X5) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation39477_implies_Equation2 (G : Type*) [Magma G] (h : Equation39477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39478_implies_Equation2 (G : Type*) [Magma G] (h : Equation39478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X6 : G) : ((X0 ◇ X6) ◇ X6) = X4 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq27 eq18


@[equational_result]
theorem Equation39479_implies_Equation2 (G : Type*) [Magma G] (h : Equation39479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39481_implies_Equation2 (G : Type*) [Magma G] (h : Equation39481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) ◇ X3)) ◇ X3) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) ◇ X0) ◇ X1) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq11
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0)) = X1 := superpose eq7 eq9
  have eq50 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) = ((((((((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) ◇ X0) ◇ X1) ◇ X4) ◇ X1) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) ◇ X0) ◇ X1)) := superpose eq7 eq10
  have eq61 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) ◇ X2) ◇ X0) = ((X0 ◇ ((((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) ◇ X2) ◇ X0)) ◇ X0) := superpose eq10 eq11
  have eq63 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (((((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X2) ◇ (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq17 eq17
  have eq87 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) := superpose eq17 eq11
  have eq88 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := superpose eq17 eq12
  have eq89 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (((((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X2) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq63
  have eq129 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq87 eq7
  have eq182 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq17 eq88
  have eq193 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq88 eq17
  have eq210 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq7 eq182
  have eq212 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq210 eq89
  have eq213 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq129 eq193
  have eq470 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq129 eq11
  have eq717 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) = ((X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ X0)) ◇ X0) := superpose eq470 eq61
  have eq744 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq717
  have eq756 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq744 eq11
  have eq856 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq744 eq210
  have eq857 (X0 X2 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq744 eq212
  have eq886 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq756 eq213
  have eq965 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) = X0 := superpose eq744 eq857
  have eq966 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq965 eq886
  have eq1016 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq966 eq856
  have eq1038 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq744 eq1016
  have eq1040 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) ◇ X0) ◇ X1)) := superpose eq1038 eq50
  have eq1098 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0)) ◇ X1) := superpose eq1038 eq1040
  have eq1099 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq1038 eq1098
  have eq1100 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq1038 eq1099
  have eq1101 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq1038 eq1100
  have eq1113 (X0 X2 : G) : X0 = X2 := superpose eq1101 eq1101
  have eq1115 (X0 : G) : sK0 ≠ X0 := superpose eq1113 eq8
  subsumption eq1115 eq1113


@[equational_result]
theorem Equation39483_implies_Equation2 (G : Type*) [Magma G] (h : Equation39483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) ◇ X4)) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (((X0 ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq25 eq17


@[equational_result]
theorem Equation39487_implies_Equation2 (G : Type*) [Magma G] (h : Equation39487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0))) ◇ X4) = X3 := superpose eq7 eq7
  have eq26 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq84 eq26


@[equational_result]
theorem Equation39491_implies_Equation2 (G : Type*) [Magma G] (h : Equation39491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ X4) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq58 eq17


@[equational_result]
theorem Equation39493_implies_Equation2 (G : Type*) [Magma G] (h : Equation39493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq58 eq15


@[equational_result]
theorem Equation39494_implies_Equation2 (G : Type*) [Magma G] (h : Equation39494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq54 eq15


@[equational_result]
theorem Equation39495_implies_Equation2 (G : Type*) [Magma G] (h : Equation39495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X4) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq48 eq17


@[equational_result]
theorem Equation39496_implies_Equation2 (G : Type*) [Magma G] (h : Equation39496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X0)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation39498_implies_Equation2 (G : Type*) [Magma G] (h : Equation39498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0))) ◇ X3) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X0) := superpose eq10 eq10
  have eq18 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X0 ◇ ((((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X0) ◇ (((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X0))) ◇ X1) ◇ ((X0 ◇ ((((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X0) ◇ (((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X0))) ◇ X1))) ◇ X4) ◇ ((X0 ◇ ((((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X0) ◇ (((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X0))) ◇ X1)) = X4 := superpose eq7 eq9
  have eq25 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X1) ◇ (((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X1))) ◇ X0) := superpose eq9 eq10
  have eq32 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq12 eq12
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq12 eq12
  have eq34 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq10 eq12
  have eq36 (X0 X1 X2 : G) : (((X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X2 := superpose eq12 eq9
  have eq40 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) ◇ X2) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X2 := superpose eq12 eq9
  have eq41 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq12 eq7
  have eq55 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X0) ◇ (((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X0))))) ◇ X4) ◇ ((X0 ◇ ((((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X0) ◇ (((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X0))) ◇ X1)) = X4 := superpose eq33 eq18
  have eq58 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X4) ◇ ((X0 ◇ ((((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X0) ◇ (((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X0))) ◇ X1)) = X4 := superpose eq32 eq55
  have eq59 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X4) ◇ ((X0 ◇ ((((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X0) ◇ (((X2 ◇ X3) ◇ (X2 ◇ X2)) ◇ X0))) ◇ X1)) = X4 := superpose eq33 eq58
  have eq60 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X4) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X1)) = X4 := superpose eq34 eq59
  have eq61 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := superpose eq34 eq25
  have eq65 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq34 eq33
  have eq70 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X1)) = X4 := superpose eq65 eq60
  have eq71 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X2 := superpose eq34 eq36
  have eq73 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X2 := superpose eq10 eq40
  have eq74 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq61 eq41
  have eq81 (X0 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = X2 := superpose eq74 eq73
  have eq84 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq65 eq81
  have eq87 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X0 := superpose eq84 eq61
  have eq89 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq84 eq71
  have eq99 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X4) ◇ X1) = X4 := superpose eq87 eq70
  have eq100 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq87 eq89
  have eq101 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq100 eq87
  have eq102 (X1 X4 : G) : (X4 ◇ X1) = X4 := superpose eq101 eq99
  have eq137 (X0 X1 : G) : X0 = X1 := superpose eq101 eq102
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq137 eq8
  subsumption eq151 eq137


@[equational_result]
theorem Equation39500_implies_Equation2 (G : Type*) [Magma G] (h : Equation39500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0))) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (((X0 ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq29 eq17


@[equational_result]
theorem Equation39502_implies_Equation2 (G : Type*) [Magma G] (h : Equation39502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39503_implies_Equation2 (G : Type*) [Magma G] (h : Equation39503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39504_implies_Equation2 (G : Type*) [Magma G] (h : Equation39504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39506_implies_Equation2 (G : Type*) [Magma G] (h : Equation39506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39507_implies_Equation2 (G : Type*) [Magma G] (h : Equation39507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39508_implies_Equation2 (G : Type*) [Magma G] (h : Equation39508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39510_implies_Equation2 (G : Type*) [Magma G] (h : Equation39510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39511_implies_Equation2 (G : Type*) [Magma G] (h : Equation39511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39512_implies_Equation2 (G : Type*) [Magma G] (h : Equation39512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39513_implies_Equation2 (G : Type*) [Magma G] (h : Equation39513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39515_implies_Equation2 (G : Type*) [Magma G] (h : Equation39515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3) ◇ (X0 ◇ X0)) = X3 := superpose eq9 eq9
  have eq26 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq10 eq9
  have eq29 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := superpose eq9 eq7
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq29 eq26
  have eq35 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) ◇ (X0 ◇ X0)) = X3 := superpose eq34 eq25
  have eq38 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq34 eq10
  have eq46 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X0)) = X3 := superpose eq34 eq35
  have eq48 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq38 eq34
  have eq49 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X0)) = X3 := superpose eq48 eq46
  have eq56 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X3 := superpose eq48 eq49
  have eq57 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq48 eq56
  have eq58 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq48 eq57
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq58 eq58
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq64 eq59


@[equational_result]
theorem Equation39516_implies_Equation2 (G : Type*) [Magma G] (h : Equation39516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq9 eq9
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq11 eq7
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq24 eq22


@[equational_result]
theorem Equation39517_implies_Equation2 (G : Type*) [Magma G] (h : Equation39517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (((X0 ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq10 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation39519_implies_Equation2 (G : Type*) [Magma G] (h : Equation39519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation39520_implies_Equation2 (G : Type*) [Magma G] (h : Equation39520 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation39521_implies_Equation2 (G : Type*) [Magma G] (h : Equation39521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39523_implies_Equation2 (G : Type*) [Magma G] (h : Equation39523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation39524_implies_Equation2 (G : Type*) [Magma G] (h : Equation39524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation39525_implies_Equation2 (G : Type*) [Magma G] (h : Equation39525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39527_implies_Equation2 (G : Type*) [Magma G] (h : Equation39527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39528_implies_Equation2 (G : Type*) [Magma G] (h : Equation39528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39529_implies_Equation2 (G : Type*) [Magma G] (h : Equation39529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39530_implies_Equation2 (G : Type*) [Magma G] (h : Equation39530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39532_implies_Equation2 (G : Type*) [Magma G] (h : Equation39532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X4)) ◇ X5) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq11 eq7
  have eq17 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) = X4 := superpose eq11 eq7
  have eq19 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ X0) ◇ X5) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0)) = X5 := superpose eq16 eq9
  have eq24 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) = ((X0 ◇ X0) ◇ (((X4 ◇ X5) ◇ (X4 ◇ X6)) ◇ (X0 ◇ X0))) := superpose eq19 eq19
  have eq41 (X0 X1 X2 X6 : G) : ((((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X0) ◇ X6) ◇ ((X1 ◇ X1) ◇ X0)) = X6 := superpose eq19 eq7
  have eq70 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq16 eq7
  have eq78 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) = X4 := superpose eq70 eq17
  have eq82 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) = X0 := superpose eq78 eq24
  have eq84 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq82 eq7
  have eq92 (X0 X1 X2 X6 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ X6) ◇ ((X1 ◇ X1) ◇ X0)) = X6 := superpose eq84 eq41
  have eq111 (X1 X2 X6 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X6) ◇ (X1 ◇ X1)) = X6 := superpose eq84 eq92
  have eq112 (X1 X2 X6 : G) : (((X1 ◇ X2) ◇ X6) ◇ X1) = X6 := superpose eq84 eq111
  have eq113 (X1 X2 X6 : G) : ((X1 ◇ X2) ◇ X1) = X6 := superpose eq84 eq112
  have eq114 (X1 X6 : G) : (X1 ◇ X1) = X6 := superpose eq84 eq113
  have eq121 (X0 X1 : G) : X0 = X1 := superpose eq84 eq114
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq121 eq8
  subsumption eq135 eq121


@[equational_result]
theorem Equation39533_implies_Equation2 (G : Type*) [Magma G] (h : Equation39533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X4)) ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) = X1 := superpose eq7 eq7
  have eq31 (X0 X1 X2 X3 X5 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ X5) ◇ X3) = X5 := superpose eq11 eq9
  have eq32 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X4) ◇ (X3 ◇ X5))) ◇ X6) ◇ X1) = X4 := superpose eq7 eq9
  have eq53 (X1 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ (X3 ◇ X5)) ◇ X1) = X4 := superpose eq31 eq32
  have eq54 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq53 eq7
  have eq70 (X0 X2 : G) : X0 = X2 := superpose eq54 eq54
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq72 eq70


@[equational_result]
theorem Equation39534_implies_Equation2 (G : Type*) [Magma G] (h : Equation39534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq61 eq18


@[equational_result]
theorem Equation39535_implies_Equation2 (G : Type*) [Magma G] (h : Equation39535 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (((X0 ◇ ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X0) ◇ X5)) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq11 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (((X0 ◇ X0) ◇ X6) ◇ X7) = X6 := superpose eq7 eq9
  have eq16 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq11 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq29 eq17


@[equational_result]
theorem Equation39537_implies_Equation2 (G : Type*) [Magma G] (h : Equation39537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39538_implies_Equation2 (G : Type*) [Magma G] (h : Equation39538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39539_implies_Equation2 (G : Type*) [Magma G] (h : Equation39539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39540_implies_Equation2 (G : Type*) [Magma G] (h : Equation39540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39542_implies_Equation2 (G : Type*) [Magma G] (h : Equation39542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39543_implies_Equation2 (G : Type*) [Magma G] (h : Equation39543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39544_implies_Equation2 (G : Type*) [Magma G] (h : Equation39544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39545_implies_Equation2 (G : Type*) [Magma G] (h : Equation39545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39547_implies_Equation2 (G : Type*) [Magma G] (h : Equation39547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39548_implies_Equation2 (G : Type*) [Magma G] (h : Equation39548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39549_implies_Equation2 (G : Type*) [Magma G] (h : Equation39549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39550_implies_Equation2 (G : Type*) [Magma G] (h : Equation39550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39552_implies_Equation2 (G : Type*) [Magma G] (h : Equation39552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39553_implies_Equation2 (G : Type*) [Magma G] (h : Equation39553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39554_implies_Equation2 (G : Type*) [Magma G] (h : Equation39554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39555_implies_Equation2 (G : Type*) [Magma G] (h : Equation39555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39556_implies_Equation2 (G : Type*) [Magma G] (h : Equation39556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39559_implies_Equation2 (G : Type*) [Magma G] (h : Equation39559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ (X2 ◇ X3)) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq11
  have eq22 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq9
  have eq45 (X0 X2 : G) : X0 = X2 := superpose eq13 eq22
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq49 eq45


@[equational_result]
theorem Equation39560_implies_Equation2 (G : Type*) [Magma G] (h : Equation39560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ (X3 ◇ X4)) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X0)) ◇ X0)) ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq9 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation39564_implies_Equation2 (G : Type*) [Magma G] (h : Equation39564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation39567_implies_Equation2 (G : Type*) [Magma G] (h : Equation39567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ (X2 ◇ X3)) ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = X3 := superpose eq7 eq9
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq98 eq35


@[equational_result]
theorem Equation39568_implies_Equation2 (G : Type*) [Magma G] (h : Equation39568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation39570_implies_Equation2 (G : Type*) [Magma G] (h : Equation39570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq57 eq16


@[equational_result]
theorem Equation39571_implies_Equation2 (G : Type*) [Magma G] (h : Equation39571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ X2) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation39572_implies_Equation2 (G : Type*) [Magma G] (h : Equation39572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq11
  have eq24 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = X3 := superpose eq14 eq11
  have eq28 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq14 eq24
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation39573_implies_Equation2 (G : Type*) [Magma G] (h : Equation39573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : (((X0 ◇ (X4 ◇ X5)) ◇ X6) ◇ X7) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X0)) ◇ X4)) ◇ X0) ◇ X6) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X4 X5 X7 : G) : (X4 ◇ X7) = X5 := superpose eq9 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation39577_implies_Equation2 (G : Type*) [Magma G] (h : Equation39577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = X0 := superpose eq11 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq15 eq15
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq20 eq18


@[equational_result]
theorem Equation39579_implies_Equation2 (G : Type*) [Magma G] (h : Equation39579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39580_implies_Equation2 (G : Type*) [Magma G] (h : Equation39580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39581_implies_Equation2 (G : Type*) [Magma G] (h : Equation39581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39583_implies_Equation2 (G : Type*) [Magma G] (h : Equation39583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39584_implies_Equation2 (G : Type*) [Magma G] (h : Equation39584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39585_implies_Equation2 (G : Type*) [Magma G] (h : Equation39585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39587_implies_Equation2 (G : Type*) [Magma G] (h : Equation39587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39588_implies_Equation2 (G : Type*) [Magma G] (h : Equation39588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39589_implies_Equation2 (G : Type*) [Magma G] (h : Equation39589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39590_implies_Equation2 (G : Type*) [Magma G] (h : Equation39590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39593_implies_Equation2 (G : Type*) [Magma G] (h : Equation39593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq10 eq7
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq10 eq14
  have eq19 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq17 eq7
  have eq26 (X0 X1 : G) : X0 = X1 := superpose eq19 eq17
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq36 eq26


@[equational_result]
theorem Equation39594_implies_Equation2 (G : Type*) [Magma G] (h : Equation39594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X0 := superpose eq11 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq20 eq18


@[equational_result]
theorem Equation39596_implies_Equation2 (G : Type*) [Magma G] (h : Equation39596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39597_implies_Equation2 (G : Type*) [Magma G] (h : Equation39597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39598_implies_Equation2 (G : Type*) [Magma G] (h : Equation39598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39600_implies_Equation2 (G : Type*) [Magma G] (h : Equation39600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39601_implies_Equation2 (G : Type*) [Magma G] (h : Equation39601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation39602_implies_Equation2 (G : Type*) [Magma G] (h : Equation39602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39604_implies_Equation2 (G : Type*) [Magma G] (h : Equation39604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39605_implies_Equation2 (G : Type*) [Magma G] (h : Equation39605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39606_implies_Equation2 (G : Type*) [Magma G] (h : Equation39606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39607_implies_Equation2 (G : Type*) [Magma G] (h : Equation39607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39609_implies_Equation2 (G : Type*) [Magma G] (h : Equation39609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X3))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq35 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq11
  have eq36 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq12 eq11
  have eq52 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq36 eq35
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq52 eq52
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq70 eq58


@[equational_result]
theorem Equation39610_implies_Equation2 (G : Type*) [Magma G] (h : Equation39610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ (X2 ◇ X4)) ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq22 (X0 X2 X5 : G) : ((X0 ◇ X5) ◇ X2) = X5 := superpose eq7 eq9
  have eq36 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X0 := superpose eq22 eq7
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq36 eq36
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq53 eq45


@[equational_result]
theorem Equation39611_implies_Equation2 (G : Type*) [Magma G] (h : Equation39611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X0 := superpose eq11 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq20 eq18


@[equational_result]
theorem Equation39612_implies_Equation2 (G : Type*) [Magma G] (h : Equation39612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : (((X0 ◇ (X4 ◇ X5)) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X6 X7 : G) : ((((X1 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X4)) ◇ X0)) ◇ X0) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq9 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation39614_implies_Equation2 (G : Type*) [Magma G] (h : Equation39614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39615_implies_Equation2 (G : Type*) [Magma G] (h : Equation39615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39616_implies_Equation2 (G : Type*) [Magma G] (h : Equation39616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39617_implies_Equation2 (G : Type*) [Magma G] (h : Equation39617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39619_implies_Equation2 (G : Type*) [Magma G] (h : Equation39619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39620_implies_Equation2 (G : Type*) [Magma G] (h : Equation39620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39621_implies_Equation2 (G : Type*) [Magma G] (h : Equation39621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39622_implies_Equation2 (G : Type*) [Magma G] (h : Equation39622 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39624_implies_Equation2 (G : Type*) [Magma G] (h : Equation39624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39625_implies_Equation2 (G : Type*) [Magma G] (h : Equation39625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39626_implies_Equation2 (G : Type*) [Magma G] (h : Equation39626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39627_implies_Equation2 (G : Type*) [Magma G] (h : Equation39627 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39629_implies_Equation2 (G : Type*) [Magma G] (h : Equation39629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39630_implies_Equation2 (G : Type*) [Magma G] (h : Equation39630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39631_implies_Equation2 (G : Type*) [Magma G] (h : Equation39631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39632_implies_Equation2 (G : Type*) [Magma G] (h : Equation39632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39633_implies_Equation2 (G : Type*) [Magma G] (h : Equation39633 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39635_implies_Equation2 (G : Type*) [Magma G] (h : Equation39635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X0 ◇ (X1 ◇ X4)) = X1 := superpose eq7 eq12
  have eq20 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ X4) = X2 := superpose eq13 eq11
  have eq23 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq20 eq10
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq12 eq23
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq33 eq24


@[equational_result]
theorem Equation39636_implies_Equation2 (G : Type*) [Magma G] (h : Equation39636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X4) ◇ X2) = X4 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : ((X0 ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq11 eq7
  have eq20 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X0 := superpose eq15 eq7
  have eq22 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq20 eq10
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq11 eq22
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq53 eq26


@[equational_result]
theorem Equation39637_implies_Equation2 (G : Type*) [Magma G] (h : Equation39637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq24 eq17


@[equational_result]
theorem Equation39638_implies_Equation2 (G : Type*) [Magma G] (h : Equation39638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 X7 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq11 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq7
  have eq14 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation39640_implies_Equation2 (G : Type*) [Magma G] (h : Equation39640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq54 eq19


@[equational_result]
theorem Equation39641_implies_Equation2 (G : Type*) [Magma G] (h : Equation39641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X2) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq56 eq19


@[equational_result]
theorem Equation39642_implies_Equation2 (G : Type*) [Magma G] (h : Equation39642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq51 eq13


@[equational_result]
theorem Equation39643_implies_Equation2 (G : Type*) [Magma G] (h : Equation39643 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation39645_implies_Equation2 (G : Type*) [Magma G] (h : Equation39645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X1) = X3 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq53 eq22


@[equational_result]
theorem Equation39646_implies_Equation2 (G : Type*) [Magma G] (h : Equation39646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq12
  have eq18 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) = X0 := superpose eq13 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq13 eq18
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq13 eq23
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation39647_implies_Equation2 (G : Type*) [Magma G] (h : Equation39647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ X3) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation39648_implies_Equation2 (G : Type*) [Magma G] (h : Equation39648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39650_implies_Equation2 (G : Type*) [Magma G] (h : Equation39650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq56 eq16


@[equational_result]
theorem Equation39651_implies_Equation2 (G : Type*) [Magma G] (h : Equation39651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ X4) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation39652_implies_Equation2 (G : Type*) [Magma G] (h : Equation39652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X3) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation39653_implies_Equation2 (G : Type*) [Magma G] (h : Equation39653 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39655_implies_Equation2 (G : Type*) [Magma G] (h : Equation39655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : (X0 ◇ (X1 ◇ X2)) = X5 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation39656_implies_Equation2 (G : Type*) [Magma G] (h : Equation39656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 X6 : G) : ((X0 ◇ X6) ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation39657_implies_Equation2 (G : Type*) [Magma G] (h : Equation39657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39658_implies_Equation2 (G : Type*) [Magma G] (h : Equation39658 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X6 : G) : ((X0 ◇ X6) ◇ X6) = X5 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq26 eq17


@[equational_result]
theorem Equation39659_implies_Equation2 (G : Type*) [Magma G] (h : Equation39659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39661_implies_Equation2 (G : Type*) [Magma G] (h : Equation39661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X5) ◇ X1) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) = X4 := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq10
  have eq21 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq16 eq14
  have eq27 (X0 X1 X5 : G) : (X0 ◇ X1) = X5 := superpose eq21 eq10
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation39662_implies_Equation2 (G : Type*) [Magma G] (h : Equation39662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq12 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X2) = X5 := superpose eq7 eq10
  have eq22 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X2) = X0 := superpose eq12 eq7
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq22 eq22
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation39663_implies_Equation2 (G : Type*) [Magma G] (h : Equation39663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq56 eq18


@[equational_result]
theorem Equation39664_implies_Equation2 (G : Type*) [Magma G] (h : Equation39664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 X7 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq11 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq7
  have eq15 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq28 eq16


@[equational_result]
theorem Equation39666_implies_Equation2 (G : Type*) [Magma G] (h : Equation39666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39667_implies_Equation2 (G : Type*) [Magma G] (h : Equation39667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39668_implies_Equation2 (G : Type*) [Magma G] (h : Equation39668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39669_implies_Equation2 (G : Type*) [Magma G] (h : Equation39669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39671_implies_Equation2 (G : Type*) [Magma G] (h : Equation39671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39672_implies_Equation2 (G : Type*) [Magma G] (h : Equation39672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39673_implies_Equation2 (G : Type*) [Magma G] (h : Equation39673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39674_implies_Equation2 (G : Type*) [Magma G] (h : Equation39674 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39676_implies_Equation2 (G : Type*) [Magma G] (h : Equation39676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39677_implies_Equation2 (G : Type*) [Magma G] (h : Equation39677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39678_implies_Equation2 (G : Type*) [Magma G] (h : Equation39678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39679_implies_Equation2 (G : Type*) [Magma G] (h : Equation39679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39681_implies_Equation2 (G : Type*) [Magma G] (h : Equation39681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39682_implies_Equation2 (G : Type*) [Magma G] (h : Equation39682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39683_implies_Equation2 (G : Type*) [Magma G] (h : Equation39683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39684_implies_Equation2 (G : Type*) [Magma G] (h : Equation39684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39685_implies_Equation2 (G : Type*) [Magma G] (h : Equation39685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39687_implies_Equation2 (G : Type*) [Magma G] (h : Equation39687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X5) ◇ X1) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X2))) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq10
  have eq23 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq17 eq11
  have eq30 (X0 X1 X5 : G) : (X0 ◇ X1) = X5 := superpose eq23 eq10
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq30 eq30
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation39688_implies_Equation2 (G : Type*) [Magma G] (h : Equation39688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ (X4 ◇ X2)) ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq11 (X0 X4 : G) : ((X0 ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X1 X3 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X3) = X5 := superpose eq7 eq9
  have eq35 (X0 X2 X5 : G) : (X0 ◇ X2) = X5 := superpose eq19 eq10
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq11 eq35
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq61 eq38


@[equational_result]
theorem Equation39689_implies_Equation2 (G : Type*) [Magma G] (h : Equation39689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = X0 := superpose eq11 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq21 eq18


@[equational_result]
theorem Equation39690_implies_Equation2 (G : Type*) [Magma G] (h : Equation39690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 X7 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq11 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq7
  have eq14 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq28 eq16


@[equational_result]
theorem Equation39692_implies_Equation2 (G : Type*) [Magma G] (h : Equation39692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39693_implies_Equation2 (G : Type*) [Magma G] (h : Equation39693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39694_implies_Equation2 (G : Type*) [Magma G] (h : Equation39694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39695_implies_Equation2 (G : Type*) [Magma G] (h : Equation39695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39697_implies_Equation2 (G : Type*) [Magma G] (h : Equation39697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39698_implies_Equation2 (G : Type*) [Magma G] (h : Equation39698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39699_implies_Equation2 (G : Type*) [Magma G] (h : Equation39699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39700_implies_Equation2 (G : Type*) [Magma G] (h : Equation39700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39702_implies_Equation2 (G : Type*) [Magma G] (h : Equation39702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39703_implies_Equation2 (G : Type*) [Magma G] (h : Equation39703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39704_implies_Equation2 (G : Type*) [Magma G] (h : Equation39704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39705_implies_Equation2 (G : Type*) [Magma G] (h : Equation39705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39707_implies_Equation2 (G : Type*) [Magma G] (h : Equation39707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39708_implies_Equation2 (G : Type*) [Magma G] (h : Equation39708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39709_implies_Equation2 (G : Type*) [Magma G] (h : Equation39709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39710_implies_Equation2 (G : Type*) [Magma G] (h : Equation39710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39711_implies_Equation2 (G : Type*) [Magma G] (h : Equation39711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X2)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39713_implies_Equation2 (G : Type*) [Magma G] (h : Equation39713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X3))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq11 eq11
  have eq21 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq12 eq10
  have eq28 (X0 X1 : G) : X0 = X1 := superpose eq11 eq21
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq32 eq28


@[equational_result]
theorem Equation39714_implies_Equation2 (G : Type*) [Magma G] (h : Equation39714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X3 ◇ X3)) = X2 := superpose eq7 eq7
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq39 eq23


@[equational_result]
theorem Equation39715_implies_Equation2 (G : Type*) [Magma G] (h : Equation39715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : ((X3 ◇ X3) ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq18 eq15


@[equational_result]
theorem Equation39716_implies_Equation2 (G : Type*) [Magma G] (h : Equation39716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 X7 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq11 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq7
  have eq14 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq28 eq16


@[equational_result]
theorem Equation39718_implies_Equation2 (G : Type*) [Magma G] (h : Equation39718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39719_implies_Equation2 (G : Type*) [Magma G] (h : Equation39719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39720_implies_Equation2 (G : Type*) [Magma G] (h : Equation39720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39721_implies_Equation2 (G : Type*) [Magma G] (h : Equation39721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39723_implies_Equation2 (G : Type*) [Magma G] (h : Equation39723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39724_implies_Equation2 (G : Type*) [Magma G] (h : Equation39724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39725_implies_Equation2 (G : Type*) [Magma G] (h : Equation39725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39726_implies_Equation2 (G : Type*) [Magma G] (h : Equation39726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39728_implies_Equation2 (G : Type*) [Magma G] (h : Equation39728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39729_implies_Equation2 (G : Type*) [Magma G] (h : Equation39729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39730_implies_Equation2 (G : Type*) [Magma G] (h : Equation39730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation39731_implies_Equation2 (G : Type*) [Magma G] (h : Equation39731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39733_implies_Equation2 (G : Type*) [Magma G] (h : Equation39733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39734_implies_Equation2 (G : Type*) [Magma G] (h : Equation39734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39735_implies_Equation2 (G : Type*) [Magma G] (h : Equation39735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39736_implies_Equation2 (G : Type*) [Magma G] (h : Equation39736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39737_implies_Equation2 (G : Type*) [Magma G] (h : Equation39737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39739_implies_Equation2 (G : Type*) [Magma G] (h : Equation39739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X7) ◇ X1) = X7 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ X6) ◇ (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X5))) = X6 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 X6 : G) : ((X0 ◇ X6) ◇ X4) = X6 := superpose eq12 eq11
  have eq16 (X0 X1 X7 : G) : (X0 ◇ X1) = X7 := superpose eq13 eq10
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq25 eq17


@[equational_result]
theorem Equation39740_implies_Equation2 (G : Type*) [Magma G] (h : Equation39740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X4 ◇ X5)) = X3 := superpose eq7 eq7
  have eq27 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq45 eq27


@[equational_result]
theorem Equation39741_implies_Equation2 (G : Type*) [Magma G] (h : Equation39741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X6 : G) : ((X0 ◇ X6) ◇ X3) = X6 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ X3) = X0 := superpose eq11 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq21 eq18


@[equational_result]
theorem Equation39742_implies_Equation2 (G : Type*) [Magma G] (h : Equation39742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 X7 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X7) ◇ X6) = X7 := superpose eq7 eq7
  have eq11 (X0 X5 X6 : G) : ((X0 ◇ X6) ◇ X5) = X6 := superpose eq7 eq7
  have eq14 (X0 X6 X7 : G) : (X0 ◇ X6) = X7 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq28 eq16


@[equational_result]
theorem Equation39743_implies_Equation2 (G : Type*) [Magma G] (h : Equation39743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X8 X9 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X8) ◇ X9) = X8 := superpose eq7 eq7
  have eq11 (X0 X7 X8 : G) : ((X0 ◇ X7) ◇ X8) = X7 := superpose eq7 eq7
  have eq14 (X0 X8 X9 : G) : (X0 ◇ X9) = X8 := superpose eq11 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq28 eq16


@[equational_result]
theorem Equation39745_implies_Equation2 (G : Type*) [Magma G] (h : Equation39745 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39746_implies_Equation2 (G : Type*) [Magma G] (h : Equation39746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39747_implies_Equation2 (G : Type*) [Magma G] (h : Equation39747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39748_implies_Equation2 (G : Type*) [Magma G] (h : Equation39748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39749_implies_Equation2 (G : Type*) [Magma G] (h : Equation39749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X1) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39751_implies_Equation2 (G : Type*) [Magma G] (h : Equation39751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39752_implies_Equation2 (G : Type*) [Magma G] (h : Equation39752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39753_implies_Equation2 (G : Type*) [Magma G] (h : Equation39753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39754_implies_Equation2 (G : Type*) [Magma G] (h : Equation39754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39755_implies_Equation2 (G : Type*) [Magma G] (h : Equation39755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X2) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39757_implies_Equation2 (G : Type*) [Magma G] (h : Equation39757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39758_implies_Equation2 (G : Type*) [Magma G] (h : Equation39758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39759_implies_Equation2 (G : Type*) [Magma G] (h : Equation39759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39760_implies_Equation2 (G : Type*) [Magma G] (h : Equation39760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39761_implies_Equation2 (G : Type*) [Magma G] (h : Equation39761 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X3) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39763_implies_Equation2 (G : Type*) [Magma G] (h : Equation39763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39764_implies_Equation2 (G : Type*) [Magma G] (h : Equation39764 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39765_implies_Equation2 (G : Type*) [Magma G] (h : Equation39765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39766_implies_Equation2 (G : Type*) [Magma G] (h : Equation39766 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation39767_implies_Equation2 (G : Type*) [Magma G] (h : Equation39767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39769_implies_Equation2 (G : Type*) [Magma G] (h : Equation39769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39770_implies_Equation2 (G : Type*) [Magma G] (h : Equation39770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39771_implies_Equation2 (G : Type*) [Magma G] (h : Equation39771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39772_implies_Equation2 (G : Type*) [Magma G] (h : Equation39772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39773_implies_Equation2 (G : Type*) [Magma G] (h : Equation39773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39774_implies_Equation2 (G : Type*) [Magma G] (h : Equation39774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ X6) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation39980_implies_Equation2 (G : Type*) [Magma G] (h : Equation39980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq10
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq12 eq7
  have eq22 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq20 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq28 eq23


@[equational_result]
theorem Equation39983_implies_Equation2 (G : Type*) [Magma G] (h : Equation39983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X2) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = X1 := superpose eq12 eq11
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq12 eq12
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = X1 := superpose eq15 eq13
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq39 eq24


@[equational_result]
theorem Equation39985_implies_Equation2 (G : Type*) [Magma G] (h : Equation39985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq10 eq7
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq98 eq24


@[equational_result]
theorem Equation39986_implies_Equation2 (G : Type*) [Magma G] (h : Equation39986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq10
  have eq14 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq11 eq7
  have eq19 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq14 eq9
  have eq28 (X2 X3 : G) : (X3 ◇ X3) = X2 := superpose eq19 eq9
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq28 eq28
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation39987_implies_Equation2 (G : Type*) [Magma G] (h : Equation39987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ X5) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X0 := superpose eq10 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq14 eq11
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq26 eq19


@[equational_result]
theorem Equation39990_implies_Equation2 (G : Type*) [Magma G] (h : Equation39990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) = ((X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) ◇ X2) := superpose eq7 eq11
  have eq15 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq11 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ X3) = X2 := superpose eq12 eq10
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq15 eq11
  have eq21 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X3) = X2 := superpose eq20 eq18
  have eq26 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X3) = X2 := superpose eq20 eq21
  have eq27 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq20 eq26
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq33 eq28


@[equational_result]
theorem Equation39993_implies_Equation2 (G : Type*) [Magma G] (h : Equation39993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) ◇ X2) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) ◇ X3) = X2 := superpose eq7 eq11
  have eq20 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq12
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq7 eq20
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq162 eq50


@[equational_result]
theorem Equation39995_implies_Equation2 (G : Type*) [Magma G] (h : Equation39995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq10 eq7
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq77 eq28


@[equational_result]
theorem Equation39997_implies_Equation2 (G : Type*) [Magma G] (h : Equation39997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation39999_implies_Equation2 (G : Type*) [Magma G] (h : Equation39999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X2 := superpose eq11 eq7
  have eq19 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq15 eq7
  have eq23 (X0 X2 : G) : X0 = X2 := superpose eq11 eq19
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq32 eq23


@[equational_result]
theorem Equation40000_implies_Equation2 (G : Type*) [Magma G] (h : Equation40000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq9
  have eq17 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq11 eq7
  have eq21 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq23 eq21


@[equational_result]
theorem Equation40001_implies_Equation2 (G : Type*) [Magma G] (h : Equation40001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40003_implies_Equation2 (G : Type*) [Magma G] (h : Equation40003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2) ◇ (X1 ◇ X1))) ◇ ((((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2) ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2)) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) = X1 := superpose eq11 eq10
  have eq16 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X1 ◇ X1))) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X1 ◇ X1))) = X1 := superpose eq11 eq9
  have eq23 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := superpose eq7 eq15
  have eq28 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X1 ◇ X1))) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X1 ◇ X1))) = X1 := superpose eq23 eq16
  have eq34 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq23
  have eq39 (X0 X1 X3 : G) : (((X0 ◇ X3) ◇ X0) ◇ X0) = X1 := superpose eq34 eq28
  have eq47 (X0 X3 : G) : X0 = X3 := superpose eq39 eq39
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq64 eq47


@[equational_result]
theorem Equation40005_implies_Equation2 (G : Type*) [Magma G] (h : Equation40005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq51 eq13


@[equational_result]
theorem Equation40008_implies_Equation2 (G : Type*) [Magma G] (h : Equation40008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq11 eq11
  have eq15 (X2 X3 : G) : ((X3 ◇ X3) ◇ X3) = X2 := superpose eq14 eq9
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq15 eq15
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation40009_implies_Equation2 (G : Type*) [Magma G] (h : Equation40009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40011_implies_Equation2 (G : Type*) [Magma G] (h : Equation40011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq60 eq16


@[equational_result]
theorem Equation40012_implies_Equation2 (G : Type*) [Magma G] (h : Equation40012 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation40013_implies_Equation2 (G : Type*) [Magma G] (h : Equation40013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq46 eq12


@[equational_result]
theorem Equation40014_implies_Equation2 (G : Type*) [Magma G] (h : Equation40014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40017_implies_Equation2 (G : Type*) [Magma G] (h : Equation40017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq10
  have eq18 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq11 eq7
  have eq20 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq18 eq11
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq26 eq21


@[equational_result]
theorem Equation40020_implies_Equation2 (G : Type*) [Magma G] (h : Equation40020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq19 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq10
  have eq54 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq143 eq54


@[equational_result]
theorem Equation40022_implies_Equation2 (G : Type*) [Magma G] (h : Equation40022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq10 eq7
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq128 eq40


@[equational_result]
theorem Equation40024_implies_Equation2 (G : Type*) [Magma G] (h : Equation40024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq13 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation40027_implies_Equation2 (G : Type*) [Magma G] (h : Equation40027 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ (((X2 ◇ X0) ◇ X2) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0))) ◇ X3) ◇ X4) = X3 := superpose eq7 eq10
  have eq24 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq11
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq24 eq7
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation40030_implies_Equation2 (G : Type*) [Magma G] (h : Equation40030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq73 eq52


@[equational_result]
theorem Equation40032_implies_Equation2 (G : Type*) [Magma G] (h : Equation40032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2) = ((((X1 ◇ X0) ◇ X1) ◇ X3) ◇ X1) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X4) ◇ X0) := superpose eq9 eq9
  have eq22 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X2) = X0 := superpose eq7 eq9
  have eq37 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0)) ◇ X0) ◇ X3) := superpose eq9 eq22
  have eq107 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0)) ◇ X0) ◇ X3) := superpose eq14 eq22
  have eq135 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq37 eq107
  have eq144 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ X1) = X0 := superpose eq135 eq7
  have eq309 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X2 := superpose eq144 eq144
  have eq321 (X0 X3 : G) : X0 = X3 := superpose eq309 eq309
  have eq372 (X0 : G) : sK0 ≠ X0 := superpose eq321 eq8
  subsumption eq372 eq321


@[equational_result]
theorem Equation40033_implies_Equation2 (G : Type*) [Magma G] (h : Equation40033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X3) ◇ X3) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) = ((((X0 ◇ X1) ◇ X0) ◇ X4) ◇ X4) := superpose eq9 eq9
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ (X0 ◇ X3)) ◇ X3) ◇ ((X4 ◇ (X1 ◇ X4)) ◇ X4)) = (((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ ((X4 ◇ (X1 ◇ X4)) ◇ X4)) ◇ X5) ◇ X5) := superpose eq9 eq9
  have eq18 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ (((X2 ◇ X1) ◇ X2) ◇ X3)) ◇ X3) ◇ ((X2 ◇ X1) ◇ X2)) = (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) ◇ X4) ◇ X4) := superpose eq9 eq9
  have eq22 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ ((X1 ◇ X4) ◇ X3)) ◇ X3) ◇ X4) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X0) := superpose eq9 eq9
  have eq23 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) ◇ X2) = X0 := superpose eq7 eq9
  have eq29 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X0) = X1 := superpose eq23 eq22
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1)) ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq29 eq9
  have eq62 (X0 X1 X2 X4 : G) : (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) ◇ X4) ◇ X4) = (X1 ◇ X2) := superpose eq57 eq18
  have eq70 (X0 X1 X2 X4 : G) : (X1 ◇ X0) = ((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X4) ◇ X4) := superpose eq9 eq62
  have eq71 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = ((X0 ◇ X2) ◇ X2) := superpose eq23 eq62
  have eq99 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X3) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq71 eq71
  have eq104 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ X2) = X0 := superpose eq23 eq71
  have eq125 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X0 := superpose eq71 eq29
  have eq288 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) ◇ X3) = X0 := superpose eq71 eq104
  have eq461 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = ((((X0 ◇ X1) ◇ X3) ◇ X3) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X2)) := superpose eq29 eq125
  have eq481 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq13 eq125
  have eq529 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq29 eq481
  have eq530 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) = X0 := superpose eq529 eq7
  have eq531 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X3) ◇ X3) = (((X0 ◇ X2) ◇ X2) ◇ X1) := superpose eq529 eq9
  have eq537 (X0 X1 X2 X3 X4 X5 : G) : (((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ ((X4 ◇ (X1 ◇ X4)) ◇ X4)) ◇ X5) ◇ X5) = (((X0 ◇ X3) ◇ X3) ◇ ((X4 ◇ (X1 ◇ X4)) ◇ X4)) := superpose eq529 eq16
  have eq646 (X0 X1 X2 X3 X4 X5 : G) : (((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) ◇ ((X1 ◇ X4) ◇ X4)) ◇ X5) ◇ X5) = (((X0 ◇ X3) ◇ X3) ◇ ((X1 ◇ X4) ◇ X4)) := superpose eq529 eq537
  have eq647 (X0 X1 X3 X4 : G) : (((X0 ◇ X3) ◇ X3) ◇ ((X1 ◇ X4) ◇ X4)) = X1 := superpose eq288 eq646
  have eq648 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := superpose eq647 eq461
  have eq650 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose eq648 eq29
  have eq653 (X0 X1 X4 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X4) ◇ X4) := superpose eq648 eq70
  have eq659 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X2) ◇ X2) ◇ X1) := superpose eq653 eq531
  have eq663 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X3) ◇ X3) := superpose eq659 eq99
  have eq665 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq659 eq530
  have eq677 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X3) = X0 := superpose eq665 eq288
  have eq689 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq677 eq663
  have eq693 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq689 eq650
  have eq700 (X0 X2 : G) : X0 = X2 := superpose eq693 eq693
  have eq702 (X0 : G) : sK0 ≠ X0 := superpose eq700 eq8
  subsumption eq702 eq700


@[equational_result]
theorem Equation40034_implies_Equation2 (G : Type*) [Magma G] (h : Equation40034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation40036_implies_Equation2 (G : Type*) [Magma G] (h : Equation40036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq10
  have eq13 (X0 X1 X2 : G) : (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X2 := superpose eq10 eq7
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq14 eq13
  have eq16 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = X1 := superpose eq14 eq11
  have eq20 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq16 eq15
  have eq22 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq20 eq14
  have eq24 (X0 X1 : G) : X0 = X1 := superpose eq20 eq22
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq34 eq24


@[equational_result]
theorem Equation40038_implies_Equation2 (G : Type*) [Magma G] (h : Equation40038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40040_implies_Equation2 (G : Type*) [Magma G] (h : Equation40040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) = ((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X2) ◇ X1) = X0 := superpose eq7 eq9
  have eq41 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X2 := superpose eq22 eq22
  have eq66 (X0 X3 : G) : X0 = X3 := superpose eq41 eq41
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq66 eq8
  subsumption eq123 eq66


@[equational_result]
theorem Equation40041_implies_Equation2 (G : Type*) [Magma G] (h : Equation40041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X2)) ◇ X1) ◇ X2) = ((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ X3) := superpose eq7 eq7
  have eq24 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) ◇ X1) = X0 := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X1) ◇ X4) ◇ X2) = (((X3 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) ◇ X3)) ◇ X4) ◇ X3) := superpose eq9 eq24
  have eq40 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = (((X1 ◇ X0) ◇ X2) ◇ X1) := superpose eq24 eq24
  have eq50 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ X2) = X0 := superpose eq40 eq7
  have eq56 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X1) ◇ X4) ◇ X2) = (((X3 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) ◇ X3)) ◇ X4) ◇ X3) := superpose eq40 eq34
  have eq82 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq24 eq50
  have eq84 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq50 eq50
  have eq100 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq84 eq50
  have eq108 (X0 X1 : G) : (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose eq100 eq84
  have eq112 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose eq100 eq50
  have eq114 (X0 X1 : G) : (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0))) = X1 := superpose eq82 eq108
  have eq115 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq112 eq114
  have eq119 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) ◇ X3)) ◇ X4) ◇ X3) = X2 := superpose eq115 eq56
  have eq172 (X2 X3 X4 : G) : (X4 ◇ X3) = X2 := superpose eq115 eq119
  have eq173 (X0 X1 : G) : X0 = X1 := superpose eq100 eq172
  have eq181 (X0 : G) : sK0 ≠ X0 := superpose eq173 eq8
  subsumption eq181 eq173


@[equational_result]
theorem Equation40042_implies_Equation2 (G : Type*) [Magma G] (h : Equation40042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq69 eq12


@[equational_result]
theorem Equation40044_implies_Equation2 (G : Type*) [Magma G] (h : Equation40044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) = ((((X1 ◇ X0) ◇ X3) ◇ X3) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X5) ◇ X5) ◇ X3) = (((X3 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0)) ◇ X4) ◇ X4) := superpose eq9 eq9
  have eq31 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X1 ◇ X0)) = (((X3 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0)) ◇ X4) ◇ X4) := superpose eq7 eq12
  have eq431 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq7 eq31
  have eq512 (X0 X3 : G) : X0 = X3 := superpose eq431 eq431
  have eq691 (X0 : G) : sK0 ≠ X0 := superpose eq512 eq8
  subsumption eq691 eq512


@[equational_result]
theorem Equation40046_implies_Equation2 (G : Type*) [Magma G] (h : Equation40046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation40048_implies_Equation2 (G : Type*) [Magma G] (h : Equation40048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation40049_implies_Equation2 (G : Type*) [Magma G] (h : Equation40049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation40050_implies_Equation2 (G : Type*) [Magma G] (h : Equation40050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq46 eq12


@[equational_result]
theorem Equation40051_implies_Equation2 (G : Type*) [Magma G] (h : Equation40051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40053_implies_Equation2 (G : Type*) [Magma G] (h : Equation40053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X3)) ◇ X0) ◇ X0) = ((((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X0) ◇ X0)) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X0) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) ◇ X0)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((((X1 ◇ X3) ◇ ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) ◇ X4)) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0)) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0))) = X1 := superpose eq7 eq10
  have eq23 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = ((((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X1) := superpose eq10 eq7
  have eq26 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq11 eq11
  have eq29 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq11 eq11
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = ((((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X1) := superpose eq11 eq7
  have eq47 (X0 X2 : G) : ((((X2 ◇ X0) ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq7 eq23
  have eq51 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq23 eq10
  have eq107 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq7 eq47
  have eq108 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq47 eq47
  have eq112 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X0 := superpose eq47 eq7
  have eq115 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq47 eq10
  have eq131 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq107 eq115
  have eq132 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq107 eq131
  have eq133 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X3)) ◇ X0)) := superpose eq132 eq29
  have eq156 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq35 eq47
  have eq185 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq108 eq9
  have eq221 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = (((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq133 eq7
  have eq246 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq108 eq107
  have eq262 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq107 eq47
  have eq267 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq246 eq156
  have eq268 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq246 eq26
  have eq280 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) = (((X0 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0)) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0)) ◇ X0) := superpose eq246 eq185
  have eq300 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq107 eq262
  have eq301 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq107 eq300
  have eq302 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq246 eq301
  have eq304 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq302 eq221
  have eq307 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq302 eq51
  have eq312 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq302 eq112
  have eq338 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = ((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) ◇ X0) := superpose eq302 eq304
  have eq339 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq302 eq338
  have eq340 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq339 eq268
  have eq341 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq340 eq267
  have eq344 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq302 eq307
  have eq350 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq302 eq312
  have eq352 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq350 eq339
  have eq355 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq352 eq341
  have eq359 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq355 eq344
  have eq387 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq246 eq359
  have eq391 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) = X0 := superpose eq387 eq7
  have eq393 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((((X1 ◇ X3) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X4)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) = X1 := superpose eq387 eq12
  have eq400 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = (((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X0) := superpose eq387 eq280
  have eq431 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ X3) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X4)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) = X1 := superpose eq387 eq393
  have eq442 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X0) := superpose eq387 eq400
  have eq443 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq355 eq442
  have eq448 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X1 := superpose eq443 eq431
  have eq449 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq443 eq391
  have eq461 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq443 eq448
  have eq467 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq449 eq461
  have eq653 (X0 X1 : G) : X0 = X1 := superpose eq449 eq467
  have eq658 (X0 : G) : sK0 ≠ X0 := superpose eq653 eq8
  subsumption eq658 eq653


@[equational_result]
theorem Equation40054_implies_Equation2 (G : Type*) [Magma G] (h : Equation40054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq10
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq12 eq7
  have eq23 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq20 eq12
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq29 eq24


@[equational_result]
theorem Equation40055_implies_Equation2 (G : Type*) [Magma G] (h : Equation40055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 : G) : (((X0 ◇ X3) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq10
  have eq20 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq12 eq7
  have eq23 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq20 eq12
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq29 eq24


@[equational_result]
theorem Equation40059_implies_Equation2 (G : Type*) [Magma G] (h : Equation40059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ X3) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X1)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ X3) ◇ (X1 ◇ (X0 ◇ X2))) ◇ X5) = X3 := superpose eq12 eq10
  have eq17 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq12 eq13
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq26 eq18


@[equational_result]
theorem Equation40062_implies_Equation2 (G : Type*) [Magma G] (h : Equation40062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq10
  have eq26 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq17 eq7
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq26 eq26
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation40063_implies_Equation2 (G : Type*) [Magma G] (h : Equation40063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq14 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation40065_implies_Equation2 (G : Type*) [Magma G] (h : Equation40065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X0 ◇ X4) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq11 eq7
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq130 eq40


@[equational_result]
theorem Equation40066_implies_Equation2 (G : Type*) [Magma G] (h : Equation40066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X5 : G) : (((X0 ◇ X2) ◇ X5) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq10 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq14 eq11
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation40067_implies_Equation2 (G : Type*) [Magma G] (h : Equation40067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 : G) : (((X0 ◇ X3) ◇ X5) ◇ X5) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq7 eq7
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq11 eq10
  have eq60 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq65 eq60


@[equational_result]
theorem Equation40068_implies_Equation2 (G : Type*) [Magma G] (h : Equation40068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X6 X7 : G) : (((X0 ◇ X4) ◇ X6) ◇ X7) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq14 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation40072_implies_Equation2 (G : Type*) [Magma G] (h : Equation40072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X4) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40074_implies_Equation2 (G : Type*) [Magma G] (h : Equation40074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X2) = ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) ◇ ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) ◇ ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X1) ◇ X1) = X0 := superpose eq7 eq9
  have eq55 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = ((((X5 ◇ ((X2 ◇ ((((X0 ◇ X3) ◇ (X2 ◇ X4)) ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3))) ◇ ((((X0 ◇ X3) ◇ (X2 ◇ X4)) ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3)))) ◇ X5) ◇ X5) ◇ X5) := superpose eq10 eq9
  have eq77 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = (X2 ◇ X5) := superpose eq22 eq55
  have eq86 (X0 X1 X4 X5 : G) : (X0 ◇ X1) = (X4 ◇ X5) := superpose eq77 eq77
  have eq146 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq86
  have eq262 (X0 X3 : G) : X0 = X3 := superpose eq7 eq146
  have eq396 (X0 : G) : sK0 ≠ X0 := superpose eq262 eq8
  subsumption eq396 eq262


@[equational_result]
theorem Equation40075_implies_Equation2 (G : Type*) [Magma G] (h : Equation40075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X2) = ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X3) := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ (X2 ◇ X3)))) ◇ X0) ◇ X0) ◇ (((X2 ◇ X3) ◇ X1) ◇ (X2 ◇ X3))) ◇ X3) = X2 := superpose eq9 eq7
  have eq37 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq7 eq29
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq7 eq37
  have eq144 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq144 eq58


@[equational_result]
theorem Equation40076_implies_Equation2 (G : Type*) [Magma G] (h : Equation40076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2))) ◇ X4) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X6 : G) : (((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) ◇ (((X3 ◇ X4) ◇ X0) ◇ (X3 ◇ X4))) ◇ X6) = X3 := superpose eq7 eq11
  have eq25 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq7 eq12
  have eq63 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq182 eq63


@[equational_result]
theorem Equation40078_implies_Equation2 (G : Type*) [Magma G] (h : Equation40078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X3) = ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X1) := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) ◇ X2) = X0 := superpose eq7 eq9
  have eq58 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq23 eq23
  have eq90 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X2)) ◇ X1) = X0 := superpose eq58 eq7
  have eq158 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (((X0 ◇ X2) ◇ X1) ◇ X2))) ◇ X1) = X1 := superpose eq90 eq90
  have eq167 (X0 X1 X2 : G) : (X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X2)) = X1 := superpose eq158 eq23
  have eq236 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ X2)) = X2 := superpose eq90 eq167
  have eq238 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) ◇ X0)) = X0 := superpose eq158 eq167
  have eq256 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ X0) = X0 := superpose eq158 eq238
  have eq257 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) = X2 := superpose eq256 eq236
  have eq261 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq257 eq167
  have eq296 (X0 X3 : G) : X0 = X3 := superpose eq23 eq261
  have eq450 (X0 : G) : sK0 ≠ X0 := superpose eq296 eq8
  subsumption eq450 eq296


@[equational_result]
theorem Equation40080_implies_Equation2 (G : Type*) [Magma G] (h : Equation40080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq73 eq15


@[equational_result]
theorem Equation40082_implies_Equation2 (G : Type*) [Magma G] (h : Equation40082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X1 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq11 eq7
  have eq64 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq150 eq64


@[equational_result]
theorem Equation40083_implies_Equation2 (G : Type*) [Magma G] (h : Equation40083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq75 eq12


@[equational_result]
theorem Equation40084_implies_Equation2 (G : Type*) [Magma G] (h : Equation40084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((X0 ◇ X3) ◇ X3) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X1 := superpose eq7 eq7
  have eq42 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ X1))) = X3 := superpose eq11 eq12
  have eq43 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq12 eq12
  have eq55 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq43 eq42
  have eq58 (X0 X4 : G) : X0 = X4 := superpose eq7 eq55
  have eq178 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq178 eq58


@[equational_result]
theorem Equation40085_implies_Equation2 (G : Type*) [Magma G] (h : Equation40085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X0 ◇ X5) = X1 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40088_implies_Equation2 (G : Type*) [Magma G] (h : Equation40088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq10
  have eq20 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq12 eq7
  have eq22 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq24 eq22


@[equational_result]
theorem Equation40089_implies_Equation2 (G : Type*) [Magma G] (h : Equation40089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40093_implies_Equation2 (G : Type*) [Magma G] (h : Equation40093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq52 eq13


@[equational_result]
theorem Equation40096_implies_Equation2 (G : Type*) [Magma G] (h : Equation40096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq71 eq17


@[equational_result]
theorem Equation40097_implies_Equation2 (G : Type*) [Magma G] (h : Equation40097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq56 eq15


@[equational_result]
theorem Equation40099_implies_Equation2 (G : Type*) [Magma G] (h : Equation40099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) = X3 := superpose eq7 eq7
  have eq37 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq57 eq37


@[equational_result]
theorem Equation40100_implies_Equation2 (G : Type*) [Magma G] (h : Equation40100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40101_implies_Equation2 (G : Type*) [Magma G] (h : Equation40101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation40102_implies_Equation2 (G : Type*) [Magma G] (h : Equation40102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40104_implies_Equation2 (G : Type*) [Magma G] (h : Equation40104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq12 eq12
  have eq23 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq14 eq12
  have eq33 (X0 X2 : G) : X0 = X2 := superpose eq23 eq23
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq35 eq33


@[equational_result]
theorem Equation40105_implies_Equation2 (G : Type*) [Magma G] (h : Equation40105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X5 : G) : (((X0 ◇ X5) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40106_implies_Equation2 (G : Type*) [Magma G] (h : Equation40106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 : G) : (((X0 ◇ X5) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq7 eq10
  have eq20 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq12 eq7
  have eq23 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation40107_implies_Equation2 (G : Type*) [Magma G] (h : Equation40107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X6 X7 : G) : (((X0 ◇ X6) ◇ X4) ◇ X7) = X4 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40109_implies_Equation2 (G : Type*) [Magma G] (h : Equation40109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ (X0 ◇ X3)) ◇ X4) ◇ X2) = ((((X1 ◇ X0) ◇ X5) ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4)) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4)) = X1 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X1) = (((X0 ◇ X7) ◇ (((X2 ◇ (X0 ◇ X5)) ◇ X6) ◇ X2)) ◇ (((X2 ◇ (X0 ◇ X5)) ◇ X6) ◇ X2)) := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X4) ◇ X1) = X0 := superpose eq7 eq9
  have eq67 (X0 X1 X2 X3 X5 X6 : G) : (X0 ◇ X1) = ((((X5 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3))) ◇ X6) ◇ X5) ◇ X5) := superpose eq11 eq9
  have eq76 (X0 X1 X5 : G) : (X0 ◇ X1) = (X0 ◇ X5) := superpose eq29 eq67
  have eq99 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X4) ◇ X0) ◇ X0) = X2 := superpose eq76 eq7
  have eq110 (X0 X1 X2 X3 X5 : G) : ((X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X5)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X5)) = X0 := superpose eq76 eq11
  have eq149 (X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X1) = X2 := superpose eq110 eq22
  have eq151 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq149 eq7
  have eq171 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X4) ◇ X0) = X2 := superpose eq151 eq99
  have eq217 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq151 eq171
  have eq218 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq151 eq217
  have eq258 (X0 X1 : G) : X0 = X1 := superpose eq151 eq218
  have eq277 (X0 : G) : sK0 ≠ X0 := superpose eq258 eq8
  subsumption eq277 eq258


@[equational_result]
theorem Equation40110_implies_Equation2 (G : Type*) [Magma G] (h : Equation40110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4)) ◇ X2) = X1 := superpose eq7 eq7
  have eq20 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq7
  have eq72 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq181 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq181 eq72


@[equational_result]
theorem Equation40111_implies_Equation2 (G : Type*) [Magma G] (h : Equation40111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40112_implies_Equation2 (G : Type*) [Magma G] (h : Equation40112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation40114_implies_Equation2 (G : Type*) [Magma G] (h : Equation40114 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation40115_implies_Equation2 (G : Type*) [Magma G] (h : Equation40115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40116_implies_Equation2 (G : Type*) [Magma G] (h : Equation40116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq56 eq15


@[equational_result]
theorem Equation40117_implies_Equation2 (G : Type*) [Magma G] (h : Equation40117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40119_implies_Equation2 (G : Type*) [Magma G] (h : Equation40119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq12 eq12
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ ((X0 ◇ X4) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X5))) ◇ X1) = X2 := superpose eq12 eq7
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq16 eq21
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq160 eq47


@[equational_result]
theorem Equation40120_implies_Equation2 (G : Type*) [Magma G] (h : Equation40120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40121_implies_Equation2 (G : Type*) [Magma G] (h : Equation40121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 : G) : (((X0 ◇ X5) ◇ X5) ◇ X5) = X3 := superpose eq7 eq7
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq30 eq23


@[equational_result]
theorem Equation40122_implies_Equation2 (G : Type*) [Magma G] (h : Equation40122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40124_implies_Equation2 (G : Type*) [Magma G] (h : Equation40124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation40125_implies_Equation2 (G : Type*) [Magma G] (h : Equation40125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40126_implies_Equation2 (G : Type*) [Magma G] (h : Equation40126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40127_implies_Equation2 (G : Type*) [Magma G] (h : Equation40127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40128_implies_Equation2 (G : Type*) [Magma G] (h : Equation40128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X7 : G) : (X0 ◇ X7) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40131_implies_Equation2 (G : Type*) [Magma G] (h : Equation40131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq11
  have eq18 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq12 eq7
  have eq20 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq18 eq12
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq26 eq21


@[equational_result]
theorem Equation40134_implies_Equation2 (G : Type*) [Magma G] (h : Equation40134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) ◇ X0) ◇ X2) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq9
  have eq19 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq11
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq55 eq27


@[equational_result]
theorem Equation40136_implies_Equation2 (G : Type*) [Magma G] (h : Equation40136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq10 eq7
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq101 eq38


@[equational_result]
theorem Equation40138_implies_Equation2 (G : Type*) [Magma G] (h : Equation40138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ X5) = X3 := superpose eq7 eq9
  have eq13 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq12 eq7
  have eq14 (X3 X5 : G) : (X3 ◇ X5) = X3 := superpose eq13 eq12
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq14 eq13
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40141_implies_Equation2 (G : Type*) [Magma G] (h : Equation40141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq17 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq11
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq17 eq7
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq29 eq29
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq33 eq31


@[equational_result]
theorem Equation40144_implies_Equation2 (G : Type*) [Magma G] (h : Equation40144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq9
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq34 eq24


@[equational_result]
theorem Equation40146_implies_Equation2 (G : Type*) [Magma G] (h : Equation40146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2)) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1)) ◇ X2) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1)) = X0 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2)) := superpose eq7 eq10
  have eq28 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) ◇ X0) ◇ X1) = X2 := superpose eq14 eq7
  have eq55 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq28 eq7
  have eq80 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2))) ◇ X3) = X0 := superpose eq7 eq55
  have eq81 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X4 ◇ ((((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2)) ◇ X3))) ◇ X4) = X0 := superpose eq9 eq55
  have eq113 (X0 X1 X2 X3 : G) : (((X2 ◇ (X2 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1))) ◇ X2) ◇ X1) = X3 := superpose eq55 eq28
  have eq161 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ X2) = X0 := superpose eq55 eq7
  have eq178 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq80 eq113
  have eq205 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X4 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2)) ◇ X3))) ◇ X4) = X0 := superpose eq161 eq81
  have eq347 (X0 X4 : G) : ((X4 ◇ (X4 ◇ X0)) ◇ X4) = X0 := superpose eq161 eq205
  have eq348 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq347 eq55
  have eq367 (X0 X1 : G) : X0 = X1 := superpose eq348 eq178
  have eq381 (X0 : G) : sK0 ≠ X0 := superpose eq367 eq8
  subsumption eq381 eq367


@[equational_result]
theorem Equation40148_implies_Equation2 (G : Type*) [Magma G] (h : Equation40148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation40150_implies_Equation2 (G : Type*) [Magma G] (h : Equation40150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X2 := superpose eq10 eq7
  have eq19 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq16 eq7
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq35 eq33


@[equational_result]
theorem Equation40152_implies_Equation2 (G : Type*) [Magma G] (h : Equation40152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) ◇ X0) ◇ X4) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ X3) ◇ X5) = X3 := superpose eq7 eq9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq12 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40154_implies_Equation2 (G : Type*) [Magma G] (h : Equation40154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) ◇ X0) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) = X0 := superpose eq7 eq9
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0) = ((((((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0)) ◇ X0) ◇ X3) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0))) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0))) := superpose eq10 eq7
  have eq19 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X1))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X1))) := superpose eq7 eq18
  have eq50 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) = (((((X2 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) ◇ X3) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))) := superpose eq19 eq7
  have eq67 (X0 X1 : G) : ((X0 ◇ (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) = ((X0 ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))) := superpose eq9 eq50
  have eq85 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) = ((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))) := superpose eq7 eq67
  have eq107 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) = ((((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) ◇ X0) ◇ X0) := superpose eq85 eq7
  have eq108 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0))) = (((((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0))) ◇ X2) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0))))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0))))) := superpose eq85 eq7
  have eq114 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))))) ◇ X2) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0))))) = (((((((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))))) ◇ X2) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0))))) ◇ X3) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))))) ◇ X2) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0))))))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)))))) ◇ X2) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0))))))) := superpose eq85 eq18
  have eq117 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) = X0 := superpose eq7 eq107
  have eq122 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq117 eq85
  have eq123 (X0 X2 : G) : (X0 ◇ X0) = (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq117 eq108
  have eq129 (X0 X2 X3 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) = (((((X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3) ◇ (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq117 eq114
  have eq163 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq122 eq10
  have eq168 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq122 eq7
  have eq270 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq122 eq163
  have eq271 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq168 eq163
  have eq378 (X0 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) = (((((X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq270 eq129
  have eq404 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq270 eq117
  have eq406 (X0 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X2) ◇ X0) ◇ X0) := superpose eq270 eq123
  have eq496 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = (((((X0 ◇ ((X0 ◇ X2) ◇ X0)) ◇ X0) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0))) := superpose eq270 eq378
  have eq505 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = ((((X0 ◇ X0) ◇ X3) ◇ X0) ◇ X0) := superpose eq404 eq496
  have eq509 (X0 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X2) ◇ X0) := superpose eq406 eq505
  have eq820 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X0 := superpose eq271 eq509
  have eq1210 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X1 := superpose eq271 eq7
  have eq1248 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq820 eq1210
  have eq1307 (X0 X2 : G) : X0 = X2 := superpose eq1248 eq1248
  have eq1467 (X0 : G) : sK0 ≠ X0 := superpose eq1307 eq8
  subsumption eq1467 eq1307


@[equational_result]
theorem Equation40156_implies_Equation2 (G : Type*) [Magma G] (h : Equation40156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation40160_implies_Equation2 (G : Type*) [Magma G] (h : Equation40160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq52 eq13


@[equational_result]
theorem Equation40162_implies_Equation2 (G : Type*) [Magma G] (h : Equation40162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq66 eq17


@[equational_result]
theorem Equation40163_implies_Equation2 (G : Type*) [Magma G] (h : Equation40163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation40164_implies_Equation2 (G : Type*) [Magma G] (h : Equation40164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq46 eq12


@[equational_result]
theorem Equation40165_implies_Equation2 (G : Type*) [Magma G] (h : Equation40165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation40168_implies_Equation2 (G : Type*) [Magma G] (h : Equation40168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq12
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq13 eq7
  have eq23 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq20 eq13
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq29 eq24


@[equational_result]
theorem Equation40171_implies_Equation2 (G : Type*) [Magma G] (h : Equation40171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) ◇ X0) ◇ X2) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq9
  have eq36 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq7 eq12
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq7 eq36
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq121 eq50


@[equational_result]
theorem Equation40173_implies_Equation2 (G : Type*) [Magma G] (h : Equation40173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq23 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq37 eq23


@[equational_result]
theorem Equation40174_implies_Equation2 (G : Type*) [Magma G] (h : Equation40174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = ((X0 ◇ X2) ◇ X2) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) ◇ X2) ◇ X2) = X1 := superpose eq10 eq7
  have eq22 (X0 X1 X2 : G) : (((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) ◇ X2) ◇ X2) = X1 := superpose eq10 eq16
  have eq23 (X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X1 := superpose eq10 eq22
  have eq24 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X0 := superpose eq23 eq9
  have eq27 (X0 X1 : G) : (((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1)) = X1 := superpose eq10 eq24
  have eq39 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) = X1 := superpose eq10 eq27
  have eq40 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq10 eq39
  have eq42 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X1) = X1 := superpose eq40 eq10
  have eq46 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq40 eq42
  have eq47 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq40 eq46
  have eq48 (X1 X2 : G) : (X2 ◇ X2) = X1 := superpose eq47 eq23
  have eq53 (X0 X1 : G) : X0 = X1 := superpose eq47 eq48
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq61 eq53


@[equational_result]
theorem Equation40175_implies_Equation2 (G : Type*) [Magma G] (h : Equation40175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X3) = X0 := superpose eq13 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40178_implies_Equation2 (G : Type*) [Magma G] (h : Equation40178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq7 eq11
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq65 eq22


@[equational_result]
theorem Equation40180_implies_Equation2 (G : Type*) [Magma G] (h : Equation40180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation40181_implies_Equation2 (G : Type*) [Magma G] (h : Equation40181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40183_implies_Equation2 (G : Type*) [Magma G] (h : Equation40183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation40184_implies_Equation2 (G : Type*) [Magma G] (h : Equation40184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation40185_implies_Equation2 (G : Type*) [Magma G] (h : Equation40185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40187_implies_Equation2 (G : Type*) [Magma G] (h : Equation40187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq28 eq12


@[equational_result]
theorem Equation40188_implies_Equation2 (G : Type*) [Magma G] (h : Equation40188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ (X1 ◇ (X1 ◇ X1))) = X2 := superpose eq10 eq7
  have eq31 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X1 := superpose eq7 eq9
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) = (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq10 eq9
  have eq78 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq31 eq7
  have eq89 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X1 ◇ (X1 ◇ X1))) = X2 := superpose eq78 eq18
  have eq94 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq78 eq33
  have eq114 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X1 ◇ X1)) = X2 := superpose eq78 eq89
  have eq115 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X2) ◇ X1) = X2 := superpose eq78 eq114
  have eq116 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ X1) = X2 := superpose eq78 eq115
  have eq117 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X2 := superpose eq78 eq116
  have eq123 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := superpose eq78 eq94
  have eq124 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := superpose eq78 eq123
  have eq125 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq117 eq124
  have eq127 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq125 eq117
  have eq142 (X0 X1 : G) : X0 = X1 := superpose eq125 eq127
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq142 eq8
  subsumption eq146 eq142


@[equational_result]
theorem Equation40189_implies_Equation2 (G : Type*) [Magma G] (h : Equation40189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) ◇ X0) ◇ X3) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq13 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40191_implies_Equation2 (G : Type*) [Magma G] (h : Equation40191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation40192_implies_Equation2 (G : Type*) [Magma G] (h : Equation40192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation40193_implies_Equation2 (G : Type*) [Magma G] (h : Equation40193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40195_implies_Equation2 (G : Type*) [Magma G] (h : Equation40195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation40196_implies_Equation2 (G : Type*) [Magma G] (h : Equation40196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40197_implies_Equation2 (G : Type*) [Magma G] (h : Equation40197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40199_implies_Equation2 (G : Type*) [Magma G] (h : Equation40199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40200_implies_Equation2 (G : Type*) [Magma G] (h : Equation40200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40201_implies_Equation2 (G : Type*) [Magma G] (h : Equation40201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40202_implies_Equation2 (G : Type*) [Magma G] (h : Equation40202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40204_implies_Equation2 (G : Type*) [Magma G] (h : Equation40204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) ◇ X0) ◇ X3) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) = X2 := superpose eq7 eq9
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq7 eq9
  have eq27 (X0 X1 X3 : G) : ((((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X3) ◇ X3) ◇ ((X1 ◇ X0) ◇ X0)) = X3 := superpose eq10 eq7
  have eq40 (X0 X2 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq27
  have eq77 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq40 eq27
  have eq105 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq77 eq7
  have eq159 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq11 eq105
  have eq168 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq40 eq105
  have eq173 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)))) := superpose eq10 eq105
  have eq177 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq105 eq10
  have eq181 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq105 eq7
  have eq205 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq181 eq77
  have eq209 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq181 eq168
  have eq212 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq205 eq209
  have eq220 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq212 eq159
  have eq222 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0))) := superpose eq212 eq173
  have eq228 (X0 X1 : G) : (X0 ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose eq212 eq177
  have eq241 (X0 X1 : G) : (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) = X0 := superpose eq212 eq228
  have eq243 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) := superpose eq241 eq222
  have eq247 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X0 := superpose eq7 eq243
  have eq320 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq212 eq7
  have eq321 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq212 eq27
  have eq330 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq212 eq320
  have eq332 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq330 eq247
  have eq333 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq332 eq330
  have eq334 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq333 eq220
  have eq335 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq333 eq11
  have eq349 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq333 eq334
  have eq350 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq333 eq349
  have eq351 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X0)) = X0 := superpose eq333 eq350
  have eq352 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq333 eq335
  have eq353 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq333 eq352
  have eq359 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq212 eq321
  have eq367 (X0 X1 X2 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X0) ◇ X0) = ((X0 ◇ (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X0) ◇ X0)) ◇ (((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X0) ◇ X0)) := superpose eq27 eq353
  have eq368 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq353 eq353
  have eq374 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq351 eq368
  have eq375 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq351 eq374
  have eq376 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X1) := superpose eq375 eq359
  have eq383 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0) = ((X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0)) ◇ ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X0)) := superpose eq376 eq367
  have eq387 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq375 eq375
  have eq388 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq333 eq387
  have eq389 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) := superpose eq388 eq383
  have eq397 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq388 eq389
  have eq398 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq388 eq397
  have eq399 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq388 eq398
  have eq400 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq388 eq399
  have eq406 (X0 X1 : G) : X0 = X1 := superpose eq388 eq400
  have eq419 (X0 : G) : sK0 ≠ X0 := superpose eq406 eq8
  subsumption eq419 eq406


@[equational_result]
theorem Equation40206_implies_Equation2 (G : Type*) [Magma G] (h : Equation40206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) ◇ X0) ◇ X4) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (((X0 ◇ X4) ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) = X0 := superpose eq11 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = X2 := superpose eq13 eq11
  have eq15 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq14 eq13
  have eq16 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ X5) = X4 := superpose eq15 eq12
  have eq18 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq15 eq16
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq24 eq19


@[equational_result]
theorem Equation40209_implies_Equation2 (G : Type*) [Magma G] (h : Equation40209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ X0) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1)) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((((((((((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) ◇ X3) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1)) ◇ X0) ◇ X4) ◇ ((((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) ◇ X3) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1))) ◇ X4) ◇ X5) ◇ (((((((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) ◇ X3) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1)) ◇ X0) ◇ X4) ◇ ((((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) ◇ X3) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1)))) ◇ X2) = X5 := superpose eq9 eq9
  have eq22 (X0 X1 X2 : G) : (((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) = ((X0 ◇ X1) ◇ X1) := superpose eq10 eq7
  have eq38 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq22 eq7
  have eq49 (X0 X1 X2 : G) : (((X2 ◇ (X2 ◇ X1)) ◇ X1) ◇ X2) = ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X0) ◇ X1) := superpose eq22 eq10
  have eq57 (X1 X2 : G) : (((X2 ◇ (X2 ◇ X1)) ◇ X1) ◇ X2) = X1 := superpose eq7 eq49
  have eq58 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X0) = X2 := superpose eq57 eq10
  have eq63 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq57 eq22
  have eq79 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq63 eq38
  have eq110 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) = (X0 ◇ X2) := superpose eq58 eq9
  have eq116 (X0 X2 X3 X4 X5 : G) : (((((((((((X3 ◇ X2) ◇ X3) ◇ X0) ◇ (X3 ◇ X2)) ◇ X0) ◇ X4) ◇ ((((X3 ◇ X2) ◇ X3) ◇ X0) ◇ (X3 ◇ X2))) ◇ X4) ◇ X5) ◇ (((((((X3 ◇ X2) ◇ X3) ◇ X0) ◇ (X3 ◇ X2)) ◇ X0) ◇ X4) ◇ ((((X3 ◇ X2) ◇ X3) ◇ X0) ◇ (X3 ◇ X2)))) ◇ X2) = X5 := superpose eq110 eq12
  have eq134 (X0 X1 X2 X3 : G) : ((((((((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ X2) ◇ X3) ◇ ((((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)))) ◇ X1) = X3 := superpose eq79 eq116
  have eq140 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X1 ◇ X2))) := superpose eq58 eq116
  have eq149 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X1) = X3 := superpose eq140 eq134
  have eq150 (X1 X2 : G) : (X2 ◇ X2) = X1 := superpose eq149 eq57
  have eq189 (X0 X2 : G) : X0 = X2 := superpose eq150 eq150
  have eq198 (X0 : G) : sK0 ≠ X0 := superpose eq189 eq8
  subsumption eq198 eq189


@[equational_result]
theorem Equation40210_implies_Equation2 (G : Type*) [Magma G] (h : Equation40210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40214_implies_Equation2 (G : Type*) [Magma G] (h : Equation40214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) ◇ X0) ◇ X4) ◇ X3) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ X3) ◇ X5) = X4 := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X0 := superpose eq12 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40216_implies_Equation2 (G : Type*) [Magma G] (h : Equation40216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq33 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq51 eq33


@[equational_result]
theorem Equation40217_implies_Equation2 (G : Type*) [Magma G] (h : Equation40217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq60 eq15


@[equational_result]
theorem Equation40218_implies_Equation2 (G : Type*) [Magma G] (h : Equation40218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq11 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40219_implies_Equation2 (G : Type*) [Magma G] (h : Equation40219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (((((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) ◇ X0) ◇ X5) ◇ X6) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X6 X7 : G) : (((X0 ◇ X5) ◇ X6) ◇ X7) = X5 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X4) = X0 := superpose eq13 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40222_implies_Equation2 (G : Type*) [Magma G] (h : Equation40222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0)) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) = X2 := superpose eq7 eq10
  have eq18 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ (((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3)))) ◇ X0) ◇ (((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3))) ◇ (((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3))) = X2 := superpose eq9 eq10
  have eq102 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq17
  have eq115 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq102 eq7
  have eq116 (X0 X2 X3 : G) : (((((X2 ◇ X0) ◇ X0) ◇ (X2 ◇ X0)) ◇ X3) ◇ X2) = X3 := superpose eq102 eq9
  have eq124 (X0 X2 X3 : G) : ((((X0 ◇ (X0 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X2 ◇ X3)))) ◇ X0) ◇ (((X2 ◇ X3) ◇ X3) ◇ (X2 ◇ X3))) ◇ (((X2 ◇ X3) ◇ X3) ◇ (X2 ◇ X3))) = X2 := superpose eq102 eq18
  have eq188 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq115 eq116
  have eq189 (X0 X2 X3 : G) : ((((X0 ◇ (X0 ◇ X3)) ◇ X0) ◇ X3) ◇ X3) = X2 := superpose eq115 eq124
  have eq190 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq188 eq189
  have eq192 (X0 X2 : G) : X0 = X2 := superpose eq115 eq190
  have eq207 (X0 : G) : sK0 ≠ X0 := superpose eq192 eq8
  subsumption eq207 eq192


@[equational_result]
theorem Equation40223_implies_Equation2 (G : Type*) [Magma G] (h : Equation40223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X2 X3 X4 : G) : (X2 ◇ X4) = X3 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq57 eq14


@[equational_result]
theorem Equation40225_implies_Equation2 (G : Type*) [Magma G] (h : Equation40225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40226_implies_Equation2 (G : Type*) [Magma G] (h : Equation40226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40227_implies_Equation2 (G : Type*) [Magma G] (h : Equation40227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40229_implies_Equation2 (G : Type*) [Magma G] (h : Equation40229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40230_implies_Equation2 (G : Type*) [Magma G] (h : Equation40230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40231_implies_Equation2 (G : Type*) [Magma G] (h : Equation40231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40233_implies_Equation2 (G : Type*) [Magma G] (h : Equation40233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40234_implies_Equation2 (G : Type*) [Magma G] (h : Equation40234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40235_implies_Equation2 (G : Type*) [Magma G] (h : Equation40235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40236_implies_Equation2 (G : Type*) [Magma G] (h : Equation40236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40240_implies_Equation2 (G : Type*) [Magma G] (h : Equation40240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0) ◇ X0) ◇ X3) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ X5) = X4 := superpose eq7 eq9
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq12 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40242_implies_Equation2 (G : Type*) [Magma G] (h : Equation40242 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40243_implies_Equation2 (G : Type*) [Magma G] (h : Equation40243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40244_implies_Equation2 (G : Type*) [Magma G] (h : Equation40244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40246_implies_Equation2 (G : Type*) [Magma G] (h : Equation40246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40247_implies_Equation2 (G : Type*) [Magma G] (h : Equation40247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40248_implies_Equation2 (G : Type*) [Magma G] (h : Equation40248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40250_implies_Equation2 (G : Type*) [Magma G] (h : Equation40250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40251_implies_Equation2 (G : Type*) [Magma G] (h : Equation40251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40252_implies_Equation2 (G : Type*) [Magma G] (h : Equation40252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40253_implies_Equation2 (G : Type*) [Magma G] (h : Equation40253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40255_implies_Equation2 (G : Type*) [Magma G] (h : Equation40255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation40256_implies_Equation2 (G : Type*) [Magma G] (h : Equation40256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation40257_implies_Equation2 (G : Type*) [Magma G] (h : Equation40257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ X0) := superpose eq7 eq7
  have eq21 (X0 X3 X4 : G) : (((X0 ◇ X0) ◇ X4) ◇ X3) = X4 := superpose eq11 eq7
  have eq25 (X0 X4 X5 : G) : ((((X0 ◇ X0) ◇ X4) ◇ X5) ◇ X4) = X5 := superpose eq11 eq7
  have eq29 (X4 X5 : G) : (X4 ◇ X4) = X5 := superpose eq21 eq25
  have eq56 (X0 X2 : G) : X0 = X2 := superpose eq29 eq29
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq134 eq56


@[equational_result]
theorem Equation40258_implies_Equation2 (G : Type*) [Magma G] (h : Equation40258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (((((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ X0) ◇ X5) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 X6 X7 : G) : (((X0 ◇ X5) ◇ X6) ◇ X7) = X6 := superpose eq7 eq9
  have eq14 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq13 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40260_implies_Equation2 (G : Type*) [Magma G] (h : Equation40260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40261_implies_Equation2 (G : Type*) [Magma G] (h : Equation40261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40262_implies_Equation2 (G : Type*) [Magma G] (h : Equation40262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40263_implies_Equation2 (G : Type*) [Magma G] (h : Equation40263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40265_implies_Equation2 (G : Type*) [Magma G] (h : Equation40265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40266_implies_Equation2 (G : Type*) [Magma G] (h : Equation40266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40267_implies_Equation2 (G : Type*) [Magma G] (h : Equation40267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40268_implies_Equation2 (G : Type*) [Magma G] (h : Equation40268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40270_implies_Equation2 (G : Type*) [Magma G] (h : Equation40270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40271_implies_Equation2 (G : Type*) [Magma G] (h : Equation40271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40272_implies_Equation2 (G : Type*) [Magma G] (h : Equation40272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40273_implies_Equation2 (G : Type*) [Magma G] (h : Equation40273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40275_implies_Equation2 (G : Type*) [Magma G] (h : Equation40275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40276_implies_Equation2 (G : Type*) [Magma G] (h : Equation40276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40277_implies_Equation2 (G : Type*) [Magma G] (h : Equation40277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40278_implies_Equation2 (G : Type*) [Magma G] (h : Equation40278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40279_implies_Equation2 (G : Type*) [Magma G] (h : Equation40279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40281_implies_Equation2 (G : Type*) [Magma G] (h : Equation40281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((((X3 ◇ X1) ◇ (X4 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0))) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0)) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0))) = X1 := superpose eq7 eq10
  have eq43 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq10 eq17
  have eq44 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq17 eq17
  have eq48 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) ◇ X0) ◇ X0)) := superpose eq17 eq10
  have eq52 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq17 eq9
  have eq53 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) ◇ X0) ◇ X0)) := superpose eq17 eq48
  have eq54 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq17 eq52
  have eq56 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1)) = X1 := superpose eq54 eq11
  have eq69 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq17 eq56
  have eq79 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq44 eq69
  have eq80 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq79 eq43
  have eq85 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq80 eq53
  have eq86 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((((X3 ◇ X1) ◇ (X4 ◇ X0)) ◇ X0) ◇ X0)) = X1 := superpose eq80 eq21
  have eq104 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq44 eq85
  have eq117 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ (((X3 ◇ X1) ◇ (X4 ◇ X0)) ◇ X0)) = X1 := superpose eq104 eq86
  have eq118 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X3 ◇ X1) ◇ (X4 ◇ X0))) = X1 := superpose eq104 eq117
  have eq119 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X1)) = X1 := superpose eq104 eq118
  have eq120 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X1 := superpose eq104 eq119
  have eq121 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq104 eq120
  have eq122 (X0 X3 : G) : X0 = X3 := superpose eq121 eq121
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq122 eq8
  subsumption eq127 eq122


@[equational_result]
theorem Equation40282_implies_Equation2 (G : Type*) [Magma G] (h : Equation40282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq10
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq12 eq7
  have eq22 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq20 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq28 eq23


@[equational_result]
theorem Equation40283_implies_Equation2 (G : Type*) [Magma G] (h : Equation40283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : (((X0 ◇ X4) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq10
  have eq19 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq12 eq7
  have eq22 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq19 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq28 eq23


@[equational_result]
theorem Equation40285_implies_Equation2 (G : Type*) [Magma G] (h : Equation40285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) ◇ (X1 ◇ X2))) ◇ ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) ◇ (X1 ◇ X2))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq9 eq9
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1)))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1)))) := superpose eq14 eq10
  have eq68 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X0 := superpose eq14 eq42
  have eq71 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq68 eq9
  have eq89 (X0 X3 : G) : X0 = X3 := superpose eq71 eq71
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq8
  subsumption eq92 eq89


@[equational_result]
theorem Equation40287_implies_Equation2 (G : Type*) [Magma G] (h : Equation40287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X1)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (((X0 ◇ X4) ◇ X0) ◇ X5) = X4 := superpose eq12 eq10
  have eq17 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq12 eq13
  have eq18 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq17 eq12
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq24 eq19


@[equational_result]
theorem Equation40290_implies_Equation2 (G : Type*) [Magma G] (h : Equation40290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq17 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq10
  have eq26 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq17 eq7
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq26 eq26
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation40291_implies_Equation2 (G : Type*) [Magma G] (h : Equation40291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ X3) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X4 X5 : G) : (X4 ◇ X5) = X4 := superpose eq14 eq10
  have eq16 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq15 eq14
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40293_implies_Equation2 (G : Type*) [Magma G] (h : Equation40293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X0 ◇ X4) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq37 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq11 eq7
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq37
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq105 eq42


@[equational_result]
theorem Equation40294_implies_Equation2 (G : Type*) [Magma G] (h : Equation40294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X5 : G) : (((X0 ◇ X3) ◇ X5) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq10 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq14 eq11
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq26 eq19


@[equational_result]
theorem Equation40295_implies_Equation2 (G : Type*) [Magma G] (h : Equation40295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq25 eq14


@[equational_result]
theorem Equation40296_implies_Equation2 (G : Type*) [Magma G] (h : Equation40296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 X7 : G) : (((X0 ◇ X5) ◇ X6) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : ((X2 ◇ X0) ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X5 X7 : G) : (X5 ◇ X7) = X5 := superpose eq13 eq10
  have eq16 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq15 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40298_implies_Equation2 (G : Type*) [Magma G] (h : Equation40298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X0)) ◇ X2) ◇ ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9
  have eq22 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ ((X1 ◇ ((((X2 ◇ X0) ◇ (X3 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X1)) ◇ X0)) ◇ X1)) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ ((((X2 ◇ X0) ◇ (X3 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X1)) ◇ X0)) ◇ X1)) = X0 := superpose eq10 eq10
  have eq30 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X0) = (X0 ◇ X0) := superpose eq7 eq13
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq13 eq13
  have eq41 (X0 X1 : G) : (((X1 ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X1)) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X1)) = X0 := superpose eq30 eq22
  have eq46 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq30 eq7
  have eq51 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X1)) = X0 := superpose eq33 eq41
  have eq57 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq33 eq51
  have eq58 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq46 eq57
  have eq59 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq46 eq58
  have eq63 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq59 eq9
  have eq83 (X0 X1 : G) : X0 = X1 := superpose eq63 eq59
  have eq93 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq93 eq83


@[equational_result]
theorem Equation40300_implies_Equation2 (G : Type*) [Magma G] (h : Equation40300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : (((X0 ◇ X1) ◇ X1) ◇ X4) = X1 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq11
  have eq21 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq7
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation40302_implies_Equation2 (G : Type*) [Magma G] (h : Equation40302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation40303_implies_Equation2 (G : Type*) [Magma G] (h : Equation40303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ X2) ◇ X2)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X1)) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X1)) ◇ (((X3 ◇ (X4 ◇ X2)) ◇ X3) ◇ X3)) = X4 := superpose eq7 eq9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (((X4 ◇ (X5 ◇ (((X3 ◇ (X0 ◇ X2)) ◇ X3) ◇ X3))) ◇ X4) ◇ X4)) = X5 := superpose eq9 eq9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ (X2 ◇ X0)) ◇ X4) ◇ X4) = ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (((X3 ◇ X0) ◇ X3) ◇ X3)) := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ ((X0 ◇ (((X3 ◇ ((X4 ◇ X2) ◇ X0)) ◇ X3) ◇ X3)) ◇ (((X3 ◇ ((X4 ◇ X2) ◇ X0)) ◇ X3) ◇ X3))) = X4 := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ X4)) ◇ X2) = ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ ((X0 ◇ (((X3 ◇ X4) ◇ X3) ◇ X3)) ◇ (((X3 ◇ X4) ◇ X3) ◇ X3))) := superpose eq9 eq9
  have eq57 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X1) ◇ X1) = X0 := superpose eq9 eq13
  have eq143 (X0 X2 X3 X4 : G) : (X0 ◇ (((X3 ◇ (X4 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X3) ◇ X3)) = X4 := superpose eq57 eq9
  have eq502 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (((X2 ◇ (X3 ◇ (X4 ◇ X3))) ◇ X2) ◇ X2))) = X1 := superpose eq13 eq143
  have eq541 (X0 X1 X4 : G) : (X4 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X4)) = X1 := superpose eq57 eq502
  have eq791 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ X1)) := superpose eq57 eq541
  have eq981 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq791 eq791
  have eq1035 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq791 eq57
  have eq1212 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) ◇ X0) = X2 := superpose eq16 eq15
  have eq1258 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq57 eq1212
  have eq1268 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) := superpose eq143 eq1212
  have eq1334 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ (X3 ◇ (((X4 ◇ ((X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1)) ◇ (X0 ◇ X0))) ◇ X4) ◇ X4))) ◇ X2) ◇ X2)) = X3 := superpose eq11 eq12
  have eq1747 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) = X0 := superpose eq1212 eq1258
  have eq2672 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq1258 eq1268
  have eq3163 (X0 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq2672 eq1212
  have eq3165 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X1) := superpose eq2672 eq57
  have eq3714 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq1035 eq1747
  have eq3716 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq3714 eq3163
  have eq3718 (X0 X1 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X1) = X0 := superpose eq3716 eq3165
  have eq3728 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq541 eq3716
  have eq3778 (X0 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ (X3 ◇ (((X4 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X4) ◇ X4))) ◇ X2) ◇ X2)) = X3 := superpose eq3728 eq1334
  have eq5874 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ (((X4 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X4) ◇ X4))) = X3 := superpose eq3728 eq3778
  have eq5875 (X0 X3 : G) : (X0 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X3 := superpose eq3728 eq5874
  have eq5876 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) = X3 := superpose eq3716 eq5875
  have eq5877 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq3716 eq5876
  have eq5881 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X1) = (X3 ◇ (X2 ◇ X3)) := superpose eq5877 eq981
  have eq5904 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X2 := superpose eq5877 eq5881
  have eq5906 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq5904 eq3718
  have eq5912 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq5904 eq5906
  have eq5914 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq5912 eq5877
  have eq5936 (X0 X1 : G) : X0 = X1 := superpose eq5914 eq5912
  have eq5946 (X0 : G) : sK0 ≠ X0 := superpose eq5936 eq8
  subsumption eq5946 eq5936


@[equational_result]
theorem Equation40304_implies_Equation2 (G : Type*) [Magma G] (h : Equation40304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X5) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation40308_implies_Equation2 (G : Type*) [Magma G] (h : Equation40308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq73 eq15


@[equational_result]
theorem Equation40310_implies_Equation2 (G : Type*) [Magma G] (h : Equation40310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X5) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation40311_implies_Equation2 (G : Type*) [Magma G] (h : Equation40311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq58 eq12


@[equational_result]
theorem Equation40312_implies_Equation2 (G : Type*) [Magma G] (h : Equation40312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X3) = X1 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation40313_implies_Equation2 (G : Type*) [Magma G] (h : Equation40313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40316_implies_Equation2 (G : Type*) [Magma G] (h : Equation40316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq10
  have eq20 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq12 eq7
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation40317_implies_Equation2 (G : Type*) [Magma G] (h : Equation40317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40321_implies_Equation2 (G : Type*) [Magma G] (h : Equation40321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq52 eq13


@[equational_result]
theorem Equation40324_implies_Equation2 (G : Type*) [Magma G] (h : Equation40324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq51 eq17


@[equational_result]
theorem Equation40325_implies_Equation2 (G : Type*) [Magma G] (h : Equation40325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq56 eq15


@[equational_result]
theorem Equation40327_implies_Equation2 (G : Type*) [Magma G] (h : Equation40327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) = X3 := superpose eq7 eq7
  have eq37 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq57 eq37


@[equational_result]
theorem Equation40328_implies_Equation2 (G : Type*) [Magma G] (h : Equation40328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40329_implies_Equation2 (G : Type*) [Magma G] (h : Equation40329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation40330_implies_Equation2 (G : Type*) [Magma G] (h : Equation40330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40332_implies_Equation2 (G : Type*) [Magma G] (h : Equation40332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq12
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq13 eq12
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation40333_implies_Equation2 (G : Type*) [Magma G] (h : Equation40333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X5 : G) : (((X0 ◇ X5) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40334_implies_Equation2 (G : Type*) [Magma G] (h : Equation40334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : (((X0 ◇ X5) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq7 eq10
  have eq19 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq12 eq7
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation40335_implies_Equation2 (G : Type*) [Magma G] (h : Equation40335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 X7 : G) : (((X0 ◇ X6) ◇ X5) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40337_implies_Equation2 (G : Type*) [Magma G] (h : Equation40337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((((X1 ◇ X0) ◇ X5) ◇ X1) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq54 eq19


@[equational_result]
theorem Equation40338_implies_Equation2 (G : Type*) [Magma G] (h : Equation40338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X4)) ◇ X1) = X2 := superpose eq7 eq7
  have eq20 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq11 eq7
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq154 eq52


@[equational_result]
theorem Equation40339_implies_Equation2 (G : Type*) [Magma G] (h : Equation40339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((((X1 ◇ X0) ◇ X5) ◇ X1) ◇ X5) = X4 := superpose eq7 eq7
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq63 eq44


@[equational_result]
theorem Equation40340_implies_Equation2 (G : Type*) [Magma G] (h : Equation40340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation40342_implies_Equation2 (G : Type*) [Magma G] (h : Equation40342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation40343_implies_Equation2 (G : Type*) [Magma G] (h : Equation40343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40344_implies_Equation2 (G : Type*) [Magma G] (h : Equation40344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ X4) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq56 eq15


@[equational_result]
theorem Equation40345_implies_Equation2 (G : Type*) [Magma G] (h : Equation40345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40347_implies_Equation2 (G : Type*) [Magma G] (h : Equation40347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((((X1 ◇ X0) ◇ X5) ◇ X5) ◇ X1) = X2 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq53 eq22


@[equational_result]
theorem Equation40348_implies_Equation2 (G : Type*) [Magma G] (h : Equation40348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40349_implies_Equation2 (G : Type*) [Magma G] (h : Equation40349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : (((X0 ◇ X5) ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq30 eq22


@[equational_result]
theorem Equation40350_implies_Equation2 (G : Type*) [Magma G] (h : Equation40350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40352_implies_Equation2 (G : Type*) [Magma G] (h : Equation40352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq64 eq19


@[equational_result]
theorem Equation40353_implies_Equation2 (G : Type*) [Magma G] (h : Equation40353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40354_implies_Equation2 (G : Type*) [Magma G] (h : Equation40354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40355_implies_Equation2 (G : Type*) [Magma G] (h : Equation40355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40356_implies_Equation2 (G : Type*) [Magma G] (h : Equation40356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40358_implies_Equation2 (G : Type*) [Magma G] (h : Equation40358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((((X1 ◇ X0) ◇ X3) ◇ X3) ◇ X1) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq7 eq9
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9
  have eq19 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq15 eq15
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq15 eq9
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq15 eq24
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq19 eq9
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq26 eq31
  have eq44 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X0) := superpose eq14 eq9
  have eq57 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq26 eq44
  have eq58 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq26 eq57
  have eq59 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq33 eq58
  have eq61 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq59 eq26
  have eq64 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ X1) = X3 := superpose eq61 eq9
  have eq70 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq61 eq64
  have eq76 (X0 X3 : G) : X0 = X3 := superpose eq70 eq70
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq113 eq76


@[equational_result]
theorem Equation40359_implies_Equation2 (G : Type*) [Magma G] (h : Equation40359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X3) ◇ X3) ◇ (((X2 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X3) ◇ (((X4 ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X0) ◇ X4)) ◇ X2) ◇ X2)) = X3 := superpose eq7 eq9
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (((X3 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X3)) ◇ X0) ◇ X0)) = X2 := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ (X1 ◇ X3)) ◇ X2) ◇ X2) = ((X0 ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X2) ◇ X2)) ◇ (((X4 ◇ (((X1 ◇ X2) ◇ X0) ◇ X4)) ◇ X0) ◇ X0)) := superpose eq9 eq9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) ◇ X0)) = X0 := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) = ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ (((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2))) := superpose eq9 eq9
  have eq16 (X0 X1 X2 X3 X4 : G) : (((((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X0) ◇ X3) ◇ X4) ◇ X4) ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) = X4 := superpose eq7 eq9
  have eq17 (X0 X1 X2 X3 X4 X5 : G) : (((((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X3) ◇ X4) ◇ X4) ◇ ((((((X5 ◇ (X1 ◇ X5)) ◇ X2) ◇ X2) ◇ X0) ◇ X3) ◇ X3)) = X4 := superpose eq9 eq9
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ (((((X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2)) ◇ X0) ◇ X0) ◇ X0) ◇ X1)) ◇ X0) ◇ X0)) = X0 := superpose eq14 eq14
  have eq23 (X0 X1 X2 X3 : G) : (X1 ◇ ((((((X2 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X1)) = X1 := superpose eq14 eq14
  have eq24 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ X3) ◇ X4) ◇ X4) ◇ ((X0 ◇ X3) ◇ X3)) = X4 := superpose eq14 eq9
  have eq25 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X3) ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0)) = X3 := superpose eq14 eq7
  have eq30 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (((X2 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X1) := superpose eq14 eq7
  have eq33 (X0 X1 X2 X3 : G) : (((X2 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq14 eq30
  have eq35 (X0 X1 : G) : (X1 ◇ (((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) ◇ X1)) = X1 := superpose eq33 eq23
  have eq40 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ X0) = ((X0 ◇ (((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ X0)) ◇ ((X3 ◇ ((X4 ◇ (X0 ◇ X4)) ◇ X3)) ◇ X0)) := superpose eq14 eq25
  have eq41 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X3)) ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) = X0 := superpose eq7 eq25
  have eq58 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ X0) = (X0 ◇ ((X3 ◇ ((X4 ◇ (X0 ◇ X4)) ◇ X3)) ◇ X0)) := superpose eq14 eq40
  have eq80 (X0 X1 X2 X3 : G) : (X0 ◇ ((((((X2 ◇ (((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X1) ◇ X2)) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) = X0 := superpose eq12 eq14
  have eq115 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ X0) = ((X0 ◇ (((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ X0)) ◇ (((X3 ◇ ((((X4 ◇ (X5 ◇ X4)) ◇ X0) ◇ X0) ◇ X3)) ◇ X5) ◇ X5)) := superpose eq14 eq10
  have eq133 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) = X1 := superpose eq7 eq10
  have eq161 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ X0) = (X0 ◇ (((X3 ◇ ((((X4 ◇ (X5 ◇ X4)) ◇ X0) ◇ X0) ◇ X3)) ◇ X5) ◇ X5)) := superpose eq14 eq115
  have eq164 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (((X3 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X0)) ◇ X3) ◇ X3)) = X2 := superpose eq7 eq133
  have eq171 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ X0) = ((X0 ◇ (((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ X0)) ◇ (((X3 ◇ X0) ◇ X3) ◇ X3)) := superpose eq14 eq133
  have eq172 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X2) ◇ X2)) = X0 := superpose eq7 eq133
  have eq189 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq133 eq7
  have eq212 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ X0) = (X0 ◇ (((X3 ◇ X0) ◇ X3) ◇ X3)) := superpose eq14 eq171
  have eq408 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X0) ◇ X0) = ((X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ X0)) ◇ ((((((X4 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X4)) ◇ X3) ◇ X3) ◇ X0) ◇ X0) ◇ X0)) := superpose eq16 eq17
  have eq536 (X0 X1 X2 : G) : (((((((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq35 eq7
  have eq760 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X1) ◇ X1)) := superpose eq133 eq164
  have eq838 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X1) ◇ X1)) := superpose eq189 eq760
  have eq1077 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3)) ◇ X2) ◇ X2) = (((((X4 ◇ ((X1 ◇ X2) ◇ X4)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X3 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3)) ◇ X2) ◇ X2)) ◇ (((X5 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ X5)) ◇ (((X4 ◇ ((X1 ◇ X2) ◇ X4)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2))) ◇ (((X4 ◇ ((X1 ◇ X2) ◇ X4)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)))) := superpose eq15 eq13
  have eq1080 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) = (((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ (((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2))) ◇ (((X4 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X4)) ◇ X2) ◇ X2)) := superpose eq15 eq9
  have eq1107 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) = (((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ (((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2))) ◇ (((X4 ◇ ((((X5 ◇ (X6 ◇ X5)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ X4)) ◇ X6) ◇ X6)) := superpose eq15 eq10
  have eq1125 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) = ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ (((X4 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X4)) ◇ X2) ◇ X2)) := superpose eq15 eq1080
  have eq1130 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) = ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ (((X4 ◇ ((((X5 ◇ (X6 ◇ X5)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ X4)) ◇ X6) ◇ X6)) := superpose eq15 eq1107
  have eq1181 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ (((X4 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2))) ◇ X4) ◇ X4)) = X0 := superpose eq212 eq133
  have eq1185 (X0 X1 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X3))) = X0 := superpose eq212 eq7
  have eq1190 (X0 X1 X4 : G) : ((((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ X4) ◇ X4) ◇ ((X0 ◇ X0) ◇ X0)) = X4 := superpose eq212 eq24
  have eq1243 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X1) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq1185 eq25
  have eq1348 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq133 eq1190
  have eq1359 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq33 eq172
  have eq1375 (X0 X1 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq1359 eq172
  have eq1413 (X0 X1 : G) : (((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) = X0 := superpose eq9 eq1348
  have eq1455 (X0 X1 : G) : (((X0 ◇ ((((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq35 eq1413
  have eq1468 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := superpose eq1413 eq25
  have eq1469 (X0 X1 X2 : G) : (X0 ◇ (((X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2) ◇ X2)) = X0 := superpose eq1413 eq133
  have eq1493 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq1469 eq164
  have eq1500 (X0 X1 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq1493 eq1243
  have eq1508 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq1500 eq1500
  have eq1509 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq1500
  have eq1535 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq1508 eq189
  have eq1538 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) := superpose eq1535 eq838
  have eq1541 (X0 X2 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq1509 eq536
  have eq1545 (X0 : G) : (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq1509 eq1455
  have eq1546 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq1535 eq1541
  have eq1550 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq1538 eq1545
  have eq1551 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1546 eq1550
  have eq1554 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := superpose eq1551 eq1375
  have eq1586 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq1551 eq1554
  have eq1588 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2)) ◇ X0)) = X0 := superpose eq1586 eq1468
  have eq1602 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0) ◇ X0) = X0 := superpose eq1588 eq58
  have eq1605 (X0 X1 : G) : (X0 ◇ (((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ X0)) = X0 := superpose eq1602 eq21
  have eq1612 (X0 X3 X4 X5 : G) : (X0 ◇ (((X3 ◇ ((((X4 ◇ (X5 ◇ X4)) ◇ X0) ◇ X0) ◇ X3)) ◇ X5) ◇ X5)) = X0 := superpose eq1602 eq161
  have eq1649 (X0 X1 : G) : (X0 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) = X0 := superpose eq1551 eq1605
  have eq1654 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) = (((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) := superpose eq1612 eq1130
  have eq1666 (X0 X1 X2 X3 X5 : G) : (((X3 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3)) ◇ X2) ◇ X2) = (((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ (((X3 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3)) ◇ X2) ◇ X2)) ◇ (((X5 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ X5)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2))) := superpose eq1654 eq1077
  have eq1689 (X0 X1 X2 X4 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) = ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ (((X4 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X4)) ◇ X2) ◇ X2)) := superpose eq1654 eq1125
  have eq1740 (X0 X1 X2 X3 X5 : G) : (((X3 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3)) ◇ X2) ◇ X2) = ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ (((X5 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ X5)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2))) := superpose eq1689 eq1666
  have eq1742 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) = (((X3 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3)) ◇ X2) ◇ X2) := superpose eq1649 eq1740
  have eq1760 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X0) = ((X0 ◇ (((X2 ◇ X3) ◇ X0) ◇ X0)) ◇ ((((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X3) ◇ X0) ◇ X0) ◇ X0)) := superpose eq1742 eq408
  have eq1778 (X0 X1 X3 : G) : (X0 ◇ ((((((X3 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) = X0 := superpose eq1742 eq80
  have eq1820 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq1778
  have eq1822 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X0) = (X0 ◇ ((((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X3) ◇ X0) ◇ X0) ◇ X0)) := superpose eq1820 eq1760
  have eq1843 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X0) = X0 := superpose eq1820 eq1822
  have eq1852 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (((X4 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2))) ◇ X4) ◇ X4)) = X0 := superpose eq1843 eq1181
  have eq2214 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X4) = X0 := superpose eq1843 eq1852
  have eq2215 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) = X0 := superpose eq2214 eq41
  have eq2218 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X0)) = X3 := superpose eq2214 eq25
  have eq2232 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq2214 eq2215
  have eq2237 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) = X3 := superpose eq2232 eq2218
  have eq2238 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq2232 eq2237
  have eq2239 (X0 X3 : G) : X0 = X3 := superpose eq2238 eq2238
  have eq2241 (X0 : G) : sK0 ≠ X0 := superpose eq2239 eq8
  subsumption eq2241 eq2239


@[equational_result]
theorem Equation40360_implies_Equation2 (G : Type*) [Magma G] (h : Equation40360 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : (((X0 ◇ X4) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq10
  have eq19 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq12 eq7
  have eq23 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq19 eq12
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq29 eq24


@[equational_result]
theorem Equation40362_implies_Equation2 (G : Type*) [Magma G] (h : Equation40362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((((X1 ◇ X0) ◇ X3) ◇ X1) ◇ X1) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq9 eq9
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq9 eq13
  have eq29 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ X3) := superpose eq19 eq19
  have eq60 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X1) = X0 := superpose eq29 eq7
  have eq72 (X0 X1 : G) : X0 = X1 := superpose eq9 eq60
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq82 eq72


@[equational_result]
theorem Equation40364_implies_Equation2 (G : Type*) [Magma G] (h : Equation40364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3) = X1 := superpose eq7 eq7
  have eq30 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq41 eq30


@[equational_result]
theorem Equation40368_implies_Equation2 (G : Type*) [Magma G] (h : Equation40368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ X3) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = X0 := superpose eq10 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40370_implies_Equation2 (G : Type*) [Magma G] (h : Equation40370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X0 ◇ X4) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq32 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq10 eq7
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq32
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq121 eq36


@[equational_result]
theorem Equation40371_implies_Equation2 (G : Type*) [Magma G] (h : Equation40371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq63 eq15


@[equational_result]
theorem Equation40372_implies_Equation2 (G : Type*) [Magma G] (h : Equation40372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((((X1 ◇ X0) ◇ X4) ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq7 eq9
  have eq21 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq16 eq7
  have eq33 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq35 eq33


@[equational_result]
theorem Equation40373_implies_Equation2 (G : Type*) [Magma G] (h : Equation40373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 X6 X7 : G) : ((((X1 ◇ X0) ◇ X5) ◇ X6) ◇ X7) = X5 := superpose eq7 eq7
  have eq10 (X0 X5 X6 X7 : G) : (((X0 ◇ X5) ◇ X6) ◇ X7) = X5 := superpose eq7 eq7
  have eq14 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation40375_implies_Equation2 (G : Type*) [Magma G] (h : Equation40375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X3) ◇ X1) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9
  have eq17 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq13 eq13
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq13 eq17
  have eq37 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq27 eq9
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq37 eq37
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq58 eq50


@[equational_result]
theorem Equation40377_implies_Equation2 (G : Type*) [Magma G] (h : Equation40377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq9
  have eq22 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq14 eq7
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation40379_implies_Equation2 (G : Type*) [Magma G] (h : Equation40379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40380_implies_Equation2 (G : Type*) [Magma G] (h : Equation40380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40381_implies_Equation2 (G : Type*) [Magma G] (h : Equation40381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40383_implies_Equation2 (G : Type*) [Magma G] (h : Equation40383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40384_implies_Equation2 (G : Type*) [Magma G] (h : Equation40384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40385_implies_Equation2 (G : Type*) [Magma G] (h : Equation40385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40387_implies_Equation2 (G : Type*) [Magma G] (h : Equation40387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40388_implies_Equation2 (G : Type*) [Magma G] (h : Equation40388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40389_implies_Equation2 (G : Type*) [Magma G] (h : Equation40389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40390_implies_Equation2 (G : Type*) [Magma G] (h : Equation40390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40392_implies_Equation2 (G : Type*) [Magma G] (h : Equation40392 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0)) ◇ X3) ◇ X1) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (((((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X2) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq7 eq9
  have eq81 (X0 X1 : G) : X0 = X1 := superpose eq7 eq17
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq81 eq8
  subsumption eq90 eq81


@[equational_result]
theorem Equation40394_implies_Equation2 (G : Type*) [Magma G] (h : Equation40394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40396_implies_Equation2 (G : Type*) [Magma G] (h : Equation40396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40397_implies_Equation2 (G : Type*) [Magma G] (h : Equation40397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40398_implies_Equation2 (G : Type*) [Magma G] (h : Equation40398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40400_implies_Equation2 (G : Type*) [Magma G] (h : Equation40400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40401_implies_Equation2 (G : Type*) [Magma G] (h : Equation40401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40402_implies_Equation2 (G : Type*) [Magma G] (h : Equation40402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40404_implies_Equation2 (G : Type*) [Magma G] (h : Equation40404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40405_implies_Equation2 (G : Type*) [Magma G] (h : Equation40405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40406_implies_Equation2 (G : Type*) [Magma G] (h : Equation40406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40407_implies_Equation2 (G : Type*) [Magma G] (h : Equation40407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40409_implies_Equation2 (G : Type*) [Magma G] (h : Equation40409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X1))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq26 eq15


@[equational_result]
theorem Equation40410_implies_Equation2 (G : Type*) [Magma G] (h : Equation40410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation40411_implies_Equation2 (G : Type*) [Magma G] (h : Equation40411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((((X1 ◇ X0) ◇ X4) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq7 eq9
  have eq21 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq14 eq7
  have eq25 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation40412_implies_Equation2 (G : Type*) [Magma G] (h : Equation40412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 X7 : G) : (((X0 ◇ X5) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40414_implies_Equation2 (G : Type*) [Magma G] (h : Equation40414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40415_implies_Equation2 (G : Type*) [Magma G] (h : Equation40415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40416_implies_Equation2 (G : Type*) [Magma G] (h : Equation40416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40417_implies_Equation2 (G : Type*) [Magma G] (h : Equation40417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40419_implies_Equation2 (G : Type*) [Magma G] (h : Equation40419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40420_implies_Equation2 (G : Type*) [Magma G] (h : Equation40420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40421_implies_Equation2 (G : Type*) [Magma G] (h : Equation40421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40422_implies_Equation2 (G : Type*) [Magma G] (h : Equation40422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40424_implies_Equation2 (G : Type*) [Magma G] (h : Equation40424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40425_implies_Equation2 (G : Type*) [Magma G] (h : Equation40425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40426_implies_Equation2 (G : Type*) [Magma G] (h : Equation40426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40427_implies_Equation2 (G : Type*) [Magma G] (h : Equation40427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40429_implies_Equation2 (G : Type*) [Magma G] (h : Equation40429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40430_implies_Equation2 (G : Type*) [Magma G] (h : Equation40430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40431_implies_Equation2 (G : Type*) [Magma G] (h : Equation40431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40432_implies_Equation2 (G : Type*) [Magma G] (h : Equation40432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40433_implies_Equation2 (G : Type*) [Magma G] (h : Equation40433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40436_implies_Equation2 (G : Type*) [Magma G] (h : Equation40436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq9
  have eq20 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq12 eq7
  have eq24 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq20 eq12
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq24 eq24
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq30 eq25


@[equational_result]
theorem Equation40437_implies_Equation2 (G : Type*) [Magma G] (h : Equation40437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (((X0 ◇ X0) ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = X3 := superpose eq12 eq11
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq42 eq17


@[equational_result]
theorem Equation40441_implies_Equation2 (G : Type*) [Magma G] (h : Equation40441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X3) = X1 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation40444_implies_Equation2 (G : Type*) [Magma G] (h : Equation40444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X2) ◇ X2) = X3 := superpose eq7 eq7
  have eq17 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq9
  have eq25 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq17 eq7
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq25 eq25
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq33 eq31


@[equational_result]
theorem Equation40445_implies_Equation2 (G : Type*) [Magma G] (h : Equation40445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ X3) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X0 := superpose eq10 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40447_implies_Equation2 (G : Type*) [Magma G] (h : Equation40447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation40448_implies_Equation2 (G : Type*) [Magma G] (h : Equation40448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : ((X2 ◇ X2) ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40449_implies_Equation2 (G : Type*) [Magma G] (h : Equation40449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X3 := superpose eq7 eq7
  have eq38 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq11 eq9
  have eq58 (X0 X2 : G) : X0 = X2 := superpose eq38 eq38
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq73 eq58


@[equational_result]
theorem Equation40450_implies_Equation2 (G : Type*) [Magma G] (h : Equation40450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 X6 X7 : G) : ((((X1 ◇ X0) ◇ X5) ◇ X6) ◇ X7) = X5 := superpose eq7 eq7
  have eq10 (X0 X5 X6 X7 : G) : (((X0 ◇ X5) ◇ X6) ◇ X7) = X5 := superpose eq7 eq7
  have eq14 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation40452_implies_Equation2 (G : Type*) [Magma G] (h : Equation40452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X0)) ◇ X3) ◇ ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq10 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X2)) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X2))) = X2 := superpose eq7 eq9
  have eq18 (X0 X1 X2 X3 : G) : (((X2 ◇ (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)))) ◇ X2)) ◇ X3) ◇ (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)))) ◇ X2)) = X3 := superpose eq7 eq9
  have eq19 (X0 X1 X2 : G) : (((X1 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1)) ◇ X2) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1)) = X2 := superpose eq10 eq9
  have eq35 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) := superpose eq13 eq19
  have eq64 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq15 eq10
  have eq69 (X0 X1 X5 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X5) ◇ X1) = X5 := superpose eq15 eq7
  have eq79 (X0 X1 X2 X3 : G) : (((X2 ◇ (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2)) ◇ X3) ◇ (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2)) = X3 := superpose eq64 eq18
  have eq142 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq69 eq69
  have eq143 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq9 eq69
  have eq144 (X0 X1 X2 : G) : (X0 ◇ X0) = (((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X0) := superpose eq79 eq69
  have eq164 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))))) := superpose eq142 eq35
  have eq183 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) = X1 := superpose eq142 eq164
  have eq198 (X0 X1 : G) : (X0 ◇ X0) = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X0) := superpose eq143 eq144
  have eq199 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq10 eq198
  have eq204 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X1))) = X1 := superpose eq199 eq183
  have eq209 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = X1 := superpose eq199 eq204
  have eq273 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq142
  have eq308 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq142 eq273
  have eq310 (X0 X2 X3 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X2))) = X2 := superpose eq308 eq15
  have eq322 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq308 eq209
  have eq356 (X0 X3 : G) : X0 = X3 := superpose eq310 eq322
  have eq425 (X0 : G) : sK0 ≠ X0 := superpose eq356 eq8
  subsumption eq425 eq356


@[equational_result]
theorem Equation40454_implies_Equation2 (G : Type*) [Magma G] (h : Equation40454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (((X0 ◇ X0) ◇ X3) ◇ X4) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq11
  have eq22 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq13 eq7
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation40456_implies_Equation2 (G : Type*) [Magma G] (h : Equation40456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40457_implies_Equation2 (G : Type*) [Magma G] (h : Equation40457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40458_implies_Equation2 (G : Type*) [Magma G] (h : Equation40458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40460_implies_Equation2 (G : Type*) [Magma G] (h : Equation40460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40461_implies_Equation2 (G : Type*) [Magma G] (h : Equation40461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40462_implies_Equation2 (G : Type*) [Magma G] (h : Equation40462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40464_implies_Equation2 (G : Type*) [Magma G] (h : Equation40464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40465_implies_Equation2 (G : Type*) [Magma G] (h : Equation40465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40466_implies_Equation2 (G : Type*) [Magma G] (h : Equation40466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40467_implies_Equation2 (G : Type*) [Magma G] (h : Equation40467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40470_implies_Equation2 (G : Type*) [Magma G] (h : Equation40470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq7 eq9
  have eq17 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq11 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq21 eq19


@[equational_result]
theorem Equation40471_implies_Equation2 (G : Type*) [Magma G] (h : Equation40471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40473_implies_Equation2 (G : Type*) [Magma G] (h : Equation40473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40474_implies_Equation2 (G : Type*) [Magma G] (h : Equation40474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40475_implies_Equation2 (G : Type*) [Magma G] (h : Equation40475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40477_implies_Equation2 (G : Type*) [Magma G] (h : Equation40477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40478_implies_Equation2 (G : Type*) [Magma G] (h : Equation40478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40479_implies_Equation2 (G : Type*) [Magma G] (h : Equation40479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40481_implies_Equation2 (G : Type*) [Magma G] (h : Equation40481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40482_implies_Equation2 (G : Type*) [Magma G] (h : Equation40482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40483_implies_Equation2 (G : Type*) [Magma G] (h : Equation40483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40484_implies_Equation2 (G : Type*) [Magma G] (h : Equation40484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40486_implies_Equation2 (G : Type*) [Magma G] (h : Equation40486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation40487_implies_Equation2 (G : Type*) [Magma G] (h : Equation40487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq9 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation40488_implies_Equation2 (G : Type*) [Magma G] (h : Equation40488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq24 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq7 eq9
  have eq35 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq24 eq7
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq46 eq38


@[equational_result]
theorem Equation40489_implies_Equation2 (G : Type*) [Magma G] (h : Equation40489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 X7 : G) : (((X0 ◇ X5) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40491_implies_Equation2 (G : Type*) [Magma G] (h : Equation40491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40492_implies_Equation2 (G : Type*) [Magma G] (h : Equation40492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40493_implies_Equation2 (G : Type*) [Magma G] (h : Equation40493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40494_implies_Equation2 (G : Type*) [Magma G] (h : Equation40494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40496_implies_Equation2 (G : Type*) [Magma G] (h : Equation40496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40497_implies_Equation2 (G : Type*) [Magma G] (h : Equation40497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40498_implies_Equation2 (G : Type*) [Magma G] (h : Equation40498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40499_implies_Equation2 (G : Type*) [Magma G] (h : Equation40499 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40501_implies_Equation2 (G : Type*) [Magma G] (h : Equation40501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40502_implies_Equation2 (G : Type*) [Magma G] (h : Equation40502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40503_implies_Equation2 (G : Type*) [Magma G] (h : Equation40503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40504_implies_Equation2 (G : Type*) [Magma G] (h : Equation40504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40506_implies_Equation2 (G : Type*) [Magma G] (h : Equation40506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40507_implies_Equation2 (G : Type*) [Magma G] (h : Equation40507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40508_implies_Equation2 (G : Type*) [Magma G] (h : Equation40508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40509_implies_Equation2 (G : Type*) [Magma G] (h : Equation40509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40510_implies_Equation2 (G : Type*) [Magma G] (h : Equation40510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40512_implies_Equation2 (G : Type*) [Magma G] (h : Equation40512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : ((((X1 ◇ X0) ◇ X5) ◇ X5) ◇ X1) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) := superpose eq7 eq7
  have eq18 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9
  have eq32 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) := superpose eq12 eq9
  have eq37 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ X0) := superpose eq12 eq32
  have eq49 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq18 eq9
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq37 eq49
  have eq53 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ (X4 ◇ X5)) ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X0))) = X1 := superpose eq7 eq11
  have eq81 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq11 eq12
  have eq91 (X0 X1 X4 X5 : G) : (X0 ◇ ((X1 ◇ (X4 ◇ X5)) ◇ X1)) = X1 := superpose eq37 eq53
  have eq98 (X0 X1 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X1) = X5 := superpose eq81 eq9
  have eq107 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq98 eq51
  have eq114 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq107 eq81
  have eq117 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq107 eq91
  have eq130 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq107 eq114
  have eq141 (X0 X1 : G) : X0 = X1 := superpose eq117 eq130
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq141 eq8
  subsumption eq143 eq141


@[equational_result]
theorem Equation40513_implies_Equation2 (G : Type*) [Magma G] (h : Equation40513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 : G) : (((X0 ◇ X5) ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ X4) = X2 := superpose eq7 eq10
  have eq22 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq13 eq7
  have eq26 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq22 eq13
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq32 eq27


@[equational_result]
theorem Equation40514_implies_Equation2 (G : Type*) [Magma G] (h : Equation40514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((((X1 ◇ X0) ◇ X5) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq10 (X0 X4 X5 : G) : (((X0 ◇ X5) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq7 eq7
  have eq14 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X4) = X5 := superpose eq12 eq9
  have eq15 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X5 := superpose eq12 eq10
  have eq16 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq15 eq14
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq28 eq20


@[equational_result]
theorem Equation40515_implies_Equation2 (G : Type*) [Magma G] (h : Equation40515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X6 X7 : G) : (((X0 ◇ X6) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq11 (X0 X1 X5 X6 : G) : (((X0 ◇ X1) ◇ X5) ◇ X6) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq11 eq7
  have eq15 (X0 X6 X7 : G) : ((X0 ◇ X6) ◇ X7) = X6 := superpose eq13 eq10
  have eq17 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq13 eq15
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation40517_implies_Equation2 (G : Type*) [Magma G] (h : Equation40517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : ((((X1 ◇ X0) ◇ X5) ◇ X1) ◇ X1) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = ((X0 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0)) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq9 eq9
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ (((X0 ◇ X1) ◇ (X3 ◇ X4)) ◇ X2)) = ((X5 ◇ ((X0 ◇ X1) ◇ X5)) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq11 eq11
  have eq29 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq9 eq11
  have eq36 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (((X0 ◇ X1) ◇ (X3 ◇ X4)) ◇ X2)) = X0 := superpose eq15 eq27
  have eq52 (X0 X1 X5 : G) : (((X0 ◇ X5) ◇ X1) ◇ X1) = X5 := superpose eq36 eq7
  have eq57 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq52 eq29
  have eq60 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = X0 := superpose eq57 eq7
  have eq71 (X0 X4 : G) : X0 = X4 := superpose eq60 eq60
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq73 eq71


@[equational_result]
theorem Equation40518_implies_Equation2 (G : Type*) [Magma G] (h : Equation40518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0)) ◇ X1) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = X3 := superpose eq11 eq11
  have eq61 (X0 X5 : G) : X0 = X5 := superpose eq11 eq17
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq160 eq61


@[equational_result]
theorem Equation40519_implies_Equation2 (G : Type*) [Magma G] (h : Equation40519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((((X1 ◇ X0) ◇ X5) ◇ X1) ◇ X4) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq9 eq9
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq130 eq41


@[equational_result]
theorem Equation40520_implies_Equation2 (G : Type*) [Magma G] (h : Equation40520 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X0 ◇ X1) ◇ X5) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation40522_implies_Equation2 (G : Type*) [Magma G] (h : Equation40522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X0) ◇ X5) ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X0) ◇ X3)) ◇ X1) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X1 := superpose eq12 eq12
  have eq25 (X0 X1 X2 X5 : G) : ((((X1 ◇ X0) ◇ X5) ◇ X2) ◇ X1) = X5 := superpose eq18 eq9
  have eq27 (X1 X5 : G) : (X1 ◇ X1) = X5 := superpose eq18 eq25
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq12 eq27
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq40 eq29


@[equational_result]
theorem Equation40523_implies_Equation2 (G : Type*) [Magma G] (h : Equation40523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X0) ◇ X5) ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X0) ◇ X3)) ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X0) ◇ X3)) = X5 := superpose eq7 eq7
  have eq10 (X0 X2 X5 : G) : (((X0 ◇ X5) ◇ X2) ◇ X2) = X5 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X3) = ((X0 ◇ X2) ◇ X2) := superpose eq7 eq7
  have eq21 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq10
  have eq32 (X0 X1 X3 X5 : G) : ((((X1 ◇ X0) ◇ X5) ◇ X3) ◇ X3) = X5 := superpose eq21 eq9
  have eq35 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq21 eq11
  have eq40 (X3 X5 : G) : (X3 ◇ X3) = X5 := superpose eq21 eq32
  have eq45 (X0 X1 : G) : X0 = X1 := superpose eq35 eq40
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq50 eq45


@[equational_result]
theorem Equation40524_implies_Equation2 (G : Type*) [Magma G] (h : Equation40524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (((X0 ◇ X5) ◇ X3) ◇ X4) = X5 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X0 := superpose eq10 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40525_implies_Equation2 (G : Type*) [Magma G] (h : Equation40525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X6 X7 : G) : (((X0 ◇ X6) ◇ X4) ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ X4) = X0 := superpose eq10 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40527_implies_Equation2 (G : Type*) [Magma G] (h : Equation40527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((((X1 ◇ X0) ◇ X5) ◇ X2) ◇ X1) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = X3 := superpose eq7 eq9
  have eq23 (X0 X1 X4 : G) : ((X0 ◇ X4) ◇ (X4 ◇ X0)) = X1 := superpose eq17 eq11
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq49 eq32


@[equational_result]
theorem Equation40528_implies_Equation2 (G : Type*) [Magma G] (h : Equation40528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X5 : G) : (((X0 ◇ X5) ◇ X3) ◇ X2) = X5 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X0 := superpose eq10 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40529_implies_Equation2 (G : Type*) [Magma G] (h : Equation40529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X3 ◇ X4) = ((X0 ◇ X4) ◇ X4) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq7 eq7
  have eq13 (X3 X4 : G) : (X3 ◇ X4) = X4 := superpose eq12 eq11
  have eq14 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq13 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq20 eq18


@[equational_result]
theorem Equation40530_implies_Equation2 (G : Type*) [Magma G] (h : Equation40530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 X6 X7 : G) : ((((X1 ◇ X0) ◇ X6) ◇ X5) ◇ X7) = X6 := superpose eq7 eq7
  have eq10 (X0 X5 X6 X7 : G) : (((X0 ◇ X6) ◇ X5) ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation40532_implies_Equation2 (G : Type*) [Magma G] (h : Equation40532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) = X5 := superpose eq7 eq7
  have eq35 (X0 X7 : G) : X0 = X7 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq57 eq35


@[equational_result]
theorem Equation40533_implies_Equation2 (G : Type*) [Magma G] (h : Equation40533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X6 X7 : G) : (((X0 ◇ X6) ◇ X7) ◇ X2) = X6 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X0 := superpose eq10 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40534_implies_Equation2 (G : Type*) [Magma G] (h : Equation40534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X6 X7 : G) : ((((X1 ◇ X0) ◇ X6) ◇ X7) ◇ X4) = X6 := superpose eq7 eq7
  have eq10 (X0 X4 X6 X7 : G) : (((X0 ◇ X6) ◇ X7) ◇ X4) = X6 := superpose eq7 eq7
  have eq14 (X0 X4 X6 : G) : (X0 ◇ X4) = X6 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation40535_implies_Equation2 (G : Type*) [Magma G] (h : Equation40535 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : ((X0 ◇ X1) ◇ X5) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq12 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40536_implies_Equation2 (G : Type*) [Magma G] (h : Equation40536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X7 X8 X9 : G) : ((((X1 ◇ X0) ◇ X7) ◇ X8) ◇ X9) = X7 := superpose eq7 eq7
  have eq10 (X0 X7 X8 X9 : G) : (((X0 ◇ X7) ◇ X8) ◇ X9) = X7 := superpose eq7 eq7
  have eq14 (X0 X7 X9 : G) : (X0 ◇ X9) = X7 := superpose eq10 eq9
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation40538_implies_Equation2 (G : Type*) [Magma G] (h : Equation40538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X5) ◇ X1) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9
  have eq26 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) ◇ X0) = (X0 ◇ X0) := superpose eq9 eq11
  have eq27 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq11 eq11
  have eq31 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X0 := superpose eq15 eq27
  have eq32 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = (X0 ◇ X0) := superpose eq31 eq26
  have eq35 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq31 eq11
  have eq37 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq32 eq7
  have eq50 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X1 := superpose eq35 eq37
  have eq52 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq15 eq50
  have eq53 (X0 X2 : G) : X0 = X2 := superpose eq52 eq52
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq95 eq53


@[equational_result]
theorem Equation40539_implies_Equation2 (G : Type*) [Magma G] (h : Equation40539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X1) ◇ X0)) ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ (X4 ◇ X5)) ◇ X3) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X1) := superpose eq7 eq11
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq11 eq11
  have eq21 (X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X5) ◇ X2) = X5 := superpose eq17 eq10
  have eq23 (X2 X5 : G) : ((X2 ◇ X5) ◇ X2) = X5 := superpose eq17 eq21
  have eq24 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = ((X4 ◇ X5) ◇ X0) := superpose eq23 eq14
  have eq27 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ X2) = X0 := superpose eq23 eq7
  have eq29 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ X0) = X0 := superpose eq27 eq24
  have eq31 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq29 eq27
  have eq37 (X2 X5 : G) : (X2 ◇ X2) = X5 := superpose eq31 eq23
  have eq41 (X0 X1 : G) : X0 = X1 := superpose eq31 eq37
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq46 eq41


@[equational_result]
theorem Equation40540_implies_Equation2 (G : Type*) [Magma G] (h : Equation40540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq9 eq9
  have eq22 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq14 eq7
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq22 eq22
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation40541_implies_Equation2 (G : Type*) [Magma G] (h : Equation40541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X5 X6 : G) : (((X0 ◇ X1) ◇ X5) ◇ X6) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40543_implies_Equation2 (G : Type*) [Magma G] (h : Equation40543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40544_implies_Equation2 (G : Type*) [Magma G] (h : Equation40544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40545_implies_Equation2 (G : Type*) [Magma G] (h : Equation40545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40546_implies_Equation2 (G : Type*) [Magma G] (h : Equation40546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40548_implies_Equation2 (G : Type*) [Magma G] (h : Equation40548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40549_implies_Equation2 (G : Type*) [Magma G] (h : Equation40549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40550_implies_Equation2 (G : Type*) [Magma G] (h : Equation40550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40551_implies_Equation2 (G : Type*) [Magma G] (h : Equation40551 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40553_implies_Equation2 (G : Type*) [Magma G] (h : Equation40553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40554_implies_Equation2 (G : Type*) [Magma G] (h : Equation40554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40555_implies_Equation2 (G : Type*) [Magma G] (h : Equation40555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40556_implies_Equation2 (G : Type*) [Magma G] (h : Equation40556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40558_implies_Equation2 (G : Type*) [Magma G] (h : Equation40558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40559_implies_Equation2 (G : Type*) [Magma G] (h : Equation40559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40560_implies_Equation2 (G : Type*) [Magma G] (h : Equation40560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40561_implies_Equation2 (G : Type*) [Magma G] (h : Equation40561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40562_implies_Equation2 (G : Type*) [Magma G] (h : Equation40562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40564_implies_Equation2 (G : Type*) [Magma G] (h : Equation40564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X0) ◇ (((X2 ◇ (X3 ◇ X4)) ◇ X3) ◇ X0)) ◇ X5) ◇ X1) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X5))) = X2 := superpose eq12 eq12
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq12 eq12
  have eq22 (X1 X2 X3 X4 X5 : G) : ((((X2 ◇ (X3 ◇ X4)) ◇ X3) ◇ X5) ◇ X1) = X5 := superpose eq16 eq9
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq16 eq14
  have eq30 (X1 X3 X5 : G) : (((X3 ◇ X3) ◇ X5) ◇ X1) = X5 := superpose eq16 eq22
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq30 eq27
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq59 eq33


@[equational_result]
theorem Equation40565_implies_Equation2 (G : Type*) [Magma G] (h : Equation40565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 : G) : (((X0 ◇ X2) ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq20 (X0 X2 X4 : G) : ((X0 ◇ X4) ◇ X2) = X4 := superpose eq7 eq10
  have eq34 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq20 eq7
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq34 eq34
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq44 eq38


@[equational_result]
theorem Equation40566_implies_Equation2 (G : Type*) [Magma G] (h : Equation40566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40567_implies_Equation2 (G : Type*) [Magma G] (h : Equation40567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X6 X7 : G) : (((X0 ◇ X4) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40569_implies_Equation2 (G : Type*) [Magma G] (h : Equation40569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40570_implies_Equation2 (G : Type*) [Magma G] (h : Equation40570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40571_implies_Equation2 (G : Type*) [Magma G] (h : Equation40571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40572_implies_Equation2 (G : Type*) [Magma G] (h : Equation40572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40574_implies_Equation2 (G : Type*) [Magma G] (h : Equation40574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40575_implies_Equation2 (G : Type*) [Magma G] (h : Equation40575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40576_implies_Equation2 (G : Type*) [Magma G] (h : Equation40576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40577_implies_Equation2 (G : Type*) [Magma G] (h : Equation40577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40579_implies_Equation2 (G : Type*) [Magma G] (h : Equation40579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40580_implies_Equation2 (G : Type*) [Magma G] (h : Equation40580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40581_implies_Equation2 (G : Type*) [Magma G] (h : Equation40581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40582_implies_Equation2 (G : Type*) [Magma G] (h : Equation40582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40584_implies_Equation2 (G : Type*) [Magma G] (h : Equation40584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40585_implies_Equation2 (G : Type*) [Magma G] (h : Equation40585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40586_implies_Equation2 (G : Type*) [Magma G] (h : Equation40586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40587_implies_Equation2 (G : Type*) [Magma G] (h : Equation40587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40588_implies_Equation2 (G : Type*) [Magma G] (h : Equation40588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40590_implies_Equation2 (G : Type*) [Magma G] (h : Equation40590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X5) ◇ X1) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = X1 := superpose eq7 eq9
  have eq23 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq17 eq12
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation40591_implies_Equation2 (G : Type*) [Magma G] (h : Equation40591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X5 : G) : (((X0 ◇ X3) ◇ X5) ◇ X2) = X5 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40592_implies_Equation2 (G : Type*) [Magma G] (h : Equation40592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((((X1 ◇ X0) ◇ X4) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq10 (X0 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X4) = X5 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq10 eq10
  have eq23 (X4 X5 : G) : (X4 ◇ X4) = X5 := superpose eq17 eq9
  have eq25 (X0 X2 : G) : X0 = X2 := superpose eq23 eq23
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq31 eq25


@[equational_result]
theorem Equation40593_implies_Equation2 (G : Type*) [Magma G] (h : Equation40593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 X7 : G) : (((X0 ◇ X5) ◇ X6) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40595_implies_Equation2 (G : Type*) [Magma G] (h : Equation40595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40596_implies_Equation2 (G : Type*) [Magma G] (h : Equation40596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40597_implies_Equation2 (G : Type*) [Magma G] (h : Equation40597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40598_implies_Equation2 (G : Type*) [Magma G] (h : Equation40598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40600_implies_Equation2 (G : Type*) [Magma G] (h : Equation40600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40601_implies_Equation2 (G : Type*) [Magma G] (h : Equation40601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40602_implies_Equation2 (G : Type*) [Magma G] (h : Equation40602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40603_implies_Equation2 (G : Type*) [Magma G] (h : Equation40603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40605_implies_Equation2 (G : Type*) [Magma G] (h : Equation40605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40606_implies_Equation2 (G : Type*) [Magma G] (h : Equation40606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40607_implies_Equation2 (G : Type*) [Magma G] (h : Equation40607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40608_implies_Equation2 (G : Type*) [Magma G] (h : Equation40608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40610_implies_Equation2 (G : Type*) [Magma G] (h : Equation40610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40611_implies_Equation2 (G : Type*) [Magma G] (h : Equation40611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40612_implies_Equation2 (G : Type*) [Magma G] (h : Equation40612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40613_implies_Equation2 (G : Type*) [Magma G] (h : Equation40613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40614_implies_Equation2 (G : Type*) [Magma G] (h : Equation40614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40616_implies_Equation2 (G : Type*) [Magma G] (h : Equation40616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X3))) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq12
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq29 eq17


@[equational_result]
theorem Equation40617_implies_Equation2 (G : Type*) [Magma G] (h : Equation40617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X6 X7 : G) : (((X0 ◇ X6) ◇ X7) ◇ X2) = X7 := superpose eq7 eq7
  have eq14 (X0 X2 X4 : G) : (X4 ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40618_implies_Equation2 (G : Type*) [Magma G] (h : Equation40618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X6 X7 : G) : (((X0 ◇ X6) ◇ X7) ◇ X4) = X7 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X4 ◇ X3) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40619_implies_Equation2 (G : Type*) [Magma G] (h : Equation40619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X5 X6 : G) : (((X0 ◇ X1) ◇ X6) ◇ X5) = X6 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq11 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40620_implies_Equation2 (G : Type*) [Magma G] (h : Equation40620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X0) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X7 X8 X9 : G) : (((X0 ◇ X7) ◇ X8) ◇ X9) = X8 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq10 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40622_implies_Equation2 (G : Type*) [Magma G] (h : Equation40622 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40623_implies_Equation2 (G : Type*) [Magma G] (h : Equation40623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40624_implies_Equation2 (G : Type*) [Magma G] (h : Equation40624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40625_implies_Equation2 (G : Type*) [Magma G] (h : Equation40625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40626_implies_Equation2 (G : Type*) [Magma G] (h : Equation40626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X1) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40628_implies_Equation2 (G : Type*) [Magma G] (h : Equation40628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40629_implies_Equation2 (G : Type*) [Magma G] (h : Equation40629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40630_implies_Equation2 (G : Type*) [Magma G] (h : Equation40630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40631_implies_Equation2 (G : Type*) [Magma G] (h : Equation40631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40632_implies_Equation2 (G : Type*) [Magma G] (h : Equation40632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X2) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40634_implies_Equation2 (G : Type*) [Magma G] (h : Equation40634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40635_implies_Equation2 (G : Type*) [Magma G] (h : Equation40635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40636_implies_Equation2 (G : Type*) [Magma G] (h : Equation40636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40637_implies_Equation2 (G : Type*) [Magma G] (h : Equation40637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40638_implies_Equation2 (G : Type*) [Magma G] (h : Equation40638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X3) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40640_implies_Equation2 (G : Type*) [Magma G] (h : Equation40640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X4) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40641_implies_Equation2 (G : Type*) [Magma G] (h : Equation40641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X4) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40642_implies_Equation2 (G : Type*) [Magma G] (h : Equation40642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X4) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40643_implies_Equation2 (G : Type*) [Magma G] (h : Equation40643 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X4) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40644_implies_Equation2 (G : Type*) [Magma G] (h : Equation40644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X4) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40646_implies_Equation2 (G : Type*) [Magma G] (h : Equation40646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40647_implies_Equation2 (G : Type*) [Magma G] (h : Equation40647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40648_implies_Equation2 (G : Type*) [Magma G] (h : Equation40648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40649_implies_Equation2 (G : Type*) [Magma G] (h : Equation40649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40650_implies_Equation2 (G : Type*) [Magma G] (h : Equation40650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40651_implies_Equation2 (G : Type*) [Magma G] (h : Equation40651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) ◇ X6) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40857_implies_Equation2 (G : Type*) [Magma G] (h : Equation40857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((((X0 ◇ X2) ◇ X2) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ X3) = X2 := superpose eq13 eq9
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq13 eq14
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation40860_implies_Equation2 (G : Type*) [Magma G] (h : Equation40860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ X2) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ X3) = X2 := superpose eq12 eq9
  have eq17 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ X3) = X2 := superpose eq12 eq13
  have eq18 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq17
  have eq19 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation40862_implies_Equation2 (G : Type*) [Magma G] (h : Equation40862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq12
  have eq18 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq13 eq7
  have eq28 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq13 eq18
  have eq29 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq13 eq28
  have eq30 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq13 eq29
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq30 eq30
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq40 eq38


@[equational_result]
theorem Equation40863_implies_Equation2 (G : Type*) [Magma G] (h : Equation40863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq10 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = X2 := superpose eq13 eq9
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq45 eq20


@[equational_result]
theorem Equation40864_implies_Equation2 (G : Type*) [Magma G] (h : Equation40864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((((X0 ◇ X3) ◇ X3) ◇ X4) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 X5 : G) : (((X0 ◇ X3) ◇ X3) ◇ X5) = X3 := superpose eq13 eq9
  have eq15 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq13 eq14
  have eq16 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq13 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation40867_implies_Equation2 (G : Type*) [Magma G] (h : Equation40867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X0)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq11 eq11
  have eq16 (X0 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq13 eq10
  have eq17 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq11 eq16
  have eq18 (X0 X1 X2 X3 : G) : ((((X0 ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X2) ◇ X3) = X2 := superpose eq17 eq9
  have eq23 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X3) = X2 := superpose eq17 eq18
  have eq24 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq17 eq23
  have eq25 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq17 eq24
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq31 eq26


@[equational_result]
theorem Equation40870_implies_Equation2 (G : Type*) [Magma G] (h : Equation40870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X2 ◇ X0) ◇ X0) ◇ X2) ◇ X2) = ((X1 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq7 eq11
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X3) = (X2 ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq11 eq11
  have eq15 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X1 := superpose eq11 eq11
  have eq20 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X3) = X0 := superpose eq15 eq12
  have eq23 (X0 X2 : G) : (X2 ◇ ((X0 ◇ X2) ◇ X2)) = X0 := superpose eq20 eq13
  have eq24 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq23 eq11
  have eq25 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = X1 := superpose eq24 eq15
  have eq30 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq24 eq25
  have eq31 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq24 eq30
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq37 eq32


@[equational_result]
theorem Equation40872_implies_Equation2 (G : Type*) [Magma G] (h : Equation40872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) = X1 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X1 := superpose eq11 eq7
  have eq19 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X2) = ((((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X2))) ◇ X3) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X2))) := superpose eq10 eq10
  have eq37 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq13 eq7
  have eq39 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X2) = (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X2))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X2))) := superpose eq37 eq19
  have eq64 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X2) = (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) := superpose eq37 eq39
  have eq65 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X2) = (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ X0) := superpose eq37 eq64
  have eq66 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X2) := superpose eq37 eq65
  have eq67 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = (X1 ◇ X2) := superpose eq37 eq66
  have eq68 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X1 := superpose eq37 eq67
  have eq69 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq37 eq68
  have eq70 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq37 eq69
  have eq71 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq37 eq70
  have eq126 (X0 X2 : G) : X0 = X2 := superpose eq71 eq71
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq126 eq8
  subsumption eq128 eq126


@[equational_result]
theorem Equation40873_implies_Equation2 (G : Type*) [Magma G] (h : Equation40873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X3) ◇ X3) = X2 := superpose eq7 eq7
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq40 eq28


@[equational_result]
theorem Equation40874_implies_Equation2 (G : Type*) [Magma G] (h : Equation40874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X3) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X2)) ◇ X4) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 X5 : G) : ((((X0 ◇ X3) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X4) ◇ X5) = X3 := superpose eq12 eq9
  have eq17 (X0 X1 X3 X5 : G) : (((X0 ◇ X3) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X5) = X3 := superpose eq12 eq13
  have eq18 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq12 eq17
  have eq19 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation40876_implies_Equation2 (G : Type*) [Magma G] (h : Equation40876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq11
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq11
  have eq21 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq19 eq10
  have eq31 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq19 eq21
  have eq46 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq19 eq31
  have eq58 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq19 eq46
  have eq62 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq58 eq16
  have eq158 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq62
  have eq178 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X0 := superpose eq158 eq7
  have eq218 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq158 eq178
  have eq219 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq158 eq218
  have eq220 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq158 eq219
  have eq237 (X0 X2 : G) : X0 = X2 := superpose eq220 eq220
  have eq242 (X0 : G) : sK0 ≠ X0 := superpose eq237 eq8
  subsumption eq242 eq237


@[equational_result]
theorem Equation40877_implies_Equation2 (G : Type*) [Magma G] (h : Equation40877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq10 eq7
  have eq25 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq19
  have eq45 (X0 X2 : G) : X0 = X2 := superpose eq25 eq25
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq58 eq45


@[equational_result]
theorem Equation40878_implies_Equation2 (G : Type*) [Magma G] (h : Equation40878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X3) = X0 := superpose eq12 eq7
  have eq17 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = X0 := superpose eq12 eq13
  have eq18 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq12 eq17
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation40880_implies_Equation2 (G : Type*) [Magma G] (h : Equation40880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq11 eq11
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X2) := superpose eq7 eq11
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X2) ◇ X1) ◇ X1) := superpose eq11 eq7
  have eq18 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq14 eq12
  have eq21 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq14 eq7
  have eq22 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq14 eq13
  have eq23 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq14 eq18
  have eq25 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq14 eq21
  have eq26 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq14 eq22
  have eq30 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq25 eq25
  have eq33 (X0 X1 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq25 eq30
  have eq34 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq30 eq30
  have eq41 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq16 eq34
  have eq42 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq16 eq41
  have eq43 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq23 eq42
  have eq44 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) = X1 := superpose eq43 eq33
  have eq46 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := superpose eq14 eq44
  have eq47 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq46 eq26
  have eq53 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq47 eq25
  have eq73 (X0 X2 : G) : X0 = X2 := superpose eq53 eq53
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq75 eq73


@[equational_result]
theorem Equation40882_implies_Equation2 (G : Type*) [Magma G] (h : Equation40882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X3) ◇ X4) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X1)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X3) ◇ X4) ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ X5) = X3 := superpose eq12 eq9
  have eq17 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ X5) = X3 := superpose eq12 eq13
  have eq18 (X0 X3 X5 : G) : ((X0 ◇ X3) ◇ X5) = X3 := superpose eq12 eq17
  have eq19 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation40884_implies_Equation2 (G : Type*) [Magma G] (h : Equation40884 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq7
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq43 eq28


@[equational_result]
theorem Equation40885_implies_Equation2 (G : Type*) [Magma G] (h : Equation40885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40886_implies_Equation2 (G : Type*) [Magma G] (h : Equation40886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X3) = X0 := superpose eq12 eq7
  have eq17 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = X0 := superpose eq12 eq13
  have eq18 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq12 eq17
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation40888_implies_Equation2 (G : Type*) [Magma G] (h : Equation40888 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq12
  have eq19 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X0 := superpose eq13 eq7
  have eq29 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq13 eq19
  have eq30 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq13 eq29
  have eq31 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq13 eq30
  have eq36 (X0 X2 : G) : X0 = X2 := superpose eq31 eq31
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq38 eq36


@[equational_result]
theorem Equation40889_implies_Equation2 (G : Type*) [Magma G] (h : Equation40889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40890_implies_Equation2 (G : Type*) [Magma G] (h : Equation40890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X3) = X0 := superpose eq12 eq7
  have eq17 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = X0 := superpose eq12 eq13
  have eq18 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq12 eq17
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq12 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation40891_implies_Equation2 (G : Type*) [Magma G] (h : Equation40891 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((((X0 ◇ X4) ◇ X5) ◇ X6) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq9 eq7
  have eq14 (X0 X4 X5 X7 : G) : (((X0 ◇ X4) ◇ X5) ◇ X7) = X4 := superpose eq13 eq9
  have eq15 (X0 X4 X7 : G) : ((X0 ◇ X4) ◇ X7) = X4 := superpose eq13 eq14
  have eq16 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq13 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq22 eq17


@[equational_result]
theorem Equation40894_implies_Equation2 (G : Type*) [Magma G] (h : Equation40894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0)) ◇ X2) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) = ((X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0)) ◇ X2) := superpose eq7 eq10
  have eq16 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq11 eq9
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq16
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq17
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq38 eq18


@[equational_result]
theorem Equation40897_implies_Equation2 (G : Type*) [Magma G] (h : Equation40897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ X2) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq10
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq7 eq17
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq123 eq40


@[equational_result]
theorem Equation40899_implies_Equation2 (G : Type*) [Magma G] (h : Equation40899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2)) ◇ X1) ◇ X3) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2) = (X0 ◇ ((((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2))) := superpose eq7 eq10
  have eq13 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq10 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq10 eq14
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2)) := superpose eq10 eq9
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) := superpose eq9 eq7
  have eq30 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3) ◇ (X0 ◇ X2)) := superpose eq10 eq22
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq13 eq26
  have eq39 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2) = (X0 ◇ X0) := superpose eq33 eq11
  have eq50 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq39 eq7
  have eq57 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3) ◇ (X0 ◇ X2)) := superpose eq50 eq30
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq50 eq15
  have eq61 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) ◇ (X0 ◇ X2)) := superpose eq33 eq57
  have eq62 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X3) ◇ (X0 ◇ X2)) := superpose eq50 eq61
  have eq63 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq58 eq62
  have eq65 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq63 eq13
  have eq72 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq63 eq65
  have eq94 (X0 X1 : G) : X0 = X1 := superpose eq63 eq72
  have eq99 (X0 : G) : sK0 ≠ X0 := superpose eq94 eq8
  subsumption eq99 eq94


@[equational_result]
theorem Equation40901_implies_Equation2 (G : Type*) [Magma G] (h : Equation40901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X3) ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40904_implies_Equation2 (G : Type*) [Magma G] (h : Equation40904 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = ((X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0)) ◇ X3) := superpose eq7 eq10
  have eq23 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq16 eq9
  have eq24 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq23
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq7 eq24
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq51 eq25


@[equational_result]
theorem Equation40907_implies_Equation2 (G : Type*) [Magma G] (h : Equation40907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X1)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X1)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq9 eq9
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq54 eq35


@[equational_result]
theorem Equation40910_implies_Equation2 (G : Type*) [Magma G] (h : Equation40910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = X1 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq52 eq15


@[equational_result]
theorem Equation40911_implies_Equation2 (G : Type*) [Magma G] (h : Equation40911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X1 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq69 eq15


@[equational_result]
theorem Equation40913_implies_Equation2 (G : Type*) [Magma G] (h : Equation40913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X2 := superpose eq10 eq7
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq10 eq15
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq52 eq26


@[equational_result]
theorem Equation40915_implies_Equation2 (G : Type*) [Magma G] (h : Equation40915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X0)) ◇ X4) ◇ X3) ◇ X5) = X3 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (((X0 ◇ X3) ◇ X0) ◇ X4) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X3 X4 X5 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X4) ◇ X3) ◇ X5) = X3 := superpose eq10 eq9
  have eq13 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq10 eq7
  have eq14 (X3 X4 X5 : G) : (X4 ◇ X5) = X3 := superpose eq13 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation40918_implies_Equation2 (G : Type*) [Magma G] (h : Equation40918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X1)) ◇ X3) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X1)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X3) ◇ X1) ◇ X3) = X2 := superpose eq10 eq9
  have eq13 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq10 eq11
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq19 eq14


@[equational_result]
theorem Equation40919_implies_Equation2 (G : Type*) [Magma G] (h : Equation40919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation40921_implies_Equation2 (G : Type*) [Magma G] (h : Equation40921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X2)) ◇ X3) ◇ X3) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X2)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) = X1 := superpose eq10 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq10 eq7
  have eq29 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) = (((((((X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X3) ◇ X0) ◇ (((X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X3)) ◇ (((((X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X3) ◇ X0) ◇ (((X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X3))) ◇ (((X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X3)) := superpose eq9 eq15
  have eq51 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq16
  have eq68 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq51 eq7
  have eq70 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose eq51 eq7
  have eq122 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) := superpose eq7 eq68
  have eq138 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq70 eq122
  have eq141 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) = ((((((X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X3) ◇ X0) ◇ (((X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X3)) ◇ (((X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2)) ◇ X3) ◇ X3)) := superpose eq138 eq29
  have eq169 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X2) = X0 := superpose eq70 eq141
  have eq171 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq169 eq7
  have eq293 (X0 X2 : G) : X0 = X2 := superpose eq171 eq171
  have eq295 (X0 : G) : sK0 ≠ X0 := superpose eq293 eq8
  subsumption eq295 eq293


@[equational_result]
theorem Equation40923_implies_Equation2 (G : Type*) [Magma G] (h : Equation40923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation40925_implies_Equation2 (G : Type*) [Magma G] (h : Equation40925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq11 eq7
  have eq23 (X0 X2 : G) : X0 = X2 := superpose eq11 eq16
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq55 eq23


@[equational_result]
theorem Equation40926_implies_Equation2 (G : Type*) [Magma G] (h : Equation40926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X3)) ◇ X4) ◇ X5) ◇ X4) = X2 := superpose eq7 eq7
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 X4 X5 : G) : ((((X0 ◇ X3) ◇ X4) ◇ X5) ◇ X4) = X2 := superpose eq10 eq9
  have eq14 (X2 X4 X5 : G) : (X5 ◇ X4) = X2 := superpose eq10 eq12
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation40927_implies_Equation2 (G : Type*) [Magma G] (h : Equation40927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40928_implies_Equation2 (G : Type*) [Magma G] (h : Equation40928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40930_implies_Equation2 (G : Type*) [Magma G] (h : Equation40930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq7 eq7
  have eq15 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq11 eq11
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) = X0 := superpose eq15 eq10
  have eq37 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X1)) = X1 := superpose eq7 eq21
  have eq101 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq37
  have eq123 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X0 := superpose eq101 eq7
  have eq170 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X0 := superpose eq101 eq123
  have eq171 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq101 eq170
  have eq172 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq101 eq171
  have eq202 (X0 X2 : G) : X0 = X2 := superpose eq172 eq172
  have eq207 (X0 : G) : sK0 ≠ X0 := superpose eq202 eq8
  subsumption eq207 eq202


@[equational_result]
theorem Equation40931_implies_Equation2 (G : Type*) [Magma G] (h : Equation40931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq11 eq10
  have eq14 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq13 eq7
  have eq17 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = X0 := superpose eq13 eq14
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq13 eq17
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq13 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation40932_implies_Equation2 (G : Type*) [Magma G] (h : Equation40932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 : G) : (((X0 ◇ X0) ◇ X0) ◇ X4) = X0 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X0 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq11 eq10
  have eq14 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X3) = X0 := superpose eq13 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = X0 := superpose eq13 eq14
  have eq18 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq13 eq17
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq13 eq18
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation40934_implies_Equation2 (G : Type*) [Magma G] (h : Equation40934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ X0) := superpose eq11 eq7
  have eq24 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := superpose eq24 eq12
  have eq33 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := superpose eq24 eq11
  have eq36 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq24 eq7
  have eq41 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := superpose eq33 eq33
  have eq48 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq32 eq41
  have eq50 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq48 eq32
  have eq55 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq50 eq36
  have eq56 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq55 eq50
  have eq58 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq24 eq56
  have eq63 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1) = X0 := superpose eq58 eq7
  have eq89 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = X0 := superpose eq58 eq63
  have eq90 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq58 eq89
  have eq91 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq58 eq90
  have eq107 (X0 X2 : G) : X0 = X2 := superpose eq91 eq91
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq112 eq107


@[equational_result]
theorem Equation40936_implies_Equation2 (G : Type*) [Magma G] (h : Equation40936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation40938_implies_Equation2 (G : Type*) [Magma G] (h : Equation40938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq34 eq14


@[equational_result]
theorem Equation40939_implies_Equation2 (G : Type*) [Magma G] (h : Equation40939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq10
  have eq27 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq19 eq7
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq27 eq27
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq37 eq32


@[equational_result]
theorem Equation40940_implies_Equation2 (G : Type*) [Magma G] (h : Equation40940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : ((((X0 ◇ X4) ◇ X3) ◇ X4) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40942_implies_Equation2 (G : Type*) [Magma G] (h : Equation40942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq42 eq16


@[equational_result]
theorem Equation40943_implies_Equation2 (G : Type*) [Magma G] (h : Equation40943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (((X0 ◇ X3) ◇ X4) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq10 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40944_implies_Equation2 (G : Type*) [Magma G] (h : Equation40944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq12 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40945_implies_Equation2 (G : Type*) [Magma G] (h : Equation40945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X4) ◇ X6) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X2 X4 : G) : (X2 ◇ X4) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40947_implies_Equation2 (G : Type*) [Magma G] (h : Equation40947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X3) ◇ ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X0)) ◇ X1) ◇ ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X0)) = X1 := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) ◇ X0) = ((((((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1) ◇ X3) ◇ (((X0 ◇ X5) ◇ (((X1 ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1))) ◇ (((X1 ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X0 ◇ X5) ◇ (((X1 ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1))) := superpose eq9 eq9
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X0) := superpose eq9 eq7
  have eq34 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq27 eq7
  have eq59 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq34 eq27
  have eq69 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq34 eq59
  have eq70 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq69 eq27
  have eq98 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq70 eq7
  have eq114 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq98 eq70
  have eq147 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) ◇ X0) = (((((X0 ◇ X5) ◇ (((X1 ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) ◇ (((X1 ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) ◇ X0)) ◇ (((X0 ◇ X5) ◇ (((X1 ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1))) := superpose eq114 eq21
  have eq164 (X0 X1 X2 X4 : G) : (((X1 ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) ◇ X0) = ((((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1) ◇ (((X1 ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) := superpose eq114 eq147
  have eq165 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1) = (((X1 ◇ X4) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) ◇ X0) := superpose eq114 eq164
  have eq166 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1) = X0 := superpose eq114 eq165
  have eq167 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq114 eq166
  have eq222 (X0 X1 : G) : X0 = X1 := superpose eq114 eq167
  have eq224 (X0 : G) : sK0 ≠ X0 := superpose eq222 eq8
  subsumption eq224 eq222


@[equational_result]
theorem Equation40948_implies_Equation2 (G : Type*) [Magma G] (h : Equation40948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X3) ◇ ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X0)) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq31 (X0 X1 X2 : G) : (X0 ◇ ((((X2 ◇ X0) ◇ X0) ◇ X2) ◇ X0)) = X1 := superpose eq9 eq7
  have eq48 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq108 eq48


@[equational_result]
theorem Equation40949_implies_Equation2 (G : Type*) [Magma G] (h : Equation40949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation40953_implies_Equation2 (G : Type*) [Magma G] (h : Equation40953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) ◇ X4) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((((X2 ◇ X0) ◇ X3) ◇ X2) ◇ X2) = ((X1 ◇ (X0 ◇ X4)) ◇ X5) := superpose eq7 eq11
  have eq15 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X4) = X1 := superpose eq11 eq11
  have eq21 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ X5) = X0 := superpose eq15 eq12
  have eq24 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ X4) = X1 := superpose eq21 eq10
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq11 eq24
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq37 eq32


@[equational_result]
theorem Equation40955_implies_Equation2 (G : Type*) [Magma G] (h : Equation40955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X3) ◇ ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X2)) ◇ X3) ◇ ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 : G) : ((((X0 ◇ X3) ◇ X2) ◇ X3) ◇ X2) = X1 := superpose eq12 eq9
  have eq20 (X1 X2 X3 : G) : (X3 ◇ X2) = X1 := superpose eq12 eq16
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq23 eq21


@[equational_result]
theorem Equation40957_implies_Equation2 (G : Type*) [Magma G] (h : Equation40957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X1 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq53 eq16


@[equational_result]
theorem Equation40959_implies_Equation2 (G : Type*) [Magma G] (h : Equation40959 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq59 eq15


@[equational_result]
theorem Equation40960_implies_Equation2 (G : Type*) [Magma G] (h : Equation40960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq62 eq12


@[equational_result]
theorem Equation40961_implies_Equation2 (G : Type*) [Magma G] (h : Equation40961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X3) = X1 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq48 eq16


@[equational_result]
theorem Equation40962_implies_Equation2 (G : Type*) [Magma G] (h : Equation40962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40964_implies_Equation2 (G : Type*) [Magma G] (h : Equation40964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = X0 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X1) ◇ X0) = X1 := superpose eq12 eq7
  have eq15 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq12 eq14
  have eq27 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) = X0 := superpose eq7 eq15
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq15 eq7
  have eq30 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq15 eq7
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X2)) := superpose eq15 eq10
  have eq40 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) = X1 := superpose eq15 eq10
  have eq43 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq12 eq10
  have eq56 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq30 eq43
  have eq57 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X2) ◇ X2)) = X1 := superpose eq56 eq40
  have eq58 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (((X1 ◇ X1) ◇ X2) ◇ X2)) := superpose eq56 eq35
  have eq59 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X2)) = X1 := superpose eq29 eq57
  have eq64 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ X2)) := superpose eq59 eq58
  have eq65 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq59 eq64
  have eq68 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq65 eq7
  have eq76 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq65 eq27
  have eq97 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq76 eq68
  have eq105 (X0 X3 : G) : X0 = X3 := superpose eq97 eq97
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq105 eq8
  subsumption eq107 eq105


@[equational_result]
theorem Equation40965_implies_Equation2 (G : Type*) [Magma G] (h : Equation40965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((((X0 ◇ X3) ◇ X3) ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq7 eq7
  have eq29 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq7 eq9
  have eq42 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq29 eq10
  have eq51 (X0 X2 : G) : X0 = X2 := superpose eq42 eq42
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq56 eq51


@[equational_result]
theorem Equation40966_implies_Equation2 (G : Type*) [Magma G] (h : Equation40966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40968_implies_Equation2 (G : Type*) [Magma G] (h : Equation40968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X2)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq7 eq11
  have eq28 (X0 X1 : G) : X0 = X1 := superpose eq11 eq14
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq48 eq28


@[equational_result]
theorem Equation40970_implies_Equation2 (G : Type*) [Magma G] (h : Equation40970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation40973_implies_Equation2 (G : Type*) [Magma G] (h : Equation40973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X2) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq10 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40974_implies_Equation2 (G : Type*) [Magma G] (h : Equation40974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40976_implies_Equation2 (G : Type*) [Magma G] (h : Equation40976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X3) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq46 eq16


@[equational_result]
theorem Equation40977_implies_Equation2 (G : Type*) [Magma G] (h : Equation40977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X3) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40978_implies_Equation2 (G : Type*) [Magma G] (h : Equation40978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X3) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (((X0 ◇ X3) ◇ X4) ◇ X4) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq7
  have eq15 (X3 X4 : G) : (X4 ◇ X4) = X3 := superpose eq12 eq10
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq12 eq15
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq23 eq18


@[equational_result]
theorem Equation40979_implies_Equation2 (G : Type*) [Magma G] (h : Equation40979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X3) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation40981_implies_Equation2 (G : Type*) [Magma G] (h : Equation40981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X0) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X4) ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X0) := superpose eq7 eq12
  have eq16 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ X2) ◇ X1) = X2 := superpose eq12 eq7
  have eq19 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq13 eq7
  have eq20 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) = X0 := superpose eq19 eq10
  have eq21 (X0 X2 X4 : G) : (X4 ◇ X2) = X0 := superpose eq16 eq20
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq12 eq21
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq60 eq26


@[equational_result]
theorem Equation40982_implies_Equation2 (G : Type*) [Magma G] (h : Equation40982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X0) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : ((((X0 ◇ X4) ◇ X5) ◇ X2) ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40983_implies_Equation2 (G : Type*) [Magma G] (h : Equation40983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X0) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq32 eq13


@[equational_result]
theorem Equation40984_implies_Equation2 (G : Type*) [Magma G] (h : Equation40984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X0) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : ((((X0 ◇ X5) ◇ X6) ◇ X4) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq9 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation40986_implies_Equation2 (G : Type*) [Magma G] (h : Equation40986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X1) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X2)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation40987_implies_Equation2 (G : Type*) [Magma G] (h : Equation40987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X1) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X3 := superpose eq7 eq7
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq59 eq42


@[equational_result]
theorem Equation40988_implies_Equation2 (G : Type*) [Magma G] (h : Equation40988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X1) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation40989_implies_Equation2 (G : Type*) [Magma G] (h : Equation40989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X1) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq56 eq13


@[equational_result]
theorem Equation40991_implies_Equation2 (G : Type*) [Magma G] (h : Equation40991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X2) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq55 eq16


@[equational_result]
theorem Equation40992_implies_Equation2 (G : Type*) [Magma G] (h : Equation40992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X2) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq12 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation40993_implies_Equation2 (G : Type*) [Magma G] (h : Equation40993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X2) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation40994_implies_Equation2 (G : Type*) [Magma G] (h : Equation40994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X2) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


