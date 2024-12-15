import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation10522_implies_Equation2 (G : Type*) [Magma G] (h : Equation10522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10524_implies_Equation2 (G : Type*) [Magma G] (h : Equation10524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq12 eq12
  have eq71 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq179 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq179 eq71


@[equational_result]
theorem Equation10525_implies_Equation2 (G : Type*) [Magma G] (h : Equation10525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X1)) = X3 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq67 eq21


@[equational_result]
theorem Equation10526_implies_Equation2 (G : Type*) [Magma G] (h : Equation10526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10527_implies_Equation2 (G : Type*) [Magma G] (h : Equation10527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10529_implies_Equation2 (G : Type*) [Magma G] (h : Equation10529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq67 eq17


@[equational_result]
theorem Equation10530_implies_Equation2 (G : Type*) [Magma G] (h : Equation10530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation10531_implies_Equation2 (G : Type*) [Magma G] (h : Equation10531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ ((X4 ◇ X0) ◇ ((X5 ◇ X5) ◇ X5))))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq10
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq13 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10532_implies_Equation2 (G : Type*) [Magma G] (h : Equation10532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10534_implies_Equation2 (G : Type*) [Magma G] (h : Equation10534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X4 := superpose eq7 eq7
  have eq32 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq43 eq32


@[equational_result]
theorem Equation10535_implies_Equation2 (G : Type*) [Magma G] (h : Equation10535 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation10536_implies_Equation2 (G : Type*) [Magma G] (h : Equation10536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10537_implies_Equation2 (G : Type*) [Magma G] (h : Equation10537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 X6 X7 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ ((X5 ◇ X0) ◇ ((X6 ◇ X7) ◇ X7))))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq10
  have eq15 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq13 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10538_implies_Equation2 (G : Type*) [Magma G] (h : Equation10538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X3 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10540_implies_Equation2 (G : Type*) [Magma G] (h : Equation10540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ ((X3 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2)))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq9
  have eq26 (X0 X2 X3 : G) : ((X0 ◇ ((X3 ◇ X3) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3)) = X2 := superpose eq15 eq15
  have eq33 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ (X0 ◇ X1)) = X2 := superpose eq15 eq10
  have eq35 (X0 X2 X3 X4 : G) : ((X0 ◇ ((X3 ◇ X3) ◇ (X2 ◇ X2))) ◇ (X3 ◇ ((X4 ◇ X4) ◇ (X0 ◇ ((X3 ◇ X3) ◇ (X2 ◇ X2)))))) = X4 := superpose eq15 eq9
  have eq56 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))))) = X2 := superpose eq10 eq26
  have eq57 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X2 := superpose eq15 eq26
  have eq72 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))))) = X2 := superpose eq57 eq56
  have eq86 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq57 eq33
  have eq88 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X4) ◇ (X0 ◇ X2)))) = X4 := superpose eq57 eq35
  have eq102 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) = X2 := superpose eq57 eq72
  have eq103 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X2 := superpose eq57 eq102
  have eq104 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq57 eq103
  have eq125 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) = X3 := superpose eq86 eq9
  have eq134 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X4)) = X4 := superpose eq86 eq88
  have eq135 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X3 := superpose eq134 eq125
  have eq163 (X0 X2 : G) : X0 = X2 := superpose eq135 eq104
  have eq184 (X0 : G) : sK0 ≠ X0 := superpose eq163 eq8
  subsumption eq184 eq163


@[equational_result]
theorem Equation10542_implies_Equation2 (G : Type*) [Magma G] (h : Equation10542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq56 eq38


@[equational_result]
theorem Equation10546_implies_Equation2 (G : Type*) [Magma G] (h : Equation10546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq57 eq18


@[equational_result]
theorem Equation10550_implies_Equation2 (G : Type*) [Magma G] (h : Equation10550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq63 eq18


@[equational_result]
theorem Equation10552_implies_Equation2 (G : Type*) [Magma G] (h : Equation10552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation10553_implies_Equation2 (G : Type*) [Magma G] (h : Equation10553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation10554_implies_Equation2 (G : Type*) [Magma G] (h : Equation10554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq55 eq12


@[equational_result]
theorem Equation10555_implies_Equation2 (G : Type*) [Magma G] (h : Equation10555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation10557_implies_Equation2 (G : Type*) [Magma G] (h : Equation10557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X0) ◇ ((X4 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0)))) = ((X3 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) := superpose eq10 eq10
  have eq25 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) := superpose eq10 eq10
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) = X0 := superpose eq7 eq10
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) = X2 := superpose eq26 eq25
  have eq73 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ X0) = ((X3 ◇ (X4 ◇ X0)) ◇ (((X4 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) ◇ (X4 ◇ X0))) := superpose eq10 eq26
  have eq74 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X3) = ((X1 ◇ (X2 ◇ X3)) ◇ (((X2 ◇ X3) ◇ X0) ◇ (X2 ◇ X3))) := superpose eq26 eq26
  have eq83 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0)) = X1 := superpose eq26 eq7
  have eq86 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X2) = ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq26 eq7
  have eq89 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) ◇ ((((X2 ◇ (X2 ◇ X0)) ◇ X2) ◇ X3) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2))) = (((X2 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X3 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)))) := superpose eq26 eq10
  have eq112 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq86 eq17
  have eq126 (X0 X2 X3 : G) : (((X2 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X3 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)))) = ((X2 ◇ (X2 ◇ X3)) ◇ X2) := superpose eq74 eq89
  have eq139 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X2) ◇ X0) ◇ ((X3 ◇ ((X0 ◇ X2) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))))) := superpose eq10 eq35
  have eq158 (X0 X2 X4 : G) : (X4 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq112 eq139
  have eq159 (X0 X2 X4 : G) : (X4 ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq26 eq158
  have eq176 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X1) := superpose eq159 eq159
  have eq325 (X0 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) = X0 := superpose eq26 eq176
  have eq433 (X0 X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X2) = (((X2 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq325 eq126
  have eq434 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq325 eq83
  have eq441 (X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ X2) = X2 := superpose eq434 eq433
  have eq443 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (((X2 ◇ X3) ◇ X0) ◇ (X2 ◇ X3))) = X3 := superpose eq441 eq74
  have eq464 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X0 := superpose eq443 eq73
  have eq467 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X1)) = X0 := superpose eq464 eq7
  have eq526 (X0 X3 : G) : X0 = X3 := superpose eq467 eq467
  have eq551 (X0 : G) : sK0 ≠ X0 := superpose eq526 eq8
  subsumption eq551 eq526


@[equational_result]
theorem Equation10559_implies_Equation2 (G : Type*) [Magma G] (h : Equation10559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq59 eq40


@[equational_result]
theorem Equation10561_implies_Equation2 (G : Type*) [Magma G] (h : Equation10561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10562_implies_Equation2 (G : Type*) [Magma G] (h : Equation10562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10563_implies_Equation2 (G : Type*) [Magma G] (h : Equation10563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10565_implies_Equation2 (G : Type*) [Magma G] (h : Equation10565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10566_implies_Equation2 (G : Type*) [Magma G] (h : Equation10566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10567_implies_Equation2 (G : Type*) [Magma G] (h : Equation10567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10569_implies_Equation2 (G : Type*) [Magma G] (h : Equation10569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10570_implies_Equation2 (G : Type*) [Magma G] (h : Equation10570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10571_implies_Equation2 (G : Type*) [Magma G] (h : Equation10571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10572_implies_Equation2 (G : Type*) [Magma G] (h : Equation10572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10576_implies_Equation2 (G : Type*) [Magma G] (h : Equation10576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation10578_implies_Equation2 (G : Type*) [Magma G] (h : Equation10578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation10579_implies_Equation2 (G : Type*) [Magma G] (h : Equation10579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation10580_implies_Equation2 (G : Type*) [Magma G] (h : Equation10580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10582_implies_Equation2 (G : Type*) [Magma G] (h : Equation10582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10583_implies_Equation2 (G : Type*) [Magma G] (h : Equation10583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10584_implies_Equation2 (G : Type*) [Magma G] (h : Equation10584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10586_implies_Equation2 (G : Type*) [Magma G] (h : Equation10586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10587_implies_Equation2 (G : Type*) [Magma G] (h : Equation10587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10588_implies_Equation2 (G : Type*) [Magma G] (h : Equation10588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10589_implies_Equation2 (G : Type*) [Magma G] (h : Equation10589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10591_implies_Equation2 (G : Type*) [Magma G] (h : Equation10591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X3) ◇ ((X5 ◇ X0) ◇ X3)) = (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X3 ◇ X4) ◇ ((X5 ◇ (X6 ◇ X7)) ◇ X4)) = (((X8 ◇ X2) ◇ X7) ◇ ((X9 ◇ ((X8 ◇ X2) ◇ X7)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))))) := superpose eq10 eq10
  have eq28 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X3 ◇ X4) ◇ ((X5 ◇ (X6 ◇ X2)) ◇ X4)) = (X7 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) := superpose eq10 eq10
  have eq29 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X2)) = X0 := superpose eq7 eq10
  have eq39 (X0 X1 X2 X7 : G) : (X7 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) = X2 := superpose eq29 eq28
  have eq40 (X0 X1 X2 X7 X8 X9 : G) : (((X8 ◇ X2) ◇ X7) ◇ ((X9 ◇ ((X8 ◇ X2) ◇ X7)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))))) = X7 := superpose eq29 eq27
  have eq43 (X2 X7 X8 : G) : (((X8 ◇ X2) ◇ X7) ◇ X2) = X7 := superpose eq39 eq40
  have eq84 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq43 eq43
  have eq108 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X0 := superpose eq84 eq7
  have eq150 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq84 eq108
  have eq174 (X0 X2 : G) : X0 = X2 := superpose eq150 eq150
  have eq176 (X0 : G) : sK0 ≠ X0 := superpose eq174 eq8
  subsumption eq176 eq174


@[equational_result]
theorem Equation10592_implies_Equation2 (G : Type*) [Magma G] (h : Equation10592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((X2 ◇ X0) ◇ X3) ◇ X1) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X4 : G) : (X2 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) = X4 := superpose eq12 eq7
  have eq20 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X3)) = X1 := superpose eq12 eq7
  have eq24 (X1 X3 X4 : G) : (X4 ◇ (X3 ◇ X1)) = X1 := superpose eq12 eq20
  have eq25 (X1 X2 X4 : G) : (X2 ◇ X1) = X4 := superpose eq24 eq19
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq41 eq33


@[equational_result]
theorem Equation10593_implies_Equation2 (G : Type*) [Magma G] (h : Equation10593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq62 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq187 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq187 eq62


@[equational_result]
theorem Equation10594_implies_Equation2 (G : Type*) [Magma G] (h : Equation10594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X0)) = X4 := superpose eq7 eq7
  have eq39 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation10596_implies_Equation2 (G : Type*) [Magma G] (h : Equation10596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10597_implies_Equation2 (G : Type*) [Magma G] (h : Equation10597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10598_implies_Equation2 (G : Type*) [Magma G] (h : Equation10598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10599_implies_Equation2 (G : Type*) [Magma G] (h : Equation10599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10601_implies_Equation2 (G : Type*) [Magma G] (h : Equation10601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10602_implies_Equation2 (G : Type*) [Magma G] (h : Equation10602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10603_implies_Equation2 (G : Type*) [Magma G] (h : Equation10603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10604_implies_Equation2 (G : Type*) [Magma G] (h : Equation10604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10606_implies_Equation2 (G : Type*) [Magma G] (h : Equation10606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10607_implies_Equation2 (G : Type*) [Magma G] (h : Equation10607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10608_implies_Equation2 (G : Type*) [Magma G] (h : Equation10608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10609_implies_Equation2 (G : Type*) [Magma G] (h : Equation10609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10611_implies_Equation2 (G : Type*) [Magma G] (h : Equation10611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10612_implies_Equation2 (G : Type*) [Magma G] (h : Equation10612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10613_implies_Equation2 (G : Type*) [Magma G] (h : Equation10613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10614_implies_Equation2 (G : Type*) [Magma G] (h : Equation10614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10615_implies_Equation2 (G : Type*) [Magma G] (h : Equation10615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X1) ◇ ((X3 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10617_implies_Equation2 (G : Type*) [Magma G] (h : Equation10617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation10618_implies_Equation2 (G : Type*) [Magma G] (h : Equation10618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation10619_implies_Equation2 (G : Type*) [Magma G] (h : Equation10619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation10623_implies_Equation2 (G : Type*) [Magma G] (h : Equation10623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq11 eq10
  have eq15 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq11 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq21 eq16


@[equational_result]
theorem Equation10626_implies_Equation2 (G : Type*) [Magma G] (h : Equation10626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X3 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2))) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq9
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq29 eq19


@[equational_result]
theorem Equation10627_implies_Equation2 (G : Type*) [Magma G] (h : Equation10627 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation10629_implies_Equation2 (G : Type*) [Magma G] (h : Equation10629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq60 eq19


@[equational_result]
theorem Equation10630_implies_Equation2 (G : Type*) [Magma G] (h : Equation10630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation10631_implies_Equation2 (G : Type*) [Magma G] (h : Equation10631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ ((X4 ◇ X4) ◇ ((X0 ◇ X5) ◇ X5))))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X3 := superpose eq7 eq10
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq62 eq41


@[equational_result]
theorem Equation10632_implies_Equation2 (G : Type*) [Magma G] (h : Equation10632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation10634_implies_Equation2 (G : Type*) [Magma G] (h : Equation10634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ ((X1 ◇ X0) ◇ X1)) = (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X4 ◇ X4) ◇ (((X3 ◇ X3) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2))) = ((X1 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq7 eq9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X5 ◇ X5) ◇ (((X4 ◇ X4) ◇ (X2 ◇ X1)) ◇ X1))) = ((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X1)) := superpose eq9 eq9
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X4) ◇ ((X5 ◇ X5) ◇ (((X0 ◇ X2) ◇ X0) ◇ (X4 ◇ X4)))) = ((X3 ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) ◇ (X4 ◇ X4))) := superpose eq9 eq9
  have eq15 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) = (X0 ◇ ((X4 ◇ X4) ◇ (X2 ◇ X0))) := superpose eq9 eq9
  have eq16 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))))) = X0 := superpose eq7 eq9
  have eq18 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((((X2 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X3) ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)))) = (((X2 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) ◇ ((X4 ◇ X4) ◇ X0)) := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0)))) := superpose eq9 eq9
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) = X0 := superpose eq7 eq9
  have eq33 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X1)) = ((X2 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1)))) := superpose eq9 eq7
  have eq35 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0)))) = X2 := superpose eq24 eq21
  have eq38 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) ◇ (X3 ◇ X3)) = (((X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq9 eq10
  have eq41 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) ◇ X1)) = (X1 ◇ ((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)))) := superpose eq10 eq9
  have eq45 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X4) ◇ (X2 ◇ X1)) = ((X3 ◇ X3) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) ◇ X1)) := superpose eq9 eq24
  have eq47 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) = ((X3 ◇ (X3 ◇ X0)) ◇ X3) := superpose eq24 eq24
  have eq49 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = X0 := superpose eq9 eq24
  have eq50 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq7 eq24
  have eq51 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = ((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1))) := superpose eq9 eq24
  have eq56 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq24 eq7
  have eq61 (X1 X2 X3 X4 : G) : ((X4 ◇ X4) ◇ (X2 ◇ X1)) = ((X3 ◇ X3) ◇ (X2 ◇ X1)) := superpose eq7 eq45
  have eq69 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))))) := superpose eq10 eq35
  have eq98 (X0 X1 X4 : G) : ((X1 ◇ X1) ◇ X0) = ((X4 ◇ X4) ◇ X0) := superpose eq7 eq61
  have eq119 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2)))) := superpose eq61 eq7
  have eq133 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X4) = ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))))) := superpose eq61 eq35
  have eq163 (X1 X2 X4 : G) : (X4 ◇ X4) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq119 eq133
  have eq300 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose eq98 eq7
  have eq322 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X2)))) = X1 := superpose eq98 eq7
  have eq324 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X3)) ◇ X1)) = (X1 ◇ ((X4 ◇ X4) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq98 eq9
  have eq327 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq98 eq35
  have eq373 (X1 X2 X3 : G) : ((X2 ◇ X2) ◇ ((X1 ◇ (X3 ◇ X3)) ◇ X1)) = X1 := superpose eq300 eq324
  have eq374 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ X3) := superpose eq300 eq327
  have eq527 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq374 eq35
  have eq642 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ ((X3 ◇ X3) ◇ (((X4 ◇ X4) ◇ ((((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2) ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)))) ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2))))) = ((X5 ◇ X5) ◇ X0) := superpose eq7 eq11
  have eq714 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X4) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ ((X0 ◇ (X3 ◇ X3)) ◇ X0)) ◇ X0))) ◇ (X3 ◇ X3))) = X0 := superpose eq11 eq24
  have eq761 (X0 X1 X3 X4 : G) : ((X4 ◇ X4) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X3 ◇ X3))) = X0 := superpose eq373 eq714
  have eq1112 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = ((X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ ((X2 ◇ X2) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq15 eq33
  have eq2805 (X0 X1 X2 X3 X4 X5 : G) : (((X5 ◇ X5) ◇ (X3 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) = ((X4 ◇ X4) ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X3) ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2))) := superpose eq12 eq24
  have eq3074 (X2 X3 X4 X5 : G) : (((X5 ◇ X5) ◇ (X3 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) = ((X4 ◇ X4) ◇ ((X3 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))) := superpose eq51 eq2805
  have eq3968 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X4) ◇ ((X3 ◇ (((X0 ◇ X0) ◇ X3) ◇ (X0 ◇ X0))) ◇ X3)) = (X3 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))))) := superpose eq11 eq41
  have eq3987 (X0 X1 X2 X3 X5 : G) : ((X5 ◇ X5) ◇ ((((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) ◇ X0)) = (X0 ◇ ((X3 ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X0))) := superpose eq41 eq11
  have eq4166 (X0 X3 X4 : G) : ((X4 ◇ X4) ◇ ((X3 ◇ (((X0 ◇ X0) ◇ X3) ◇ (X0 ◇ X0))) ◇ X3)) = (X3 ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) ◇ (X0 ◇ X0))) := superpose eq322 eq3968
  have eq4182 (X0 X1 X2 X3 X5 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)))) ◇ X0))) = ((X5 ◇ X5) ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) := superpose eq10 eq3987
  have eq4761 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ X3) ◇ (X1 ◇ X1)))) = ((X4 ◇ X4) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) := superpose eq163 eq13
  have eq5091 (X0 X1 X3 X4 : G) : ((X4 ◇ X4) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) = X3 := superpose eq322 eq4761
  have eq5092 (X2 X3 X5 : G) : (((X5 ◇ X5) ◇ (X3 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) = X3 := superpose eq5091 eq3074
  have eq5116 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq5092 eq51
  have eq5135 (X0 X3 X4 : G) : ((X4 ◇ X4) ◇ ((X3 ◇ (((X0 ◇ X0) ◇ X3) ◇ (X0 ◇ X0))) ◇ X3)) = (X3 ◇ ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq5116 eq4166
  have eq5202 (X0 X1 X3 : G) : (X1 ◇ ((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)))) = (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq5135 eq41
  have eq5212 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose eq5202 eq69
  have eq5226 (X0 X2 X3 X5 : G) : ((X5 ◇ X5) ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) = (X0 ◇ ((X3 ◇ X3) ◇ ((X0 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))) ◇ X0))) := superpose eq5202 eq4182
  have eq5229 (X0 X2 X5 : G) : ((X5 ◇ X5) ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) = ((X0 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) := superpose eq7 eq5226
  have eq5247 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = ((X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq5229 eq1112
  have eq5949 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = ((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq61 eq5116
  have eq6002 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) = X0 := superpose eq7 eq5116
  have eq6749 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))))) ◇ (X4 ◇ X4)) = ((((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X2) ◇ (((X3 ◇ X3) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))))) ◇ (X4 ◇ X4)) ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) := superpose eq16 eq38
  have eq6811 (X0 X1 X3 X4 : G) : (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X3 ◇ X3) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))))) ◇ (X4 ◇ X4)) = ((((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X3 ◇ X3) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))))) ◇ (X4 ◇ X4)) ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) := superpose eq5949 eq6749
  have eq6812 (X0 X1 X4 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ (X4 ◇ X4)) = (((((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ (X4 ◇ X4)) ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) := superpose eq35 eq6811
  have eq6813 (X0 X1 : G) : (X0 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) = X0 := superpose eq6002 eq6812
  have eq7804 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X4 ◇ X4) ◇ (((X5 ◇ X5) ◇ (X1 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)))) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))))) = ((X6 ◇ X6) ◇ ((((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X3 ◇ X3) ◇ X2)) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)))) := superpose eq18 eq12
  have eq7966 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X6 ◇ X6) ◇ ((((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X3 ◇ X3) ◇ X2)) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)))) = (((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X4 ◇ X4) ◇ (((X5 ◇ X5) ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))))) := superpose eq7 eq7804
  have eq8675 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)) = X0 := superpose eq49 eq50
  have eq8688 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ X2))))) = X1 := superpose eq50 eq6813
  have eq9222 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X0)) = X1 := superpose eq50 eq761
  have eq9703 (X0 X2 X3 : G) : ((X3 ◇ (X3 ◇ ((X2 ◇ X2) ◇ X0))) ◇ X3) = X0 := superpose eq24 eq47
  have eq9848 (X0 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X2 ◇ X2)) := superpose eq8688 eq9703
  have eq9920 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = ((X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq9848 eq5247
  have eq9926 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = ((X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq527 eq9920
  have eq9927 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) = X0 := superpose eq9926 eq49
  have eq9928 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9927 eq8675
  have eq9929 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq9927 eq9222
  have eq9963 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose eq9929 eq5212
  have eq10492 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq9929 eq9963
  have eq10493 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X1 ◇ X1)) := superpose eq9929 eq10492
  have eq10494 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X1 := superpose eq9928 eq10493
  have eq10496 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((((X2 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X3) ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)))) = (((X2 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X0) := superpose eq10494 eq18
  have eq10497 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) := superpose eq10494 eq56
  have eq10504 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ ((X3 ◇ X3) ◇ (((X4 ◇ X4) ◇ ((((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2) ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)))) ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2))))) = X0 := superpose eq10494 eq642
  have eq10521 (X0 X1 X2 X4 X5 X6 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X4 ◇ X4) ◇ (((X5 ◇ X5) ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))))) = ((X6 ◇ X6) ◇ ((((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)))) := superpose eq10494 eq7966
  have eq10524 (X0 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X3) = X0 := superpose eq10494 eq9703
  have eq10593 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ ((((X3 ◇ X0) ◇ X3) ◇ X3) ◇ ((X3 ◇ X0) ◇ X3))) = (((X3 ◇ X0) ◇ X3) ◇ X0) := superpose eq10494 eq10496
  have eq10599 (X0 X1 X2 X4 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ (((X4 ◇ X4) ◇ ((((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X2) ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)))) ◇ ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)))) = X0 := superpose eq10494 eq10504
  have eq10600 (X0 X2 X4 : G) : (((X2 ◇ X0) ◇ X2) ◇ (((X4 ◇ X4) ◇ ((((X2 ◇ X0) ◇ X2) ◇ X2) ◇ ((X2 ◇ X0) ◇ X2))) ◇ ((X2 ◇ X0) ◇ X2))) = X0 := superpose eq10494 eq10599
  have eq10601 (X0 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ ((((X2 ◇ X0) ◇ X2) ◇ X0) ◇ ((X2 ◇ X0) ◇ X2))) = X0 := superpose eq10593 eq10600
  have eq10646 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X4 ◇ X4) ◇ (((X5 ◇ X5) ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))))) = ((((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq10494 eq10521
  have eq10647 (X1 X2 X4 X5 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ ((X4 ◇ X4) ◇ (((X5 ◇ X5) ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)))) := superpose eq10494 eq10646
  have eq10648 (X1 X2 X5 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ (((X5 ◇ X5) ◇ X2) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq10494 eq10647
  have eq10649 (X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq10494 eq10648
  have eq10655 (X0 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2)))) = X0 := superpose eq10649 eq10601
  have eq10663 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10524 eq10497
  have eq10669 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq10663 eq9929
  have eq10691 (X0 X2 : G) : ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := superpose eq10669 eq10655
  have eq10699 (X0 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X0)) = X0 := superpose eq10669 eq10691
  have eq10700 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq10669 eq10699
  have eq10723 (X0 X2 : G) : X0 = X2 := superpose eq10700 eq10700
  have eq10734 (X0 : G) : sK0 ≠ X0 := superpose eq10723 eq8
  subsumption eq10734 eq10723


@[equational_result]
theorem Equation10636_implies_Equation2 (G : Type*) [Magma G] (h : Equation10636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = X3 := superpose eq11 eq10
  have eq15 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq11 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq21 eq16


@[equational_result]
theorem Equation10638_implies_Equation2 (G : Type*) [Magma G] (h : Equation10638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10639_implies_Equation2 (G : Type*) [Magma G] (h : Equation10639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10640_implies_Equation2 (G : Type*) [Magma G] (h : Equation10640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10642_implies_Equation2 (G : Type*) [Magma G] (h : Equation10642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10643_implies_Equation2 (G : Type*) [Magma G] (h : Equation10643 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10644_implies_Equation2 (G : Type*) [Magma G] (h : Equation10644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10646_implies_Equation2 (G : Type*) [Magma G] (h : Equation10646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10647_implies_Equation2 (G : Type*) [Magma G] (h : Equation10647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10648_implies_Equation2 (G : Type*) [Magma G] (h : Equation10648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10649_implies_Equation2 (G : Type*) [Magma G] (h : Equation10649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10652_implies_Equation2 (G : Type*) [Magma G] (h : Equation10652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((((X2 ◇ X2) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3) ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X0) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq9
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq68 eq17


@[equational_result]
theorem Equation10653_implies_Equation2 (G : Type*) [Magma G] (h : Equation10653 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation10655_implies_Equation2 (G : Type*) [Magma G] (h : Equation10655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10656_implies_Equation2 (G : Type*) [Magma G] (h : Equation10656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10657_implies_Equation2 (G : Type*) [Magma G] (h : Equation10657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10659_implies_Equation2 (G : Type*) [Magma G] (h : Equation10659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10660_implies_Equation2 (G : Type*) [Magma G] (h : Equation10660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10661_implies_Equation2 (G : Type*) [Magma G] (h : Equation10661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10663_implies_Equation2 (G : Type*) [Magma G] (h : Equation10663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10664_implies_Equation2 (G : Type*) [Magma G] (h : Equation10664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10665_implies_Equation2 (G : Type*) [Magma G] (h : Equation10665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10666_implies_Equation2 (G : Type*) [Magma G] (h : Equation10666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10668_implies_Equation2 (G : Type*) [Magma G] (h : Equation10668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq77 eq19


@[equational_result]
theorem Equation10669_implies_Equation2 (G : Type*) [Magma G] (h : Equation10669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation10670_implies_Equation2 (G : Type*) [Magma G] (h : Equation10670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X5 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq61 eq19


@[equational_result]
theorem Equation10671_implies_Equation2 (G : Type*) [Magma G] (h : Equation10671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation10673_implies_Equation2 (G : Type*) [Magma G] (h : Equation10673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10674_implies_Equation2 (G : Type*) [Magma G] (h : Equation10674 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10675_implies_Equation2 (G : Type*) [Magma G] (h : Equation10675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10676_implies_Equation2 (G : Type*) [Magma G] (h : Equation10676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10678_implies_Equation2 (G : Type*) [Magma G] (h : Equation10678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10679_implies_Equation2 (G : Type*) [Magma G] (h : Equation10679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10680_implies_Equation2 (G : Type*) [Magma G] (h : Equation10680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10681_implies_Equation2 (G : Type*) [Magma G] (h : Equation10681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10683_implies_Equation2 (G : Type*) [Magma G] (h : Equation10683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10684_implies_Equation2 (G : Type*) [Magma G] (h : Equation10684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10685_implies_Equation2 (G : Type*) [Magma G] (h : Equation10685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10686_implies_Equation2 (G : Type*) [Magma G] (h : Equation10686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10688_implies_Equation2 (G : Type*) [Magma G] (h : Equation10688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10689_implies_Equation2 (G : Type*) [Magma G] (h : Equation10689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10690_implies_Equation2 (G : Type*) [Magma G] (h : Equation10690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10691_implies_Equation2 (G : Type*) [Magma G] (h : Equation10691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10692_implies_Equation2 (G : Type*) [Magma G] (h : Equation10692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X2) ◇ ((X3 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10694_implies_Equation2 (G : Type*) [Magma G] (h : Equation10694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq44 eq28


@[equational_result]
theorem Equation10695_implies_Equation2 (G : Type*) [Magma G] (h : Equation10695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation10696_implies_Equation2 (G : Type*) [Magma G] (h : Equation10696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation10697_implies_Equation2 (G : Type*) [Magma G] (h : Equation10697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation10699_implies_Equation2 (G : Type*) [Magma G] (h : Equation10699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq47 eq29


@[equational_result]
theorem Equation10700_implies_Equation2 (G : Type*) [Magma G] (h : Equation10700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ ((X5 ◇ X1) ◇ X2))) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq140 eq45


@[equational_result]
theorem Equation10701_implies_Equation2 (G : Type*) [Magma G] (h : Equation10701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((X5 ◇ X1) ◇ ((X3 ◇ X4) ◇ ((X0 ◇ X2) ◇ X4))))) = X5 := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq50 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq151 eq50


@[equational_result]
theorem Equation10702_implies_Equation2 (G : Type*) [Magma G] (h : Equation10702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation10704_implies_Equation2 (G : Type*) [Magma G] (h : Equation10704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) = X1 := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq7 eq12
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq29
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq125 eq38


@[equational_result]
theorem Equation10705_implies_Equation2 (G : Type*) [Magma G] (h : Equation10705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation10706_implies_Equation2 (G : Type*) [Magma G] (h : Equation10706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq48 eq15


@[equational_result]
theorem Equation10707_implies_Equation2 (G : Type*) [Magma G] (h : Equation10707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation10709_implies_Equation2 (G : Type*) [Magma G] (h : Equation10709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) = X3 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq65 eq21


@[equational_result]
theorem Equation10710_implies_Equation2 (G : Type*) [Magma G] (h : Equation10710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation10711_implies_Equation2 (G : Type*) [Magma G] (h : Equation10711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ ((X5 ◇ ((X3 ◇ X4) ◇ ((X0 ◇ X4) ◇ X4))) ◇ ((X3 ◇ X4) ◇ ((X0 ◇ X4) ◇ X4))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ X0)) = X5 := superpose eq7 eq9
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq31 eq19


@[equational_result]
theorem Equation10712_implies_Equation2 (G : Type*) [Magma G] (h : Equation10712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation10714_implies_Equation2 (G : Type*) [Magma G] (h : Equation10714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) = X4 := superpose eq7 eq7
  have eq35 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq57 eq35


@[equational_result]
theorem Equation10715_implies_Equation2 (G : Type*) [Magma G] (h : Equation10715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation10716_implies_Equation2 (G : Type*) [Magma G] (h : Equation10716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation10717_implies_Equation2 (G : Type*) [Magma G] (h : Equation10717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation10718_implies_Equation2 (G : Type*) [Magma G] (h : Equation10718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation10720_implies_Equation2 (G : Type*) [Magma G] (h : Equation10720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq44 eq28


@[equational_result]
theorem Equation10721_implies_Equation2 (G : Type*) [Magma G] (h : Equation10721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X5) ◇ X2))) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq9
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq168 eq65


@[equational_result]
theorem Equation10722_implies_Equation2 (G : Type*) [Magma G] (h : Equation10722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ ((X1 ◇ X0) ◇ X5)) = (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) := superpose eq7 eq7
  have eq47 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : ((X4 ◇ X5) ◇ ((X6 ◇ (X7 ◇ X8)) ◇ X5)) = (X6 ◇ ((X9 ◇ ((X0 ◇ X3) ◇ X8)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))))) := superpose eq10 eq10
  have eq49 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X4 ◇ X5) ◇ ((X6 ◇ (X0 ◇ X3)) ◇ X5)) = (X6 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2)))) := superpose eq10 eq10
  have eq57 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X5 ◇ ((X0 ◇ X3) ◇ X6)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))))) = X6 := superpose eq10 eq7
  have eq75 (X4 X5 X6 X7 X8 : G) : ((X4 ◇ X5) ◇ ((X6 ◇ (X7 ◇ X8)) ◇ X5)) = X8 := superpose eq57 eq47
  have eq77 (X0 X1 X2 X3 X6 : G) : (X6 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2)))) = X3 := superpose eq75 eq49
  have eq85 (X3 X4 X6 : G) : (X4 ◇ X3) = X6 := superpose eq77 eq57
  have eq99 (X0 X4 : G) : X0 = X4 := superpose eq7 eq85
  have eq182 (X0 : G) : sK0 ≠ X0 := superpose eq99 eq8
  subsumption eq182 eq99


@[equational_result]
theorem Equation10723_implies_Equation2 (G : Type*) [Magma G] (h : Equation10723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation10725_implies_Equation2 (G : Type*) [Magma G] (h : Equation10725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10726_implies_Equation2 (G : Type*) [Magma G] (h : Equation10726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10727_implies_Equation2 (G : Type*) [Magma G] (h : Equation10727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10728_implies_Equation2 (G : Type*) [Magma G] (h : Equation10728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10730_implies_Equation2 (G : Type*) [Magma G] (h : Equation10730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10731_implies_Equation2 (G : Type*) [Magma G] (h : Equation10731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10732_implies_Equation2 (G : Type*) [Magma G] (h : Equation10732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10733_implies_Equation2 (G : Type*) [Magma G] (h : Equation10733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10735_implies_Equation2 (G : Type*) [Magma G] (h : Equation10735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10736_implies_Equation2 (G : Type*) [Magma G] (h : Equation10736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10737_implies_Equation2 (G : Type*) [Magma G] (h : Equation10737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10738_implies_Equation2 (G : Type*) [Magma G] (h : Equation10738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10740_implies_Equation2 (G : Type*) [Magma G] (h : Equation10740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10741_implies_Equation2 (G : Type*) [Magma G] (h : Equation10741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10742_implies_Equation2 (G : Type*) [Magma G] (h : Equation10742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10743_implies_Equation2 (G : Type*) [Magma G] (h : Equation10743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10744_implies_Equation2 (G : Type*) [Magma G] (h : Equation10744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X1 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10746_implies_Equation2 (G : Type*) [Magma G] (h : Equation10746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq34 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq51 eq34


@[equational_result]
theorem Equation10747_implies_Equation2 (G : Type*) [Magma G] (h : Equation10747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X5) ◇ X2))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X4) ◇ X0)) = X5 := superpose eq7 eq7
  have eq43 (X0 X6 : G) : X0 = X6 := superpose eq9 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq61 eq43


@[equational_result]
theorem Equation10748_implies_Equation2 (G : Type*) [Magma G] (h : Equation10748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq48 eq15


@[equational_result]
theorem Equation10749_implies_Equation2 (G : Type*) [Magma G] (h : Equation10749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation10751_implies_Equation2 (G : Type*) [Magma G] (h : Equation10751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10752_implies_Equation2 (G : Type*) [Magma G] (h : Equation10752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10753_implies_Equation2 (G : Type*) [Magma G] (h : Equation10753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10754_implies_Equation2 (G : Type*) [Magma G] (h : Equation10754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10756_implies_Equation2 (G : Type*) [Magma G] (h : Equation10756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10757_implies_Equation2 (G : Type*) [Magma G] (h : Equation10757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10758_implies_Equation2 (G : Type*) [Magma G] (h : Equation10758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10759_implies_Equation2 (G : Type*) [Magma G] (h : Equation10759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10761_implies_Equation2 (G : Type*) [Magma G] (h : Equation10761 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10762_implies_Equation2 (G : Type*) [Magma G] (h : Equation10762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10763_implies_Equation2 (G : Type*) [Magma G] (h : Equation10763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation10764_implies_Equation2 (G : Type*) [Magma G] (h : Equation10764 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10766_implies_Equation2 (G : Type*) [Magma G] (h : Equation10766 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10767_implies_Equation2 (G : Type*) [Magma G] (h : Equation10767 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10768_implies_Equation2 (G : Type*) [Magma G] (h : Equation10768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10769_implies_Equation2 (G : Type*) [Magma G] (h : Equation10769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10770_implies_Equation2 (G : Type*) [Magma G] (h : Equation10770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X2 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10772_implies_Equation2 (G : Type*) [Magma G] (h : Equation10772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq12
  have eq50 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq178 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq178 eq50


@[equational_result]
theorem Equation10773_implies_Equation2 (G : Type*) [Magma G] (h : Equation10773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq71 eq13


@[equational_result]
theorem Equation10774_implies_Equation2 (G : Type*) [Magma G] (h : Equation10774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq49 eq15


@[equational_result]
theorem Equation10775_implies_Equation2 (G : Type*) [Magma G] (h : Equation10775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation10777_implies_Equation2 (G : Type*) [Magma G] (h : Equation10777 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10778_implies_Equation2 (G : Type*) [Magma G] (h : Equation10778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10779_implies_Equation2 (G : Type*) [Magma G] (h : Equation10779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation10780_implies_Equation2 (G : Type*) [Magma G] (h : Equation10780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10782_implies_Equation2 (G : Type*) [Magma G] (h : Equation10782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10783_implies_Equation2 (G : Type*) [Magma G] (h : Equation10783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10784_implies_Equation2 (G : Type*) [Magma G] (h : Equation10784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10785_implies_Equation2 (G : Type*) [Magma G] (h : Equation10785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10787_implies_Equation2 (G : Type*) [Magma G] (h : Equation10787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10788_implies_Equation2 (G : Type*) [Magma G] (h : Equation10788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10789_implies_Equation2 (G : Type*) [Magma G] (h : Equation10789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10790_implies_Equation2 (G : Type*) [Magma G] (h : Equation10790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10792_implies_Equation2 (G : Type*) [Magma G] (h : Equation10792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10793_implies_Equation2 (G : Type*) [Magma G] (h : Equation10793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10794_implies_Equation2 (G : Type*) [Magma G] (h : Equation10794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10795_implies_Equation2 (G : Type*) [Magma G] (h : Equation10795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10796_implies_Equation2 (G : Type*) [Magma G] (h : Equation10796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X3 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10798_implies_Equation2 (G : Type*) [Magma G] (h : Equation10798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X5 := superpose eq7 eq7
  have eq35 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq53 eq35


@[equational_result]
theorem Equation10799_implies_Equation2 (G : Type*) [Magma G] (h : Equation10799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation10800_implies_Equation2 (G : Type*) [Magma G] (h : Equation10800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation10801_implies_Equation2 (G : Type*) [Magma G] (h : Equation10801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation10802_implies_Equation2 (G : Type*) [Magma G] (h : Equation10802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X0) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation10804_implies_Equation2 (G : Type*) [Magma G] (h : Equation10804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10805_implies_Equation2 (G : Type*) [Magma G] (h : Equation10805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10806_implies_Equation2 (G : Type*) [Magma G] (h : Equation10806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10807_implies_Equation2 (G : Type*) [Magma G] (h : Equation10807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10808_implies_Equation2 (G : Type*) [Magma G] (h : Equation10808 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X1) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10810_implies_Equation2 (G : Type*) [Magma G] (h : Equation10810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10811_implies_Equation2 (G : Type*) [Magma G] (h : Equation10811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10812_implies_Equation2 (G : Type*) [Magma G] (h : Equation10812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10813_implies_Equation2 (G : Type*) [Magma G] (h : Equation10813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10814_implies_Equation2 (G : Type*) [Magma G] (h : Equation10814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X2) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10816_implies_Equation2 (G : Type*) [Magma G] (h : Equation10816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10817_implies_Equation2 (G : Type*) [Magma G] (h : Equation10817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10818_implies_Equation2 (G : Type*) [Magma G] (h : Equation10818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10819_implies_Equation2 (G : Type*) [Magma G] (h : Equation10819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10820_implies_Equation2 (G : Type*) [Magma G] (h : Equation10820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X3) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10822_implies_Equation2 (G : Type*) [Magma G] (h : Equation10822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation10823_implies_Equation2 (G : Type*) [Magma G] (h : Equation10823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10824_implies_Equation2 (G : Type*) [Magma G] (h : Equation10824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10825_implies_Equation2 (G : Type*) [Magma G] (h : Equation10825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10826_implies_Equation2 (G : Type*) [Magma G] (h : Equation10826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10828_implies_Equation2 (G : Type*) [Magma G] (h : Equation10828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X5) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10829_implies_Equation2 (G : Type*) [Magma G] (h : Equation10829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X5) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10830_implies_Equation2 (G : Type*) [Magma G] (h : Equation10830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X5) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10831_implies_Equation2 (G : Type*) [Magma G] (h : Equation10831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X5) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10832_implies_Equation2 (G : Type*) [Magma G] (h : Equation10832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X5) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation10833_implies_Equation2 (G : Type*) [Magma G] (h : Equation10833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X5) ◇ X6))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11039_implies_Equation2 (G : Type*) [Magma G] (h : Equation11039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = (X1 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := superpose eq11 eq10
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq13 eq9
  have eq15 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq14
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq15 eq7
  have eq17 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq16 eq15
  have eq20 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq16 eq17
  have eq21 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq16 eq20
  have eq24 (X0 X1 : G) : X0 = X1 := superpose eq16 eq21
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation11042_implies_Equation2 (G : Type*) [Magma G] (h : Equation11042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq40 eq13


@[equational_result]
theorem Equation11044_implies_Equation2 (G : Type*) [Magma G] (h : Equation11044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq41 eq15


@[equational_result]
theorem Equation11045_implies_Equation2 (G : Type*) [Magma G] (h : Equation11045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq124 eq39


@[equational_result]
theorem Equation11046_implies_Equation2 (G : Type*) [Magma G] (h : Equation11046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation11049_implies_Equation2 (G : Type*) [Magma G] (h : Equation11049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq107 eq32


@[equational_result]
theorem Equation11052_implies_Equation2 (G : Type*) [Magma G] (h : Equation11052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq109 eq32


@[equational_result]
theorem Equation11054_implies_Equation2 (G : Type*) [Magma G] (h : Equation11054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)))) ◇ X0)) = X3 := superpose eq7 eq7
  have eq30 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := superpose eq10 eq7
  have eq48 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq30
  have eq101 (X0 X2 : G) : X0 = X2 := superpose eq48 eq48
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq101 eq8
  subsumption eq175 eq101


@[equational_result]
theorem Equation11056_implies_Equation2 (G : Type*) [Magma G] (h : Equation11056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation11058_implies_Equation2 (G : Type*) [Magma G] (h : Equation11058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq9
  have eq49 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq13 eq13
  have eq162 (X0 X3 : G) : X0 = X3 := superpose eq49 eq49
  have eq190 (X0 : G) : sK0 ≠ X0 := superpose eq162 eq8
  subsumption eq190 eq162


@[equational_result]
theorem Equation11059_implies_Equation2 (G : Type*) [Magma G] (h : Equation11059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3)))) = X2 := superpose eq7 eq10
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq13
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq7 eq20
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq68 eq42


@[equational_result]
theorem Equation11060_implies_Equation2 (G : Type*) [Magma G] (h : Equation11060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X5))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X4))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X1 ◇ X0) := superpose eq11 eq10
  have eq28 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = X0 := superpose eq13 eq7
  have eq33 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq9
  have eq49 (X0 X3 : G) : (X3 ◇ X0) = X0 := superpose eq33 eq28
  have eq50 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3))) = X0 := superpose eq49 eq7
  have eq62 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq49 eq50
  have eq63 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq49 eq62
  have eq64 (X0 X3 : G) : X0 = X3 := superpose eq63 eq63
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq66 eq64


@[equational_result]
theorem Equation11062_implies_Equation2 (G : Type*) [Magma G] (h : Equation11062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq9
  have eq27 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq10 eq10
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq9 eq10
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)))) = X1 := superpose eq10 eq7
  have eq46 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq29 eq27
  have eq53 (X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X1) = X1 := superpose eq9 eq37
  have eq54 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq46 eq53
  have eq55 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq54 eq9
  have eq56 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq54 eq11
  have eq74 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq55 eq46
  have eq83 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq74 eq56
  have eq89 (X0 X1 : G) : X0 = X1 := superpose eq54 eq83
  have eq97 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq8
  subsumption eq97 eq89


@[equational_result]
theorem Equation11064_implies_Equation2 (G : Type*) [Magma G] (h : Equation11064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq47 eq18


@[equational_result]
theorem Equation11066_implies_Equation2 (G : Type*) [Magma G] (h : Equation11066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X2)) ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ (X3 ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq12
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))) = (X1 ◇ (((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))) ◇ X2) ◇ X0)) := superpose eq12 eq9
  have eq43 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))) := superpose eq12 eq33
  have eq44 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq43 eq12
  have eq54 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X3) = X3 := superpose eq44 eq11
  have eq66 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq44 eq54
  have eq69 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = X2 := superpose eq66 eq15
  have eq78 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) = X2 := superpose eq66 eq69
  have eq79 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq66 eq78
  have eq80 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X2 := superpose eq66 eq79
  have eq81 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq66 eq80
  have eq90 (X0 X3 : G) : X0 = X3 := superpose eq81 eq81
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq101 eq90


@[equational_result]
theorem Equation11067_implies_Equation2 (G : Type*) [Magma G] (h : Equation11067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X3)))) = X2 := superpose eq7 eq12
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq14
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq7 eq21
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq84 eq50


@[equational_result]
theorem Equation11068_implies_Equation2 (G : Type*) [Magma G] (h : Equation11068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation11070_implies_Equation2 (G : Type*) [Magma G] (h : Equation11070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X5 ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) ◇ ((X4 ◇ (X4 ◇ X5)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq9
  have eq23 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) ◇ X4) = X4 := superpose eq17 eq11
  have eq26 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq17 eq23
  have eq27 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq26 eq9
  have eq33 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq26 eq27
  have eq38 (X0 X1 : G) : X0 = X1 := superpose eq26 eq33
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq52 eq38


@[equational_result]
theorem Equation11071_implies_Equation2 (G : Type*) [Magma G] (h : Equation11071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation11072_implies_Equation2 (G : Type*) [Magma G] (h : Equation11072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X5 ◇ X5))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq37 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq127 eq37


@[equational_result]
theorem Equation11073_implies_Equation2 (G : Type*) [Magma G] (h : Equation11073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation11076_implies_Equation2 (G : Type*) [Magma G] (h : Equation11076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X1 := superpose eq11 eq11
  have eq23 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq15 eq7
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq23 eq23
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq34 eq26


@[equational_result]
theorem Equation11079_implies_Equation2 (G : Type*) [Magma G] (h : Equation11079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq103 eq33


@[equational_result]
theorem Equation11083_implies_Equation2 (G : Type*) [Magma G] (h : Equation11083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation11086_implies_Equation2 (G : Type*) [Magma G] (h : Equation11086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) = X1 := superpose eq7 eq10
  have eq17 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq11 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq27 eq18


@[equational_result]
theorem Equation11089_implies_Equation2 (G : Type*) [Magma G] (h : Equation11089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq10 eq9
  have eq17 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq10
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq40 (X0 X1 : G) : X0 = X1 := superpose eq17 eq18
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq69 eq40


@[equational_result]
theorem Equation11091_implies_Equation2 (G : Type*) [Magma G] (h : Equation11091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)))) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X1 ◇ X0) := superpose eq9 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq13 eq13
  have eq32 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq7 eq15
  have eq103 (X0 X3 : G) : X0 = X3 := superpose eq7 eq32
  have eq230 (X0 : G) : sK0 ≠ X0 := superpose eq103 eq8
  subsumption eq230 eq103


@[equational_result]
theorem Equation11092_implies_Equation2 (G : Type*) [Magma G] (h : Equation11092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ X2))) = X1 := superpose eq10 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq13 eq10
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq15 eq15
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation11093_implies_Equation2 (G : Type*) [Magma G] (h : Equation11093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation11095_implies_Equation2 (G : Type*) [Magma G] (h : Equation11095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq9
  have eq37 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) = X2 := superpose eq12 eq12
  have eq55 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq37 eq7
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq9 eq55
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq85 eq56


@[equational_result]
theorem Equation11097_implies_Equation2 (G : Type*) [Magma G] (h : Equation11097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq24 (X0 X1 X2 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X4)) = X1 := superpose eq7 eq11
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq24 eq7
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq9 eq35
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq83 eq36


@[equational_result]
theorem Equation11099_implies_Equation2 (G : Type*) [Magma G] (h : Equation11099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))))) = X1 := superpose eq7 eq7
  have eq23 (X0 X2 : G) : X0 = X2 := superpose eq9 eq10
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq28 eq23


@[equational_result]
theorem Equation11100_implies_Equation2 (G : Type*) [Magma G] (h : Equation11100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = X1 := superpose eq10 eq9
  have eq25 (X0 X2 : G) : X0 = X2 := superpose eq10 eq11
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq32 eq25


@[equational_result]
theorem Equation11101_implies_Equation2 (G : Type*) [Magma G] (h : Equation11101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X5))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = X1 := superpose eq7 eq9
  have eq23 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq14 eq16
  have eq24 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X3))) = X0 := superpose eq23 eq7
  have eq30 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq23 eq24
  have eq31 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq23 eq30
  have eq37 (X0 X1 : G) : X0 = X1 := superpose eq31 eq23
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq47 eq37


@[equational_result]
theorem Equation11104_implies_Equation2 (G : Type*) [Magma G] (h : Equation11104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (((X0 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))))) := superpose eq7 eq10
  have eq19 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (((((X0 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X4)) ◇ (X4 ◇ X4)) ◇ ((((X0 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X4)) ◇ (X4 ◇ X4))))) = X2 := superpose eq7 eq9
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (((((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3)) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3))) ◇ (((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3)) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3)))) ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3)) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3))) ◇ (((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3)) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3))))))) := superpose eq9 eq10
  have eq52 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))))) = (X2 ◇ (X3 ◇ ((((X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1)))))) := superpose eq13 eq13
  have eq58 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) ◇ X2)) = X0 := superpose eq7 eq13
  have eq59 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X2)) = X0 := superpose eq10 eq13
  have eq85 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ ((((X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X0 ◇ X1)))))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq13 eq52
  have eq115 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X2))) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq59 eq59
  have eq174 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))) ◇ X2)) = X0 := superpose eq115 eq58
  have eq178 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ ((((X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ (X0 ◇ X1)))))) := superpose eq115 eq85
  have eq191 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3)) ◇ (((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3)) ◇ (((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3)) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3))))) ◇ (((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3)) ◇ (((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3)) ◇ (((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3)) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3)))))))) := superpose eq115 eq28
  have eq208 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (((X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ (X0 ◇ X1))))))) := superpose eq115 eq178
  have eq209 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (((X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))))) := superpose eq115 eq208
  have eq265 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X1 ◇ (((X0 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X1))) := superpose eq7 eq115
  have eq311 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3)))) ◇ (X2 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3))))))) := superpose eq265 eq191
  have eq316 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))) := superpose eq7 eq311
  have eq317 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))) := superpose eq115 eq316
  have eq322 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))))) := superpose eq317 eq209
  have eq324 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X2)) = X0 := superpose eq317 eq174
  have eq339 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) := superpose eq317 eq322
  have eq340 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ X1)) := superpose eq324 eq339
  have eq352 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((((X0 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X4)) ◇ (X4 ◇ X4)))) = X2 := superpose eq340 eq19
  have eq427 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ (X4 ◇ X4))) = X2 := superpose eq340 eq352
  have eq442 (X0 X3 : G) : X0 = X3 := superpose eq7 eq427
  have eq469 (X0 : G) : sK0 ≠ X0 := superpose eq442 eq8
  subsumption eq469 eq442


@[equational_result]
theorem Equation11105_implies_Equation2 (G : Type*) [Magma G] (h : Equation11105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq109 eq35


@[equational_result]
theorem Equation11107_implies_Equation2 (G : Type*) [Magma G] (h : Equation11107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X5 ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ ((X4 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X5)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1))) = X4 := superpose eq16 eq11
  have eq24 (X1 X4 : G) : (X1 ◇ X1) = X4 := superpose eq16 eq21
  have eq25 (X0 X2 : G) : X0 = X2 := superpose eq24 eq24
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq34 eq25


@[equational_result]
theorem Equation11108_implies_Equation2 (G : Type*) [Magma G] (h : Equation11108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq52 eq13


@[equational_result]
theorem Equation11109_implies_Equation2 (G : Type*) [Magma G] (h : Equation11109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X5 ◇ X5))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq103 eq35


@[equational_result]
theorem Equation11110_implies_Equation2 (G : Type*) [Magma G] (h : Equation11110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation11112_implies_Equation2 (G : Type*) [Magma G] (h : Equation11112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) = (X0 ◇ (((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))))) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq7 eq10
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X3) = (X1 ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) ◇ (((X0 ◇ (X2 ◇ X0)) ◇ X3) ◇ X1))) := superpose eq10 eq7
  have eq31 (X0 X1 X3 X4 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X3)) ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X0)) = X3 := superpose eq11 eq10
  have eq33 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X2))) = X0 := superpose eq11 eq7
  have eq38 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X1))) := superpose eq7 eq33
  have eq189 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq38
  have eq266 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = ((((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq31 eq38
  have eq288 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ X0) := superpose eq11 eq189
  have eq309 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ X0))) ◇ X0)) := superpose eq189 eq10
  have eq319 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq189 eq33
  have eq467 (X0 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq288 eq266
  have eq541 (X0 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq189 eq467
  have eq567 (X0 X1 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq288 eq319
  have eq568 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq567 eq541
  have eq569 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq568 eq567
  have eq574 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq569 eq189
  have eq581 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ X0))) ◇ X0)) := superpose eq569 eq309
  have eq685 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0))))) ◇ X0)) := superpose eq574 eq16
  have eq690 (X0 X1 X3 : G) : (X0 ◇ X3) = (X1 ◇ (((X0 ◇ X3) ◇ X0) ◇ ((X0 ◇ X3) ◇ X1))) := superpose eq574 eq22
  have eq765 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq574 eq685
  have eq766 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq574 eq765
  have eq870 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq574 eq581
  have eq871 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := superpose eq569 eq870
  have eq872 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq569 eq871
  have eq873 (X0 X1 X3 : G) : (X0 ◇ X3) = (X1 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X1))) := superpose eq872 eq690
  have eq895 (X0 X1 X3 : G) : (X0 ◇ X3) = (X1 ◇ ((X0 ◇ X3) ◇ X1)) := superpose eq872 eq873
  have eq896 (X0 X1 X3 : G) : (X0 ◇ X3) = (X1 ◇ X1) := superpose eq872 eq895
  have eq1271 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq766 eq896
  have eq1279 (X0 X1 : G) : X0 = X1 := superpose eq766 eq1271
  have eq1318 (X0 : G) : sK0 ≠ X0 := superpose eq1279 eq8
  subsumption eq1318 eq1279


@[equational_result]
theorem Equation11113_implies_Equation2 (G : Type*) [Magma G] (h : Equation11113 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq12
  have eq30 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ (X0 ◇ X2)) := superpose eq16 eq10
  have eq37 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq16 eq30
  have eq38 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ X0) := superpose eq37 eq12
  have eq40 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq37 eq38
  have eq44 (X0 X1 : G) : X0 = X1 := superpose eq37 eq40
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq54 eq44


@[equational_result]
theorem Equation11114_implies_Equation2 (G : Type*) [Magma G] (h : Equation11114 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X4))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq12
  have eq31 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ (X0 ◇ X2)) := superpose eq16 eq10
  have eq38 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq16 eq31
  have eq39 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ X2) := superpose eq38 eq12
  have eq41 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq38 eq39
  have eq44 (X0 X1 : G) : X0 = X1 := superpose eq38 eq41
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq54 eq44


@[equational_result]
theorem Equation11117_implies_Equation2 (G : Type*) [Magma G] (h : Equation11117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X3)) ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (((X3 ◇ (X4 ◇ X3)) ◇ (X3 ◇ X4)) ◇ X0)))) ◇ X2)) ◇ X3)) = X2 := superpose eq10 eq10
  have eq19 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (((X2 ◇ (X3 ◇ X2)) ◇ (X2 ◇ X3)) ◇ X0))))) = X2 := superpose eq10 eq7
  have eq53 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0)) ◇ X0) = X1 := superpose eq7 eq19
  have eq56 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2)) ◇ X0) = X1 := superpose eq19 eq19
  have eq65 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X2)) ◇ X3)) = X2 := superpose eq56 eq13
  have eq66 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X2 := superpose eq56 eq19
  have eq75 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq56 eq53
  have eq111 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq75 eq75
  have eq153 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0)) := superpose eq65 eq75
  have eq196 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq75 eq111
  have eq307 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq196 eq66
  have eq329 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq111 eq307
  have eq331 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X0 ◇ X1) := superpose eq329 eq153
  have eq447 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq196 eq331
  have eq683 (X0 X2 : G) : X0 = X2 := superpose eq196 eq447
  have eq1002 (X0 : G) : sK0 ≠ X0 := superpose eq683 eq8
  subsumption eq1002 eq683


@[equational_result]
theorem Equation11118_implies_Equation2 (G : Type*) [Magma G] (h : Equation11118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation11121_implies_Equation2 (G : Type*) [Magma G] (h : Equation11121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (((((X0 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X0) ◇ (X4 ◇ X4)) ◇ X2)) ◇ ((X0 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X3)))) = X2 := superpose eq7 eq11
  have eq41 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq20
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq7 eq41
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq133 eq42


@[equational_result]
theorem Equation11122_implies_Equation2 (G : Type*) [Magma G] (h : Equation11122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation11124_implies_Equation2 (G : Type*) [Magma G] (h : Equation11124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq39 eq17


@[equational_result]
theorem Equation11125_implies_Equation2 (G : Type*) [Magma G] (h : Equation11125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq64 eq13


@[equational_result]
theorem Equation11126_implies_Equation2 (G : Type*) [Magma G] (h : Equation11126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X2 ◇ X2) = (X1 ◇ (X0 ◇ (X4 ◇ X4))) := superpose eq7 eq7
  have eq20 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq52 (X0 X3 : G) : X0 = X3 := superpose eq7 eq20
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq132 eq52


@[equational_result]
theorem Equation11127_implies_Equation2 (G : Type*) [Magma G] (h : Equation11127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation11129_implies_Equation2 (G : Type*) [Magma G] (h : Equation11129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ ((X2 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X2 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) = X2 := superpose eq10 eq7
  have eq20 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X3 ◇ X2)) ◇ (X0 ◇ X2)))) ◇ ((X4 ◇ X1) ◇ (X4 ◇ ((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X3 ◇ X2)) ◇ (X0 ◇ X2))))))) = X4 := superpose eq7 eq9
  have eq29 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq9
  have eq31 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X3)))) = (X0 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X3)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X3)))) ◇ X0))) := superpose eq9 eq10
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = (((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ ((((X0 ◇ X2) ◇ X2) ◇ X1) ◇ X1)) := superpose eq29 eq29
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) ◇ X0)) := superpose eq29 eq9
  have eq53 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X2 ◇ X0) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1)))) = X2 := superpose eq29 eq7
  have eq141 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))))) = X2 := superpose eq10 eq53
  have eq149 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X1) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X0) ◇ X0)) := superpose eq29 eq53
  have eq640 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) = ((X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))))))) := superpose eq29 eq141
  have eq1113 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq31
  have eq1150 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq7 eq1113
  have eq1153 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = X2 := superpose eq1113 eq20
  have eq1156 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0)) := superpose eq1113 eq37
  have eq1255 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq1150 eq16
  have eq1275 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq1255 eq1156
  have eq1363 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq1275 eq7
  have eq1369 (X0 : G) : ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq1275 eq29
  have eq1373 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))))) := superpose eq1275 eq141
  have eq1374 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) ◇ X0)) := superpose eq1275 eq149
  have eq1399 (X0 : G) : ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = X0 := superpose eq1255 eq1369
  have eq1401 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq1399 eq1374
  have eq1402 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq1255 eq1401
  have eq1403 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq1402 eq1363
  have eq1412 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq1403 eq1150
  have eq1429 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq1412
  have eq1431 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) = X2 := superpose eq1429 eq1153
  have eq1439 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq1429 eq1275
  have eq1442 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))))) = X0 := superpose eq1429 eq1373
  have eq1445 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = X0 := superpose eq1439 eq1442
  have eq1446 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq1439 eq1445
  have eq1447 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1429 eq1446
  have eq1459 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq1447 eq1431
  have eq1468 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) = ((X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) := superpose eq1459 eq640
  have eq1766 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq1447 eq1468
  have eq1767 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq1459 eq1766
  have eq1768 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq1459 eq1767
  have eq1769 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq1768
  have eq1770 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq1769 eq50
  have eq1773 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq1769 eq7
  have eq2021 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq1769 eq1770
  have eq2024 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq1773 eq2021
  have eq2045 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1447 eq2024
  have eq2051 (X0 X1 : G) : X0 = X1 := superpose eq1773 eq2045
  have eq2053 (X0 : G) : sK0 ≠ X0 := superpose eq2051 eq8
  subsumption eq2053 eq2051


@[equational_result]
theorem Equation11131_implies_Equation2 (G : Type*) [Magma G] (h : Equation11131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ X4))) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq7
  have eq37 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq119 eq37


@[equational_result]
theorem Equation11133_implies_Equation2 (G : Type*) [Magma G] (h : Equation11133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq27 eq12


@[equational_result]
theorem Equation11134_implies_Equation2 (G : Type*) [Magma G] (h : Equation11134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X1))))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ (X3 ◇ X1)) ◇ (X1 ◇ X3)) ◇ X1)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq36 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ ((((X2 ◇ X1) ◇ (X3 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2))) ◇ X0)) = X1 := superpose eq11 eq10
  have eq78 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X0 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ (X4 ◇ X3)) ◇ X4)) ◇ X2) ◇ X4)) ◇ X0) ◇ ((X5 ◇ X1) ◇ (((X1 ◇ (((X0 ◇ (((X2 ◇ (X3 ◇ X4)) ◇ (X4 ◇ X3)) ◇ X4)) ◇ X2) ◇ X4)) ◇ X0) ◇ X4))) = X5 := superpose eq11 eq9
  have eq79 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq9 eq10
  have eq93 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X1 := superpose eq79 eq36
  have eq96 (X1 X4 X5 : G) : (X1 ◇ ((X5 ◇ X1) ◇ (X1 ◇ X4))) = X5 := superpose eq93 eq78
  have eq152 (X1 X5 : G) : (X1 ◇ X5) = X5 := superpose eq93 eq96
  have eq154 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq152 eq93
  have eq155 (X0 X3 : G) : X0 = X3 := superpose eq154 eq154
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq155 eq8
  subsumption eq160 eq155


@[equational_result]
theorem Equation11135_implies_Equation2 (G : Type*) [Magma G] (h : Equation11135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X4))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X4)) = X1 := superpose eq7 eq11
  have eq23 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq14 eq7
  have eq24 (X0 X1 X2 X4 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X4))) = X1 := superpose eq23 eq10
  have eq29 (X1 X2 X4 : G) : (X2 ◇ (X2 ◇ X4)) = X1 := superpose eq23 eq24
  have eq30 (X1 X2 X4 : G) : (X2 ◇ X4) = X1 := superpose eq23 eq29
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq30 eq30
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq36 eq31


@[equational_result]
theorem Equation11137_implies_Equation2 (G : Type*) [Magma G] (h : Equation11137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq9
  have eq18 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq15 eq7
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation11139_implies_Equation2 (G : Type*) [Magma G] (h : Equation11139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X4))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq11 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq45 eq36


@[equational_result]
theorem Equation11141_implies_Equation2 (G : Type*) [Magma G] (h : Equation11141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X4 ◇ (X1 ◇ X2)))) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq49 eq18


@[equational_result]
theorem Equation11142_implies_Equation2 (G : Type*) [Magma G] (h : Equation11142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq52 eq13


@[equational_result]
theorem Equation11143_implies_Equation2 (G : Type*) [Magma G] (h : Equation11143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X4 ◇ X4))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation11144_implies_Equation2 (G : Type*) [Magma G] (h : Equation11144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation11146_implies_Equation2 (G : Type*) [Magma G] (h : Equation11146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X0)) := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X1))) = X2 := superpose eq9 eq7
  have eq34 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ X0) := superpose eq10 eq7
  have eq36 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose eq10 eq9
  have eq48 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq34 eq9
  have eq74 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq48 eq36
  have eq78 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X0)) := superpose eq74 eq12
  have eq99 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X2 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X3 ◇ X0)) := superpose eq74 eq78
  have eq100 (X0 X1 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X3 ◇ X0)) := superpose eq74 eq99
  have eq102 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq100 eq16
  have eq169 (X0 X3 : G) : X0 = X3 := superpose eq102 eq102
  have eq251 (X0 : G) : sK0 ≠ X0 := superpose eq169 eq8
  subsumption eq251 eq169


@[equational_result]
theorem Equation11147_implies_Equation2 (G : Type*) [Magma G] (h : Equation11147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X3))) = X1 := superpose eq11 eq7
  have eq23 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X3 ◇ (X1 ◇ X1)))) = X3 := superpose eq11 eq7
  have eq24 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) ◇ (X0 ◇ X1))) = X1 := superpose eq11 eq7
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X1 := superpose eq22 eq24
  have eq32 (X1 X2 X3 : G) : (X2 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X1)))) = X3 := superpose eq31 eq23
  have eq33 (X1 X2 X3 : G) : (X2 ◇ X1) = X3 := superpose eq31 eq32
  have eq48 (X0 X3 : G) : X0 = X3 := superpose eq7 eq33
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq116 eq48


@[equational_result]
theorem Equation11148_implies_Equation2 (G : Type*) [Magma G] (h : Equation11148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X4))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation11150_implies_Equation2 (G : Type*) [Magma G] (h : Equation11150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = X0 := superpose eq9 eq7
  have eq21 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq15 eq9
  have eq22 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X0 := superpose eq21 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X1)) = X0 := superpose eq21 eq22
  have eq28 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq25 eq25
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq25 eq28
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq46 eq36


@[equational_result]
theorem Equation11151_implies_Equation2 (G : Type*) [Magma G] (h : Equation11151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ (X3 ◇ X3)) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ (X3 ◇ X3)) ◇ (X1 ◇ X3)))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ X2)) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ X2)))) ◇ X0) = X3 := superpose eq9 eq7
  have eq21 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq14 eq9
  have eq41 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose eq21 eq21
  have eq82 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq41 eq7
  have eq121 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq41 eq82
  have eq135 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq121 eq41
  have eq151 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq121 eq82
  have eq184 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq121 eq135
  have eq228 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq184 eq151
  have eq323 (X0 X2 : G) : X0 = X2 := superpose eq228 eq228
  have eq351 (X0 : G) : sK0 ≠ X0 := superpose eq323 eq8
  subsumption eq351 eq323


@[equational_result]
theorem Equation11152_implies_Equation2 (G : Type*) [Magma G] (h : Equation11152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X3))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq11
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation11155_implies_Equation2 (G : Type*) [Magma G] (h : Equation11155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X3 ◇ X3)) ◇ (X3 ◇ X3)))) = X2 := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq15
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq34 eq16


@[equational_result]
theorem Equation11156_implies_Equation2 (G : Type*) [Magma G] (h : Equation11156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation11158_implies_Equation2 (G : Type*) [Magma G] (h : Equation11158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X0) = X2 := superpose eq7 eq7
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq58 eq39


@[equational_result]
theorem Equation11159_implies_Equation2 (G : Type*) [Magma G] (h : Equation11159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq41 eq14


@[equational_result]
theorem Equation11160_implies_Equation2 (G : Type*) [Magma G] (h : Equation11160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq49 eq17


@[equational_result]
theorem Equation11161_implies_Equation2 (G : Type*) [Magma G] (h : Equation11161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation11163_implies_Equation2 (G : Type*) [Magma G] (h : Equation11163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq10 eq10
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq116 eq41


@[equational_result]
theorem Equation11164_implies_Equation2 (G : Type*) [Magma G] (h : Equation11164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X4 : G) : (X4 ◇ X1) = X0 := superpose eq7 eq12
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq126 eq53


@[equational_result]
theorem Equation11165_implies_Equation2 (G : Type*) [Magma G] (h : Equation11165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq18 (X0 X1 X4 : G) : (X4 ◇ X1) = X0 := superpose eq7 eq12
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq114 eq51


@[equational_result]
theorem Equation11166_implies_Equation2 (G : Type*) [Magma G] (h : Equation11166 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X6))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation11168_implies_Equation2 (G : Type*) [Magma G] (h : Equation11168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation11169_implies_Equation2 (G : Type*) [Magma G] (h : Equation11169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (((X0 ◇ (X3 ◇ X4)) ◇ (X1 ◇ X3)) ◇ X5)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X0)) = X2 := superpose eq14 eq11
  have eq34 (X0 X5 : G) : X0 = X5 := superpose eq21 eq21
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq54 eq34


@[equational_result]
theorem Equation11170_implies_Equation2 (G : Type*) [Magma G] (h : Equation11170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X4)))) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq48 eq18


@[equational_result]
theorem Equation11171_implies_Equation2 (G : Type*) [Magma G] (h : Equation11171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X6))) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq59 eq19


@[equational_result]
theorem Equation11173_implies_Equation2 (G : Type*) [Magma G] (h : Equation11173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ ((X4 ◇ (X3 ◇ X5)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq9
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3)) ◇ X3) = X4 := superpose eq17 eq11
  have eq28 (X1 X3 X4 : G) : (X1 ◇ X3) = X4 := superpose eq17 eq24
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq9 eq28
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq40 eq29


@[equational_result]
theorem Equation11174_implies_Equation2 (G : Type*) [Magma G] (h : Equation11174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ (X0 ◇ (X3 ◇ X4))))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq9
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq10
  have eq23 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq45 eq23


@[equational_result]
theorem Equation11175_implies_Equation2 (G : Type*) [Magma G] (h : Equation11175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq24 eq13


@[equational_result]
theorem Equation11176_implies_Equation2 (G : Type*) [Magma G] (h : Equation11176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X6 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ X6))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation11178_implies_Equation2 (G : Type*) [Magma G] (h : Equation11178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ ((X4 ◇ X2) ◇ X1))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq43 eq19


@[equational_result]
theorem Equation11179_implies_Equation2 (G : Type*) [Magma G] (h : Equation11179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq64 eq13


@[equational_result]
theorem Equation11180_implies_Equation2 (G : Type*) [Magma G] (h : Equation11180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ ((X4 ◇ X4) ◇ (X4 ◇ X4)))) = X2 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq50 eq30


@[equational_result]
theorem Equation11181_implies_Equation2 (G : Type*) [Magma G] (h : Equation11181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation11183_implies_Equation2 (G : Type*) [Magma G] (h : Equation11183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : (X1 ◇ (X0 ◇ (X6 ◇ X1))) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation11184_implies_Equation2 (G : Type*) [Magma G] (h : Equation11184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation11185_implies_Equation2 (G : Type*) [Magma G] (h : Equation11185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation11186_implies_Equation2 (G : Type*) [Magma G] (h : Equation11186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation11187_implies_Equation2 (G : Type*) [Magma G] (h : Equation11187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation11190_implies_Equation2 (G : Type*) [Magma G] (h : Equation11190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq7 eq17
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq69 eq23


@[equational_result]
theorem Equation11193_implies_Equation2 (G : Type*) [Magma G] (h : Equation11193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq122 eq41


@[equational_result]
theorem Equation11195_implies_Equation2 (G : Type*) [Magma G] (h : Equation11195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq9
  have eq22 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq12
  have eq62 (X0 X2 : G) : X0 = X2 := superpose eq22 eq22
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq149 eq62


@[equational_result]
theorem Equation11196_implies_Equation2 (G : Type*) [Magma G] (h : Equation11196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0)) = X2 := superpose eq10 eq7
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq14
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq7 eq48
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq154 eq55


@[equational_result]
theorem Equation11197_implies_Equation2 (G : Type*) [Magma G] (h : Equation11197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation11200_implies_Equation2 (G : Type*) [Magma G] (h : Equation11200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq7 eq16
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq105 eq36


@[equational_result]
theorem Equation11203_implies_Equation2 (G : Type*) [Magma G] (h : Equation11203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq124 eq33


@[equational_result]
theorem Equation11207_implies_Equation2 (G : Type*) [Magma G] (h : Equation11207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation11209_implies_Equation2 (G : Type*) [Magma G] (h : Equation11209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X1))) = X3 := superpose eq7 eq9
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq12 eq12
  have eq90 (X0 X3 : G) : X0 = X3 := superpose eq37 eq37
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq132 eq90


@[equational_result]
theorem Equation11210_implies_Equation2 (G : Type*) [Magma G] (h : Equation11210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq41 eq15


@[equational_result]
theorem Equation11211_implies_Equation2 (G : Type*) [Magma G] (h : Equation11211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq9
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq12 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq44 eq39


@[equational_result]
theorem Equation11213_implies_Equation2 (G : Type*) [Magma G] (h : Equation11213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq51 eq16


@[equational_result]
theorem Equation11215_implies_Equation2 (G : Type*) [Magma G] (h : Equation11215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X5))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq51 eq19


@[equational_result]
theorem Equation11219_implies_Equation2 (G : Type*) [Magma G] (h : Equation11219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq124 eq41


@[equational_result]
theorem Equation11221_implies_Equation2 (G : Type*) [Magma G] (h : Equation11221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X5 ◇ X1))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq70 eq19


@[equational_result]
theorem Equation11222_implies_Equation2 (G : Type*) [Magma G] (h : Equation11222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq60 eq15


@[equational_result]
theorem Equation11223_implies_Equation2 (G : Type*) [Magma G] (h : Equation11223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq50 eq12


@[equational_result]
theorem Equation11224_implies_Equation2 (G : Type*) [Magma G] (h : Equation11224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation11227_implies_Equation2 (G : Type*) [Magma G] (h : Equation11227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq127 eq32


@[equational_result]
theorem Equation11230_implies_Equation2 (G : Type*) [Magma G] (h : Equation11230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq145 eq45


@[equational_result]
theorem Equation11232_implies_Equation2 (G : Type*) [Magma G] (h : Equation11232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) = (X1 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X3)) ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X3) ◇ (X4 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1))))) := superpose eq7 eq9
  have eq19 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X3)) ◇ (X4 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)))) = (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) := superpose eq7 eq9
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ (X3 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X3 ◇ X0)) ◇ X4)) ◇ (X5 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X0)))) = (((X0 ◇ X1) ◇ (X3 ◇ X0)) ◇ ((((X0 ◇ X1) ◇ (X3 ◇ X0)) ◇ X4) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)))) := superpose eq9 eq9
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X1)) = X0 := superpose eq7 eq9
  have eq45 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X0)) ◇ X2) = (((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)) ◇ X0) ◇ X2)) := superpose eq10 eq10
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X3) ◇ (X5 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X3)) ◇ (X4 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0))))) ◇ X1)) := superpose eq9 eq10
  have eq58 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X3) ◇ (X4 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1))))) = (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) := superpose eq45 eq12
  have eq59 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X3) ◇ X0))) = X3 := superpose eq45 eq10
  have eq60 (X0 X1 X2 X3 X5 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ X3) ◇ (X5 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1)) := superpose eq7 eq47
  have eq61 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X0))) := superpose eq60 eq58
  have eq63 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X3)) ◇ (X4 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)))) = (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X0))) := superpose eq61 eq19
  have eq67 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X0)))) = X3 := superpose eq61 eq59
  have eq117 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = (X0 ◇ (X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)))) := superpose eq67 eq23
  have eq136 (X0 X1 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ (X3 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X3 ◇ X0)) ◇ X4)) ◇ (X5 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X0)))) = (((X0 ◇ X1) ◇ (X3 ◇ X0)) ◇ X1) := superpose eq117 eq20
  have eq138 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X0))) = (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq136 eq63
  have eq143 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0))) = X3 := superpose eq138 eq67
  have eq210 (X0 X4 : G) : X0 = X4 := superpose eq143 eq143
  have eq251 (X0 : G) : sK0 ≠ X0 := superpose eq210 eq8
  subsumption eq251 eq210


@[equational_result]
theorem Equation11233_implies_Equation2 (G : Type*) [Magma G] (h : Equation11233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) = (X1 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X2)) = X0 := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) ◇ (X3 ◇ X3))) := superpose eq9 eq7
  have eq36 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X2 ◇ X2)) = X1 := superpose eq9 eq18
  have eq39 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X3 ◇ X3))) = (X0 ◇ (X2 ◇ X2)) := superpose eq18 eq9
  have eq46 (X1 X2 : G) : (X1 ◇ (X2 ◇ X2)) = X1 := superpose eq18 eq36
  have eq51 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq46 eq7
  have eq55 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3))) := superpose eq46 eq22
  have eq69 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq46 eq55
  have eq73 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X3 ◇ X3))) = X0 := superpose eq46 eq39
  have eq74 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = X0 := superpose eq46 eq73
  have eq75 (X0 X1 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose eq69 eq74
  have eq76 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq51 eq75
  have eq77 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq76 eq46
  have eq81 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq77 eq51
  have eq87 (X0 X2 : G) : X0 = X2 := superpose eq81 eq81
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq89 eq87


@[equational_result]
theorem Equation11234_implies_Equation2 (G : Type*) [Magma G] (h : Equation11234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation11237_implies_Equation2 (G : Type*) [Magma G] (h : Equation11237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation11239_implies_Equation2 (G : Type*) [Magma G] (h : Equation11239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation11240_implies_Equation2 (G : Type*) [Magma G] (h : Equation11240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11242_implies_Equation2 (G : Type*) [Magma G] (h : Equation11242 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11243_implies_Equation2 (G : Type*) [Magma G] (h : Equation11243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation11244_implies_Equation2 (G : Type*) [Magma G] (h : Equation11244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11246_implies_Equation2 (G : Type*) [Magma G] (h : Equation11246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X3 ◇ X1))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X1))) = X3 := superpose eq7 eq9
  have eq37 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) = X2 := superpose eq11 eq11
  have eq52 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq37 eq7
  have eq61 (X0 X3 : G) : X0 = X3 := superpose eq9 eq52
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq79 eq61


@[equational_result]
theorem Equation11248_implies_Equation2 (G : Type*) [Magma G] (h : Equation11248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq51 eq30


@[equational_result]
theorem Equation11250_implies_Equation2 (G : Type*) [Magma G] (h : Equation11250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11251_implies_Equation2 (G : Type*) [Magma G] (h : Equation11251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation11252_implies_Equation2 (G : Type*) [Magma G] (h : Equation11252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11254_implies_Equation2 (G : Type*) [Magma G] (h : Equation11254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11255_implies_Equation2 (G : Type*) [Magma G] (h : Equation11255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11256_implies_Equation2 (G : Type*) [Magma G] (h : Equation11256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11258_implies_Equation2 (G : Type*) [Magma G] (h : Equation11258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11259_implies_Equation2 (G : Type*) [Magma G] (h : Equation11259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11260_implies_Equation2 (G : Type*) [Magma G] (h : Equation11260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11261_implies_Equation2 (G : Type*) [Magma G] (h : Equation11261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11263_implies_Equation2 (G : Type*) [Magma G] (h : Equation11263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X2)) = (X1 ◇ ((X1 ◇ X0) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) ◇ ((((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X1)) ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1))) = X1 := superpose eq10 eq7
  have eq37 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq14 eq10
  have eq41 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq14 eq10
  have eq42 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq14 eq7
  have eq45 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) = X1 := superpose eq14 eq7
  have eq66 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq11
  have eq68 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = (((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq11 eq10
  have eq74 (X0 X1 X2 X3 X4 X5 : G) : ((((((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)) ◇ X2) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)))) ◇ X0) = (X5 ◇ ((X5 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0))) ◇ (((((((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)) ◇ X2) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)))) ◇ X0) ◇ X5))) := superpose eq11 eq9
  have eq99 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq66 eq10
  have eq116 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq99 eq41
  have eq117 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq116
  have eq119 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq117 eq37
  have eq123 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq117 eq42
  have eq144 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) = X1 := superpose eq117 eq45
  have eq147 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq117 eq119
  have eq149 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq147 eq99
  have eq158 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := superpose eq147 eq123
  have eq159 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq158 eq149
  have eq192 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := superpose eq147 eq144
  have eq238 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq68 eq68
  have eq240 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq68
  have eq249 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose eq68 eq11
  have eq250 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq68 eq9
  have eq266 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq147 eq250
  have eq432 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)))) := superpose eq10 eq192
  have eq463 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq240 eq432
  have eq464 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq463 eq266
  have eq466 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose eq464 eq249
  have eq538 (X0 X1 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0))) := superpose eq16 eq240
  have eq580 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq240 eq538
  have eq583 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq580 eq466
  have eq752 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0))) := superpose eq583 eq192
  have eq795 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq159 eq752
  have eq796 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq147 eq795
  have eq797 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq147 eq796
  have eq798 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq797 eq238
  have eq819 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq797 eq798
  have eq820 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := superpose eq819 eq10
  have eq861 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq819 eq463
  have eq957 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq192 eq861
  have eq958 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq957 eq820
  have eq990 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq147 eq958
  have eq992 (X0 X1 X2 X5 : G) : (X5 ◇ ((X5 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0))) ◇ (X0 ◇ X5))) = X0 := superpose eq990 eq74
  have eq1127 (X0 X5 : G) : (X5 ◇ (X0 ◇ X5)) = X0 := superpose eq990 eq992
  have eq1128 (X0 X5 : G) : (X5 ◇ X5) = X0 := superpose eq990 eq1127
  have eq1638 (X0 X2 : G) : X0 = X2 := superpose eq1128 eq1128
  have eq1651 (X0 : G) : sK0 ≠ X0 := superpose eq1638 eq8
  subsumption eq1651 eq1638


@[equational_result]
theorem Equation11265_implies_Equation2 (G : Type*) [Magma G] (h : Equation11265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq120 eq39


@[equational_result]
theorem Equation11267_implies_Equation2 (G : Type*) [Magma G] (h : Equation11267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq20 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation11269_implies_Equation2 (G : Type*) [Magma G] (h : Equation11269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (X1 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ X4))) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq169 eq55


@[equational_result]
theorem Equation11273_implies_Equation2 (G : Type*) [Magma G] (h : Equation11273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq185 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq185 eq61


@[equational_result]
theorem Equation11275_implies_Equation2 (G : Type*) [Magma G] (h : Equation11275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (X3 ◇ X1) = (X1 ◇ (X0 ◇ (X4 ◇ X1))) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq75 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq176 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq176 eq75


@[equational_result]
theorem Equation11276_implies_Equation2 (G : Type*) [Magma G] (h : Equation11276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq65 eq13


@[equational_result]
theorem Equation11277_implies_Equation2 (G : Type*) [Magma G] (h : Equation11277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X3))) = X0 := superpose eq11 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq11 eq13
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11278_implies_Equation2 (G : Type*) [Magma G] (h : Equation11278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation11282_implies_Equation2 (G : Type*) [Magma G] (h : Equation11282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X3 ◇ X4))) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq10 eq7
  have eq25 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X0 := superpose eq19 eq7
  have eq34 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq19 eq25
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq19 eq34
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq42 eq40


@[equational_result]
theorem Equation11284_implies_Equation2 (G : Type*) [Magma G] (h : Equation11284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11285_implies_Equation2 (G : Type*) [Magma G] (h : Equation11285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11286_implies_Equation2 (G : Type*) [Magma G] (h : Equation11286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11288_implies_Equation2 (G : Type*) [Magma G] (h : Equation11288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation11289_implies_Equation2 (G : Type*) [Magma G] (h : Equation11289 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11290_implies_Equation2 (G : Type*) [Magma G] (h : Equation11290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11292_implies_Equation2 (G : Type*) [Magma G] (h : Equation11292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11293_implies_Equation2 (G : Type*) [Magma G] (h : Equation11293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11294_implies_Equation2 (G : Type*) [Magma G] (h : Equation11294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11295_implies_Equation2 (G : Type*) [Magma G] (h : Equation11295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11298_implies_Equation2 (G : Type*) [Magma G] (h : Equation11298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ X3)) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ X3)))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X2 ◇ X2)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X1 ◇ (X0 ◇ X0)) ◇ (((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ X3)) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ X3)))) := superpose eq7 eq10
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3)))) = ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) := superpose eq10 eq10
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X2) = ((X0 ◇ X1) ◇ (X3 ◇ X3)) := superpose eq10 eq10
  have eq16 (X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X3 ◇ X3))) = X2 := superpose eq13 eq9
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) = (X2 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3))) := superpose eq10 eq16
  have eq20 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq10 eq16
  have eq22 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (((X2 ◇ (X0 ◇ (X3 ◇ X3))) ◇ (X3 ◇ X3)) ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X3))) ◇ (X3 ◇ X3)))) ◇ X0)) = X2 := superpose eq16 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2))) := superpose eq7 eq20
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq25 eq11
  have eq47 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq46 eq25
  have eq48 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq46 eq7
  have eq51 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X3))) ◇ (X3 ◇ X3))) ◇ X0)) = X2 := superpose eq47 eq22
  have eq53 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ X3)) := superpose eq47 eq17
  have eq56 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := superpose eq47 eq12
  have eq60 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X3))) = ((X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X3 ◇ X3)) := superpose eq47 eq56
  have eq61 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := superpose eq47 eq60
  have eq63 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X3) ◇ X3)))) ◇ X0)) = X2 := superpose eq61 eq51
  have eq65 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))) := superpose eq61 eq53
  have eq67 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq48 eq20
  have eq74 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X3))) = ((X2 ◇ (X0 ◇ X1)) ◇ X3) := superpose eq67 eq61
  have eq76 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) ◇ X0)) = X2 := superpose eq67 eq63
  have eq80 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X3)) ◇ X0)))) = X2 := superpose eq74 eq76
  have eq81 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X0)))))) = X2 := superpose eq74 eq80
  have eq82 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X2 := superpose eq48 eq81
  have eq83 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq67 eq82
  have eq84 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X3)) = X0 := superpose eq83 eq65
  have eq92 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq84 eq83
  have eq132 (X0 X2 : G) : X0 = X2 := superpose eq92 eq92
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq132 eq8
  subsumption eq166 eq132


@[equational_result]
theorem Equation11299_implies_Equation2 (G : Type*) [Magma G] (h : Equation11299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9
  have eq21 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq15 eq10
  have eq29 (X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = X3 := superpose eq15 eq21
  have eq30 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq15 eq29
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq30 eq30
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq41 eq39


@[equational_result]
theorem Equation11301_implies_Equation2 (G : Type*) [Magma G] (h : Equation11301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11302_implies_Equation2 (G : Type*) [Magma G] (h : Equation11302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11303_implies_Equation2 (G : Type*) [Magma G] (h : Equation11303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11305_implies_Equation2 (G : Type*) [Magma G] (h : Equation11305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11306_implies_Equation2 (G : Type*) [Magma G] (h : Equation11306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation11307_implies_Equation2 (G : Type*) [Magma G] (h : Equation11307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11309_implies_Equation2 (G : Type*) [Magma G] (h : Equation11309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11310_implies_Equation2 (G : Type*) [Magma G] (h : Equation11310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11311_implies_Equation2 (G : Type*) [Magma G] (h : Equation11311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11312_implies_Equation2 (G : Type*) [Magma G] (h : Equation11312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11314_implies_Equation2 (G : Type*) [Magma G] (h : Equation11314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ (X4 ◇ X1))) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq10 eq10
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq100 eq35


@[equational_result]
theorem Equation11315_implies_Equation2 (G : Type*) [Magma G] (h : Equation11315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X5 ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq9
  have eq23 (X1 X4 : G) : (X1 ◇ X1) = X4 := superpose eq13 eq10
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq23 eq23
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq41 eq24


@[equational_result]
theorem Equation11316_implies_Equation2 (G : Type*) [Magma G] (h : Equation11316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (X1 ◇ (X0 ◇ (X4 ◇ (X0 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq10
  have eq26 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq13 eq10
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq7 eq26
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq40 eq27


@[equational_result]
theorem Equation11317_implies_Equation2 (G : Type*) [Magma G] (h : Equation11317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 X6 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X6))) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq119 eq36


@[equational_result]
theorem Equation11319_implies_Equation2 (G : Type*) [Magma G] (h : Equation11319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11320_implies_Equation2 (G : Type*) [Magma G] (h : Equation11320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11321_implies_Equation2 (G : Type*) [Magma G] (h : Equation11321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11322_implies_Equation2 (G : Type*) [Magma G] (h : Equation11322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11324_implies_Equation2 (G : Type*) [Magma G] (h : Equation11324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11325_implies_Equation2 (G : Type*) [Magma G] (h : Equation11325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11326_implies_Equation2 (G : Type*) [Magma G] (h : Equation11326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11327_implies_Equation2 (G : Type*) [Magma G] (h : Equation11327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11329_implies_Equation2 (G : Type*) [Magma G] (h : Equation11329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11330_implies_Equation2 (G : Type*) [Magma G] (h : Equation11330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11331_implies_Equation2 (G : Type*) [Magma G] (h : Equation11331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11332_implies_Equation2 (G : Type*) [Magma G] (h : Equation11332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11334_implies_Equation2 (G : Type*) [Magma G] (h : Equation11334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11335_implies_Equation2 (G : Type*) [Magma G] (h : Equation11335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11336_implies_Equation2 (G : Type*) [Magma G] (h : Equation11336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11337_implies_Equation2 (G : Type*) [Magma G] (h : Equation11337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11338_implies_Equation2 (G : Type*) [Magma G] (h : Equation11338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11340_implies_Equation2 (G : Type*) [Magma G] (h : Equation11340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) ◇ ((X3 ◇ (X2 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))))) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq9
  have eq33 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq14 eq7
  have eq39 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq14 eq7
  have eq46 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq10 eq11
  have eq56 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq46 eq33
  have eq61 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq46 eq39
  have eq66 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq14 eq56
  have eq72 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq14 eq61
  have eq87 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ X1) := superpose eq46 eq46
  have eq126 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq14 eq87
  have eq127 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq46 eq126
  have eq128 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq14 eq127
  have eq132 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq128 eq72
  have eq139 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq128 eq66
  have eq150 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq128 eq132
  have eq152 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq139 eq150
  have eq154 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq152 eq9
  have eq169 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq152 eq46
  have eq179 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq152 eq154
  have eq200 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq152 eq169
  have eq203 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq200 eq179
  have eq219 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq200 eq203
  have eq331 (X0 X2 : G) : X0 = X2 := superpose eq219 eq219
  have eq333 (X0 : G) : sK0 ≠ X0 := superpose eq331 eq8
  subsumption eq333 eq331


@[equational_result]
theorem Equation11341_implies_Equation2 (G : Type*) [Magma G] (h : Equation11341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X3 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) := superpose eq7 eq11
  have eq27 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq12
  have eq29 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X3)) ◇ X0)) = X3 := superpose eq27 eq10
  have eq33 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq27 eq29
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq33 eq33
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq36 eq34


@[equational_result]
theorem Equation11342_implies_Equation2 (G : Type*) [Magma G] (h : Equation11342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = (X4 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X3))) := superpose eq7 eq12
  have eq31 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq14
  have eq34 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq31 eq11
  have eq39 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq31 eq34
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq39 eq39
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq42 eq40


@[equational_result]
theorem Equation11344_implies_Equation2 (G : Type*) [Magma G] (h : Equation11344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq9
  have eq22 (X0 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq10
  have eq25 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq22 eq7
  have eq30 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq25 eq9
  have eq42 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq30
  have eq46 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq42 eq7
  have eq51 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq42 eq46
  have eq52 (X0 X2 : G) : X0 = X2 := superpose eq51 eq51
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq54 eq52


@[equational_result]
theorem Equation11346_implies_Equation2 (G : Type*) [Magma G] (h : Equation11346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq46 eq16


@[equational_result]
theorem Equation11348_implies_Equation2 (G : Type*) [Magma G] (h : Equation11348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq7 eq11
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq34 eq34
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq132 eq48


@[equational_result]
theorem Equation11349_implies_Equation2 (G : Type*) [Magma G] (h : Equation11349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq60 eq13


@[equational_result]
theorem Equation11350_implies_Equation2 (G : Type*) [Magma G] (h : Equation11350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation11352_implies_Equation2 (G : Type*) [Magma G] (h : Equation11352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq57 eq17


@[equational_result]
theorem Equation11353_implies_Equation2 (G : Type*) [Magma G] (h : Equation11353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq60 eq13


@[equational_result]
theorem Equation11354_implies_Equation2 (G : Type*) [Magma G] (h : Equation11354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation11355_implies_Equation2 (G : Type*) [Magma G] (h : Equation11355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation11357_implies_Equation2 (G : Type*) [Magma G] (h : Equation11357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 X4 : G) : ((X0 ◇ ((X3 ◇ X2) ◇ X2)) ◇ ((X4 ◇ (X3 ◇ X2)) ◇ (X3 ◇ X2))) = X2 := superpose eq10 eq10
  have eq17 (X0 X1 X3 : G) : (X3 ◇ X1) = (X1 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X1))) := superpose eq10 eq7
  have eq25 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = (((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X4 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) := superpose eq9 eq10
  have eq31 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq25 eq25
  have eq57 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq25 eq31
  have eq69 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) = X0 := superpose eq7 eq17
  have eq74 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) := superpose eq25 eq17
  have eq77 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X0 ◇ X2) ◇ X0) := superpose eq7 eq17
  have eq78 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ X2) := superpose eq10 eq17
  have eq86 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X1)) = (((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X4 ◇ X1) ◇ X1)) := superpose eq17 eq10
  have eq101 (X0 X2 X3 : G) : ((X0 ◇ ((X3 ◇ X2) ◇ X2)) ◇ ((X3 ◇ X2) ◇ X3)) = X2 := superpose eq77 eq12
  have eq109 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X4 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = (X1 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq77 eq29
  have eq112 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) = X0 := superpose eq77 eq69
  have eq133 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X1)) = (((X3 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq77 eq109
  have eq134 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X1)) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq77 eq133
  have eq141 (X0 X1 X3 X4 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ ((X4 ◇ X1) ◇ X1)) := superpose eq77 eq86
  have eq259 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X2)) = X3 := superpose eq78 eq101
  have eq296 (X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X1)) = X2 := superpose eq259 eq134
  have eq298 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ X1)) = X0 := superpose eq296 eq112
  have eq306 (X0 X1 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq298 eq141
  have eq307 (X1 : G) : ((X1 ◇ X1) ◇ X1) = X1 := superpose eq306 eq57
  have eq316 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq307 eq25
  have eq324 (X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X1))) = X1 := superpose eq316 eq74
  have eq330 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq316 eq324
  have eq333 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq330 eq316
  have eq334 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq333 eq77
  have eq351 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq333 eq334
  have eq352 (X0 X3 : G) : X0 = X3 := superpose eq351 eq351
  have eq360 (X0 : G) : sK0 ≠ X0 := superpose eq352 eq8
  subsumption eq360 eq352


@[equational_result]
theorem Equation11359_implies_Equation2 (G : Type*) [Magma G] (h : Equation11359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq129 eq45


@[equational_result]
theorem Equation11361_implies_Equation2 (G : Type*) [Magma G] (h : Equation11361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X0) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))))) := superpose eq10 eq10
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ X2)) := superpose eq10 eq10
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X3))) ◇ X3)) = X0 := superpose eq7 eq10
  have eq26 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X3)) ◇ X4)) ◇ (X4 ◇ X4)) ◇ (X0 ◇ (((X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X3)) ◇ X4)) ◇ (X4 ◇ X4)) ◇ ((X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X3)) ◇ X4)) ◇ (X4 ◇ X4))))) = X4 := superpose eq7 eq9
  have eq33 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X3) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)))) = (((X1 ◇ X0) ◇ (((X4 ◇ X3) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)))) ◇ ((X4 ◇ X3) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)))))) ◇ ((X5 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0))) ◇ (((X1 ◇ X0) ◇ (((X4 ◇ X3) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)))) ◇ ((X4 ◇ X3) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)))))) ◇ ((X1 ◇ X0) ◇ (((X4 ◇ X3) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)))) ◇ ((X4 ◇ X3) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0))))))))) := superpose eq9 eq9
  have eq48 (X0 X1 X2 X3 : G) : (X3 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1))) = X0 := superpose eq7 eq17
  have eq78 (X0 X1 X3 X4 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ ((X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))) = X1 := superpose eq17 eq9
  have eq104 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X3) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)))) = (((X1 ◇ X0) ◇ (((X4 ◇ X3) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)))) ◇ ((X4 ◇ X3) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)))))) ◇ (X3 ◇ (((X1 ◇ X0) ◇ (((X4 ◇ X3) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)))) ◇ ((X4 ◇ X3) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)))))) ◇ ((X1 ◇ X0) ◇ (((X4 ◇ X3) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)))) ◇ ((X4 ◇ X3) ◇ (((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X0))))))))) := superpose eq48 eq33
  have eq113 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X3)) ◇ X4)) ◇ (X4 ◇ X4)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X3)))) = X4 := superpose eq48 eq26
  have eq114 (X0 X1 X3 X4 : G) : ((X4 ◇ X3) ◇ X3) = (((X1 ◇ X0) ◇ (((X4 ◇ X3) ◇ X3) ◇ ((X4 ◇ X3) ◇ X3))) ◇ (X3 ◇ (((X1 ◇ X0) ◇ (((X4 ◇ X3) ◇ X3) ◇ ((X4 ◇ X3) ◇ X3))) ◇ ((X1 ◇ X0) ◇ (((X4 ◇ X3) ◇ X3) ◇ ((X4 ◇ X3) ◇ X3)))))) := superpose eq48 eq104
  have eq117 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X3)) ◇ X4)) ◇ (X4 ◇ X4)) ◇ X0) = X4 := superpose eq48 eq113
  have eq123 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq78 eq15
  have eq132 (X0 X1 X3 X4 : G) : (((X1 ◇ (((X3 ◇ X3) ◇ X3) ◇ X4)) ◇ (X4 ◇ X4)) ◇ X0) = X4 := superpose eq123 eq117
  have eq142 (X0 X1 X3 X4 : G) : ((X4 ◇ X3) ◇ X3) = (((X1 ◇ X0) ◇ ((X3 ◇ X3) ◇ X3)) ◇ (X3 ◇ (((X1 ◇ X0) ◇ ((X3 ◇ X3) ◇ X3)) ◇ ((X1 ◇ X0) ◇ ((X3 ◇ X3) ◇ X3))))) := superpose eq123 eq114
  have eq159 (X0 X4 : G) : (((X4 ◇ X4) ◇ X4) ◇ X0) = X4 := superpose eq123 eq132
  have eq163 (X3 X4 : G) : ((X4 ◇ X3) ◇ X3) = (((X3 ◇ X3) ◇ X3) ◇ (X3 ◇ (((X3 ◇ X3) ◇ X3) ◇ ((X3 ◇ X3) ◇ X3)))) := superpose eq123 eq142
  have eq164 (X3 X4 : G) : ((X4 ◇ X3) ◇ X3) = X3 := superpose eq159 eq163
  have eq165 (X0 X4 : G) : (X4 ◇ X0) = X4 := superpose eq164 eq159
  have eq168 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = X0 := superpose eq165 eq18
  have eq178 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X3))) = X0 := superpose eq165 eq168
  have eq179 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq165 eq178
  have eq180 (X0 X3 : G) : X0 = X3 := superpose eq179 eq179
  have eq185 (X0 : G) : sK0 ≠ X0 := superpose eq180 eq8
  subsumption eq185 eq180


@[equational_result]
theorem Equation11363_implies_Equation2 (G : Type*) [Magma G] (h : Equation11363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq158 eq59


@[equational_result]
theorem Equation11367_implies_Equation2 (G : Type*) [Magma G] (h : Equation11367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq122 eq41


@[equational_result]
theorem Equation11369_implies_Equation2 (G : Type*) [Magma G] (h : Equation11369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X2)) ◇ ((X4 ◇ X0) ◇ (X5 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X2))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = ((X1 ◇ X2) ◇ (X0 ◇ (X4 ◇ (X1 ◇ X2)))) := superpose eq7 eq7
  have eq45 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X4 ◇ (X3 ◇ X2)) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X4 ◇ (X3 ◇ X2)))) ◇ ((X6 ◇ X1) ◇ (X7 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X4 ◇ (X3 ◇ X2))))))) := superpose eq10 eq9
  have eq57 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq9
  have eq59 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) = X4 := superpose eq10 eq9
  have eq80 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ X2)) = (((X0 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X4 ◇ (X3 ◇ X2)))) ◇ ((X6 ◇ X1) ◇ (X4 ◇ (X3 ◇ X2)))) := superpose eq59 eq45
  have eq96 (X2 X3 X4 : G) : (X3 ◇ X2) = (X4 ◇ (X3 ◇ X2)) := superpose eq59 eq80
  have eq100 (X0 X2 X3 : G) : (((X2 ◇ X2) ◇ (X3 ◇ X2)) ◇ X0) = X2 := superpose eq96 eq57
  have eq102 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X1))) = X0 := superpose eq96 eq7
  have eq103 (X0 X1 X2 X4 : G) : (X0 ◇ X2) = ((X1 ◇ X2) ◇ (X0 ◇ (X4 ◇ (X1 ◇ X2)))) := superpose eq96 eq10
  have eq126 (X0 X2 X3 : G) : ((X3 ◇ X2) ◇ X0) = X2 := superpose eq96 eq100
  have eq130 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X0 := superpose eq96 eq102
  have eq131 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq126 eq103
  have eq137 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq131 eq130
  have eq167 (X0 X2 : G) : X0 = X2 := superpose eq137 eq137
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq167 eq8
  subsumption eq169 eq167


@[equational_result]
theorem Equation11370_implies_Equation2 (G : Type*) [Magma G] (h : Equation11370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq47 eq13


@[equational_result]
theorem Equation11371_implies_Equation2 (G : Type*) [Magma G] (h : Equation11371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq65 eq12


@[equational_result]
theorem Equation11372_implies_Equation2 (G : Type*) [Magma G] (h : Equation11372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation11374_implies_Equation2 (G : Type*) [Magma G] (h : Equation11374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3)) ◇ X0) ◇ (X3 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1))) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X0 ◇ X4)) ◇ (X0 ◇ X3)) = (X1 ◇ ((((X2 ◇ (X3 ◇ X2)) ◇ X0) ◇ X3) ◇ (((X4 ◇ (X0 ◇ X4)) ◇ (X0 ◇ X3)) ◇ X1))) := superpose eq7 eq9
  have eq18 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((((X3 ◇ (X4 ◇ X3)) ◇ (X4 ◇ X2)) ◇ X4) ◇ X0)) = X2 := superpose eq7 eq9
  have eq36 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ X1)) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq10
  have eq38 (X0 X1 X2 X3 : G) : (((X2 ◇ (((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X1) ◇ X2)) ◇ (((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X1) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq10 eq10
  have eq47 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (((X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3))) ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))) := superpose eq11 eq11
  have eq944 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X0)) = (((X3 ◇ (X0 ◇ X3)) ◇ X2) ◇ ((((X4 ◇ (X0 ◇ X4)) ◇ X2) ◇ X0) ◇ X0)) := superpose eq10 eq14
  have eq1058 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := superpose eq18 eq944
  have eq1060 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ ((((X3 ◇ (X1 ◇ X3)) ◇ X2) ◇ X1) ◇ X1))) = X2 := superpose eq944 eq7
  have eq1273 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2)) := superpose eq1058 eq1058
  have eq1282 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq11 eq1058
  have eq2275 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) := superpose eq1058 eq1273
  have eq2278 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) := superpose eq7 eq1273
  have eq2747 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq2278 eq1058
  have eq3035 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) := superpose eq1282 eq1282
  have eq3292 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = (X3 ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3)) := superpose eq1058 eq3035
  have eq3581 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) := superpose eq1273 eq3292
  have eq3594 (X0 X1 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq3581 eq2747
  have eq3595 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) := superpose eq3581 eq2278
  have eq3597 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq3595 eq3581
  have eq3599 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = ((X1 ◇ X0) ◇ X0) := superpose eq3597 eq2275
  have eq3604 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq3597 eq3594
  have eq3605 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq3597 eq3595
  have eq3607 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq3605 eq3604
  have eq3608 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq3607 eq3599
  have eq3610 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X1)) = X2 := superpose eq3608 eq1060
  have eq3612 (X0 X1 X2 X3 : G) : (((X2 ◇ (((X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq3608 eq38
  have eq3613 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := superpose eq3608 eq1282
  have eq3617 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X0 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0) := superpose eq3613 eq11
  have eq3619 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq3613 eq47
  have eq3630 (X0 X1 X2 : G) : (((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq3613 eq3612
  have eq3647 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq3617 eq3608
  have eq3652 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq36 eq3608
  have eq3684 (X0 X1 X2 : G) : (((X2 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq3647 eq3630
  have eq3686 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq3647 eq3684
  have eq3688 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (X0 ◇ X0) := superpose eq3686 eq3617
  have eq3690 (X1 X3 : G) : ((X1 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X1) = X1 := superpose eq3686 eq3619
  have eq3700 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq3686 eq3690
  have eq3701 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = X0 := superpose eq3700 eq3688
  have eq3736 (X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X1)) = X2 := superpose eq3701 eq3610
  have eq3834 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq3652 eq3736
  have eq3908 (X0 X2 : G) : X0 = X2 := superpose eq3834 eq3834
  have eq3913 (X0 : G) : sK0 ≠ X0 := superpose eq3908 eq8
  subsumption eq3913 eq3908


@[equational_result]
theorem Equation11375_implies_Equation2 (G : Type*) [Magma G] (h : Equation11375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X0) ◇ X0)) = X3 := superpose eq7 eq7
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq69 eq52


@[equational_result]
theorem Equation11376_implies_Equation2 (G : Type*) [Magma G] (h : Equation11376 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X4))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = (X3 ◇ (X0 ◇ X3)) := superpose eq11 eq10
  have eq27 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X1 := superpose eq13 eq7
  have eq32 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq13 eq7
  have eq34 (X0 X1 X3 : G) : (X3 ◇ X0) = X1 := superpose eq32 eq27
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq53 eq44


@[equational_result]
theorem Equation11380_implies_Equation2 (G : Type*) [Magma G] (h : Equation11380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq46 eq16


@[equational_result]
theorem Equation11383_implies_Equation2 (G : Type*) [Magma G] (h : Equation11383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2)) ◇ X0) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X2)) ◇ X0) ◇ X0)) = X3 := superpose eq7 eq9
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq75 eq53


@[equational_result]
theorem Equation11384_implies_Equation2 (G : Type*) [Magma G] (h : Equation11384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation11386_implies_Equation2 (G : Type*) [Magma G] (h : Equation11386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq47 eq17


@[equational_result]
theorem Equation11387_implies_Equation2 (G : Type*) [Magma G] (h : Equation11387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation11388_implies_Equation2 (G : Type*) [Magma G] (h : Equation11388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq172 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq172 eq57


@[equational_result]
theorem Equation11389_implies_Equation2 (G : Type*) [Magma G] (h : Equation11389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation11391_implies_Equation2 (G : Type*) [Magma G] (h : Equation11391 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X1))) = X5 := superpose eq7 eq9
  have eq49 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq13 eq13
  have eq121 (X0 X3 : G) : X0 = X3 := superpose eq49 eq49
  have eq248 (X0 : G) : sK0 ≠ X0 := superpose eq121 eq8
  subsumption eq248 eq121


@[equational_result]
theorem Equation11392_implies_Equation2 (G : Type*) [Magma G] (h : Equation11392 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X2 X3 X4 : G) : (X4 ◇ (X2 ◇ (X0 ◇ X3))) = X0 := superpose eq7 eq12
  have eq26 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq12 eq7
  have eq34 (X0 X3 X4 : G) : (X4 ◇ X3) = X0 := superpose eq26 eq16
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq34 eq34
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq50 eq41


@[equational_result]
theorem Equation11393_implies_Equation2 (G : Type*) [Magma G] (h : Equation11393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq60 eq19


@[equational_result]
theorem Equation11394_implies_Equation2 (G : Type*) [Magma G] (h : Equation11394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 X6 : G) : (X3 ◇ (X0 ◇ X4)) = (X1 ◇ (X0 ◇ ((X3 ◇ (X0 ◇ X4)) ◇ X6))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X4)) = (X1 ◇ X0) := superpose eq11 eq10
  have eq17 (X0 X2 X3 X5 : G) : (X5 ◇ (X2 ◇ (X0 ◇ X3))) = X0 := superpose eq7 eq13
  have eq27 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq13 eq7
  have eq33 (X0 X3 X5 : G) : (X5 ◇ X3) = X0 := superpose eq27 eq17
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq33 eq33
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq47 eq38


@[equational_result]
theorem Equation11396_implies_Equation2 (G : Type*) [Magma G] (h : Equation11396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation11397_implies_Equation2 (G : Type*) [Magma G] (h : Equation11397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq72 eq19


@[equational_result]
theorem Equation11398_implies_Equation2 (G : Type*) [Magma G] (h : Equation11398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ ((X4 ◇ (X0 ◇ X5)) ◇ (X3 ◇ X5))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X4)) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X4)))) := superpose eq7 eq7
  have eq40 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X7 ◇ (((X3 ◇ X4) ◇ (X2 ◇ ((X5 ◇ (X4 ◇ X6)) ◇ (X0 ◇ X6)))) ◇ X8)) ◇ (X9 ◇ X8))))) = X9 := superpose eq9 eq9
  have eq60 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) = X3 := superpose eq10 eq9
  have eq81 (X0 X1 X3 X4 X7 X8 X9 : G) : (X1 ◇ (X0 ◇ (X1 ◇ ((X7 ◇ (((X3 ◇ X4) ◇ X0) ◇ X8)) ◇ (X9 ◇ X8))))) = X9 := superpose eq60 eq40
  have eq94 (X0 X1 X9 : G) : (X1 ◇ (X0 ◇ X9)) = X9 := superpose eq60 eq81
  have eq95 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ (X1 ◇ X3))) = X0 := superpose eq94 eq7
  have eq121 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq94 eq95
  have eq122 (X0 X3 : G) : X0 = X3 := superpose eq121 eq121
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq122 eq8
  subsumption eq124 eq122


@[equational_result]
theorem Equation11399_implies_Equation2 (G : Type*) [Magma G] (h : Equation11399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq64 eq19


@[equational_result]
theorem Equation11401_implies_Equation2 (G : Type*) [Magma G] (h : Equation11401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X1))) = X3 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq78 eq22


@[equational_result]
theorem Equation11402_implies_Equation2 (G : Type*) [Magma G] (h : Equation11402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation11403_implies_Equation2 (G : Type*) [Magma G] (h : Equation11403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation11404_implies_Equation2 (G : Type*) [Magma G] (h : Equation11404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation11406_implies_Equation2 (G : Type*) [Magma G] (h : Equation11406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X4)) = (X1 ◇ (X0 ◇ ((X4 ◇ X2) ◇ X1))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X1))))) ◇ X0) = X3 := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X4))) ◇ X3)) = X0 := superpose eq7 eq10
  have eq48 (X0 X1 X2 X3 X7 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X7) = X3 := superpose eq12 eq12
  have eq67 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq48 eq28
  have eq73 (X0 X4 : G) : X0 = X4 := superpose eq7 eq67
  have eq179 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq179 eq73


@[equational_result]
theorem Equation11407_implies_Equation2 (G : Type*) [Magma G] (h : Equation11407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq47 eq13


@[equational_result]
theorem Equation11408_implies_Equation2 (G : Type*) [Magma G] (h : Equation11408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (((X4 ◇ (X0 ◇ X5)) ◇ (X5 ◇ X5)) ◇ ((X4 ◇ (X0 ◇ X5)) ◇ (X5 ◇ X5))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = X3 := superpose eq7 eq9
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq74 eq20


@[equational_result]
theorem Equation11409_implies_Equation2 (G : Type*) [Magma G] (h : Equation11409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (((X4 ◇ (X0 ◇ X5)) ◇ (X5 ◇ X6)) ◇ X7))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X1 X3 X5 : G) : (X1 ◇ X5) = X3 := superpose eq11 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation11411_implies_Equation2 (G : Type*) [Magma G] (h : Equation11411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X7 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X7 ◇ X1))) = X3 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq7 eq9
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq59 eq22


@[equational_result]
theorem Equation11412_implies_Equation2 (G : Type*) [Magma G] (h : Equation11412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation11413_implies_Equation2 (G : Type*) [Magma G] (h : Equation11413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation11414_implies_Equation2 (G : Type*) [Magma G] (h : Equation11414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation11415_implies_Equation2 (G : Type*) [Magma G] (h : Equation11415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation11417_implies_Equation2 (G : Type*) [Magma G] (h : Equation11417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = (X1 ◇ ((X2 ◇ X0) ◇ (((X3 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) ◇ ((X3 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) = (X0 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0))) := superpose eq7 eq10
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq10 eq10
  have eq51 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) ◇ (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X0 := superpose eq11 eq11
  have eq62 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = X0 := superpose eq7 eq51
  have eq67 (X0 X3 : G) : ((X0 ◇ (((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0) = X0 := superpose eq62 eq62
  have eq70 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq62 eq11
  have eq72 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)))) ◇ X0)) := superpose eq62 eq7
  have eq82 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq62 eq10
  have eq83 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = X1 := superpose eq62 eq7
  have eq86 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq70 eq67
  have eq95 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) = (X0 ◇ ((X1 ◇ ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq9 eq72
  have eq96 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X3 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X0)) = ((X2 ◇ X0) ◇ X0) := superpose eq70 eq95
  have eq105 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq83 eq82
  have eq108 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq86 eq7
  have eq110 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq86 eq7
  have eq126 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq108 eq110
  have eq150 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq86 eq16
  have eq171 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq108 eq150
  have eq172 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq105 eq171
  have eq173 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq126 eq172
  have eq174 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq108 eq173
  have eq175 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq174 eq96
  have eq337 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X0)) := superpose eq175 eq7
  have eq371 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq174 eq337
  have eq373 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq371 eq17
  have eq482 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq371 eq373
  have eq483 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq371 eq482
  have eq484 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq371 eq483
  have eq618 (X0 X2 : G) : X0 = X2 := superpose eq484 eq484
  have eq623 (X0 : G) : sK0 ≠ X0 := superpose eq618 eq8
  subsumption eq623 eq618


@[equational_result]
theorem Equation11419_implies_Equation2 (G : Type*) [Magma G] (h : Equation11419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq131 eq42


@[equational_result]
theorem Equation11421_implies_Equation2 (G : Type*) [Magma G] (h : Equation11421 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X1)) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X2)) = X0 := superpose eq7 eq9
  have eq42 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X2) = ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4)) ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := superpose eq9 eq10
  have eq63 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X2)) = (X2 ◇ ((X3 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq23 eq9
  have eq64 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq23 eq7
  have eq71 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X2 := superpose eq64 eq63
  have eq93 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq71 eq10
  have eq107 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X2) = ((X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X4)) ◇ (X2 ◇ X2)) := superpose eq93 eq42
  have eq108 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq71 eq107
  have eq110 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq108 eq71
  have eq111 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq108 eq93
  have eq115 (X0 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose eq110 eq111
  have eq116 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq110 eq115
  have eq139 (X0 X2 : G) : X0 = X2 := superpose eq116 eq116
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq139 eq8
  subsumption eq141 eq139


@[equational_result]
theorem Equation11423_implies_Equation2 (G : Type*) [Magma G] (h : Equation11423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq185 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq185 eq67


@[equational_result]
theorem Equation11425_implies_Equation2 (G : Type*) [Magma G] (h : Equation11425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X1)) = (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2)) ◇ ((X2 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X4 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X2))) ◇ (X4 ◇ X2))) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X5 ◇ ((X4 ◇ X2) ◇ (X4 ◇ X1))) ◇ (X5 ◇ X1))) = ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1))) ◇ (X3 ◇ X1)) := superpose eq9 eq9
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ (X3 ◇ X4)))) ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ (X4 ◇ X2))) := superpose eq7 eq9
  have eq28 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X3 ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))) := superpose eq9 eq9
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X2)) = X0 := superpose eq7 eq9
  have eq41 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X0)))) = X2 := superpose eq30 eq28
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)))) := superpose eq9 eq10
  have eq64 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ X2) := superpose eq7 eq52
  have eq72 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) := superpose eq10 eq30
  have eq82 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq30 eq10
  have eq113 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3) = (((X1 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq11 eq11
  have eq138 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X3) ◇ X0))) = X3 := superpose eq113 eq11
  have eq173 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq41 eq30
  have eq175 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X1)) = (X1 ◇ ((X3 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X1))) ◇ (X3 ◇ X1))) := superpose eq41 eq9
  have eq187 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1))) ◇ (X3 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := superpose eq175 eq13
  have eq189 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq187 eq12
  have eq191 (X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X2) := superpose eq189 eq64
  have eq230 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq9 eq138
  have eq256 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq173 eq230
  have eq257 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq189 eq256
  have eq258 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq173 eq257
  have eq291 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = X1 := superpose eq189 eq41
  have eq351 (X0 : G) : ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq138 eq191
  have eq353 (X0 X1 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) ◇ X1) = ((X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) := superpose eq191 eq191
  have eq355 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X1) = (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) := superpose eq9 eq191
  have eq381 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))) ◇ X1))) = X2 := superpose eq191 eq7
  have eq383 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = ((X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X1)) := superpose eq191 eq189
  have eq385 (X0 : G) : ((((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq82 eq351
  have eq386 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ X0) := superpose eq30 eq385
  have eq403 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq138 eq291
  have eq430 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq355 eq403
  have eq431 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq189 eq430
  have eq432 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq173 eq431
  have eq433 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq355 eq432
  have eq434 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq82 eq433
  have eq435 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq30 eq434
  have eq436 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq435 eq386
  have eq465 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq189 eq258
  have eq509 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (((X1 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq189 eq465
  have eq510 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose eq435 eq509
  have eq511 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose eq436 eq510
  have eq512 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq511 eq173
  have eq513 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq512 eq30
  have eq596 (X0 X1 X2 X4 : G) : (X2 ◇ (X0 ◇ (X4 ◇ X2))) = ((X1 ◇ (X2 ◇ (X4 ◇ X0))) ◇ (X1 ◇ X2)) := superpose eq513 eq22
  have eq741 (X0 X2 X4 : G) : (X2 ◇ (X0 ◇ (X4 ◇ X2))) = (X2 ◇ (X4 ◇ X0)) := superpose eq513 eq596
  have eq744 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1))) = X2 := superpose eq741 eq381
  have eq745 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ X1)) := superpose eq741 eq383
  have eq746 (X0 X1 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X1) = ((X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := superpose eq741 eq353
  have eq770 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X1))) = X2 := superpose eq512 eq744
  have eq771 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq513 eq745
  have eq772 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := superpose eq512 eq771
  have eq773 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X1) = ((X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq512 eq746
  have eq774 (X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ X1) := superpose eq772 eq773
  have eq775 (X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq512 eq774
  have eq776 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq513 eq775
  have eq777 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq776 eq72
  have eq781 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq512 eq777
  have eq782 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X2 := superpose eq781 eq770
  have eq801 (X1 X2 : G) : (X1 ◇ ((X1 ◇ X2) ◇ X1)) = X2 := superpose eq781 eq782
  have eq802 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq781 eq801
  have eq809 (X0 X2 : G) : X0 = X2 := superpose eq802 eq802
  have eq829 (X0 : G) : sK0 ≠ X0 := superpose eq809 eq8
  subsumption eq829 eq809


@[equational_result]
theorem Equation11427_implies_Equation2 (G : Type*) [Magma G] (h : Equation11427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq185 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq185 eq59


@[equational_result]
theorem Equation11429_implies_Equation2 (G : Type*) [Magma G] (h : Equation11429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ (X4 ◇ X1)) = (X1 ◇ ((X2 ◇ X0) ◇ (X5 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X2) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq7 eq7
  have eq46 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : (X4 ◇ X1) = ((X5 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1))) ◇ (((X6 ◇ X2) ◇ (X7 ◇ X1)) ◇ (X8 ◇ (X5 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)))))) := superpose eq9 eq10
  have eq60 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq10 eq10
  have eq84 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X1))) = X0 := superpose eq7 eq60
  have eq98 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ (X4 ◇ X2))) = X1 := superpose eq60 eq7
  have eq141 (X1 X2 X4 X6 X7 X8 : G) : (X4 ◇ X1) = (X2 ◇ (((X6 ◇ X2) ◇ (X7 ◇ X1)) ◇ (X8 ◇ X2))) := superpose eq84 eq46
  have eq147 (X1 X4 : G) : (X4 ◇ X1) = X1 := superpose eq98 eq141
  have eq153 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1))) = X0 := superpose eq147 eq7
  have eq211 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X0 := superpose eq147 eq153
  have eq212 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq147 eq211
  have eq222 (X0 X2 : G) : X0 = X2 := superpose eq212 eq212
  have eq224 (X0 : G) : sK0 ≠ X0 := superpose eq222 eq8
  subsumption eq224 eq222


@[equational_result]
theorem Equation11430_implies_Equation2 (G : Type*) [Magma G] (h : Equation11430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq66 eq13


@[equational_result]
theorem Equation11431_implies_Equation2 (G : Type*) [Magma G] (h : Equation11431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq62 eq12


@[equational_result]
theorem Equation11432_implies_Equation2 (G : Type*) [Magma G] (h : Equation11432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation11434_implies_Equation2 (G : Type*) [Magma G] (h : Equation11434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2)) ◇ ((X3 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2)))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ (((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose eq9 eq7
  have eq26 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X3 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := superpose eq13 eq9
  have eq36 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq26
  have eq37 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq36 eq13
  have eq62 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X3 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X2 ◇ (X0 ◇ X0)))) := superpose eq37 eq9
  have eq70 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq62
  have eq77 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X0 := superpose eq70 eq7
  have eq103 (X0 X1 : G) : X0 = X1 := superpose eq70 eq77
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq103 eq8
  subsumption eq117 eq103


@[equational_result]
theorem Equation11436_implies_Equation2 (G : Type*) [Magma G] (h : Equation11436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq60 eq42


@[equational_result]
theorem Equation11438_implies_Equation2 (G : Type*) [Magma G] (h : Equation11438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation11439_implies_Equation2 (G : Type*) [Magma G] (h : Equation11439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11440_implies_Equation2 (G : Type*) [Magma G] (h : Equation11440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11442_implies_Equation2 (G : Type*) [Magma G] (h : Equation11442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11443_implies_Equation2 (G : Type*) [Magma G] (h : Equation11443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11444_implies_Equation2 (G : Type*) [Magma G] (h : Equation11444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11446_implies_Equation2 (G : Type*) [Magma G] (h : Equation11446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11447_implies_Equation2 (G : Type*) [Magma G] (h : Equation11447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11448_implies_Equation2 (G : Type*) [Magma G] (h : Equation11448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11449_implies_Equation2 (G : Type*) [Magma G] (h : Equation11449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11453_implies_Equation2 (G : Type*) [Magma G] (h : Equation11453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq78 eq22


@[equational_result]
theorem Equation11455_implies_Equation2 (G : Type*) [Magma G] (h : Equation11455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11456_implies_Equation2 (G : Type*) [Magma G] (h : Equation11456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation11457_implies_Equation2 (G : Type*) [Magma G] (h : Equation11457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11459_implies_Equation2 (G : Type*) [Magma G] (h : Equation11459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11460_implies_Equation2 (G : Type*) [Magma G] (h : Equation11460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11461_implies_Equation2 (G : Type*) [Magma G] (h : Equation11461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11463_implies_Equation2 (G : Type*) [Magma G] (h : Equation11463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11464_implies_Equation2 (G : Type*) [Magma G] (h : Equation11464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11465_implies_Equation2 (G : Type*) [Magma G] (h : Equation11465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11466_implies_Equation2 (G : Type*) [Magma G] (h : Equation11466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11468_implies_Equation2 (G : Type*) [Magma G] (h : Equation11468 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X5 ◇ X1))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X1))) = X5 := superpose eq7 eq9
  have eq42 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) = X2 := superpose eq12 eq12
  have eq60 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq42 eq7
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq9 eq60
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq90 eq61


@[equational_result]
theorem Equation11469_implies_Equation2 (G : Type*) [Magma G] (h : Equation11469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X4 ◇ X2))) = X4 := superpose eq7 eq7
  have eq35 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq7
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq7 eq35
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq119 eq42


@[equational_result]
theorem Equation11470_implies_Equation2 (G : Type*) [Magma G] (h : Equation11470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X3)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X4 ◇ X5) = (X2 ◇ ((X3 ◇ (X4 ◇ (X0 ◇ X1))) ◇ ((X6 ◇ (X0 ◇ (X1 ◇ X7))) ◇ X7))) := superpose eq12 eq12
  have eq45 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X5) = (X2 ◇ (X0 ◇ X1)) := superpose eq12 eq28
  have eq60 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq45
  have eq149 (X0 X4 : G) : X0 = X4 := superpose eq7 eq60
  have eq290 (X0 : G) : sK0 ≠ X0 := superpose eq149 eq8
  subsumption eq290 eq149


@[equational_result]
theorem Equation11471_implies_Equation2 (G : Type*) [Magma G] (h : Equation11471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq35 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq57 eq35


@[equational_result]
theorem Equation11473_implies_Equation2 (G : Type*) [Magma G] (h : Equation11473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11474_implies_Equation2 (G : Type*) [Magma G] (h : Equation11474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11475_implies_Equation2 (G : Type*) [Magma G] (h : Equation11475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11476_implies_Equation2 (G : Type*) [Magma G] (h : Equation11476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11478_implies_Equation2 (G : Type*) [Magma G] (h : Equation11478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11479_implies_Equation2 (G : Type*) [Magma G] (h : Equation11479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11480_implies_Equation2 (G : Type*) [Magma G] (h : Equation11480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11481_implies_Equation2 (G : Type*) [Magma G] (h : Equation11481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11483_implies_Equation2 (G : Type*) [Magma G] (h : Equation11483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11484_implies_Equation2 (G : Type*) [Magma G] (h : Equation11484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11485_implies_Equation2 (G : Type*) [Magma G] (h : Equation11485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11486_implies_Equation2 (G : Type*) [Magma G] (h : Equation11486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11488_implies_Equation2 (G : Type*) [Magma G] (h : Equation11488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11489_implies_Equation2 (G : Type*) [Magma G] (h : Equation11489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11490_implies_Equation2 (G : Type*) [Magma G] (h : Equation11490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11491_implies_Equation2 (G : Type*) [Magma G] (h : Equation11491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11492_implies_Equation2 (G : Type*) [Magma G] (h : Equation11492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11494_implies_Equation2 (G : Type*) [Magma G] (h : Equation11494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X2)) = (X1 ◇ ((X2 ◇ X0) ◇ (((X3 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X2 ◇ X0))) = (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) ◇ ((X3 ◇ (X3 ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) ◇ ((X3 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) = X2 := superpose eq7 eq11
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X3 ◇ X0))) = (((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X0))))) ◇ (X0 ◇ X2)) := superpose eq7 eq11
  have eq37 (X0 X1 X2 X3 : G) : (X2 ◇ (((X1 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X2))) = X1 := superpose eq12 eq7
  have eq121 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = (((X3 ◇ (X3 ◇ X0)) ◇ X2) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq11 eq9
  have eq206 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := superpose eq11 eq121
  have eq338 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) := superpose eq7 eq206
  have eq342 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X4 ◇ X0)) ◇ X3) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X0)))) := superpose eq11 eq206
  have eq385 (X0 X1 X3 X4 : G) : ((X4 ◇ (X4 ◇ X0)) ◇ X3) = ((X1 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq7 eq342
  have eq498 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) ◇ X2) := superpose eq7 eq385
  have eq557 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1))))) ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X3))) = X1 := superpose eq385 eq37
  have eq708 (X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X1 ◇ X3))) = X1 := superpose eq498 eq557
  have eq776 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq7 eq15
  have eq819 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) := superpose eq21 eq776
  have eq877 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := superpose eq10 eq708
  have eq883 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ X0) := superpose eq708 eq10
  have eq980 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq883 eq819
  have eq1034 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq883 eq883
  have eq1037 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) = (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq7 eq883
  have eq1162 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) = X0 := superpose eq877 eq1037
  have eq1178 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq1162 eq338
  have eq1193 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) := superpose eq1178 eq980
  have eq1204 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq1178 eq1193
  have eq1205 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ X0) := superpose eq1204 eq883
  have eq1326 (X1 X3 : G) : (X3 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X3))) = X1 := superpose eq1205 eq708
  have eq1397 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq1205 eq1034
  have eq1458 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1326 eq1397
  have eq1459 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq1458 eq1178
  have eq1585 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq1459 eq7
  have eq1814 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq1459 eq1585
  have eq1865 (X0 X2 : G) : X0 = X2 := superpose eq1814 eq1814
  have eq1867 (X0 : G) : sK0 ≠ X0 := superpose eq1865 eq8
  subsumption eq1867 eq1865


@[equational_result]
theorem Equation11495_implies_Equation2 (G : Type*) [Magma G] (h : Equation11495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) ◇ (((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X0)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (X3 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2))) := superpose eq7 eq12
  have eq31 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq13
  have eq33 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X0)) = X3 := superpose eq31 eq11
  have eq41 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq31 eq33
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq41 eq41
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq47 eq42


@[equational_result]
theorem Equation11496_implies_Equation2 (G : Type*) [Magma G] (h : Equation11496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ X0)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = (X4 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3))) := superpose eq7 eq12
  have eq31 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq13
  have eq32 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) = X0 := superpose eq31 eq7
  have eq37 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq31 eq32
  have eq38 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq31 eq37
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq38 eq38
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq41 eq39


@[equational_result]
theorem Equation11500_implies_Equation2 (G : Type*) [Magma G] (h : Equation11500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq49 eq18


@[equational_result]
theorem Equation11503_implies_Equation2 (G : Type*) [Magma G] (h : Equation11503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X3)) = (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq7 eq7
  have eq36 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((((X3 ◇ X1) ◇ (X3 ◇ X3)) ◇ (((X3 ◇ X1) ◇ (X3 ◇ X3)) ◇ X4)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)))) = X4 := superpose eq9 eq7
  have eq47 (X1 X2 X4 : G) : (X2 ◇ X1) = X4 := superpose eq7 eq36
  have eq63 (X0 X3 : G) : X0 = X3 := superpose eq7 eq47
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq157 eq63


@[equational_result]
theorem Equation11504_implies_Equation2 (G : Type*) [Magma G] (h : Equation11504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation11506_implies_Equation2 (G : Type*) [Magma G] (h : Equation11506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation11507_implies_Equation2 (G : Type*) [Magma G] (h : Equation11507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq63 eq13


@[equational_result]
theorem Equation11508_implies_Equation2 (G : Type*) [Magma G] (h : Equation11508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (X3 ◇ X3) = (X1 ◇ (X0 ◇ (X4 ◇ X4))) := superpose eq7 eq7
  have eq20 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq52 (X0 X3 : G) : X0 = X3 := superpose eq7 eq20
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq160 eq52


@[equational_result]
theorem Equation11509_implies_Equation2 (G : Type*) [Magma G] (h : Equation11509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation11511_implies_Equation2 (G : Type*) [Magma G] (h : Equation11511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X0) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ ((X3 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (((X3 ◇ (X3 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X2)) ◇ (X0 ◇ (X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (((X3 ◇ (X3 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X2))))) = X4 := superpose eq7 eq9
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)))) ◇ (((X3 ◇ X4) ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)))) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)))) ◇ (X0 ◇ (X5 ◇ ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)))) ◇ (((X3 ◇ X4) ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)))) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3))))))) = X5 := superpose eq9 eq9
  have eq17 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq9
  have eq18 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ (X1 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq7 eq9
  have eq46 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq17 eq9
  have eq53 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ X2) = (((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X0) ◇ ((X4 ◇ (X4 ◇ ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X0))) ◇ ((X3 ◇ (X3 ◇ X0)) ◇ (X2 ◇ X0)))) := superpose eq17 eq10
  have eq54 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq17 eq46
  have eq66 (X0 X1 X3 X4 : G) : (X1 ◇ X1) = (((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X1 ◇ X1))) ◇ ((X4 ◇ (X4 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X1 ◇ X1))))) ◇ X3)) := superpose eq18 eq10
  have eq106 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq54 eq54
  have eq109 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)))) = ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)))) ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)))) := superpose eq9 eq54
  have eq111 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)))) ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)))) := superpose eq17 eq54
  have eq112 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ X3) = ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) := superpose eq54 eq54
  have eq117 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq18 eq54
  have eq132 (X0 X1 X2 X3 : G) : (X3 ◇ (X3 ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ ((X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X0)) := superpose eq54 eq7
  have eq137 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ X2) = (((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X0) ◇ ((X4 ◇ (X4 ◇ ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X0))) ◇ (X3 ◇ (X3 ◇ X2)))) := superpose eq54 eq10
  have eq143 (X0 X2 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)))) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)))) ◇ (X0 ◇ (X5 ◇ ((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3)))) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3))))))) = X5 := superpose eq109 eq12
  have eq151 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)))) ◇ X3) = ((X0 ◇ X3) ◇ X3) := superpose eq7 eq111
  have eq174 (X1 X3 X4 : G) : (X1 ◇ X1) = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1))) ◇ ((X4 ◇ (X4 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1))))) ◇ X3)) := superpose eq117 eq66
  have eq237 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (((X4 ◇ (X4 ◇ X3)) ◇ (X5 ◇ X3)) ◇ X3)))) = ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (((X4 ◇ (X4 ◇ X3)) ◇ (X5 ◇ X3)) ◇ X3)))) ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (((X4 ◇ (X4 ◇ X3)) ◇ (X5 ◇ X3)) ◇ X3)))) := superpose eq11 eq54
  have eq260 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq106 eq106
  have eq263 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq106
  have eq270 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq18 eq106
  have eq273 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq106 eq7
  have eq298 (X1 X3 X4 : G) : (X1 ◇ X1) = (((X1 ◇ X3) ◇ X1) ◇ ((X4 ◇ (X4 ◇ ((X1 ◇ X3) ◇ X1))) ◇ X3)) := superpose eq260 eq174
  have eq310 (X1 X2 : G) : (X1 ◇ X1) = (X2 ◇ (X2 ◇ (X1 ◇ X1))) := superpose eq270 eq18
  have eq446 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq310 eq273
  have eq476 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq446 eq263
  have eq487 (X1 X3 X4 : G) : (((X1 ◇ X3) ◇ X1) ◇ ((X4 ◇ (X4 ◇ ((X1 ◇ X3) ◇ X1))) ◇ X3)) = X1 := superpose eq446 eq298
  have eq560 (X0 X1 X2 X4 : G) : ((X0 ◇ X2) ◇ X2) = (((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X0) ◇ ((X4 ◇ (X4 ◇ ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X0))) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq476 eq53
  have eq565 (X0 X1 X3 X4 : G) : ((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ (X4 ◇ X3)))) = ((X1 ◇ (X1 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ (X0 ◇ (X3 ◇ (X4 ◇ X3)))) := superpose eq476 eq109
  have eq567 (X0 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ (X3 ◇ (X4 ◇ X3)))) ◇ (X0 ◇ (X5 ◇ ((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ (X3 ◇ (X4 ◇ X3))))))) = X5 := superpose eq476 eq143
  have eq570 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X3) = ((X1 ◇ (X1 ◇ (X0 ◇ (X3 ◇ X0)))) ◇ X3) := superpose eq476 eq151
  have eq587 (X0 X1 X2 X3 X5 : G) : (X5 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ (X5 ◇ X3)) ◇ X3)))) = ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ (X5 ◇ X3)) ◇ X3)))) ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ ((X3 ◇ (X5 ◇ X3)) ◇ X3)))) := superpose eq476 eq237
  have eq623 (X0 X1 X3 X5 : G) : (X5 ◇ (X0 ◇ (X5 ◇ X3))) = ((X1 ◇ (X1 ◇ (X5 ◇ X3))) ◇ (X0 ◇ (X5 ◇ X3))) := superpose eq54 eq587
  have eq624 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ (X0 ◇ (X3 ◇ (X4 ◇ X3)))) = (X3 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X3)))) := superpose eq623 eq565
  have eq637 (X0 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ ((X3 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ (X3 ◇ (X4 ◇ X3)))) ◇ (X0 ◇ (X5 ◇ ((X3 ◇ X4) ◇ ((X3 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ (X3 ◇ (X4 ◇ X3))))))) = X5 := superpose eq624 eq567
  have eq644 (X0 X3 X4 X5 : G) : ((X3 ◇ ((X3 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ (X3 ◇ (X4 ◇ X3)))) ◇ (X0 ◇ (X5 ◇ (X3 ◇ ((X3 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X3)))) ◇ (X3 ◇ (X4 ◇ X3))))))) = X5 := superpose eq624 eq637
  have eq657 (X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = X1 := superpose eq487 eq132
  have eq660 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X3) = ((X1 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X3)) := superpose eq657 eq112
  have eq665 (X0 X1 X2 X4 : G) : ((X2 ◇ X0) ◇ X2) = (((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X0) ◇ ((X4 ◇ (X4 ◇ ((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X0))) ◇ X2)) := superpose eq657 eq137
  have eq684 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ X2) = ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ ((X4 ◇ (X4 ◇ (((X0 ◇ X2) ◇ X2) ◇ X0))) ◇ (X0 ◇ (X2 ◇ X0)))) := superpose eq657 eq560
  have eq692 (X0 X3 : G) : ((X0 ◇ X3) ◇ X3) = ((X0 ◇ (X3 ◇ X0)) ◇ X3) := superpose eq657 eq570
  have eq698 (X0 X3 : G) : ((X3 ◇ X0) ◇ X3) = (X3 ◇ (X0 ◇ X3)) := superpose eq657 eq660
  have eq721 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X0) ◇ (((X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X0) ◇ X2)) := superpose eq657 eq665
  have eq722 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X2 := superpose eq657 eq721
  have eq723 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X3 := superpose eq722 eq698
  have eq738 (X0 X3 X5 : G) : ((X3 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X3)) ◇ (X0 ◇ (X5 ◇ (X3 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X3))))) = X5 := superpose eq723 eq644
  have eq753 (X0 X3 X5 : G) : (X3 ◇ (X0 ◇ (X5 ◇ X3))) = X5 := superpose eq723 eq738
  have eq764 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ X2) = ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ ((X4 ◇ (X4 ◇ (((X0 ◇ X2) ◇ X2) ◇ X0))) ◇ X0)) := superpose eq723 eq684
  have eq765 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ X0)) := superpose eq657 eq764
  have eq766 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq657 eq765
  have eq795 (X0 X3 : G) : (X0 ◇ X3) = ((X0 ◇ X3) ◇ X3) := superpose eq723 eq692
  have eq796 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq766 eq795
  have eq802 (X0 X3 X5 : G) : (X3 ◇ (X0 ◇ X5)) = X5 := superpose eq796 eq753
  have eq806 (X0 X3 X5 : G) : (X3 ◇ X0) = X5 := superpose eq796 eq802
  have eq807 (X0 X3 : G) : X0 = X3 := superpose eq806 eq806
  have eq809 (X0 : G) : sK0 ≠ X0 := superpose eq807 eq8
  subsumption eq809 eq807


@[equational_result]
theorem Equation11513_implies_Equation2 (G : Type*) [Magma G] (h : Equation11513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation11515_implies_Equation2 (G : Type*) [Magma G] (h : Equation11515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11516_implies_Equation2 (G : Type*) [Magma G] (h : Equation11516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11517_implies_Equation2 (G : Type*) [Magma G] (h : Equation11517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11519_implies_Equation2 (G : Type*) [Magma G] (h : Equation11519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation11520_implies_Equation2 (G : Type*) [Magma G] (h : Equation11520 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11521_implies_Equation2 (G : Type*) [Magma G] (h : Equation11521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11523_implies_Equation2 (G : Type*) [Magma G] (h : Equation11523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11524_implies_Equation2 (G : Type*) [Magma G] (h : Equation11524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11525_implies_Equation2 (G : Type*) [Magma G] (h : Equation11525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11526_implies_Equation2 (G : Type*) [Magma G] (h : Equation11526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11529_implies_Equation2 (G : Type*) [Magma G] (h : Equation11529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X3 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X0) ◇ X0)) = X3 := superpose eq7 eq9
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq70 eq54


@[equational_result]
theorem Equation11530_implies_Equation2 (G : Type*) [Magma G] (h : Equation11530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq130 eq47


@[equational_result]
theorem Equation11532_implies_Equation2 (G : Type*) [Magma G] (h : Equation11532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation11533_implies_Equation2 (G : Type*) [Magma G] (h : Equation11533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11534_implies_Equation2 (G : Type*) [Magma G] (h : Equation11534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11536_implies_Equation2 (G : Type*) [Magma G] (h : Equation11536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11537_implies_Equation2 (G : Type*) [Magma G] (h : Equation11537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation11538_implies_Equation2 (G : Type*) [Magma G] (h : Equation11538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11540_implies_Equation2 (G : Type*) [Magma G] (h : Equation11540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11541_implies_Equation2 (G : Type*) [Magma G] (h : Equation11541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11542_implies_Equation2 (G : Type*) [Magma G] (h : Equation11542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11543_implies_Equation2 (G : Type*) [Magma G] (h : Equation11543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11545_implies_Equation2 (G : Type*) [Magma G] (h : Equation11545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ (X4 ◇ X1))) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq10 eq10
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq120 eq41


@[equational_result]
theorem Equation11546_implies_Equation2 (G : Type*) [Magma G] (h : Equation11546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X2 ◇ (X2 ◇ X4)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X3 X4 : G) : (X3 ◇ X4) = X0 := superpose eq7 eq12
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq126 eq53


@[equational_result]
theorem Equation11547_implies_Equation2 (G : Type*) [Magma G] (h : Equation11547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X5 ◇ ((X3 ◇ (X3 ◇ X4)) ◇ (X0 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = X5 := superpose eq7 eq9
  have eq43 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq64 eq43


@[equational_result]
theorem Equation11548_implies_Equation2 (G : Type*) [Magma G] (h : Equation11548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 X6 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X6))) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation11550_implies_Equation2 (G : Type*) [Magma G] (h : Equation11550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11551_implies_Equation2 (G : Type*) [Magma G] (h : Equation11551 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11552_implies_Equation2 (G : Type*) [Magma G] (h : Equation11552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11553_implies_Equation2 (G : Type*) [Magma G] (h : Equation11553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11555_implies_Equation2 (G : Type*) [Magma G] (h : Equation11555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11556_implies_Equation2 (G : Type*) [Magma G] (h : Equation11556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11557_implies_Equation2 (G : Type*) [Magma G] (h : Equation11557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11558_implies_Equation2 (G : Type*) [Magma G] (h : Equation11558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11560_implies_Equation2 (G : Type*) [Magma G] (h : Equation11560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11561_implies_Equation2 (G : Type*) [Magma G] (h : Equation11561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11562_implies_Equation2 (G : Type*) [Magma G] (h : Equation11562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11563_implies_Equation2 (G : Type*) [Magma G] (h : Equation11563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11565_implies_Equation2 (G : Type*) [Magma G] (h : Equation11565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11566_implies_Equation2 (G : Type*) [Magma G] (h : Equation11566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11567_implies_Equation2 (G : Type*) [Magma G] (h : Equation11567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11568_implies_Equation2 (G : Type*) [Magma G] (h : Equation11568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11569_implies_Equation2 (G : Type*) [Magma G] (h : Equation11569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11571_implies_Equation2 (G : Type*) [Magma G] (h : Equation11571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X3)) ◇ ((X4 ◇ (X5 ◇ X3)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ X0)) = ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0))))) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X4 ◇ (X1 ◇ (X0 ◇ X4))) = X0 := superpose eq7 eq10
  have eq32 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0))))) = (X0 ◇ ((X5 ◇ (X6 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0))))))) ◇ (X3 ◇ (X4 ◇ X0)))) := superpose eq7 eq11
  have eq95 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq12 eq10
  have eq104 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X2 := superpose eq12 eq13
  have eq108 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) = (X2 ◇ X1) := superpose eq13 eq95
  have eq109 (X0 X3 X4 X5 X6 : G) : (X0 ◇ X4) = (X0 ◇ ((X5 ◇ (X6 ◇ (X0 ◇ X4))) ◇ (X3 ◇ (X4 ◇ X0)))) := superpose eq108 eq32
  have eq114 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq104 eq109
  have eq123 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) = X0 := superpose eq114 eq7
  have eq161 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq114 eq123
  have eq162 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq114 eq161
  have eq231 (X0 X2 : G) : X0 = X2 := superpose eq162 eq162
  have eq233 (X0 : G) : sK0 ≠ X0 := superpose eq231 eq8
  subsumption eq233 eq231


@[equational_result]
theorem Equation11572_implies_Equation2 (G : Type*) [Magma G] (h : Equation11572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X2 ◇ (X4 ◇ X0)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 X5 : G) : (X1 ◇ X0) = (X5 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ (X0 ◇ X3))) := superpose eq7 eq12
  have eq32 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq13
  have eq33 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) = X0 := superpose eq32 eq7
  have eq38 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq32 eq33
  have eq39 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq32 eq38
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq39 eq39
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq42 eq40


@[equational_result]
theorem Equation11573_implies_Equation2 (G : Type*) [Magma G] (h : Equation11573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (((X3 ◇ (X4 ◇ X0)) ◇ (X0 ◇ X4)) ◇ X5)) ◇ X0)) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X3 X4 : G) : (X4 ◇ (X3 ◇ X0)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 X5 : G) : (X5 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ (X0 ◇ X4))) = (X1 ◇ X0) := superpose eq7 eq12
  have eq32 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq13
  have eq34 (X0 X1 X3 X4 X5 : G) : (X1 ◇ ((((X3 ◇ (X4 ◇ X0)) ◇ (X0 ◇ X4)) ◇ X5) ◇ X0)) = X5 := superpose eq32 eq11
  have eq42 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq32 eq34
  have eq43 (X0 X3 : G) : X0 = X3 := superpose eq42 eq42
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq48 eq43


@[equational_result]
theorem Equation11574_implies_Equation2 (G : Type*) [Magma G] (h : Equation11574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 X5 : G) : (X4 ◇ (X5 ◇ X0)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X3 X4 X5 X6 : G) : (X1 ◇ X0) = (X6 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ (X0 ◇ X5))) := superpose eq7 eq12
  have eq33 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq14
  have eq34 (X0 X1 X2 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X4))) = X0 := superpose eq33 eq7
  have eq39 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X4)) = X0 := superpose eq33 eq34
  have eq40 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq33 eq39
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq40 eq40
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq43 eq41


@[equational_result]
theorem Equation11576_implies_Equation2 (G : Type*) [Magma G] (h : Equation11576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq45 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq47 eq45


@[equational_result]
theorem Equation11577_implies_Equation2 (G : Type*) [Magma G] (h : Equation11577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq81 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq81 eq8
  subsumption eq191 eq81


@[equational_result]
theorem Equation11578_implies_Equation2 (G : Type*) [Magma G] (h : Equation11578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ (X3 ◇ X5)) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X4) = (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X4 ◇ X0))))) := superpose eq7 eq7
  have eq27 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq10 eq10
  have eq88 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X4 ◇ ((X5 ◇ (((X6 ◇ X2) ◇ (X4 ◇ X3)) ◇ X7)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X1)))) = X7 := superpose eq9 eq7
  have eq91 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X3))) = X0 := superpose eq7 eq27
  have eq143 (X2 X4 X7 : G) : (X4 ◇ X2) = X7 := superpose eq91 eq88
  have eq216 (X0 X4 : G) : X0 = X4 := superpose eq7 eq143
  have eq380 (X0 : G) : sK0 ≠ X0 := superpose eq216 eq8
  subsumption eq380 eq216


@[equational_result]
theorem Equation11579_implies_Equation2 (G : Type*) [Magma G] (h : Equation11579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X5 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq64 eq19


@[equational_result]
theorem Equation11581_implies_Equation2 (G : Type*) [Magma G] (h : Equation11581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq62 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq191 eq62


@[equational_result]
theorem Equation11582_implies_Equation2 (G : Type*) [Magma G] (h : Equation11582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation11583_implies_Equation2 (G : Type*) [Magma G] (h : Equation11583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation11584_implies_Equation2 (G : Type*) [Magma G] (h : Equation11584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation11586_implies_Equation2 (G : Type*) [Magma G] (h : Equation11586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X2) = (X1 ◇ (X0 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X1))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X4))) ◇ X0) = X4 := superpose eq7 eq7
  have eq32 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0))) ◇ (X5 ◇ X4))) = X6 := superpose eq10 eq7
  have eq47 (X0 X1 X2 X6 X7 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X7))) ◇ X6) = X7 := superpose eq12 eq12
  have eq74 (X0 X4 X6 : G) : (X4 ◇ X0) = X6 := superpose eq47 eq32
  have eq76 (X0 X4 : G) : X0 = X4 := superpose eq7 eq74
  have eq213 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq213 eq76


@[equational_result]
theorem Equation11587_implies_Equation2 (G : Type*) [Magma G] (h : Equation11587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation11588_implies_Equation2 (G : Type*) [Magma G] (h : Equation11588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X5 ◇ X0)) ◇ (X5 ◇ X5)) = (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq38 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X3 ◇ ((X4 ◇ (((X5 ◇ X2) ◇ (X6 ◇ X6)) ◇ X7)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)))) = X7 := superpose eq9 eq7
  have eq47 (X2 X3 X7 : G) : (X3 ◇ X2) = X7 := superpose eq7 eq38
  have eq70 (X0 X4 : G) : X0 = X4 := superpose eq7 eq47
  have eq172 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq172 eq70


@[equational_result]
theorem Equation11589_implies_Equation2 (G : Type*) [Magma G] (h : Equation11589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation11591_implies_Equation2 (G : Type*) [Magma G] (h : Equation11591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) = X4 := superpose eq7 eq7
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq59 eq47


@[equational_result]
theorem Equation11592_implies_Equation2 (G : Type*) [Magma G] (h : Equation11592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation11593_implies_Equation2 (G : Type*) [Magma G] (h : Equation11593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq66 eq13


@[equational_result]
theorem Equation11594_implies_Equation2 (G : Type*) [Magma G] (h : Equation11594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation11595_implies_Equation2 (G : Type*) [Magma G] (h : Equation11595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation11597_implies_Equation2 (G : Type*) [Magma G] (h : Equation11597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3)) ◇ ((X4 ◇ X0) ◇ (X5 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X4 ◇ (X0 ◇ X1)))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3)) ◇ ((X4 ◇ (X5 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3)))) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X4 : G) : (X0 ◇ (X1 ◇ (X4 ◇ X0))) = X4 := superpose eq7 eq10
  have eq90 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ X0) = (X4 ◇ (X5 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0)))) := superpose eq11 eq12
  have eq118 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3)) = X5 := superpose eq90 eq9
  have eq166 (X0 X5 : G) : X0 = X5 := superpose eq118 eq118
  have eq199 (X0 : G) : sK0 ≠ X0 := superpose eq166 eq8
  subsumption eq199 eq166


@[equational_result]
theorem Equation11598_implies_Equation2 (G : Type*) [Magma G] (h : Equation11598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X4 ◇ X2))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X4 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X1)))) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X4 X5 : G) : (X0 ◇ (X1 ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq10
  have eq23 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ X0) := superpose eq13 eq12
  have eq25 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq23
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq119 eq51


@[equational_result]
theorem Equation11599_implies_Equation2 (G : Type*) [Magma G] (h : Equation11599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X4 ◇ (X3 ◇ (X1 ◇ X2))))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ (X1 ◇ (X4 ◇ (X5 ◇ (((X2 ◇ (X3 ◇ X1)) ◇ (X0 ◇ X3)) ◇ X6))))) = X4 := superpose eq7 eq10
  have eq22 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X1 := superpose eq10 eq10
  have eq26 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X1 ◇ (X4 ◇ (X5 ◇ X2)))) = X4 := superpose eq22 eq13
  have eq29 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ X3) = X4 := superpose eq26 eq10
  have eq33 (X0 X5 : G) : X0 = X5 := superpose eq7 eq29
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq46 eq33


@[equational_result]
theorem Equation11600_implies_Equation2 (G : Type*) [Magma G] (h : Equation11600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 X6 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X5 ◇ X6))) = X5 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq7
  have eq50 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq132 eq50


@[equational_result]
theorem Equation11602_implies_Equation2 (G : Type*) [Magma G] (h : Equation11602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11603_implies_Equation2 (G : Type*) [Magma G] (h : Equation11603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11604_implies_Equation2 (G : Type*) [Magma G] (h : Equation11604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11605_implies_Equation2 (G : Type*) [Magma G] (h : Equation11605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11607_implies_Equation2 (G : Type*) [Magma G] (h : Equation11607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11608_implies_Equation2 (G : Type*) [Magma G] (h : Equation11608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11609_implies_Equation2 (G : Type*) [Magma G] (h : Equation11609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11610_implies_Equation2 (G : Type*) [Magma G] (h : Equation11610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11612_implies_Equation2 (G : Type*) [Magma G] (h : Equation11612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11613_implies_Equation2 (G : Type*) [Magma G] (h : Equation11613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11614_implies_Equation2 (G : Type*) [Magma G] (h : Equation11614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11615_implies_Equation2 (G : Type*) [Magma G] (h : Equation11615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11617_implies_Equation2 (G : Type*) [Magma G] (h : Equation11617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11618_implies_Equation2 (G : Type*) [Magma G] (h : Equation11618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11619_implies_Equation2 (G : Type*) [Magma G] (h : Equation11619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11620_implies_Equation2 (G : Type*) [Magma G] (h : Equation11620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11621_implies_Equation2 (G : Type*) [Magma G] (h : Equation11621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11623_implies_Equation2 (G : Type*) [Magma G] (h : Equation11623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ X3)) = ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X3 := superpose eq11 eq7
  have eq68 (X0 X3 : G) : X0 = X3 := superpose eq7 eq28
  have eq170 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq170 eq68


@[equational_result]
theorem Equation11624_implies_Equation2 (G : Type*) [Magma G] (h : Equation11624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X1 ◇ X0) = (X2 ◇ (X4 ◇ X2)) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq158 eq53


@[equational_result]
theorem Equation11625_implies_Equation2 (G : Type*) [Magma G] (h : Equation11625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 X4 : G) : (X1 ◇ X0) = (X4 ◇ (X3 ◇ X4)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq150 eq55


@[equational_result]
theorem Equation11626_implies_Equation2 (G : Type*) [Magma G] (h : Equation11626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 X6 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X6))) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq133 eq49


@[equational_result]
theorem Equation11628_implies_Equation2 (G : Type*) [Magma G] (h : Equation11628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11629_implies_Equation2 (G : Type*) [Magma G] (h : Equation11629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11630_implies_Equation2 (G : Type*) [Magma G] (h : Equation11630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11631_implies_Equation2 (G : Type*) [Magma G] (h : Equation11631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11633_implies_Equation2 (G : Type*) [Magma G] (h : Equation11633 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11634_implies_Equation2 (G : Type*) [Magma G] (h : Equation11634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11635_implies_Equation2 (G : Type*) [Magma G] (h : Equation11635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11636_implies_Equation2 (G : Type*) [Magma G] (h : Equation11636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11638_implies_Equation2 (G : Type*) [Magma G] (h : Equation11638 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11639_implies_Equation2 (G : Type*) [Magma G] (h : Equation11639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11640_implies_Equation2 (G : Type*) [Magma G] (h : Equation11640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11641_implies_Equation2 (G : Type*) [Magma G] (h : Equation11641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11643_implies_Equation2 (G : Type*) [Magma G] (h : Equation11643 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11644_implies_Equation2 (G : Type*) [Magma G] (h : Equation11644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11645_implies_Equation2 (G : Type*) [Magma G] (h : Equation11645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11646_implies_Equation2 (G : Type*) [Magma G] (h : Equation11646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11647_implies_Equation2 (G : Type*) [Magma G] (h : Equation11647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11649_implies_Equation2 (G : Type*) [Magma G] (h : Equation11649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X1))) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq9 eq9
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq136 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq136 eq57


@[equational_result]
theorem Equation11650_implies_Equation2 (G : Type*) [Magma G] (h : Equation11650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X5 ◇ X2))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 : G) : (X2 ◇ (X4 ◇ X4)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq44 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq12 eq9
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq44
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation11651_implies_Equation2 (G : Type*) [Magma G] (h : Equation11651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X5 ◇ ((X3 ◇ (X4 ◇ X4)) ◇ (X0 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = X5 := superpose eq7 eq9
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq60 eq42


@[equational_result]
theorem Equation11652_implies_Equation2 (G : Type*) [Magma G] (h : Equation11652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation11654_implies_Equation2 (G : Type*) [Magma G] (h : Equation11654 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11655_implies_Equation2 (G : Type*) [Magma G] (h : Equation11655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11656_implies_Equation2 (G : Type*) [Magma G] (h : Equation11656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation11657_implies_Equation2 (G : Type*) [Magma G] (h : Equation11657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11659_implies_Equation2 (G : Type*) [Magma G] (h : Equation11659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11660_implies_Equation2 (G : Type*) [Magma G] (h : Equation11660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11661_implies_Equation2 (G : Type*) [Magma G] (h : Equation11661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11662_implies_Equation2 (G : Type*) [Magma G] (h : Equation11662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11664_implies_Equation2 (G : Type*) [Magma G] (h : Equation11664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11665_implies_Equation2 (G : Type*) [Magma G] (h : Equation11665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11666_implies_Equation2 (G : Type*) [Magma G] (h : Equation11666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation11667_implies_Equation2 (G : Type*) [Magma G] (h : Equation11667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11669_implies_Equation2 (G : Type*) [Magma G] (h : Equation11669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11670_implies_Equation2 (G : Type*) [Magma G] (h : Equation11670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11671_implies_Equation2 (G : Type*) [Magma G] (h : Equation11671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11672_implies_Equation2 (G : Type*) [Magma G] (h : Equation11672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11673_implies_Equation2 (G : Type*) [Magma G] (h : Equation11673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11675_implies_Equation2 (G : Type*) [Magma G] (h : Equation11675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X6 : G) : (X1 ◇ (X0 ◇ (X6 ◇ X1))) = X6 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq10 eq10
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq128 eq41


@[equational_result]
theorem Equation11676_implies_Equation2 (G : Type*) [Magma G] (h : Equation11676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 : G) : (X1 ◇ (X0 ◇ (X6 ◇ X2))) = X6 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation11677_implies_Equation2 (G : Type*) [Magma G] (h : Equation11677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 X5 X6 : G) : (X5 ◇ (X3 ◇ X6)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq126 eq53


@[equational_result]
theorem Equation11678_implies_Equation2 (G : Type*) [Magma G] (h : Equation11678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 X6 X7 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X7 ◇ ((X4 ◇ (X5 ◇ X6)) ◇ (X0 ◇ X6))))) = X7 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X7 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X0)) = X7 := superpose eq7 eq9
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq65 eq44


@[equational_result]
theorem Equation11679_implies_Equation2 (G : Type*) [Magma G] (h : Equation11679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X0 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X7 X8 : G) : (X1 ◇ (X0 ◇ (X7 ◇ X8))) = X7 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq49 (X0 X6 : G) : X0 = X6 := superpose eq7 eq16
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation11681_implies_Equation2 (G : Type*) [Magma G] (h : Equation11681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11682_implies_Equation2 (G : Type*) [Magma G] (h : Equation11682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11683_implies_Equation2 (G : Type*) [Magma G] (h : Equation11683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11684_implies_Equation2 (G : Type*) [Magma G] (h : Equation11684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11685_implies_Equation2 (G : Type*) [Magma G] (h : Equation11685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X1 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11687_implies_Equation2 (G : Type*) [Magma G] (h : Equation11687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11688_implies_Equation2 (G : Type*) [Magma G] (h : Equation11688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11689_implies_Equation2 (G : Type*) [Magma G] (h : Equation11689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11690_implies_Equation2 (G : Type*) [Magma G] (h : Equation11690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11691_implies_Equation2 (G : Type*) [Magma G] (h : Equation11691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11693_implies_Equation2 (G : Type*) [Magma G] (h : Equation11693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11694_implies_Equation2 (G : Type*) [Magma G] (h : Equation11694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11695_implies_Equation2 (G : Type*) [Magma G] (h : Equation11695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11696_implies_Equation2 (G : Type*) [Magma G] (h : Equation11696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation11697_implies_Equation2 (G : Type*) [Magma G] (h : Equation11697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X3 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11699_implies_Equation2 (G : Type*) [Magma G] (h : Equation11699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11700_implies_Equation2 (G : Type*) [Magma G] (h : Equation11700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11701_implies_Equation2 (G : Type*) [Magma G] (h : Equation11701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11702_implies_Equation2 (G : Type*) [Magma G] (h : Equation11702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation11703_implies_Equation2 (G : Type*) [Magma G] (h : Equation11703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11705_implies_Equation2 (G : Type*) [Magma G] (h : Equation11705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X5 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11706_implies_Equation2 (G : Type*) [Magma G] (h : Equation11706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X5 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11707_implies_Equation2 (G : Type*) [Magma G] (h : Equation11707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X5 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11708_implies_Equation2 (G : Type*) [Magma G] (h : Equation11708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X5 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11709_implies_Equation2 (G : Type*) [Magma G] (h : Equation11709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X5 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11710_implies_Equation2 (G : Type*) [Magma G] (h : Equation11710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X5 ◇ X6))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation11916_implies_Equation2 (G : Type*) [Magma G] (h : Equation11916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq7 eq30
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq117 eq45


@[equational_result]
theorem Equation11919_implies_Equation2 (G : Type*) [Magma G] (h : Equation11919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq39 eq13


@[equational_result]
theorem Equation11921_implies_Equation2 (G : Type*) [Magma G] (h : Equation11921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq33 eq14


@[equational_result]
theorem Equation11922_implies_Equation2 (G : Type*) [Magma G] (h : Equation11922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq7 eq17
  have eq165 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq165 eq59


@[equational_result]
theorem Equation11923_implies_Equation2 (G : Type*) [Magma G] (h : Equation11923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation11926_implies_Equation2 (G : Type*) [Magma G] (h : Equation11926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq99 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq99 eq29


@[equational_result]
theorem Equation11929_implies_Equation2 (G : Type*) [Magma G] (h : Equation11929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq100 eq29


@[equational_result]
theorem Equation11931_implies_Equation2 (G : Type*) [Magma G] (h : Equation11931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X3 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1)))))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ (((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X1))) ◇ X0)) = X3 := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (((((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq9
  have eq46 (X0 X2 : G) : X0 = X2 := superpose eq10 eq21
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq117 eq46


@[equational_result]
theorem Equation11932_implies_Equation2 (G : Type*) [Magma G] (h : Equation11932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X3))) = X1 := superpose eq7 eq7
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X0)) = X2 := superpose eq10 eq9
  have eq25 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X0) = X1 := superpose eq7 eq9
  have eq28 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq9 eq7
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ X0) = X1 := superpose eq10 eq25
  have eq36 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq28
  have eq37 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X1 ◇ X0)) = X2 := superpose eq36 eq24
  have eq42 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq37 eq33
  have eq44 (X0 X1 : G) : X0 = X1 := superpose eq10 eq42
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq82 eq44


@[equational_result]
theorem Equation11933_implies_Equation2 (G : Type*) [Magma G] (h : Equation11933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation11935_implies_Equation2 (G : Type*) [Magma G] (h : Equation11935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X2 ◇ X2) ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq9 eq9
  have eq41 (X0 X1 : G) : X0 = X1 := superpose eq10 eq15
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq95 eq41


@[equational_result]
theorem Equation11936_implies_Equation2 (G : Type*) [Magma G] (h : Equation11936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X3) ◇ (X0 ◇ X3))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq10
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq55 eq18


@[equational_result]
theorem Equation11937_implies_Equation2 (G : Type*) [Magma G] (h : Equation11937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X5))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq111 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq111 eq47


@[equational_result]
theorem Equation11939_implies_Equation2 (G : Type*) [Magma G] (h : Equation11939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq32 eq15


@[equational_result]
theorem Equation11940_implies_Equation2 (G : Type*) [Magma G] (h : Equation11940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (((X0 ◇ X0) ◇ X3) ◇ ((X2 ◇ X2) ◇ X3))))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq9
  have eq35 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq15 eq15
  have eq54 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq35 eq7
  have eq55 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X3))))) = X2 := superpose eq35 eq9
  have eq73 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq54 eq55
  have eq85 (X0 X1 : G) : X0 = X1 := superpose eq15 eq73
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq94 eq85


@[equational_result]
theorem Equation11941_implies_Equation2 (G : Type*) [Magma G] (h : Equation11941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X5))) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation11944_implies_Equation2 (G : Type*) [Magma G] (h : Equation11944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation11945_implies_Equation2 (G : Type*) [Magma G] (h : Equation11945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation11947_implies_Equation2 (G : Type*) [Magma G] (h : Equation11947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X1))) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq51 eq18


@[equational_result]
theorem Equation11948_implies_Equation2 (G : Type*) [Magma G] (h : Equation11948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation11949_implies_Equation2 (G : Type*) [Magma G] (h : Equation11949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation11950_implies_Equation2 (G : Type*) [Magma G] (h : Equation11950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation11953_implies_Equation2 (G : Type*) [Magma G] (h : Equation11953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq107 eq34


@[equational_result]
theorem Equation11956_implies_Equation2 (G : Type*) [Magma G] (h : Equation11956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq99 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq99 eq29


@[equational_result]
theorem Equation11958_implies_Equation2 (G : Type*) [Magma G] (h : Equation11958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1))))) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq9
  have eq208 (X0 X2 : G) : X0 = X2 := superpose eq7 eq17
  have eq229 (X0 : G) : sK0 ≠ X0 := superpose eq208 eq8
  subsumption eq229 eq208


@[equational_result]
theorem Equation11960_implies_Equation2 (G : Type*) [Magma G] (h : Equation11960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation11963_implies_Equation2 (G : Type*) [Magma G] (h : Equation11963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq104 eq32


@[equational_result]
theorem Equation11966_implies_Equation2 (G : Type*) [Magma G] (h : Equation11966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq102 eq31


@[equational_result]
theorem Equation11968_implies_Equation2 (G : Type*) [Magma G] (h : Equation11968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) = X0 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) ◇ X0)) = X1 := superpose eq7 eq9
  have eq34 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq11
  have eq72 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq34 eq7
  have eq73 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) := superpose eq34 eq7
  have eq116 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq72
  have eq136 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq116 eq73
  have eq139 (X0 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq136 eq11
  have eq163 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq7 eq139
  have eq197 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq163 eq136
  have eq230 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq197 eq163
  have eq239 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)))) = X1 := superpose eq230 eq16
  have eq322 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ X0) = X1 := superpose eq230 eq239
  have eq323 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq230 eq322
  have eq324 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq230 eq323
  have eq325 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq230 eq324
  have eq370 (X0 X2 : G) : X0 = X2 := superpose eq325 eq325
  have eq372 (X0 : G) : sK0 ≠ X0 := superpose eq370 eq8
  subsumption eq372 eq370


@[equational_result]
theorem Equation11970_implies_Equation2 (G : Type*) [Magma G] (h : Equation11970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation11972_implies_Equation2 (G : Type*) [Magma G] (h : Equation11972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X3) ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq9 eq9
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq10 eq14
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq108 eq37


@[equational_result]
theorem Equation11974_implies_Equation2 (G : Type*) [Magma G] (h : Equation11974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq10 eq11
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq36 eq29


@[equational_result]
theorem Equation11976_implies_Equation2 (G : Type*) [Magma G] (h : Equation11976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation11978_implies_Equation2 (G : Type*) [Magma G] (h : Equation11978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X5))) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq51 eq18


@[equational_result]
theorem Equation11982_implies_Equation2 (G : Type*) [Magma G] (h : Equation11982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq141 eq44


@[equational_result]
theorem Equation11984_implies_Equation2 (G : Type*) [Magma G] (h : Equation11984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X1))) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation11985_implies_Equation2 (G : Type*) [Magma G] (h : Equation11985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation11986_implies_Equation2 (G : Type*) [Magma G] (h : Equation11986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation11987_implies_Equation2 (G : Type*) [Magma G] (h : Equation11987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation11989_implies_Equation2 (G : Type*) [Magma G] (h : Equation11989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ (((X2 ◇ X3) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) := superpose eq9 eq9
  have eq35 (X0 X1 X2 X3 X4 : G) : (((((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X4) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2)))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq10
  have eq49 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ X2) := superpose eq10 eq17
  have eq98 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X3) = ((X3 ◇ X1) ◇ X3) := superpose eq7 eq49
  have eq232 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X3))) ◇ X3) := superpose eq7 eq98
  have eq244 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq17 eq98
  have eq315 (X0 X1 X2 X3 X4 : G) : (((((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X4) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2)))) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X0) = X2 := superpose eq244 eq35
  have eq320 (X0 X1 X2 X3 : G) : (((((X2 ◇ X3) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2)))) ◇ ((X2 ◇ X3) ◇ X2)) ◇ X0) = X2 := superpose eq49 eq315
  have eq321 (X0 X2 X3 : G) : ((X0 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X0) = X2 := superpose eq232 eq320
  have eq341 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq321 eq321
  have eq416 (X0 X2 : G) : X0 = X2 := superpose eq10 eq341
  have eq596 (X0 : G) : sK0 ≠ X0 := superpose eq416 eq8
  subsumption eq596 eq416


@[equational_result]
theorem Equation11990_implies_Equation2 (G : Type*) [Magma G] (h : Equation11990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq10
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq117 eq45


@[equational_result]
theorem Equation11991_implies_Equation2 (G : Type*) [Magma G] (h : Equation11991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq105 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq127 (X0 X4 : G) : X0 = X4 := superpose eq7 eq105
  have eq216 (X0 : G) : sK0 ≠ X0 := superpose eq127 eq8
  subsumption eq216 eq127


@[equational_result]
theorem Equation11993_implies_Equation2 (G : Type*) [Magma G] (h : Equation11993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9
  have eq17 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ X0) := superpose eq12 eq12
  have eq21 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = X0 := superpose eq12 eq17
  have eq38 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq21 eq7
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq38 eq38
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq55 eq48


@[equational_result]
theorem Equation11994_implies_Equation2 (G : Type*) [Magma G] (h : Equation11994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ (((X0 ◇ X3) ◇ X0) ◇ (X2 ◇ X3))))) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq7 eq9
  have eq36 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq7 eq17
  have eq39 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq17 eq17
  have eq43 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ X0)) = X1 := superpose eq17 eq7
  have eq52 (X0 X1 X2 : G) : (((((X0 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq17 eq9
  have eq56 (X0 X1 X2 : G) : ((((X0 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) = X1 := superpose eq36 eq52
  have eq57 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = X2 := superpose eq56 eq36
  have eq58 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq57 eq39
  have eq85 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq58 eq17
  have eq87 (X0 X1 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = X1 := superpose eq58 eq43
  have eq97 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq58 eq87
  have eq98 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq85 eq97
  have eq156 (X0 X2 : G) : X0 = X2 := superpose eq98 eq98
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq156 eq8
  subsumption eq164 eq156


@[equational_result]
theorem Equation11995_implies_Equation2 (G : Type*) [Magma G] (h : Equation11995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq43 eq16


@[equational_result]
theorem Equation11998_implies_Equation2 (G : Type*) [Magma G] (h : Equation11998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ ((((X0 ◇ X3) ◇ X0) ◇ (X3 ◇ X3)) ◇ (((X0 ◇ X3) ◇ X0) ◇ (X3 ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq9
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq12
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq7 eq16
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq153 eq56


@[equational_result]
theorem Equation11999_implies_Equation2 (G : Type*) [Magma G] (h : Equation11999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12001_implies_Equation2 (G : Type*) [Magma G] (h : Equation12001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq39 eq28


@[equational_result]
theorem Equation12002_implies_Equation2 (G : Type*) [Magma G] (h : Equation12002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation12003_implies_Equation2 (G : Type*) [Magma G] (h : Equation12003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X5 ◇ X5))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq9 eq9
  have eq37 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq138 eq37


@[equational_result]
theorem Equation12004_implies_Equation2 (G : Type*) [Magma G] (h : Equation12004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12006_implies_Equation2 (G : Type*) [Magma G] (h : Equation12006 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq9 eq9
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = (((((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)) ◇ X3) ◇ (((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1)) ◇ X0) ◇ ((((((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ X5) ◇ ((((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)) ◇ X3) ◇ (((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0))) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq11 eq11
  have eq45 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq13
  have eq105 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1)))) = X3 := superpose eq45 eq9
  have eq154 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq45 eq105
  have eq156 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq105
  have eq201 (X0 X1 X2 X3 X5 : G) : ((X1 ◇ X1) ◇ X1) = (((((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)) ◇ X3) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) ◇ (((((X1 ◇ X1) ◇ X1) ◇ X5) ◇ ((((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)) ◇ X3) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq156 eq30
  have eq233 (X0 X1 X2 X5 : G) : ((X1 ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ (((((X1 ◇ X1) ◇ X1) ◇ X5) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq156 eq201
  have eq234 (X0 X1 X2 X5 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (((((X1 ◇ X1) ◇ X1) ◇ X5) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq154 eq233
  have eq235 (X0 X1 X2 X5 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((((X1 ◇ X1) ◇ X5) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq154 eq234
  have eq236 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq154 eq235
  have eq237 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq154 eq236
  have eq238 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq154 eq237
  have eq355 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq45 eq238
  have eq395 (X0 X2 : G) : X0 = X2 := superpose eq355 eq355
  have eq490 (X0 : G) : sK0 ≠ X0 := superpose eq395 eq8
  subsumption eq490 eq395


@[equational_result]
theorem Equation12007_implies_Equation2 (G : Type*) [Magma G] (h : Equation12007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation12008_implies_Equation2 (G : Type*) [Magma G] (h : Equation12008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X5))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X0 ◇ X3) ◇ (X2 ◇ X1)) := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (X0 ◇ X2))) = X0 := superpose eq16 eq7
  have eq27 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq22 eq22
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq22 eq27
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq55 eq28


@[equational_result]
theorem Equation12010_implies_Equation2 (G : Type*) [Magma G] (h : Equation12010 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation12012_implies_Equation2 (G : Type*) [Magma G] (h : Equation12012 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X5))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq51 eq19


@[equational_result]
theorem Equation12016_implies_Equation2 (G : Type*) [Magma G] (h : Equation12016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X3) ◇ X2) ◇ (X3 ◇ X4)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq11 eq9
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq47 eq39


@[equational_result]
theorem Equation12018_implies_Equation2 (G : Type*) [Magma G] (h : Equation12018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X5 ◇ X1))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq61 eq19


@[equational_result]
theorem Equation12019_implies_Equation2 (G : Type*) [Magma G] (h : Equation12019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq60 eq13


@[equational_result]
theorem Equation12020_implies_Equation2 (G : Type*) [Magma G] (h : Equation12020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X4)) ◇ (X0 ◇ (X5 ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X4)) ◇ X5) = X2 := superpose eq11 eq10
  have eq15 (X2 X4 X5 : G) : (X4 ◇ X5) = X2 := superpose eq11 eq12
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation12021_implies_Equation2 (G : Type*) [Magma G] (h : Equation12021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation12024_implies_Equation2 (G : Type*) [Magma G] (h : Equation12024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X3) ◇ (X0 ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq9
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq51 eq17


@[equational_result]
theorem Equation12025_implies_Equation2 (G : Type*) [Magma G] (h : Equation12025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = (X1 ◇ X0) := superpose eq7 eq7
  have eq18 (X0 X1 X4 : G) : (X4 ◇ X1) = X0 := superpose eq7 eq12
  have eq50 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq115 eq50


@[equational_result]
theorem Equation12029_implies_Equation2 (G : Type*) [Magma G] (h : Equation12029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq57 eq18


@[equational_result]
theorem Equation12032_implies_Equation2 (G : Type*) [Magma G] (h : Equation12032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (((X0 ◇ X3) ◇ X3) ◇ (X3 ◇ X3))) ◇ ((((X0 ◇ X3) ◇ X3) ◇ (X3 ◇ X3)) ◇ (((X0 ◇ X3) ◇ X3) ◇ (X3 ◇ X3))))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (((X0 ◇ X3) ◇ X3) ◇ (X3 ◇ X3))) ◇ X0)) = X2 := superpose eq7 eq9
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq12
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq30 eq19


@[equational_result]
theorem Equation12033_implies_Equation2 (G : Type*) [Magma G] (h : Equation12033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation12035_implies_Equation2 (G : Type*) [Magma G] (h : Equation12035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq48 eq17


@[equational_result]
theorem Equation12036_implies_Equation2 (G : Type*) [Magma G] (h : Equation12036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq52 eq17


@[equational_result]
theorem Equation12037_implies_Equation2 (G : Type*) [Magma G] (h : Equation12037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ (((X0 ◇ X3) ◇ X3) ◇ (X4 ◇ X4))) ◇ (X5 ◇ X5))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X5))) = X2 := superpose eq7 eq9
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq52 eq18


@[equational_result]
theorem Equation12038_implies_Equation2 (G : Type*) [Magma G] (h : Equation12038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation12040_implies_Equation2 (G : Type*) [Magma G] (h : Equation12040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq10 eq10
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq119 eq41


@[equational_result]
theorem Equation12041_implies_Equation2 (G : Type*) [Magma G] (h : Equation12041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ X0)) = X2 := superpose eq7 eq7
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq45 eq27


@[equational_result]
theorem Equation12042_implies_Equation2 (G : Type*) [Magma G] (h : Equation12042 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (((X0 ◇ X4) ◇ X5) ◇ (X0 ◇ X5))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq10
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq58 eq18


@[equational_result]
theorem Equation12043_implies_Equation2 (G : Type*) [Magma G] (h : Equation12043 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X7))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation12045_implies_Equation2 (G : Type*) [Magma G] (h : Equation12045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation12046_implies_Equation2 (G : Type*) [Magma G] (h : Equation12046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X3))) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq59 eq18


@[equational_result]
theorem Equation12047_implies_Equation2 (G : Type*) [Magma G] (h : Equation12047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ (X1 ◇ X5))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation12048_implies_Equation2 (G : Type*) [Magma G] (h : Equation12048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X7))) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq59 eq19


@[equational_result]
theorem Equation12050_implies_Equation2 (G : Type*) [Magma G] (h : Equation12050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X1))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation12051_implies_Equation2 (G : Type*) [Magma G] (h : Equation12051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X3))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq61 eq19


@[equational_result]
theorem Equation12052_implies_Equation2 (G : Type*) [Magma G] (h : Equation12052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq48 eq15


@[equational_result]
theorem Equation12053_implies_Equation2 (G : Type*) [Magma G] (h : Equation12053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation12055_implies_Equation2 (G : Type*) [Magma G] (h : Equation12055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X1 ◇ ((X0 ◇ X5) ◇ (X5 ◇ X1))) = X2 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq60 eq22


@[equational_result]
theorem Equation12056_implies_Equation2 (G : Type*) [Magma G] (h : Equation12056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation12057_implies_Equation2 (G : Type*) [Magma G] (h : Equation12057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation12058_implies_Equation2 (G : Type*) [Magma G] (h : Equation12058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation12060_implies_Equation2 (G : Type*) [Magma G] (h : Equation12060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : (X1 ◇ (X0 ◇ (X7 ◇ X1))) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation12061_implies_Equation2 (G : Type*) [Magma G] (h : Equation12061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation12062_implies_Equation2 (G : Type*) [Magma G] (h : Equation12062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation12063_implies_Equation2 (G : Type*) [Magma G] (h : Equation12063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation12064_implies_Equation2 (G : Type*) [Magma G] (h : Equation12064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation12067_implies_Equation2 (G : Type*) [Magma G] (h : Equation12067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq105 eq32


@[equational_result]
theorem Equation12070_implies_Equation2 (G : Type*) [Magma G] (h : Equation12070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq105 eq32


@[equational_result]
theorem Equation12072_implies_Equation2 (G : Type*) [Magma G] (h : Equation12072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X1)) = (X1 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X1))) ◇ (X3 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X1)) ◇ ((((((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq10 eq9
  have eq78 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq29 eq29
  have eq112 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq7 eq78
  have eq264 (X0 X3 : G) : X0 = X3 := superpose eq7 eq112
  have eq461 (X0 : G) : sK0 ≠ X0 := superpose eq264 eq8
  subsumption eq461 eq264


@[equational_result]
theorem Equation12074_implies_Equation2 (G : Type*) [Magma G] (h : Equation12074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation12077_implies_Equation2 (G : Type*) [Magma G] (h : Equation12077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq146 eq38


@[equational_result]
theorem Equation12080_implies_Equation2 (G : Type*) [Magma G] (h : Equation12080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq52 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq165 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq165 eq52


@[equational_result]
theorem Equation12082_implies_Equation2 (G : Type*) [Magma G] (h : Equation12082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ ((((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ X3) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1))) ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1))) ◇ (X3 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)))) = ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X4 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1))))) := superpose eq7 eq9
  have eq26 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X2 ◇ X1)) = X0 := superpose eq7 eq9
  have eq31 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X4 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq9 eq7
  have eq37 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X1)) ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X1))) ◇ X2) = ((((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X1)) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X1))) ◇ X2)) := superpose eq10 eq10
  have eq59 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1))) ◇ X0))) = X3 := superpose eq37 eq10
  have eq80 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := superpose eq9 eq26
  have eq97 (X0 X1 X3 : G) : (X3 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := superpose eq80 eq31
  have eq148 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X1) := superpose eq97 eq97
  have eq212 (X0 X1 X2 X3 : G) : (X3 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1))) = X0 := superpose eq7 eq148
  have eq302 (X0 X1 X2 X4 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X4 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1))))) = ((((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1))) ◇ X0) := superpose eq212 eq19
  have eq305 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X0))) = X3 := superpose eq212 eq59
  have eq325 (X0 X1 X2 X4 : G) : (X0 ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X4 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1))))) := superpose eq212 eq302
  have eq326 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq212 eq325
  have eq331 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X0)) = X3 := superpose eq326 eq305
  have eq388 (X0 X4 : G) : X0 = X4 := superpose eq331 eq331
  have eq440 (X0 : G) : sK0 ≠ X0 := superpose eq388 eq8
  subsumption eq440 eq388


@[equational_result]
theorem Equation12084_implies_Equation2 (G : Type*) [Magma G] (h : Equation12084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation12086_implies_Equation2 (G : Type*) [Magma G] (h : Equation12086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq10 eq10
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq109 eq42


@[equational_result]
theorem Equation12088_implies_Equation2 (G : Type*) [Magma G] (h : Equation12088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq10 eq11
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq36 eq29


@[equational_result]
theorem Equation12090_implies_Equation2 (G : Type*) [Magma G] (h : Equation12090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq60 eq14


@[equational_result]
theorem Equation12092_implies_Equation2 (G : Type*) [Magma G] (h : Equation12092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X5))) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq51 eq18


@[equational_result]
theorem Equation12096_implies_Equation2 (G : Type*) [Magma G] (h : Equation12096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq11
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq169 eq65


@[equational_result]
theorem Equation12098_implies_Equation2 (G : Type*) [Magma G] (h : Equation12098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X1))) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq79 eq18


@[equational_result]
theorem Equation12099_implies_Equation2 (G : Type*) [Magma G] (h : Equation12099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq78 eq13


@[equational_result]
theorem Equation12100_implies_Equation2 (G : Type*) [Magma G] (h : Equation12100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation12101_implies_Equation2 (G : Type*) [Magma G] (h : Equation12101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation12104_implies_Equation2 (G : Type*) [Magma G] (h : Equation12104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq142 eq37


@[equational_result]
theorem Equation12107_implies_Equation2 (G : Type*) [Magma G] (h : Equation12107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq10
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq161 eq51


@[equational_result]
theorem Equation12109_implies_Equation2 (G : Type*) [Magma G] (h : Equation12109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ (X2 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X3 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) ◇ ((((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X1))) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq50 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X3 := superpose eq9 eq10
  have eq136 (X0 X2 : G) : X0 = X2 := superpose eq7 eq50
  have eq176 (X0 : G) : sK0 ≠ X0 := superpose eq136 eq8
  subsumption eq176 eq136


@[equational_result]
theorem Equation12110_implies_Equation2 (G : Type*) [Magma G] (h : Equation12110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq7
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq156 eq49


@[equational_result]
theorem Equation12111_implies_Equation2 (G : Type*) [Magma G] (h : Equation12111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq41 eq12


@[equational_result]
theorem Equation12114_implies_Equation2 (G : Type*) [Magma G] (h : Equation12114 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation12116_implies_Equation2 (G : Type*) [Magma G] (h : Equation12116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation12117_implies_Equation2 (G : Type*) [Magma G] (h : Equation12117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12119_implies_Equation2 (G : Type*) [Magma G] (h : Equation12119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12120_implies_Equation2 (G : Type*) [Magma G] (h : Equation12120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation12121_implies_Equation2 (G : Type*) [Magma G] (h : Equation12121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12123_implies_Equation2 (G : Type*) [Magma G] (h : Equation12123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X1))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq9 eq9
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq80 eq41


@[equational_result]
theorem Equation12124_implies_Equation2 (G : Type*) [Magma G] (h : Equation12124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X3) ◇ (X0 ◇ X3))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq43 (X0 X1 X2 : G) : (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq18 eq18
  have eq67 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X2 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1))))) = X2 := superpose eq18 eq9
  have eq73 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = X2 := superpose eq43 eq67
  have eq106 (X0 X3 : G) : X0 = X3 := superpose eq73 eq73
  have eq206 (X0 : G) : sK0 ≠ X0 := superpose eq106 eq8
  subsumption eq206 eq106


@[equational_result]
theorem Equation12125_implies_Equation2 (G : Type*) [Magma G] (h : Equation12125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq49 eq30


@[equational_result]
theorem Equation12127_implies_Equation2 (G : Type*) [Magma G] (h : Equation12127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation12128_implies_Equation2 (G : Type*) [Magma G] (h : Equation12128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12129_implies_Equation2 (G : Type*) [Magma G] (h : Equation12129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12131_implies_Equation2 (G : Type*) [Magma G] (h : Equation12131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12132_implies_Equation2 (G : Type*) [Magma G] (h : Equation12132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12133_implies_Equation2 (G : Type*) [Magma G] (h : Equation12133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12135_implies_Equation2 (G : Type*) [Magma G] (h : Equation12135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12136_implies_Equation2 (G : Type*) [Magma G] (h : Equation12136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12137_implies_Equation2 (G : Type*) [Magma G] (h : Equation12137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12138_implies_Equation2 (G : Type*) [Magma G] (h : Equation12138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12140_implies_Equation2 (G : Type*) [Magma G] (h : Equation12140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ (X3 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) ◇ X1) ◇ X0)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X2) ◇ X0)) = X2 := superpose eq9 eq9
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) := superpose eq9 eq9
  have eq39 (X0 X1 X2 X3 X4 : G) : ((((((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) ◇ X2) ◇ (X4 ◇ X0)) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) ◇ X2)) = X0 := superpose eq11 eq16
  have eq43 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ X2) := superpose eq11 eq16
  have eq60 (X0 X2 X4 : G) : ((((X2 ◇ X0) ◇ X2) ◇ (X4 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := superpose eq43 eq39
  have eq79 (X0 X1 X2 X3 : G) : (X3 ◇ (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X3 ◇ (X0 ◇ X1))) ◇ X0)) = (((((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X3 ◇ (X0 ◇ X1))) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X3 ◇ (X0 ◇ X1))) ◇ X0)) := superpose eq10 eq16
  have eq116 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X2) := superpose eq15 eq16
  have eq123 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1))) := superpose eq116 eq10
  have eq126 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X0)) = ((((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X3 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X0)) := superpose eq116 eq79
  have eq149 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = (X3 ◇ ((X0 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X0)) := superpose eq60 eq126
  have eq151 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq149 eq123
  have eq188 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) ◇ X3) ◇ X1) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq7 eq151
  have eq190 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (((X0 ◇ X2) ◇ X4) ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq151 eq151
  have eq194 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = X1 := superpose eq151 eq7
  have eq202 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X4) ◇ X1) = ((X1 ◇ (X0 ◇ X2)) ◇ ((((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (((X0 ◇ X2) ◇ X4) ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq151 eq7
  have eq212 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ X0) := superpose eq116 eq188
  have eq215 (X0 X1 X2 X4 : G) : (((X0 ◇ X2) ◇ X4) ◇ X1) = ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := superpose eq190 eq202
  have eq216 (X0 X1 X2 X4 : G) : (((X0 ◇ X2) ◇ X4) ◇ X1) = X0 := superpose eq194 eq215
  have eq218 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq216 eq212
  have eq262 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq218 eq116
  have eq270 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq262 eq216
  have eq289 (X0 X3 : G) : X0 = X3 := superpose eq270 eq270
  have eq294 (X0 : G) : sK0 ≠ X0 := superpose eq289 eq8
  subsumption eq294 eq289


@[equational_result]
theorem Equation12142_implies_Equation2 (G : Type*) [Magma G] (h : Equation12142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq31 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq31
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq112 eq39


@[equational_result]
theorem Equation12144_implies_Equation2 (G : Type*) [Magma G] (h : Equation12144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq10 eq7
  have eq36 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (X1 ◇ X0) := superpose eq13 eq13
  have eq41 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq13 eq10
  have eq46 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq41
  have eq60 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq9 eq25
  have eq80 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq60 eq46
  have eq83 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) = X0 := superpose eq80 eq7
  have eq91 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq80 eq36
  have eq105 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq80 eq91
  have eq106 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq105 eq83
  have eq123 (X0 X2 : G) : X0 = X2 := superpose eq106 eq106
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq123 eq8
  subsumption eq125 eq123


@[equational_result]
theorem Equation12145_implies_Equation2 (G : Type*) [Magma G] (h : Equation12145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq110 eq33


@[equational_result]
theorem Equation12146_implies_Equation2 (G : Type*) [Magma G] (h : Equation12146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq28 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq37 (X0 X4 : G) : X0 = X4 := superpose eq7 eq28
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq148 eq37


@[equational_result]
theorem Equation12149_implies_Equation2 (G : Type*) [Magma G] (h : Equation12149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X3 ◇ X3)) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X3) ◇ (X4 ◇ (X1 ◇ X1))) = (((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X4) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) := superpose eq10 eq10
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X1 := superpose eq10 eq7
  have eq34 (X0 X1 X2 X3 : G) : (X0 ◇ ((((((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X1) ◇ X3) ◇ (X1 ◇ X1)) ◇ (X3 ◇ X3))) = X2 := superpose eq10 eq7
  have eq42 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (((((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X2)) ◇ X4) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1)))) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X2)) ◇ X4) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1))))))) = X5 := superpose eq10 eq9
  have eq44 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X3) ◇ (((X3 ◇ X3) ◇ X4) ◇ (((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X1 ◇ X1))))) = X4 := superpose eq10 eq9
  have eq52 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X1))) ◇ X3) ◇ (X2 ◇ X4)) ◇ (X3 ◇ X3)) = X4 := superpose eq10 eq9
  have eq60 (X2 X3 X4 : G) : (((X2 ◇ X3) ◇ (X2 ◇ X4)) ◇ (X3 ◇ X3)) = X4 := superpose eq7 eq52
  have eq72 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X4) ◇ X1) = ((X3 ◇ X4) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := superpose eq10 eq28
  have eq92 (X0 X1 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ ((((X3 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1)))) ◇ X3))) = X5 := superpose eq72 eq42
  have eq97 (X0 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (X3 ◇ X3))) = X5 := superpose eq28 eq92
  have eq105 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X3) ◇ (((X3 ◇ X3) ◇ X4) ◇ (X1 ◇ (X2 ◇ X2)))) = X4 := superpose eq97 eq44
  have eq108 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X3) ◇ (X4 ◇ (X1 ◇ X1))) = X3 := superpose eq97 eq14
  have eq123 (X0 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X3) ◇ X4) = X4 := superpose eq108 eq105
  have eq126 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X3) ◇ (X1 ◇ X1)) ◇ (X3 ◇ X3))) = X2 := superpose eq123 eq34
  have eq147 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq60 eq126
  have eq148 (X0 X3 : G) : X0 = X3 := superpose eq28 eq147
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq148 eq8
  subsumption eq161 eq148


@[equational_result]
theorem Equation12150_implies_Equation2 (G : Type*) [Magma G] (h : Equation12150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X4) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X3)) ◇ X5))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X4 X5 : G) : (X1 ◇ ((X0 ◇ X4) ◇ X5)) = X4 := superpose eq7 eq11
  have eq21 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X3)) = X4 := superpose eq12 eq9
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq48 eq26


@[equational_result]
theorem Equation12152_implies_Equation2 (G : Type*) [Magma G] (h : Equation12152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ ((X0 ◇ X4) ◇ (X5 ◇ X1))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X4 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X5 ◇ X1))) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq9
  have eq39 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X1)) ◇ X4) ◇ X5) ◇ X6) ◇ (X7 ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X1)) ◇ X4))) = ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X1)) ◇ (X6 ◇ X0)) := superpose eq7 eq10
  have eq71 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X1)) ◇ X4) ◇ X5) ◇ X6) ◇ (X7 ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X1)) ◇ X4))) = X1 := superpose eq16 eq39
  have eq72 (X1 X5 X6 X7 : G) : (((X1 ◇ X5) ◇ X6) ◇ (X7 ◇ X1)) = X1 := superpose eq16 eq71
  have eq74 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq72 eq7
  have eq107 (X0 X2 : G) : X0 = X2 := superpose eq74 eq74
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq109 eq107


@[equational_result]
theorem Equation12153_implies_Equation2 (G : Type*) [Magma G] (h : Equation12153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation12154_implies_Equation2 (G : Type*) [Magma G] (h : Equation12154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ ((X0 ◇ X4) ◇ (X5 ◇ X5))) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq9 eq9
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq146 eq35


@[equational_result]
theorem Equation12155_implies_Equation2 (G : Type*) [Magma G] (h : Equation12155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12157_implies_Equation2 (G : Type*) [Magma G] (h : Equation12157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1))) ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq9 eq9
  have eq24 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = ((((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0) ◇ ((((((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0) ◇ X4) ◇ (((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) ◇ X2)) := superpose eq9 eq10
  have eq39 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq12
  have eq82 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq39 eq7
  have eq133 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq9 eq82
  have eq134 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq12 eq82
  have eq155 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = ((((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq133 eq24
  have eq165 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq133 eq10
  have eq175 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (((X0 ◇ X0) ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq133 eq155
  have eq203 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) ◇ ((((X3 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq39 eq165
  have eq234 (X0 X1 X2 : G) : (X1 ◇ X1) = (((((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) := superpose eq134 eq203
  have eq240 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq39 eq133
  have eq304 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq240 eq234
  have eq359 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ X2)) := superpose eq304 eq175
  have eq379 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq304 eq359
  have eq380 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X2 := superpose eq240 eq379
  have eq383 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq380 eq9
  have eq433 (X0 X2 : G) : X0 = X2 := superpose eq383 eq383
  have eq435 (X0 : G) : sK0 ≠ X0 := superpose eq433 eq8
  subsumption eq435 eq433


@[equational_result]
theorem Equation12158_implies_Equation2 (G : Type*) [Magma G] (h : Equation12158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X2) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = (X1 ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq7 eq9
  have eq20 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X0)) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq7 eq9
  have eq44 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) = ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq7 eq19
  have eq47 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq19 eq19
  have eq59 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq19 eq7
  have eq60 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq19 eq9
  have eq63 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq19 eq59
  have eq64 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X2 ◇ X0)) = X1 := superpose eq63 eq20
  have eq65 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ X1)) := superpose eq60 eq44
  have eq70 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq65 eq47
  have eq95 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq70 eq19
  have eq107 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) := superpose eq70 eq11
  have eq152 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq107 eq64
  have eq161 (X0 X2 : G) : X0 = X2 := superpose eq95 eq152
  have eq213 (X0 : G) : sK0 ≠ X0 := superpose eq161 eq8
  subsumption eq213 eq161


@[equational_result]
theorem Equation12159_implies_Equation2 (G : Type*) [Magma G] (h : Equation12159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq51 eq30


@[equational_result]
theorem Equation12161_implies_Equation2 (G : Type*) [Magma G] (h : Equation12161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12162_implies_Equation2 (G : Type*) [Magma G] (h : Equation12162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation12163_implies_Equation2 (G : Type*) [Magma G] (h : Equation12163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12165_implies_Equation2 (G : Type*) [Magma G] (h : Equation12165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12166_implies_Equation2 (G : Type*) [Magma G] (h : Equation12166 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12167_implies_Equation2 (G : Type*) [Magma G] (h : Equation12167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12169_implies_Equation2 (G : Type*) [Magma G] (h : Equation12169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12170_implies_Equation2 (G : Type*) [Magma G] (h : Equation12170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12171_implies_Equation2 (G : Type*) [Magma G] (h : Equation12171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12172_implies_Equation2 (G : Type*) [Magma G] (h : Equation12172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12175_implies_Equation2 (G : Type*) [Magma G] (h : Equation12175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ (X0 ◇ X3))) ◇ (((X2 ◇ X3) ◇ X3) ◇ (X0 ◇ X3))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X2) ◇ X2) = (X1 ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) = (((X0 ◇ X1) ◇ X3) ◇ X3) := superpose eq11 eq11
  have eq20 (X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X3) ◇ X3)) = X2 := superpose eq16 eq10
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq11 eq20
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2) := superpose eq20 eq7
  have eq66 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) = X1 := superpose eq7 eq9
  have eq67 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) = (X1 ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) := superpose eq26 eq9
  have eq83 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) = X1 := superpose eq66 eq67
  have eq84 (X0 X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ X0) := superpose eq83 eq27
  have eq86 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq7 eq84
  have eq193 (X0 X3 : G) : X0 = X3 := superpose eq7 eq86
  have eq341 (X0 : G) : sK0 ≠ X0 := superpose eq193 eq8
  subsumption eq341 eq193


@[equational_result]
theorem Equation12176_implies_Equation2 (G : Type*) [Magma G] (h : Equation12176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation12178_implies_Equation2 (G : Type*) [Magma G] (h : Equation12178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12179_implies_Equation2 (G : Type*) [Magma G] (h : Equation12179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation12180_implies_Equation2 (G : Type*) [Magma G] (h : Equation12180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12182_implies_Equation2 (G : Type*) [Magma G] (h : Equation12182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12183_implies_Equation2 (G : Type*) [Magma G] (h : Equation12183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12184_implies_Equation2 (G : Type*) [Magma G] (h : Equation12184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12186_implies_Equation2 (G : Type*) [Magma G] (h : Equation12186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12187_implies_Equation2 (G : Type*) [Magma G] (h : Equation12187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12188_implies_Equation2 (G : Type*) [Magma G] (h : Equation12188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12189_implies_Equation2 (G : Type*) [Magma G] (h : Equation12189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12191_implies_Equation2 (G : Type*) [Magma G] (h : Equation12191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X1))) = X5 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq10 eq10
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq106 eq38


@[equational_result]
theorem Equation12192_implies_Equation2 (G : Type*) [Magma G] (h : Equation12192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X4) ◇ (X5 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X2))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X2))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X4 X5 : G) : (X1 ◇ ((X0 ◇ X4) ◇ X0)) = X5 := superpose eq10 eq9
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq50 eq30


@[equational_result]
theorem Equation12193_implies_Equation2 (G : Type*) [Magma G] (h : Equation12193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X1 ◇ ((X0 ◇ X4) ◇ (X5 ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X0 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ X0)) = X5 := superpose eq9 eq10
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq50 eq18


@[equational_result]
theorem Equation12194_implies_Equation2 (G : Type*) [Magma G] (h : Equation12194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X6 X7 : G) : (X1 ◇ (X0 ◇ (X6 ◇ X7))) = X6 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq119 eq36


@[equational_result]
theorem Equation12196_implies_Equation2 (G : Type*) [Magma G] (h : Equation12196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12197_implies_Equation2 (G : Type*) [Magma G] (h : Equation12197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12198_implies_Equation2 (G : Type*) [Magma G] (h : Equation12198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12199_implies_Equation2 (G : Type*) [Magma G] (h : Equation12199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12201_implies_Equation2 (G : Type*) [Magma G] (h : Equation12201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12202_implies_Equation2 (G : Type*) [Magma G] (h : Equation12202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12203_implies_Equation2 (G : Type*) [Magma G] (h : Equation12203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12204_implies_Equation2 (G : Type*) [Magma G] (h : Equation12204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12206_implies_Equation2 (G : Type*) [Magma G] (h : Equation12206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12207_implies_Equation2 (G : Type*) [Magma G] (h : Equation12207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12208_implies_Equation2 (G : Type*) [Magma G] (h : Equation12208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12209_implies_Equation2 (G : Type*) [Magma G] (h : Equation12209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12211_implies_Equation2 (G : Type*) [Magma G] (h : Equation12211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12212_implies_Equation2 (G : Type*) [Magma G] (h : Equation12212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12213_implies_Equation2 (G : Type*) [Magma G] (h : Equation12213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12214_implies_Equation2 (G : Type*) [Magma G] (h : Equation12214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12215_implies_Equation2 (G : Type*) [Magma G] (h : Equation12215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12217_implies_Equation2 (G : Type*) [Magma G] (h : Equation12217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X0) ◇ (X0 ◇ X2)) = (X1 ◇ ((X0 ◇ (((X3 ◇ X0) ◇ X0) ◇ (X0 ◇ X2))) ◇ ((((X3 ◇ X0) ◇ X0) ◇ (X0 ◇ X2)) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X2)) ◇ (((X3 ◇ X2) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4)))) ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4)))) ◇ ((((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4))) ◇ X4)) ◇ X0) = X4 := superpose eq7 eq10
  have eq21 (X0 X1 X3 X4 : G) : (((X4 ◇ X0) ◇ X0) ◇ X3) = (X1 ◇ ((X0 ◇ (((X4 ◇ X0) ◇ X0) ◇ X3)) ◇ ((((X4 ◇ X0) ◇ X0) ◇ X3) ◇ X1))) := superpose eq10 eq7
  have eq43 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X2))) := superpose eq7 eq9
  have eq56 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X0)) = ((((X3 ◇ X0) ◇ X0) ◇ X2) ◇ ((X2 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X0))) ◇ X0)) := superpose eq10 eq9
  have eq85 (X0 X1 X2 X3 : G) : ((X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X2)) ◇ (((X3 ◇ X2) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)))) = X2 := superpose eq43 eq7
  have eq104 (X0 X2 X4 : G) : (X4 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X4))) = X0 := superpose eq7 eq21
  have eq154 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0) := superpose eq104 eq104
  have eq191 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4)))) ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4)))) ◇ ((((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4))) ◇ X4)) = (X0 ◇ (((((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4))) ◇ (((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4)))) ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4)))) ◇ ((((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4))) ◇ X4))) ◇ X4)) := superpose eq7 eq56
  have eq212 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X3) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) = ((((X4 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X3))) ◇ (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X3))) ◇ X3) ◇ ((X3 ◇ (((X2 ◇ X3) ◇ X3) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X3)))) := superpose eq43 eq56
  have eq255 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ X2) := superpose eq10 eq154
  have eq259 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) ◇ X2) = ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) ◇ X2) := superpose eq56 eq154
  have eq260 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X2)) = ((((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq43 eq154
  have eq296 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) = (((X3 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X3))) ◇ X3) ◇ ((X3 ◇ (((X2 ◇ X3) ◇ X3) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X3)))) := superpose eq255 eq212
  have eq321 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) = (((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X3) ◇ ((X3 ◇ (((X2 ◇ X3) ◇ X3) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)))) ◇ (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X3)))) := superpose eq154 eq296
  have eq332 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) ◇ X2) := superpose eq154 eq259
  have eq343 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4)))) ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4)))) ◇ ((((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4))) ◇ X4)) = (X0 ◇ ((((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4))) ◇ X4)) := superpose eq332 eq191
  have eq354 (X0 X2 X3 X4 : G) : ((X0 ◇ ((((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4))) ◇ X4)) ◇ X0) = X4 := superpose eq343 eq19
  have eq397 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X2 := superpose eq354 eq104
  have eq399 (X0 X1 X4 : G) : ((X1 ◇ (X4 ◇ X0)) ◇ X1) = X0 := superpose eq354 eq154
  have eq410 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) = X1 := superpose eq397 eq321
  have eq411 (X0 X1 X2 : G) : ((X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X2)) ◇ X1) = X2 := superpose eq410 eq85
  have eq412 (X0 X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) ◇ X2)) := superpose eq399 eq260
  have eq428 (X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = X2 := superpose eq412 eq411
  have eq472 (X0 X2 : G) : X0 = X2 := superpose eq428 eq428
  have eq591 (X0 : G) : sK0 ≠ X0 := superpose eq472 eq8
  subsumption eq591 eq472


@[equational_result]
theorem Equation12218_implies_Equation2 (G : Type*) [Magma G] (h : Equation12218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((((((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq33 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((((X0 ◇ (((X3 ◇ X0) ◇ X0) ◇ (X0 ◇ X3))) ◇ ((((X3 ◇ X0) ◇ X0) ◇ (X0 ◇ X3)) ◇ X2)) ◇ X4) ◇ X4) ◇ (((X3 ◇ X0) ◇ X0) ◇ (X0 ◇ X3)))) = X4 := superpose eq7 eq11
  have eq69 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq33
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq7 eq69
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq164 eq70


@[equational_result]
theorem Equation12219_implies_Equation2 (G : Type*) [Magma G] (h : Equation12219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X0) = (X1 ◇ X0) := superpose eq7 eq7
  have eq30 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) = X1 := superpose eq12 eq7
  have eq41 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq12 eq11
  have eq57 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ (X1 ◇ X2))) = X1 := superpose eq41 eq30
  have eq60 (X1 X2 X3 : G) : (X3 ◇ X2) = X1 := superpose eq41 eq57
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq11 eq60
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq110 eq61


@[equational_result]
theorem Equation12221_implies_Equation2 (G : Type*) [Magma G] (h : Equation12221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X0) ◇ (X2 ◇ X2)) = (X1 ◇ ((X0 ◇ (((X3 ◇ X0) ◇ X0) ◇ (X2 ◇ X2))) ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq7 eq9
  have eq19 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) ◇ (((X2 ◇ X0) ◇ X0) ◇ ((X2 ◇ X0) ◇ X0))) = X0 := superpose eq7 eq12
  have eq23 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq12 eq7
  have eq36 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq23
  have eq38 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) := superpose eq12 eq23
  have eq46 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq36 eq19
  have eq367 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq36 eq36
  have eq379 (X0 X1 X2 : G) : (X2 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X2))) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := superpose eq36 eq12
  have eq402 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq7 eq379
  have eq410 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X1 := superpose eq46 eq46
  have eq439 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq36 eq410
  have eq444 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X2))) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq439 eq12
  have eq455 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq439 eq38
  have eq540 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = (X2 ◇ (X0 ◇ X2)) := superpose eq439 eq444
  have eq555 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = X0 := superpose eq455 eq540
  have eq557 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq555 eq402
  have eq558 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq555 eq367
  have eq587 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq439 eq558
  have eq588 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq557 eq587
  have eq589 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq588 eq555
  have eq669 (X0 X2 : G) : X0 = X2 := superpose eq589 eq589
  have eq671 (X0 : G) : sK0 ≠ X0 := superpose eq669 eq8
  subsumption eq671 eq669


@[equational_result]
theorem Equation12223_implies_Equation2 (G : Type*) [Magma G] (h : Equation12223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq50 eq18


@[equational_result]
theorem Equation12225_implies_Equation2 (G : Type*) [Magma G] (h : Equation12225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X0) ◇ (X3 ◇ X2)) = (X1 ◇ ((X0 ◇ (((X3 ◇ X0) ◇ X0) ◇ (X3 ◇ X2))) ◇ (X2 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) ◇ (((X2 ◇ X3) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ ((((X2 ◇ ((((X2 ◇ X1) ◇ X1) ◇ X0) ◇ X0)) ◇ X3) ◇ X3) ◇ X0)) = X3 := superpose eq11 eq7
  have eq20 (X0 X1 X2 X3 : G) : ((X0 ◇ (((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X1) ◇ X2)) ◇ (((X2 ◇ X3) ◇ X3) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1))) = X3 := superpose eq10 eq10
  have eq36 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X1) := superpose eq10 eq11
  have eq54 (X0 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq36 eq11
  have eq71 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq7 eq9
  have eq122 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) = ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq71 eq71
  have eq126 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := superpose eq71 eq7
  have eq183 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3) ◇ X3) ◇ X1)) = X3 := superpose eq126 eq10
  have eq226 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq11 eq15
  have eq262 (X0 X1 : G) : (X0 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X0 := superpose eq36 eq226
  have eq265 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose eq10 eq226
  have eq292 (X0 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq265 eq54
  have eq309 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq226 eq292
  have eq311 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) = (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq309 eq122
  have eq328 (X1 X2 : G) : (((X2 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) = X1 := superpose eq7 eq311
  have eq329 (X0 X2 : G) : (X2 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq328 eq71
  have eq383 (X0 X1 X3 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (((X0 ◇ X3) ◇ X3) ◇ X1)) = X3 := superpose eq329 eq183
  have eq401 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq383 eq262
  have eq402 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X2)) ◇ (((X2 ◇ X3) ◇ X3) ◇ ((X1 ◇ X0) ◇ X0))) = X3 := superpose eq401 eq20
  have eq531 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X2)) ◇ ((X2 ◇ X3) ◇ X3)) = X3 := superpose eq401 eq402
  have eq532 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X2)) ◇ (X2 ◇ X3)) = X3 := superpose eq401 eq531
  have eq533 (X0 X1 X2 X3 : G) : ((X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X2)) ◇ X2) = X3 := superpose eq401 eq532
  have eq534 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq401 eq533
  have eq535 (X0 X3 : G) : X0 = X3 := superpose eq534 eq534
  have eq537 (X0 : G) : sK0 ≠ X0 := superpose eq535 eq8
  subsumption eq537 eq535


@[equational_result]
theorem Equation12226_implies_Equation2 (G : Type*) [Magma G] (h : Equation12226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X0) ◇ (X3 ◇ X3)) = (X1 ◇ ((X0 ◇ (((X3 ◇ X0) ◇ X0) ◇ (X3 ◇ X3))) ◇ (X2 ◇ X2))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ ((((((X2 ◇ X0) ◇ X0) ◇ (X2 ◇ X2)) ◇ X3) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X0) ◇ (X3 ◇ X3)) = (X1 ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq7 eq9
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ ((X4 ◇ X1) ◇ X1)) ◇ ((X4 ◇ X1) ◇ X1)) ◇ (X3 ◇ X3)) = (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq12 eq12
  have eq27 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq12
  have eq31 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (X3 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq12 eq7
  have eq39 (X0 X1 X2 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X1 := superpose eq27 eq26
  have eq42 (X1 X3 : G) : (X1 ◇ X1) = (X3 ◇ X1) := superpose eq39 eq31
  have eq44 (X0 X1 X2 X3 : G) : (X1 ◇ (((((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ X3) ◇ X3) ◇ X0)) = X3 := superpose eq42 eq11
  have eq57 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = X3 := superpose eq42 eq44
  have eq67 (X0 X3 : G) : X0 = X3 := superpose eq57 eq57
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq69 eq67


@[equational_result]
theorem Equation12227_implies_Equation2 (G : Type*) [Magma G] (h : Equation12227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation12229_implies_Equation2 (G : Type*) [Magma G] (h : Equation12229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq37 eq17


@[equational_result]
theorem Equation12230_implies_Equation2 (G : Type*) [Magma G] (h : Equation12230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq74 eq14


@[equational_result]
theorem Equation12231_implies_Equation2 (G : Type*) [Magma G] (h : Equation12231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq65 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq177 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq177 eq65


@[equational_result]
theorem Equation12232_implies_Equation2 (G : Type*) [Magma G] (h : Equation12232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation12236_implies_Equation2 (G : Type*) [Magma G] (h : Equation12236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq141 eq47


@[equational_result]
theorem Equation12238_implies_Equation2 (G : Type*) [Magma G] (h : Equation12238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X2) ◇ (X2 ◇ X2)) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))) ◇ (X0 ◇ ((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3)))))) = X3 := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X3 ◇ X3)) = X0 := superpose eq7 eq9
  have eq28 (X0 X1 X2 X4 : G) : (X4 ◇ X4) = (X2 ◇ (((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) ◇ (X2 ◇ X2))) := superpose eq9 eq7
  have eq38 (X0 X2 X4 : G) : (X4 ◇ X4) = (X2 ◇ (X0 ◇ X0)) := superpose eq24 eq28
  have eq42 (X0 X1 X3 X4 X5 : G) : ((((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X4 ◇ X5)) ◇ ((X4 ◇ X5) ◇ (X4 ◇ X5))) ◇ ((X3 ◇ X3) ◇ ((((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X4 ◇ X5)) ◇ ((X4 ◇ X5) ◇ (X4 ◇ X5))) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X4 ◇ X5)) ◇ ((X4 ◇ X5) ◇ (X4 ◇ X5)))))) = X5 := superpose eq9 eq10
  have eq61 (X0 X3 X5 : G) : ((X0 ◇ X0) ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X5 := superpose eq24 eq42
  have eq91 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ X1))) = X3 := superpose eq38 eq7
  have eq135 (X0 X3 X5 : G) : ((X0 ◇ X0) ◇ X3) = X5 := superpose eq91 eq61
  have eq163 (X0 X3 : G) : X0 = X3 := superpose eq135 eq135
  have eq171 (X0 : G) : sK0 ≠ X0 := superpose eq163 eq8
  subsumption eq171 eq163


@[equational_result]
theorem Equation12240_implies_Equation2 (G : Type*) [Magma G] (h : Equation12240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq163 eq61


@[equational_result]
theorem Equation12244_implies_Equation2 (G : Type*) [Magma G] (h : Equation12244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq64 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq164 eq64


@[equational_result]
theorem Equation12246_implies_Equation2 (G : Type*) [Magma G] (h : Equation12246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ X2) ◇ (X4 ◇ X2)) = (X1 ◇ ((X0 ◇ X1) ◇ (X5 ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X2)) ◇ (((X4 ◇ X5) ◇ (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ X2))) ◇ X0)) = X5 := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X3 ◇ (X4 ◇ X1)) ◇ X5) ◇ (X6 ◇ X5)) = (X7 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) := superpose eq9 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X4 ◇ X3)) = X0 := superpose eq7 eq9
  have eq33 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ X4) ◇ (((X5 ◇ X6) ◇ (X3 ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))))) = X6 := superpose eq9 eq7
  have eq40 (X0 X1 X2 X7 : G) : (X7 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) = X1 := superpose eq29 eq28
  have eq44 (X1 X3 X4 X6 : G) : ((X3 ◇ X4) ◇ X1) = X6 := superpose eq40 eq33
  have eq86 (X0 X6 : G) : X0 = X6 := superpose eq11 eq44
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq191 eq86


@[equational_result]
theorem Equation12247_implies_Equation2 (G : Type*) [Magma G] (h : Equation12247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq78 eq13


@[equational_result]
theorem Equation12248_implies_Equation2 (G : Type*) [Magma G] (h : Equation12248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq68 eq12


@[equational_result]
theorem Equation12249_implies_Equation2 (G : Type*) [Magma G] (h : Equation12249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12251_implies_Equation2 (G : Type*) [Magma G] (h : Equation12251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X3 ◇ X2) ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X0)) ◇ X1) ◇ ((((X2 ◇ X0) ◇ X2) ◇ X0) ◇ X0)) ◇ X0) = X0 := superpose eq10 eq10
  have eq22 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ X0) ◇ X4) ◇ X3) = (X1 ◇ ((X0 ◇ (((X2 ◇ X3) ◇ X2) ◇ (X3 ◇ X0))) ◇ ((((X4 ◇ X0) ◇ X4) ◇ X3) ◇ X1))) := superpose eq10 eq7
  have eq25 (X0 X1 X3 X4 : G) : (((X4 ◇ X0) ◇ X4) ◇ X3) = (X1 ◇ (X3 ◇ ((((X4 ◇ X0) ◇ X4) ◇ X3) ◇ X1))) := superpose eq7 eq22
  have eq29 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3)) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) := superpose eq11 eq11
  have eq30 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq11
  have eq31 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) = ((X1 ◇ (X0 ◇ (((X2 ◇ (X1 ◇ X0)) ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)))) ◇ X1) := superpose eq10 eq11
  have eq43 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq7 eq31
  have eq44 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = X0 := superpose eq30 eq10
  have eq45 (X0 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq30 eq7
  have eq57 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq30 eq7
  have eq93 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (((X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X2) ◇ X0)) := superpose eq45 eq10
  have eq101 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2))) = ((X1 ◇ (X1 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2))) ◇ X1) := superpose eq11 eq43
  have eq102 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq43
  have eq135 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq102 eq102
  have eq143 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2))) = X0 := superpose eq102 eq7
  have eq220 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0))) := superpose eq102 eq25
  have eq242 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq143
  have eq279 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq143 eq11
  have eq300 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (((X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X2) ◇ X0)) := superpose eq279 eq93
  have eq301 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq279 eq44
  have eq302 (X0 X1 X2 : G) : ((((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ (((X2 ◇ X0) ◇ X2) ◇ X0)) ◇ X0) = X0 := superpose eq279 eq19
  have eq305 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq301 eq57
  have eq309 (X0 X1 X2 : G) : ((((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) = X0 := superpose eq279 eq302
  have eq310 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ X0) = X0 := superpose eq279 eq309
  have eq317 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq30 eq310
  have eq324 (X0 X1 : G) : (((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) ◇ X0) = X0 := superpose eq30 eq310
  have eq326 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) = (((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3)) := superpose eq11 eq310
  have eq364 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq301 eq317
  have eq365 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq364 eq30
  have eq366 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq365 eq45
  have eq382 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (((X2 ◇ (X0 ◇ X0)) ◇ X2) ◇ X0)) := superpose eq365 eq300
  have eq383 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq365 eq301
  have eq391 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) = X0 := superpose eq366 eq324
  have eq392 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose eq391 eq382
  have eq393 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = (((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2)) := superpose eq326 eq29
  have eq394 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X3 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X3) := superpose eq393 eq326
  have eq411 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) := superpose eq394 eq101
  have eq416 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X0) = (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq394 eq220
  have eq421 (X0 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq394 eq310
  have eq433 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) := superpose eq416 eq411
  have eq437 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) := superpose eq279 eq433
  have eq442 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq421 eq392
  have eq445 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq442 eq305
  have eq461 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq442 eq383
  have eq474 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X1) ◇ X1) := superpose eq461 eq437
  have eq477 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X1 ◇ X1) := superpose eq442 eq474
  have eq478 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq442 eq477
  have eq492 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq478 eq43
  have eq514 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq478 eq135
  have eq594 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq478 eq492
  have eq622 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := superpose eq478 eq514
  have eq624 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq622 eq445
  have eq638 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq624 eq594
  have eq640 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X2 := superpose eq638 eq242
  have eq651 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq638 eq640
  have eq664 (X0 X3 : G) : X0 = X3 := superpose eq651 eq651
  have eq678 (X0 : G) : sK0 ≠ X0 := superpose eq664 eq8
  subsumption eq678 eq664


@[equational_result]
theorem Equation12252_implies_Equation2 (G : Type*) [Magma G] (h : Equation12252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq10
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq57 eq18


@[equational_result]
theorem Equation12253_implies_Equation2 (G : Type*) [Magma G] (h : Equation12253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq114 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq114 eq49


@[equational_result]
theorem Equation12257_implies_Equation2 (G : Type*) [Magma G] (h : Equation12257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation12260_implies_Equation2 (G : Type*) [Magma G] (h : Equation12260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ ((((X2 ◇ X0) ◇ X2) ◇ (X2 ◇ X2)) ◇ (((X2 ◇ X0) ◇ X2) ◇ (X2 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq10
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq75 eq17


@[equational_result]
theorem Equation12261_implies_Equation2 (G : Type*) [Magma G] (h : Equation12261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12263_implies_Equation2 (G : Type*) [Magma G] (h : Equation12263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq69 eq17


@[equational_result]
theorem Equation12264_implies_Equation2 (G : Type*) [Magma G] (h : Equation12264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation12265_implies_Equation2 (G : Type*) [Magma G] (h : Equation12265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X5))) = X4 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq51 eq17


@[equational_result]
theorem Equation12266_implies_Equation2 (G : Type*) [Magma G] (h : Equation12266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation12268_implies_Equation2 (G : Type*) [Magma G] (h : Equation12268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X1))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) ◇ (((X4 ◇ X3) ◇ X5) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq10 eq10
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq131 eq53


@[equational_result]
theorem Equation12269_implies_Equation2 (G : Type*) [Magma G] (h : Equation12269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X2))) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq142 eq49


@[equational_result]
theorem Equation12270_implies_Equation2 (G : Type*) [Magma G] (h : Equation12270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (X3 ◇ (((X4 ◇ X0) ◇ X5) ◇ (X0 ◇ X5))))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq10
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq58 eq18


@[equational_result]
theorem Equation12271_implies_Equation2 (G : Type*) [Magma G] (h : Equation12271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X7 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X7))) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq50 (X0 X5 : G) : X0 = X5 := superpose eq7 eq17
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq115 eq50


@[equational_result]
theorem Equation12273_implies_Equation2 (G : Type*) [Magma G] (h : Equation12273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq42 eq16


@[equational_result]
theorem Equation12274_implies_Equation2 (G : Type*) [Magma G] (h : Equation12274 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq79 eq18


@[equational_result]
theorem Equation12275_implies_Equation2 (G : Type*) [Magma G] (h : Equation12275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ X4) ◇ (X2 ◇ X4)) = (X1 ◇ ((X0 ◇ X5) ◇ (X1 ◇ X5))) := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X3 ◇ (X4 ◇ X1)) ◇ X5) ◇ (X6 ◇ X5)) = (X7 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2)))) := superpose eq9 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X4 ◇ X3)) = X0 := superpose eq7 eq9
  have eq33 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X3 ◇ X1) ◇ X4) ◇ (((X5 ◇ X6) ◇ (X7 ◇ X4)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X6 := superpose eq9 eq7
  have eq40 (X0 X1 X2 X7 : G) : (X7 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2)))) = X1 := superpose eq29 eq28
  have eq44 (X1 X3 X4 X6 : G) : (((X3 ◇ X1) ◇ X4) ◇ X1) = X6 := superpose eq40 eq33
  have eq92 (X0 X4 : G) : X0 = X4 := superpose eq44 eq44
  have eq192 (X0 : G) : sK0 ≠ X0 := superpose eq92 eq8
  subsumption eq192 eq92


@[equational_result]
theorem Equation12276_implies_Equation2 (G : Type*) [Magma G] (h : Equation12276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X7 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X7))) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq59 eq19


@[equational_result]
theorem Equation12278_implies_Equation2 (G : Type*) [Magma G] (h : Equation12278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation12279_implies_Equation2 (G : Type*) [Magma G] (h : Equation12279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X2))) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq79 eq17


@[equational_result]
theorem Equation12280_implies_Equation2 (G : Type*) [Magma G] (h : Equation12280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq48 eq15


@[equational_result]
theorem Equation12281_implies_Equation2 (G : Type*) [Magma G] (h : Equation12281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation12283_implies_Equation2 (G : Type*) [Magma G] (h : Equation12283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X0) ◇ X4) ◇ (X4 ◇ X2)) = (X1 ◇ ((X0 ◇ X5) ◇ (X5 ◇ X1))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ X0) ◇ X1))) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 X7 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ X7) = X3 := superpose eq12 eq12
  have eq57 (X0 X1 X2 X3 X5 X6 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) ◇ ((X5 ◇ X6) ◇ X3))) = X5 := superpose eq9 eq7
  have eq78 (X2 X3 X5 : G) : (X3 ◇ X2) = X5 := superpose eq16 eq57
  have eq79 (X0 X4 : G) : X0 = X4 := superpose eq7 eq78
  have eq189 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq189 eq79


@[equational_result]
theorem Equation12284_implies_Equation2 (G : Type*) [Magma G] (h : Equation12284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq71 eq13


@[equational_result]
theorem Equation12285_implies_Equation2 (G : Type*) [Magma G] (h : Equation12285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation12286_implies_Equation2 (G : Type*) [Magma G] (h : Equation12286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 X5 X6 X7 : G) : (X1 ◇ (X0 ◇ ((((X4 ◇ X0) ◇ X5) ◇ (X5 ◇ X6)) ◇ X7))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X1 X3 X5 : G) : (X1 ◇ X5) = X3 := superpose eq11 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation12288_implies_Equation2 (G : Type*) [Magma G] (h : Equation12288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X7 : G) : (X1 ◇ (X0 ◇ (X7 ◇ X1))) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation12289_implies_Equation2 (G : Type*) [Magma G] (h : Equation12289 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation12290_implies_Equation2 (G : Type*) [Magma G] (h : Equation12290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation12291_implies_Equation2 (G : Type*) [Magma G] (h : Equation12291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation12292_implies_Equation2 (G : Type*) [Magma G] (h : Equation12292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation12296_implies_Equation2 (G : Type*) [Magma G] (h : Equation12296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq127 eq41


@[equational_result]
theorem Equation12298_implies_Equation2 (G : Type*) [Magma G] (h : Equation12298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X3) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) ◇ (((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X3 ◇ (X2 ◇ X1)) ◇ X0) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X3 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = ((X0 ◇ X3) ◇ ((((X2 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) ◇ (((X2 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)))) := superpose eq7 eq10
  have eq12 (X0 X1 X3 X4 : G) : ((X3 ◇ X0) ◇ (X4 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X0)))) = (((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X4) ◇ (((X3 ◇ X0) ◇ (X3 ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X0)))) := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq10 eq7
  have eq18 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X1))) := superpose eq10 eq7
  have eq20 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))))) = X3 := superpose eq11 eq9
  have eq42 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = ((X3 ◇ X2) ◇ X0) := superpose eq7 eq17
  have eq43 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq17 eq17
  have eq151 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X4 ◇ X1) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X0))) := superpose eq10 eq42
  have eq181 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X1 := superpose eq42 eq7
  have eq239 (X0 X1 X3 X4 : G) : ((X3 ◇ X0) ◇ (X4 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X0)))) = (((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X4) ◇ (X0 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq151 eq12
  have eq244 (X0 X1 X3 X4 : G) : ((X3 ◇ X0) ◇ (X4 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X0)))) = (((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X4) ◇ X0) := superpose eq181 eq239
  have eq309 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0))) ◇ (X1 ◇ X1))) := superpose eq18 eq7
  have eq425 (X0 X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1))) := superpose eq181 eq309
  have eq426 (X1 X2 : G) : (X2 ◇ X1) = (X1 ◇ X1) := superpose eq43 eq425
  have eq427 (X0 X3 X4 : G) : (X0 ◇ X0) = ((X3 ◇ X0) ◇ (X4 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X0)))) := superpose eq426 eq244
  have eq432 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) = X3 := superpose eq427 eq20
  have eq561 (X0 X4 : G) : X0 = X4 := superpose eq432 eq432
  have eq627 (X0 : G) : sK0 ≠ X0 := superpose eq561 eq8
  subsumption eq627 eq561


@[equational_result]
theorem Equation12300_implies_Equation2 (G : Type*) [Magma G] (h : Equation12300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq166 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq166 eq67


@[equational_result]
theorem Equation12302_implies_Equation2 (G : Type*) [Magma G] (h : Equation12302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X3 ◇ (X2 ◇ X1))) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (((((X3 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X4) ◇ (((X3 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X3 ◇ (X1 ◇ X2))))) = X4 := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X4 ◇ (X3 ◇ (X1 ◇ X2))))) = X4 := superpose eq9 eq12
  have eq33 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq9 eq7
  have eq72 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X2 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq33
  have eq80 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X1) = ((X3 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := superpose eq9 eq33
  have eq92 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X1) = X0 := superpose eq21 eq80
  have eq105 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq92 eq72
  have eq113 (X0 X3 : G) : X0 = X3 := superpose eq7 eq105
  have eq219 (X0 : G) : sK0 ≠ X0 := superpose eq113 eq8
  subsumption eq219 eq113


@[equational_result]
theorem Equation12304_implies_Equation2 (G : Type*) [Magma G] (h : Equation12304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq174 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq174 eq47


@[equational_result]
theorem Equation12306_implies_Equation2 (G : Type*) [Magma G] (h : Equation12306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ X4) ◇ (X5 ◇ (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X2))))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X4 ◇ (X2 ◇ X1))) = (X1 ◇ (X0 ◇ (X5 ◇ X1))) := superpose eq7 eq7
  have eq31 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X3) ◇ X0)) ◇ (X5 ◇ (X2 ◇ X3))) = X0 := superpose eq7 eq10
  have eq62 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ X3) = ((((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X3) ◇ X5)) ◇ (((X4 ◇ X3) ◇ X5) ◇ (X2 ◇ X3))) ◇ X0) := superpose eq9 eq9
  have eq77 (X0 X2 X3 X5 : G) : (X5 ◇ X0) = (X2 ◇ X3) := superpose eq31 eq62
  have eq78 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq77
  have eq192 (X0 X4 : G) : X0 = X4 := superpose eq7 eq78
  have eq336 (X0 : G) : sK0 ≠ X0 := superpose eq192 eq8
  subsumption eq336 eq192


@[equational_result]
theorem Equation12307_implies_Equation2 (G : Type*) [Magma G] (h : Equation12307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation12308_implies_Equation2 (G : Type*) [Magma G] (h : Equation12308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq7 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq176 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq176 eq49


@[equational_result]
theorem Equation12309_implies_Equation2 (G : Type*) [Magma G] (h : Equation12309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation12311_implies_Equation2 (G : Type*) [Magma G] (h : Equation12311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) ◇ (((X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X2 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))))) = X2 := superpose eq7 eq9
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ (X3 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)))) ◇ ((X3 ◇ ((X0 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ (X3 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))))) ◇ (X4 ◇ ((X0 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) ◇ (X3 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))))))) = X4 := superpose eq7 eq9
  have eq34 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq11
  have eq73 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) = X2 := superpose eq34 eq7
  have eq117 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq34 eq73
  have eq118 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq73
  have eq119 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) = (((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) := superpose eq9 eq73
  have eq120 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))))) = ((((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)))) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))))) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))))) := superpose eq12 eq73
  have eq128 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X2 ◇ X2))) = ((((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X0) ◇ (((X3 ◇ (((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X0)) ◇ (((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X0)) ◇ (X2 ◇ X2))) := superpose eq73 eq10
  have eq137 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq117 eq34
  have eq178 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq118 eq7
  have eq190 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) = ((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) ◇ (((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))))) := superpose eq118 eq9
  have eq217 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) = ((((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) ◇ (X2 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))))) := superpose eq119 eq190
  have eq218 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq9 eq217
  have eq219 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) = X3 := superpose eq218 eq9
  have eq257 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) = ((((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ X0) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) := superpose eq218 eq120
  have eq284 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) = X3 := superpose eq218 eq219
  have eq326 (X0 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := superpose eq218 eq257
  have eq327 (X0 X3 : G) : (X3 ◇ (X0 ◇ X0)) = X0 := superpose eq137 eq326
  have eq342 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) ◇ X0) ◇ (((X3 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) ◇ X0)) ◇ (((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) ◇ X0)) ◇ (X2 ◇ X2))) := superpose eq327 eq128
  have eq422 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X1 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) ◇ X0) ◇ X2) := superpose eq327 eq342
  have eq423 (X0 X2 : G) : (X2 ◇ X2) = ((X2 ◇ X0) ◇ X2) := superpose eq327 eq422
  have eq425 (X0 X1 X2 : G) : (X2 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq423 eq178
  have eq428 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq7 eq425
  have eq429 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) ◇ X0) = X3 := superpose eq428 eq284
  have eq439 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X0) = X3 := superpose eq428 eq429
  have eq440 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq428 eq439
  have eq441 (X0 X3 : G) : X0 = X3 := superpose eq440 eq440
  have eq443 (X0 : G) : sK0 ≠ X0 := superpose eq441 eq8
  subsumption eq443 eq441


@[equational_result]
theorem Equation12313_implies_Equation2 (G : Type*) [Magma G] (h : Equation12313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation12315_implies_Equation2 (G : Type*) [Magma G] (h : Equation12315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12316_implies_Equation2 (G : Type*) [Magma G] (h : Equation12316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12317_implies_Equation2 (G : Type*) [Magma G] (h : Equation12317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12319_implies_Equation2 (G : Type*) [Magma G] (h : Equation12319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation12320_implies_Equation2 (G : Type*) [Magma G] (h : Equation12320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12321_implies_Equation2 (G : Type*) [Magma G] (h : Equation12321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12323_implies_Equation2 (G : Type*) [Magma G] (h : Equation12323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12324_implies_Equation2 (G : Type*) [Magma G] (h : Equation12324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12325_implies_Equation2 (G : Type*) [Magma G] (h : Equation12325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12326_implies_Equation2 (G : Type*) [Magma G] (h : Equation12326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12328_implies_Equation2 (G : Type*) [Magma G] (h : Equation12328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2))) ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq9
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0))) ◇ X2) := superpose eq10 eq7
  have eq58 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq15 eq9
  have eq71 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq15 eq58
  have eq92 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X3 ◇ (X0 ◇ X1)) ◇ X3) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)))) = X2 := superpose eq29 eq10
  have eq110 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq71 eq92
  have eq118 (X0 X2 : G) : X0 = X2 := superpose eq15 eq110
  have eq285 (X0 : G) : sK0 ≠ X0 := superpose eq118 eq8
  subsumption eq285 eq118


@[equational_result]
theorem Equation12330_implies_Equation2 (G : Type*) [Magma G] (h : Equation12330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation12332_implies_Equation2 (G : Type*) [Magma G] (h : Equation12332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12333_implies_Equation2 (G : Type*) [Magma G] (h : Equation12333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12334_implies_Equation2 (G : Type*) [Magma G] (h : Equation12334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12336_implies_Equation2 (G : Type*) [Magma G] (h : Equation12336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation12337_implies_Equation2 (G : Type*) [Magma G] (h : Equation12337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12338_implies_Equation2 (G : Type*) [Magma G] (h : Equation12338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12340_implies_Equation2 (G : Type*) [Magma G] (h : Equation12340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12341_implies_Equation2 (G : Type*) [Magma G] (h : Equation12341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12342_implies_Equation2 (G : Type*) [Magma G] (h : Equation12342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12343_implies_Equation2 (G : Type*) [Magma G] (h : Equation12343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12345_implies_Equation2 (G : Type*) [Magma G] (h : Equation12345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X1))) = X5 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq10 eq10
  have eq46 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq122 eq46


@[equational_result]
theorem Equation12346_implies_Equation2 (G : Type*) [Magma G] (h : Equation12346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ X2))) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq43 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq130 eq43


@[equational_result]
theorem Equation12347_implies_Equation2 (G : Type*) [Magma G] (h : Equation12347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X0 ◇ (X5 ◇ (((X3 ◇ (X2 ◇ X1)) ◇ X4) ◇ (X0 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X0) = ((X4 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X3))) ◇ X3) := superpose eq7 eq7
  have eq23 (X0 X1 X2 X5 X6 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X5) ◇ (X6 ◇ X5))) = X6 := superpose eq12 eq7
  have eq25 (X0 X1 X5 : G) : (X1 ◇ (X0 ◇ X0)) = X5 := superpose eq23 eq10
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq53 eq30


@[equational_result]
theorem Equation12348_implies_Equation2 (G : Type*) [Magma G] (h : Equation12348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ X0)) = X4 := superpose eq7 eq7
  have eq33 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq53 eq33


@[equational_result]
theorem Equation12350_implies_Equation2 (G : Type*) [Magma G] (h : Equation12350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12351_implies_Equation2 (G : Type*) [Magma G] (h : Equation12351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12352_implies_Equation2 (G : Type*) [Magma G] (h : Equation12352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12353_implies_Equation2 (G : Type*) [Magma G] (h : Equation12353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12355_implies_Equation2 (G : Type*) [Magma G] (h : Equation12355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation12356_implies_Equation2 (G : Type*) [Magma G] (h : Equation12356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12357_implies_Equation2 (G : Type*) [Magma G] (h : Equation12357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12358_implies_Equation2 (G : Type*) [Magma G] (h : Equation12358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12360_implies_Equation2 (G : Type*) [Magma G] (h : Equation12360 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12361_implies_Equation2 (G : Type*) [Magma G] (h : Equation12361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12362_implies_Equation2 (G : Type*) [Magma G] (h : Equation12362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation12363_implies_Equation2 (G : Type*) [Magma G] (h : Equation12363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12365_implies_Equation2 (G : Type*) [Magma G] (h : Equation12365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12366_implies_Equation2 (G : Type*) [Magma G] (h : Equation12366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12367_implies_Equation2 (G : Type*) [Magma G] (h : Equation12367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12368_implies_Equation2 (G : Type*) [Magma G] (h : Equation12368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation12369_implies_Equation2 (G : Type*) [Magma G] (h : Equation12369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X3) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation12372_implies_Equation2 (G : Type*) [Magma G] (h : Equation12372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ (X3 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ X0) = (X1 ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq9
  have eq39 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X1 := superpose eq12 eq13
  have eq53 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq39 eq7
  have eq59 (X0 X3 : G) : X0 = X3 := superpose eq13 eq53
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq123 eq59


@[equational_result]
theorem Equation12373_implies_Equation2 (G : Type*) [Magma G] (h : Equation12373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq107 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq129 (X0 X4 : G) : X0 = X4 := superpose eq7 eq107
  have eq216 (X0 : G) : sK0 ≠ X0 := superpose eq129 eq8
  subsumption eq216 eq129


@[equational_result]
theorem Equation12375_implies_Equation2 (G : Type*) [Magma G] (h : Equation12375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq18 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq7 eq9
  have eq21 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ X1)) ◇ ((X4 ◇ X4) ◇ (X4 ◇ X4))) = ((X5 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq9 eq9
  have eq24 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) = X0 := superpose eq7 eq9
  have eq35 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq21 eq10
  have eq36 (X0 X1 X5 : G) : ((X5 ◇ X5) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq24 eq22
  have eq40 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq9 eq35
  have eq51 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq40 eq18
  have eq62 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq51 eq21
  have eq73 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq51 eq62
  have eq74 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq51 eq73
  have eq94 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq7 eq36
  have eq97 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq36 eq36
  have eq101 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq74 eq94
  have eq106 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq97 eq101
  have eq111 (X0 X1 X5 : G) : ((X5 ◇ X5) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq106 eq36
  have eq123 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq106 eq97
  have eq130 (X0 X1 X5 : G) : (X5 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq106 eq111
  have eq137 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq106 eq123
  have eq138 (X0 X1 X5 : G) : (X5 ◇ (X1 ◇ X0)) = X1 := superpose eq137 eq130
  have eq143 (X0 X1 X5 : G) : (X5 ◇ X0) = X1 := superpose eq137 eq138
  have eq144 (X0 X3 : G) : X0 = X3 := superpose eq143 eq143
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq144 eq8
  subsumption eq156 eq144


@[equational_result]
theorem Equation12377_implies_Equation2 (G : Type*) [Magma G] (h : Equation12377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation12379_implies_Equation2 (G : Type*) [Magma G] (h : Equation12379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X0) ◇ (X3 ◇ (X2 ◇ X2))) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X3) ◇ ((X4 ◇ X4) ◇ X1)) ◇ (X3 ◇ (X4 ◇ X4))) = ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X1 ◇ (X2 ◇ X2))) = X0 := superpose eq7 eq9
  have eq37 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := superpose eq25 eq24
  have eq89 (X0 X1 : G) : X0 = X1 := superpose eq7 eq37
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq8
  subsumption eq132 eq89


