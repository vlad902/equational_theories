import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation31497_implies_Equation2 (G : Type*) [Magma G] (h : Equation31497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31498_implies_Equation2 (G : Type*) [Magma G] (h : Equation31498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31500_implies_Equation2 (G : Type*) [Magma G] (h : Equation31500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31501_implies_Equation2 (G : Type*) [Magma G] (h : Equation31501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31502_implies_Equation2 (G : Type*) [Magma G] (h : Equation31502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31503_implies_Equation2 (G : Type*) [Magma G] (h : Equation31503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31505_implies_Equation2 (G : Type*) [Magma G] (h : Equation31505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31506_implies_Equation2 (G : Type*) [Magma G] (h : Equation31506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31507_implies_Equation2 (G : Type*) [Magma G] (h : Equation31507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31508_implies_Equation2 (G : Type*) [Magma G] (h : Equation31508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31509_implies_Equation2 (G : Type*) [Magma G] (h : Equation31509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31511_implies_Equation2 (G : Type*) [Magma G] (h : Equation31511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq9
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq130 eq58


@[equational_result]
theorem Equation31512_implies_Equation2 (G : Type*) [Magma G] (h : Equation31512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation31513_implies_Equation2 (G : Type*) [Magma G] (h : Equation31513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31515_implies_Equation2 (G : Type*) [Magma G] (h : Equation31515 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq9
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq137 eq37


@[equational_result]
theorem Equation31517_implies_Equation2 (G : Type*) [Magma G] (h : Equation31517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31520_implies_Equation2 (G : Type*) [Magma G] (h : Equation31520 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq52 eq12


@[equational_result]
theorem Equation31521_implies_Equation2 (G : Type*) [Magma G] (h : Equation31521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq63 eq13


@[equational_result]
theorem Equation31523_implies_Equation2 (G : Type*) [Magma G] (h : Equation31523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X5))) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq9
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq161 eq67


@[equational_result]
theorem Equation31524_implies_Equation2 (G : Type*) [Magma G] (h : Equation31524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation31525_implies_Equation2 (G : Type*) [Magma G] (h : Equation31525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation31526_implies_Equation2 (G : Type*) [Magma G] (h : Equation31526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation31528_implies_Equation2 (G : Type*) [Magma G] (h : Equation31528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq9
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq108 eq38


@[equational_result]
theorem Equation31530_implies_Equation2 (G : Type*) [Magma G] (h : Equation31530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation31532_implies_Equation2 (G : Type*) [Magma G] (h : Equation31532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation31534_implies_Equation2 (G : Type*) [Magma G] (h : Equation31534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1))) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation31538_implies_Equation2 (G : Type*) [Magma G] (h : Equation31538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X2))) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation31540_implies_Equation2 (G : Type*) [Magma G] (h : Equation31540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X5))) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq76 eq19


@[equational_result]
theorem Equation31541_implies_Equation2 (G : Type*) [Magma G] (h : Equation31541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X3))) ◇ ((X4 ◇ X5) ◇ X0)) ◇ X4) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X3) ◇ X0) ◇ (X2 ◇ X4)) = ((X1 ◇ X0) ◇ X2) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ X5) ◇ ((X0 ◇ X6) ◇ X1)) = (((X3 ◇ X4) ◇ X5) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq11 eq11
  have eq25 (X0 X1 X3 X5 X6 : G) : ((X3 ◇ X5) ◇ ((X0 ◇ X6) ◇ X1)) = ((X3 ◇ X5) ◇ (X0 ◇ X1)) := superpose eq11 eq17
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X3))) ◇ (X4 ◇ X0)) ◇ X4) = X5 := superpose eq25 eq10
  have eq55 (X0 X6 : G) : X0 = X6 := superpose eq26 eq26
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq84 eq55


@[equational_result]
theorem Equation31542_implies_Equation2 (G : Type*) [Magma G] (h : Equation31542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X5))) ◇ X5) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation31543_implies_Equation2 (G : Type*) [Magma G] (h : Equation31543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 X7 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X3))) ◇ ((X4 ◇ X5) ◇ X0)) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation31545_implies_Equation2 (G : Type*) [Magma G] (h : Equation31545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation31546_implies_Equation2 (G : Type*) [Magma G] (h : Equation31546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq43 eq11


@[equational_result]
theorem Equation31547_implies_Equation2 (G : Type*) [Magma G] (h : Equation31547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq48 eq12


@[equational_result]
theorem Equation31551_implies_Equation2 (G : Type*) [Magma G] (h : Equation31551 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation31554_implies_Equation2 (G : Type*) [Magma G] (h : Equation31554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq58 eq12


@[equational_result]
theorem Equation31555_implies_Equation2 (G : Type*) [Magma G] (h : Equation31555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation31557_implies_Equation2 (G : Type*) [Magma G] (h : Equation31557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ (X3 ◇ X4))) ◇ X5))) ◇ X1) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq9
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq141 eq50


@[equational_result]
theorem Equation31558_implies_Equation2 (G : Type*) [Magma G] (h : Equation31558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq65 eq13


@[equational_result]
theorem Equation31559_implies_Equation2 (G : Type*) [Magma G] (h : Equation31559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation31560_implies_Equation2 (G : Type*) [Magma G] (h : Equation31560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation31562_implies_Equation2 (G : Type*) [Magma G] (h : Equation31562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X0 ◇ (X5 ◇ X2))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1) = X3 := superpose eq7 eq7
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq9 eq10
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq41 eq32


@[equational_result]
theorem Equation31563_implies_Equation2 (G : Type*) [Magma G] (h : Equation31563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation31564_implies_Equation2 (G : Type*) [Magma G] (h : Equation31564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation31565_implies_Equation2 (G : Type*) [Magma G] (h : Equation31565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31567_implies_Equation2 (G : Type*) [Magma G] (h : Equation31567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X0 ◇ (X5 ◇ X1))) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq51 eq19


@[equational_result]
theorem Equation31568_implies_Equation2 (G : Type*) [Magma G] (h : Equation31568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X2) = X3 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq10
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq125 eq41


@[equational_result]
theorem Equation31569_implies_Equation2 (G : Type*) [Magma G] (h : Equation31569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X5 ◇ X1))) ◇ X5) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation31570_implies_Equation2 (G : Type*) [Magma G] (h : Equation31570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation31572_implies_Equation2 (G : Type*) [Magma G] (h : Equation31572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X5 ◇ (X2 ◇ ((X3 ◇ X0) ◇ (X4 ◇ X3)))))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1) = X3 := superpose eq7 eq7
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq10 eq9
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq44 eq36


@[equational_result]
theorem Equation31573_implies_Equation2 (G : Type*) [Magma G] (h : Equation31573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31574_implies_Equation2 (G : Type*) [Magma G] (h : Equation31574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation31575_implies_Equation2 (G : Type*) [Magma G] (h : Equation31575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31577_implies_Equation2 (G : Type*) [Magma G] (h : Equation31577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X0 ◇ (X5 ◇ X5))) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation31578_implies_Equation2 (G : Type*) [Magma G] (h : Equation31578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq65 eq12


@[equational_result]
theorem Equation31579_implies_Equation2 (G : Type*) [Magma G] (h : Equation31579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation31580_implies_Equation2 (G : Type*) [Magma G] (h : Equation31580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation31582_implies_Equation2 (G : Type*) [Magma G] (h : Equation31582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X6 X7 : G) : ((X1 ◇ (X0 ◇ (X6 ◇ X7))) ◇ X1) = X2 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq7 eq9
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq57 eq22


@[equational_result]
theorem Equation31583_implies_Equation2 (G : Type*) [Magma G] (h : Equation31583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31584_implies_Equation2 (G : Type*) [Magma G] (h : Equation31584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation31585_implies_Equation2 (G : Type*) [Magma G] (h : Equation31585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation31586_implies_Equation2 (G : Type*) [Magma G] (h : Equation31586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X9 : G) : (X0 ◇ X9) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation31588_implies_Equation2 (G : Type*) [Magma G] (h : Equation31588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ (X3 ◇ X3))) ◇ X1) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq9 eq10
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq30 eq24


@[equational_result]
theorem Equation31590_implies_Equation2 (G : Type*) [Magma G] (h : Equation31590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31592_implies_Equation2 (G : Type*) [Magma G] (h : Equation31592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ (X3 ◇ X1))) ◇ X1) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq9
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq123 eq57


@[equational_result]
theorem Equation31594_implies_Equation2 (G : Type*) [Magma G] (h : Equation31594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31598_implies_Equation2 (G : Type*) [Magma G] (h : Equation31598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation31600_implies_Equation2 (G : Type*) [Magma G] (h : Equation31600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X4 ◇ X5))) ◇ X1) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq9
  have eq68 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq152 eq68


@[equational_result]
theorem Equation31601_implies_Equation2 (G : Type*) [Magma G] (h : Equation31601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) ◇ X0) ◇ X3) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ (X4 ◇ X5)) ◇ X4) ◇ X2) = X1 := superpose eq7 eq11
  have eq65 (X0 X5 : G) : X0 = X5 := superpose eq11 eq14
  have eq187 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq187 eq65


@[equational_result]
theorem Equation31602_implies_Equation2 (G : Type*) [Magma G] (h : Equation31602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X4 ◇ X5))) ◇ X5) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))) ◇ X0) ◇ X4) = X3 := superpose eq7 eq7
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq9 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq44 eq36


@[equational_result]
theorem Equation31603_implies_Equation2 (G : Type*) [Magma G] (h : Equation31603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31605_implies_Equation2 (G : Type*) [Magma G] (h : Equation31605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X3))) ◇ X1) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq9
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq107 eq36


@[equational_result]
theorem Equation31607_implies_Equation2 (G : Type*) [Magma G] (h : Equation31607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0))) ◇ ((X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X0)))) ◇ X0)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation31609_implies_Equation2 (G : Type*) [Magma G] (h : Equation31609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31610_implies_Equation2 (G : Type*) [Magma G] (h : Equation31610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31611_implies_Equation2 (G : Type*) [Magma G] (h : Equation31611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31613_implies_Equation2 (G : Type*) [Magma G] (h : Equation31613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31614_implies_Equation2 (G : Type*) [Magma G] (h : Equation31614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31615_implies_Equation2 (G : Type*) [Magma G] (h : Equation31615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31617_implies_Equation2 (G : Type*) [Magma G] (h : Equation31617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31618_implies_Equation2 (G : Type*) [Magma G] (h : Equation31618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31619_implies_Equation2 (G : Type*) [Magma G] (h : Equation31619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31620_implies_Equation2 (G : Type*) [Magma G] (h : Equation31620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31624_implies_Equation2 (G : Type*) [Magma G] (h : Equation31624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation31626_implies_Equation2 (G : Type*) [Magma G] (h : Equation31626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation31627_implies_Equation2 (G : Type*) [Magma G] (h : Equation31627 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation31628_implies_Equation2 (G : Type*) [Magma G] (h : Equation31628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31630_implies_Equation2 (G : Type*) [Magma G] (h : Equation31630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31631_implies_Equation2 (G : Type*) [Magma G] (h : Equation31631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31632_implies_Equation2 (G : Type*) [Magma G] (h : Equation31632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31634_implies_Equation2 (G : Type*) [Magma G] (h : Equation31634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31635_implies_Equation2 (G : Type*) [Magma G] (h : Equation31635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31636_implies_Equation2 (G : Type*) [Magma G] (h : Equation31636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31637_implies_Equation2 (G : Type*) [Magma G] (h : Equation31637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31639_implies_Equation2 (G : Type*) [Magma G] (h : Equation31639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1) = X3 := superpose eq7 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq51 eq30


@[equational_result]
theorem Equation31640_implies_Equation2 (G : Type*) [Magma G] (h : Equation31640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X2) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation31641_implies_Equation2 (G : Type*) [Magma G] (h : Equation31641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X4 ◇ X5))) ◇ X4) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X0) ◇ X3) = X4 := superpose eq7 eq7
  have eq34 (X0 X4 : G) : X0 = X4 := superpose eq9 eq11
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq42 eq34


@[equational_result]
theorem Equation31642_implies_Equation2 (G : Type*) [Magma G] (h : Equation31642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31644_implies_Equation2 (G : Type*) [Magma G] (h : Equation31644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31645_implies_Equation2 (G : Type*) [Magma G] (h : Equation31645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31646_implies_Equation2 (G : Type*) [Magma G] (h : Equation31646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31647_implies_Equation2 (G : Type*) [Magma G] (h : Equation31647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31649_implies_Equation2 (G : Type*) [Magma G] (h : Equation31649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31650_implies_Equation2 (G : Type*) [Magma G] (h : Equation31650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31651_implies_Equation2 (G : Type*) [Magma G] (h : Equation31651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31652_implies_Equation2 (G : Type*) [Magma G] (h : Equation31652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31654_implies_Equation2 (G : Type*) [Magma G] (h : Equation31654 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31655_implies_Equation2 (G : Type*) [Magma G] (h : Equation31655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31656_implies_Equation2 (G : Type*) [Magma G] (h : Equation31656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31657_implies_Equation2 (G : Type*) [Magma G] (h : Equation31657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31659_implies_Equation2 (G : Type*) [Magma G] (h : Equation31659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31660_implies_Equation2 (G : Type*) [Magma G] (h : Equation31660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31661_implies_Equation2 (G : Type*) [Magma G] (h : Equation31661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31662_implies_Equation2 (G : Type*) [Magma G] (h : Equation31662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31663_implies_Equation2 (G : Type*) [Magma G] (h : Equation31663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31665_implies_Equation2 (G : Type*) [Magma G] (h : Equation31665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq9
  have eq35 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) = X3 := superpose eq9 eq10
  have eq36 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq10 eq10
  have eq44 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq15 eq36
  have eq45 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X1)))) = X3 := superpose eq44 eq35
  have eq66 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) = X3 := superpose eq44 eq45
  have eq67 (X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X2)) = X3 := superpose eq44 eq66
  have eq68 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq44 eq67
  have eq69 (X0 X3 : G) : X0 = X3 := superpose eq68 eq68
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq74 eq69


@[equational_result]
theorem Equation31666_implies_Equation2 (G : Type*) [Magma G] (h : Equation31666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq43 eq11


@[equational_result]
theorem Equation31667_implies_Equation2 (G : Type*) [Magma G] (h : Equation31667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31671_implies_Equation2 (G : Type*) [Magma G] (h : Equation31671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation31674_implies_Equation2 (G : Type*) [Magma G] (h : Equation31674 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq65 eq11


@[equational_result]
theorem Equation31675_implies_Equation2 (G : Type*) [Magma G] (h : Equation31675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31677_implies_Equation2 (G : Type*) [Magma G] (h : Equation31677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq76 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq168 eq76


@[equational_result]
theorem Equation31678_implies_Equation2 (G : Type*) [Magma G] (h : Equation31678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation31679_implies_Equation2 (G : Type*) [Magma G] (h : Equation31679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation31680_implies_Equation2 (G : Type*) [Magma G] (h : Equation31680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31684_implies_Equation2 (G : Type*) [Magma G] (h : Equation31684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X3 ◇ X3) ◇ X0)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation31686_implies_Equation2 (G : Type*) [Magma G] (h : Equation31686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation31687_implies_Equation2 (G : Type*) [Magma G] (h : Equation31687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation31688_implies_Equation2 (G : Type*) [Magma G] (h : Equation31688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31690_implies_Equation2 (G : Type*) [Magma G] (h : Equation31690 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31691_implies_Equation2 (G : Type*) [Magma G] (h : Equation31691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31692_implies_Equation2 (G : Type*) [Magma G] (h : Equation31692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31694_implies_Equation2 (G : Type*) [Magma G] (h : Equation31694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31695_implies_Equation2 (G : Type*) [Magma G] (h : Equation31695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31696_implies_Equation2 (G : Type*) [Magma G] (h : Equation31696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31697_implies_Equation2 (G : Type*) [Magma G] (h : Equation31697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31700_implies_Equation2 (G : Type*) [Magma G] (h : Equation31700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation31701_implies_Equation2 (G : Type*) [Magma G] (h : Equation31701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation31703_implies_Equation2 (G : Type*) [Magma G] (h : Equation31703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31704_implies_Equation2 (G : Type*) [Magma G] (h : Equation31704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31705_implies_Equation2 (G : Type*) [Magma G] (h : Equation31705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31707_implies_Equation2 (G : Type*) [Magma G] (h : Equation31707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation31708_implies_Equation2 (G : Type*) [Magma G] (h : Equation31708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation31709_implies_Equation2 (G : Type*) [Magma G] (h : Equation31709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31711_implies_Equation2 (G : Type*) [Magma G] (h : Equation31711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31712_implies_Equation2 (G : Type*) [Magma G] (h : Equation31712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31713_implies_Equation2 (G : Type*) [Magma G] (h : Equation31713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31714_implies_Equation2 (G : Type*) [Magma G] (h : Equation31714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31716_implies_Equation2 (G : Type*) [Magma G] (h : Equation31716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X3 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ X1) ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X4) ◇ (X5 ◇ X0)))) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0))) = X0 := superpose eq7 eq10
  have eq30 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq18 eq11
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq18 eq7
  have eq41 (X0 X1 : G) : X0 = X1 := superpose eq32 eq30
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq46 eq41


@[equational_result]
theorem Equation31717_implies_Equation2 (G : Type*) [Magma G] (h : Equation31717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation31718_implies_Equation2 (G : Type*) [Magma G] (h : Equation31718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation31719_implies_Equation2 (G : Type*) [Magma G] (h : Equation31719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31721_implies_Equation2 (G : Type*) [Magma G] (h : Equation31721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31722_implies_Equation2 (G : Type*) [Magma G] (h : Equation31722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31723_implies_Equation2 (G : Type*) [Magma G] (h : Equation31723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31724_implies_Equation2 (G : Type*) [Magma G] (h : Equation31724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31726_implies_Equation2 (G : Type*) [Magma G] (h : Equation31726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31727_implies_Equation2 (G : Type*) [Magma G] (h : Equation31727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31728_implies_Equation2 (G : Type*) [Magma G] (h : Equation31728 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31729_implies_Equation2 (G : Type*) [Magma G] (h : Equation31729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31731_implies_Equation2 (G : Type*) [Magma G] (h : Equation31731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31732_implies_Equation2 (G : Type*) [Magma G] (h : Equation31732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31733_implies_Equation2 (G : Type*) [Magma G] (h : Equation31733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31734_implies_Equation2 (G : Type*) [Magma G] (h : Equation31734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31736_implies_Equation2 (G : Type*) [Magma G] (h : Equation31736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31737_implies_Equation2 (G : Type*) [Magma G] (h : Equation31737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31738_implies_Equation2 (G : Type*) [Magma G] (h : Equation31738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31739_implies_Equation2 (G : Type*) [Magma G] (h : Equation31739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31740_implies_Equation2 (G : Type*) [Magma G] (h : Equation31740 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31742_implies_Equation2 (G : Type*) [Magma G] (h : Equation31742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation31743_implies_Equation2 (G : Type*) [Magma G] (h : Equation31743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation31744_implies_Equation2 (G : Type*) [Magma G] (h : Equation31744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation31745_implies_Equation2 (G : Type*) [Magma G] (h : Equation31745 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31747_implies_Equation2 (G : Type*) [Magma G] (h : Equation31747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation31748_implies_Equation2 (G : Type*) [Magma G] (h : Equation31748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq62 eq15


@[equational_result]
theorem Equation31749_implies_Equation2 (G : Type*) [Magma G] (h : Equation31749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X5 ◇ X1))) ◇ X4) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X3 ◇ (X4 ◇ X1)) ◇ (X0 ◇ X2))) = X4 := superpose eq7 eq7
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq9 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq45 eq36


@[equational_result]
theorem Equation31750_implies_Equation2 (G : Type*) [Magma G] (h : Equation31750 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31752_implies_Equation2 (G : Type*) [Magma G] (h : Equation31752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X5 ◇ (X2 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X3)))))) ◇ X1) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X4 ◇ X5) ◇ (X0 ◇ X4))) = ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X1) = X3 := superpose eq7 eq9
  have eq20 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X5) ◇ (X1 ◇ X4))))) ◇ ((X6 ◇ X7) ◇ (X0 ◇ X6)))) = X2 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = ((X6 ◇ ((X1 ◇ X7) ◇ (X2 ◇ ((X4 ◇ X5) ◇ (X0 ◇ X4))))) ◇ X6) := superpose eq7 eq10
  have eq76 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq16 eq29
  have eq77 (X0 X2 X6 : G) : (X0 ◇ X6) = X2 := superpose eq76 eq20
  have eq94 (X0 X3 : G) : X0 = X3 := superpose eq77 eq77
  have eq105 (X0 : G) : sK0 ≠ X0 := superpose eq94 eq8
  subsumption eq105 eq94


@[equational_result]
theorem Equation31753_implies_Equation2 (G : Type*) [Magma G] (h : Equation31753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31754_implies_Equation2 (G : Type*) [Magma G] (h : Equation31754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation31755_implies_Equation2 (G : Type*) [Magma G] (h : Equation31755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31757_implies_Equation2 (G : Type*) [Magma G] (h : Equation31757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation31758_implies_Equation2 (G : Type*) [Magma G] (h : Equation31758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation31759_implies_Equation2 (G : Type*) [Magma G] (h : Equation31759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation31760_implies_Equation2 (G : Type*) [Magma G] (h : Equation31760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31762_implies_Equation2 (G : Type*) [Magma G] (h : Equation31762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation31763_implies_Equation2 (G : Type*) [Magma G] (h : Equation31763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31764_implies_Equation2 (G : Type*) [Magma G] (h : Equation31764 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31765_implies_Equation2 (G : Type*) [Magma G] (h : Equation31765 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31766_implies_Equation2 (G : Type*) [Magma G] (h : Equation31766 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X7 X9 : G) : (X0 ◇ X9) = X7 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31768_implies_Equation2 (G : Type*) [Magma G] (h : Equation31768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq43 eq15


@[equational_result]
theorem Equation31769_implies_Equation2 (G : Type*) [Magma G] (h : Equation31769 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq62 eq15


@[equational_result]
theorem Equation31770_implies_Equation2 (G : Type*) [Magma G] (h : Equation31770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X5))) ◇ X4) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) ◇ ((X4 ◇ X5) ◇ X0)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq9 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation31771_implies_Equation2 (G : Type*) [Magma G] (h : Equation31771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) ◇ ((X4 ◇ X5) ◇ X0)) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation31773_implies_Equation2 (G : Type*) [Magma G] (h : Equation31773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31774_implies_Equation2 (G : Type*) [Magma G] (h : Equation31774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31775_implies_Equation2 (G : Type*) [Magma G] (h : Equation31775 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31776_implies_Equation2 (G : Type*) [Magma G] (h : Equation31776 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31778_implies_Equation2 (G : Type*) [Magma G] (h : Equation31778 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31779_implies_Equation2 (G : Type*) [Magma G] (h : Equation31779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31780_implies_Equation2 (G : Type*) [Magma G] (h : Equation31780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31781_implies_Equation2 (G : Type*) [Magma G] (h : Equation31781 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31783_implies_Equation2 (G : Type*) [Magma G] (h : Equation31783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31784_implies_Equation2 (G : Type*) [Magma G] (h : Equation31784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31785_implies_Equation2 (G : Type*) [Magma G] (h : Equation31785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31786_implies_Equation2 (G : Type*) [Magma G] (h : Equation31786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31788_implies_Equation2 (G : Type*) [Magma G] (h : Equation31788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31789_implies_Equation2 (G : Type*) [Magma G] (h : Equation31789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31790_implies_Equation2 (G : Type*) [Magma G] (h : Equation31790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31791_implies_Equation2 (G : Type*) [Magma G] (h : Equation31791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31792_implies_Equation2 (G : Type*) [Magma G] (h : Equation31792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31794_implies_Equation2 (G : Type*) [Magma G] (h : Equation31794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ ((X3 ◇ X4) ◇ (X3 ◇ X0))) ◇ X5))) ◇ X1) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq9
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq7 eq18
  have eq141 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq141 eq50


@[equational_result]
theorem Equation31795_implies_Equation2 (G : Type*) [Magma G] (h : Equation31795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31796_implies_Equation2 (G : Type*) [Magma G] (h : Equation31796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation31797_implies_Equation2 (G : Type*) [Magma G] (h : Equation31797 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation31799_implies_Equation2 (G : Type*) [Magma G] (h : Equation31799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31800_implies_Equation2 (G : Type*) [Magma G] (h : Equation31800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31801_implies_Equation2 (G : Type*) [Magma G] (h : Equation31801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31802_implies_Equation2 (G : Type*) [Magma G] (h : Equation31802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31804_implies_Equation2 (G : Type*) [Magma G] (h : Equation31804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31805_implies_Equation2 (G : Type*) [Magma G] (h : Equation31805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31806_implies_Equation2 (G : Type*) [Magma G] (h : Equation31806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31807_implies_Equation2 (G : Type*) [Magma G] (h : Equation31807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31809_implies_Equation2 (G : Type*) [Magma G] (h : Equation31809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31810_implies_Equation2 (G : Type*) [Magma G] (h : Equation31810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31811_implies_Equation2 (G : Type*) [Magma G] (h : Equation31811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation31812_implies_Equation2 (G : Type*) [Magma G] (h : Equation31812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31814_implies_Equation2 (G : Type*) [Magma G] (h : Equation31814 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31815_implies_Equation2 (G : Type*) [Magma G] (h : Equation31815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31816_implies_Equation2 (G : Type*) [Magma G] (h : Equation31816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31817_implies_Equation2 (G : Type*) [Magma G] (h : Equation31817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31818_implies_Equation2 (G : Type*) [Magma G] (h : Equation31818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31820_implies_Equation2 (G : Type*) [Magma G] (h : Equation31820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X1) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation31821_implies_Equation2 (G : Type*) [Magma G] (h : Equation31821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation31822_implies_Equation2 (G : Type*) [Magma G] (h : Equation31822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation31823_implies_Equation2 (G : Type*) [Magma G] (h : Equation31823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation31825_implies_Equation2 (G : Type*) [Magma G] (h : Equation31825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31826_implies_Equation2 (G : Type*) [Magma G] (h : Equation31826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31827_implies_Equation2 (G : Type*) [Magma G] (h : Equation31827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31828_implies_Equation2 (G : Type*) [Magma G] (h : Equation31828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31830_implies_Equation2 (G : Type*) [Magma G] (h : Equation31830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31831_implies_Equation2 (G : Type*) [Magma G] (h : Equation31831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31832_implies_Equation2 (G : Type*) [Magma G] (h : Equation31832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31833_implies_Equation2 (G : Type*) [Magma G] (h : Equation31833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31835_implies_Equation2 (G : Type*) [Magma G] (h : Equation31835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31836_implies_Equation2 (G : Type*) [Magma G] (h : Equation31836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31837_implies_Equation2 (G : Type*) [Magma G] (h : Equation31837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation31838_implies_Equation2 (G : Type*) [Magma G] (h : Equation31838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31840_implies_Equation2 (G : Type*) [Magma G] (h : Equation31840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31841_implies_Equation2 (G : Type*) [Magma G] (h : Equation31841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31842_implies_Equation2 (G : Type*) [Magma G] (h : Equation31842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31843_implies_Equation2 (G : Type*) [Magma G] (h : Equation31843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31844_implies_Equation2 (G : Type*) [Magma G] (h : Equation31844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31846_implies_Equation2 (G : Type*) [Magma G] (h : Equation31846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation31847_implies_Equation2 (G : Type*) [Magma G] (h : Equation31847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X2) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31848_implies_Equation2 (G : Type*) [Magma G] (h : Equation31848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X4) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation31849_implies_Equation2 (G : Type*) [Magma G] (h : Equation31849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X6) = X7 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31850_implies_Equation2 (G : Type*) [Magma G] (h : Equation31850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X0))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X8 X9 : G) : (X0 ◇ X9) = X8 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation31852_implies_Equation2 (G : Type*) [Magma G] (h : Equation31852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X1))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31853_implies_Equation2 (G : Type*) [Magma G] (h : Equation31853 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X1))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31854_implies_Equation2 (G : Type*) [Magma G] (h : Equation31854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X1))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31855_implies_Equation2 (G : Type*) [Magma G] (h : Equation31855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X1))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31856_implies_Equation2 (G : Type*) [Magma G] (h : Equation31856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X1))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31858_implies_Equation2 (G : Type*) [Magma G] (h : Equation31858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X2))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31859_implies_Equation2 (G : Type*) [Magma G] (h : Equation31859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X2))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31860_implies_Equation2 (G : Type*) [Magma G] (h : Equation31860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X2))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31861_implies_Equation2 (G : Type*) [Magma G] (h : Equation31861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X2))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31862_implies_Equation2 (G : Type*) [Magma G] (h : Equation31862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X2))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31864_implies_Equation2 (G : Type*) [Magma G] (h : Equation31864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31865_implies_Equation2 (G : Type*) [Magma G] (h : Equation31865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31866_implies_Equation2 (G : Type*) [Magma G] (h : Equation31866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31867_implies_Equation2 (G : Type*) [Magma G] (h : Equation31867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31868_implies_Equation2 (G : Type*) [Magma G] (h : Equation31868 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31870_implies_Equation2 (G : Type*) [Magma G] (h : Equation31870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X4))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31871_implies_Equation2 (G : Type*) [Magma G] (h : Equation31871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X4))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31872_implies_Equation2 (G : Type*) [Magma G] (h : Equation31872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X4))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31873_implies_Equation2 (G : Type*) [Magma G] (h : Equation31873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X4))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation31874_implies_Equation2 (G : Type*) [Magma G] (h : Equation31874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X4))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31876_implies_Equation2 (G : Type*) [Magma G] (h : Equation31876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31877_implies_Equation2 (G : Type*) [Magma G] (h : Equation31877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31878_implies_Equation2 (G : Type*) [Magma G] (h : Equation31878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31879_implies_Equation2 (G : Type*) [Magma G] (h : Equation31879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31880_implies_Equation2 (G : Type*) [Magma G] (h : Equation31880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation31881_implies_Equation2 (G : Type*) [Magma G] (h : Equation31881 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5))) ◇ X6) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32087_implies_Equation2 (G : Type*) [Magma G] (h : Equation32087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq54 eq13


@[equational_result]
theorem Equation32090_implies_Equation2 (G : Type*) [Magma G] (h : Equation32090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq56 eq14


@[equational_result]
theorem Equation32092_implies_Equation2 (G : Type*) [Magma G] (h : Equation32092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X3))) = X1 := superpose eq7 eq7
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq10 eq7
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq7 eq33
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq94 eq41


@[equational_result]
theorem Equation32093_implies_Equation2 (G : Type*) [Magma G] (h : Equation32093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq37 eq11


@[equational_result]
theorem Equation32094_implies_Equation2 (G : Type*) [Magma G] (h : Equation32094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq56 eq14


@[equational_result]
theorem Equation32097_implies_Equation2 (G : Type*) [Magma G] (h : Equation32097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq56 eq13


@[equational_result]
theorem Equation32100_implies_Equation2 (G : Type*) [Magma G] (h : Equation32100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation32102_implies_Equation2 (G : Type*) [Magma G] (h : Equation32102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X1 ◇ (((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) ◇ X3)) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = ((X0 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq9
  have eq14 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X0) = (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq12 eq12
  have eq15 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X3)) ◇ X0) := superpose eq12 eq12
  have eq19 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X0 := superpose eq12 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X1) = X0 := superpose eq12 eq7
  have eq26 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ X2) = X0 := superpose eq12 eq7
  have eq28 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ X3)) ◇ X0) := superpose eq12 eq7
  have eq33 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq19 eq19
  have eq39 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq19 eq33
  have eq119 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ (X0 ◇ (X0 ◇ X2))) = (((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq12 eq15
  have eq120 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq19 eq15
  have eq143 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq15 eq12
  have eq167 (X0 X2 X3 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq26 eq119
  have eq168 (X0 X3 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X3)) ◇ X0) := superpose eq167 eq14
  have eq172 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq167 eq23
  have eq174 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq168 eq12
  have eq181 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq168 eq39
  have eq202 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X0)) ◇ X3)) ◇ X0) := superpose eq174 eq28
  have eq219 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq168 eq120
  have eq220 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq168 eq219
  have eq221 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq172 eq220
  have eq256 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq168 eq143
  have eq257 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq168 eq256
  have eq260 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq257 eq181
  have eq264 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq221 eq260
  have eq265 (X0 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X0) = X0 := superpose eq264 eq168
  have eq270 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3)) ◇ X0) := superpose eq264 eq202
  have eq281 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = ((X0 ◇ (X0 ◇ X3)) ◇ X0) := superpose eq265 eq270
  have eq282 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq265 eq281
  have eq289 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X0 := superpose eq282 eq7
  have eq468 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq289 eq289
  have eq470 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X0 := superpose eq172 eq468
  have eq478 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq470 eq289
  have eq490 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq478 eq470
  have eq495 (X0 X1 : G) : X0 = X1 := superpose eq478 eq490
  have eq497 (X0 : G) : sK0 ≠ X0 := superpose eq495 eq8
  subsumption eq497 eq495


@[equational_result]
theorem Equation32104_implies_Equation2 (G : Type*) [Magma G] (h : Equation32104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq70 eq13


@[equational_result]
theorem Equation32106_implies_Equation2 (G : Type*) [Magma G] (h : Equation32106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ X0))) = X1 := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : ((X2 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ X2) = X1 := superpose eq10 eq7
  have eq48 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) = X2 := superpose eq11 eq7
  have eq51 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = X1 := superpose eq48 eq23
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq7 eq51
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq140 eq58


@[equational_result]
theorem Equation32107_implies_Equation2 (G : Type*) [Magma G] (h : Equation32107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation32108_implies_Equation2 (G : Type*) [Magma G] (h : Equation32108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq58 eq14


@[equational_result]
theorem Equation32110_implies_Equation2 (G : Type*) [Magma G] (h : Equation32110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ (X0 ◇ X3)) ◇ X2)) = ((X1 ◇ (((X2 ◇ ((X0 ◇ (X0 ◇ X3)) ◇ X2)) ◇ X0) ◇ X1)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X2 ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ X2) := superpose eq10 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X2) := superpose eq10 eq14
  have eq17 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq7 eq16
  have eq25 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = ((X2 ◇ (X0 ◇ X2)) ◇ X2) := superpose eq7 eq9
  have eq32 (X0 X2 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ X2) = (X0 ◇ X0) := superpose eq17 eq25
  have eq37 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq17
  have eq48 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq37 eq7
  have eq58 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq48 eq32
  have eq78 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq48 eq48
  have eq85 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq78 eq48
  have eq90 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq37 eq85
  have eq91 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq58 eq90
  have eq96 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq91 eq48
  have eq101 (X0 X2 : G) : X0 = X2 := superpose eq96 eq96
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq101 eq8
  subsumption eq106 eq101


@[equational_result]
theorem Equation32112_implies_Equation2 (G : Type*) [Magma G] (h : Equation32112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation32115_implies_Equation2 (G : Type*) [Magma G] (h : Equation32115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq52 eq13


@[equational_result]
theorem Equation32116_implies_Equation2 (G : Type*) [Magma G] (h : Equation32116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq57 eq14


@[equational_result]
theorem Equation32118_implies_Equation2 (G : Type*) [Magma G] (h : Equation32118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ ((X0 ◇ (X0 ◇ X4)) ◇ X5))) = X1 := superpose eq7 eq7
  have eq59 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq11 eq7
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq59
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq157 eq67


@[equational_result]
theorem Equation32119_implies_Equation2 (G : Type*) [Magma G] (h : Equation32119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq55 eq12


@[equational_result]
theorem Equation32120_implies_Equation2 (G : Type*) [Magma G] (h : Equation32120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq55 eq12


@[equational_result]
theorem Equation32121_implies_Equation2 (G : Type*) [Magma G] (h : Equation32121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation32124_implies_Equation2 (G : Type*) [Magma G] (h : Equation32124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation32127_implies_Equation2 (G : Type*) [Magma G] (h : Equation32127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ ((X2 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation32129_implies_Equation2 (G : Type*) [Magma G] (h : Equation32129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) := superpose eq7 eq10
  have eq12 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq10 eq7
  have eq19 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2)) ◇ (X0 ◇ X3)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2))) := superpose eq10 eq9
  have eq24 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))))) := superpose eq9 eq10
  have eq25 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X3)) = ((((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X0)) := superpose eq9 eq10
  have eq28 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X3)) = ((X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) ◇ X1) := superpose eq7 eq25
  have eq29 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) ◇ X1)) := superpose eq28 eq24
  have eq32 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)))) := superpose eq10 eq11
  have eq38 (X0 X1 : G) : ((((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq11 eq10
  have eq39 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = ((X0 ◇ (((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) ◇ X0) := superpose eq11 eq7
  have eq51 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X2)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq10 eq12
  have eq55 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2)) = ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X0) := superpose eq10 eq12
  have eq82 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2)) = X1 := superpose eq7 eq55
  have eq83 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = ((X1 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq82 eq19
  have eq84 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq82 eq14
  have eq85 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq82 eq32
  have eq88 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq83 eq29
  have eq92 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X2)) := superpose eq88 eq51
  have eq102 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq84 eq92
  have eq105 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = ((X0 ◇ (((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X1) ◇ X2)) ◇ X0) := superpose eq85 eq39
  have eq106 (X0 X1 : G) : ((((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X1) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X1)) = X0 := superpose eq85 eq38
  have eq109 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = ((X0 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq105
  have eq110 (X0 X1 : G) : ((X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X0) = X0 := superpose eq7 eq106
  have eq111 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq11 eq110
  have eq112 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq111 eq10
  have eq115 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = X1 := superpose eq111 eq83
  have eq117 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq111 eq85
  have eq124 (X0 X1 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose eq115 eq109
  have eq126 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq124 eq11
  have eq133 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq126 eq102
  have eq135 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq126 eq112
  have eq143 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq126 eq117
  have eq144 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq143 eq133
  have eq156 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq144 eq135
  have eq167 (X0 X2 : G) : X0 = X2 := superpose eq156 eq156
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq167 eq8
  subsumption eq169 eq167


@[equational_result]
theorem Equation32130_implies_Equation2 (G : Type*) [Magma G] (h : Equation32130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3) = X2 := superpose eq10 eq9
  have eq27 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ X2)) := superpose eq9 eq10
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq27 eq10
  have eq36 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) = X0 := superpose eq27 eq7
  have eq63 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq35 eq10
  have eq96 (X0 X1 X2 : G) : (((X1 ◇ ((((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X0)) ◇ X0) ◇ X2) = X0 := superpose eq36 eq9
  have eq106 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ X2) = X0 := superpose eq7 eq96
  have eq148 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) := superpose eq9 eq106
  have eq150 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq27 eq106
  have eq167 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq150 eq63
  have eq169 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq167 eq35
  have eq196 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3) = X2 := superpose eq169 eq16
  have eq198 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq169 eq36
  have eq218 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X0 := superpose eq27 eq198
  have eq219 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq218 eq148
  have eq222 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq218 eq219
  have eq223 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq218 eq222
  have eq228 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X2 ◇ X0) ◇ X3)) ◇ X3) = X2 := superpose eq223 eq196
  have eq271 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X3) = X2 := superpose eq223 eq228
  have eq272 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X3) = X2 := superpose eq223 eq271
  have eq273 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq223 eq272
  have eq274 (X0 X3 : G) : X0 = X3 := superpose eq273 eq273
  have eq276 (X0 : G) : sK0 ≠ X0 := superpose eq274 eq8
  subsumption eq276 eq274


@[equational_result]
theorem Equation32131_implies_Equation2 (G : Type*) [Magma G] (h : Equation32131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation32134_implies_Equation2 (G : Type*) [Magma G] (h : Equation32134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation32137_implies_Equation2 (G : Type*) [Magma G] (h : Equation32137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ ((X2 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation32139_implies_Equation2 (G : Type*) [Magma G] (h : Equation32139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X2)) = ((X1 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ X2))) ◇ X0) = X1 := superpose eq7 eq10
  have eq15 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := superpose eq10 eq7
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2))) ◇ X0) = X1 := superpose eq15 eq13
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = ((X1 ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2)) := superpose eq15 eq9
  have eq33 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2))) := superpose eq18 eq18
  have eq41 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X3)) = ((X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X2)) ◇ X4)) ◇ X0) := superpose eq18 eq7
  have eq52 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X3)) = ((X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X2)) ◇ X4)) ◇ X0) := superpose eq15 eq41
  have eq53 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X3)) = ((X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X2)) ◇ X4)) ◇ X0) := superpose eq15 eq52
  have eq55 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq15 eq15
  have eq65 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq15 eq18
  have eq71 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X2))) := superpose eq55 eq33
  have eq82 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq15 eq65
  have eq83 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ X2)) := superpose eq15 eq82
  have eq85 (X0 X1 X3 X4 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X3)) = ((X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) ◇ X4)) ◇ X0) := superpose eq83 eq53
  have eq88 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X3)) := superpose eq7 eq85
  have eq93 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) ◇ X1)) ◇ X0) = X1 := superpose eq88 eq17
  have eq94 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = ((X1 ◇ X1) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X0)) := superpose eq88 eq71
  have eq97 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose eq7 eq94
  have eq98 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = X1 := superpose eq97 eq93
  have eq120 (X0 X1 : G) : X0 = X1 := superpose eq10 eq98
  have eq234 (X0 : G) : sK0 ≠ X0 := superpose eq120 eq8
  subsumption eq234 eq120


@[equational_result]
theorem Equation32141_implies_Equation2 (G : Type*) [Magma G] (h : Equation32141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation32143_implies_Equation2 (G : Type*) [Magma G] (h : Equation32143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0)) = ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0)))) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) := superpose eq7 eq11
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2))) = X1 := superpose eq11 eq11
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0))) ◇ X0) = X1 := superpose eq7 eq11
  have eq21 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0)) = ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X1) := superpose eq12 eq10
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = X1 := superpose eq12 eq16
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ X1) = ((X1 ◇ X2) ◇ X1) := superpose eq22 eq21
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X0 := superpose eq7 eq23
  have eq52 (X0 X1 X3 : G) : (X0 ◇ X3) = X1 := superpose eq28 eq13
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq52 eq52
  have eq88 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq88 eq55


@[equational_result]
theorem Equation32145_implies_Equation2 (G : Type*) [Magma G] (h : Equation32145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation32147_implies_Equation2 (G : Type*) [Magma G] (h : Equation32147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ ((X3 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2))) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ ((X3 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)))) = ((X1 ◇ (X3 ◇ X1)) ◇ X1) := superpose eq7 eq10
  have eq17 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X2)) = X1 := superpose eq10 eq7
  have eq20 (X0 X1 X2 X3 : G) : (((X1 ◇ (X3 ◇ X1)) ◇ X1) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) = X3 := superpose eq11 eq9
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ ((X4 ◇ ((X0 ◇ X2) ◇ X5)) ◇ (X0 ◇ X2)))) := superpose eq10 eq20
  have eq37 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X0 ◇ X1))) = (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X2 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq20 eq10
  have eq43 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X4 ◇ X0)) ◇ X0)) := superpose eq10 eq27
  have eq44 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = (X1 ◇ ((X0 ◇ (X4 ◇ X0)) ◇ X0)) := superpose eq17 eq43
  have eq313 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X0) = X1 := superpose eq44 eq7
  have eq321 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = (((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X0) ◇ (X0 ◇ X4)) := superpose eq44 eq17
  have eq387 (X0 X1 X3 X4 : G) : (X1 ◇ X3) = (X1 ◇ (X0 ◇ X4)) := superpose eq313 eq321
  have eq400 (X0 X1 X4 X5 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X4 ◇ X5)) = X0 := superpose eq20 eq387
  have eq526 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq400 eq37
  have eq871 (X0 X2 : G) : X0 = X2 := superpose eq7 eq526
  have eq921 (X0 : G) : sK0 ≠ X0 := superpose eq871 eq8
  subsumption eq921 eq871


@[equational_result]
theorem Equation32149_implies_Equation2 (G : Type*) [Magma G] (h : Equation32149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ ((X3 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation32153_implies_Equation2 (G : Type*) [Magma G] (h : Equation32153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation32155_implies_Equation2 (G : Type*) [Magma G] (h : Equation32155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4))) ◇ X0) = X1 := superpose eq7 eq11
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = X1 := superpose eq12 eq16
  have eq65 (X0 X1 : G) : X0 = X1 := superpose eq11 eq21
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq157 eq65


@[equational_result]
theorem Equation32156_implies_Equation2 (G : Type*) [Magma G] (h : Equation32156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq11 eq11
  have eq46 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq171 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq171 eq46


@[equational_result]
theorem Equation32157_implies_Equation2 (G : Type*) [Magma G] (h : Equation32157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X3) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq11 eq11
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq168 eq47


@[equational_result]
theorem Equation32158_implies_Equation2 (G : Type*) [Magma G] (h : Equation32158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X6 X7 : G) : (((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ ((X4 ◇ X0) ◇ X6)) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation32160_implies_Equation2 (G : Type*) [Magma G] (h : Equation32160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X0 := superpose eq10 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq10 eq9
  have eq21 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq10 eq12
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq21 eq13
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq37 eq32


@[equational_result]
theorem Equation32161_implies_Equation2 (G : Type*) [Magma G] (h : Equation32161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq38 eq12


@[equational_result]
theorem Equation32162_implies_Equation2 (G : Type*) [Magma G] (h : Equation32162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation32164_implies_Equation2 (G : Type*) [Magma G] (h : Equation32164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq28 eq13


@[equational_result]
theorem Equation32165_implies_Equation2 (G : Type*) [Magma G] (h : Equation32165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq56 eq16


@[equational_result]
theorem Equation32166_implies_Equation2 (G : Type*) [Magma G] (h : Equation32166 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32169_implies_Equation2 (G : Type*) [Magma G] (h : Equation32169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq47 eq11


@[equational_result]
theorem Equation32170_implies_Equation2 (G : Type*) [Magma G] (h : Equation32170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32172_implies_Equation2 (G : Type*) [Magma G] (h : Equation32172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation32173_implies_Equation2 (G : Type*) [Magma G] (h : Equation32173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation32174_implies_Equation2 (G : Type*) [Magma G] (h : Equation32174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation32175_implies_Equation2 (G : Type*) [Magma G] (h : Equation32175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32177_implies_Equation2 (G : Type*) [Magma G] (h : Equation32177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation32179_implies_Equation2 (G : Type*) [Magma G] (h : Equation32179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq46 eq13


@[equational_result]
theorem Equation32181_implies_Equation2 (G : Type*) [Magma G] (h : Equation32181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq32 eq15


@[equational_result]
theorem Equation32183_implies_Equation2 (G : Type*) [Magma G] (h : Equation32183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq24 eq16


@[equational_result]
theorem Equation32187_implies_Equation2 (G : Type*) [Magma G] (h : Equation32187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32189_implies_Equation2 (G : Type*) [Magma G] (h : Equation32189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation32190_implies_Equation2 (G : Type*) [Magma G] (h : Equation32190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X5)) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X4))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X3 ◇ X2))) = X2 := superpose eq7 eq7
  have eq41 (X0 X2 : G) : X0 = X2 := superpose eq11 eq9
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq50 eq41


@[equational_result]
theorem Equation32191_implies_Equation2 (G : Type*) [Magma G] (h : Equation32191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq46 eq15


@[equational_result]
theorem Equation32192_implies_Equation2 (G : Type*) [Magma G] (h : Equation32192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32194_implies_Equation2 (G : Type*) [Magma G] (h : Equation32194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X3 ◇ X3)) ◇ X0))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq10 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq15 eq7
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq31 eq29


@[equational_result]
theorem Equation32195_implies_Equation2 (G : Type*) [Magma G] (h : Equation32195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq49 eq11


@[equational_result]
theorem Equation32196_implies_Equation2 (G : Type*) [Magma G] (h : Equation32196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation32200_implies_Equation2 (G : Type*) [Magma G] (h : Equation32200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation32203_implies_Equation2 (G : Type*) [Magma G] (h : Equation32203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq66 eq11


@[equational_result]
theorem Equation32204_implies_Equation2 (G : Type*) [Magma G] (h : Equation32204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq69 eq12


@[equational_result]
theorem Equation32206_implies_Equation2 (G : Type*) [Magma G] (h : Equation32206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation32207_implies_Equation2 (G : Type*) [Magma G] (h : Equation32207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation32208_implies_Equation2 (G : Type*) [Magma G] (h : Equation32208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation32209_implies_Equation2 (G : Type*) [Magma G] (h : Equation32209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32211_implies_Equation2 (G : Type*) [Magma G] (h : Equation32211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation32212_implies_Equation2 (G : Type*) [Magma G] (h : Equation32212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation32213_implies_Equation2 (G : Type*) [Magma G] (h : Equation32213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq46 eq13


@[equational_result]
theorem Equation32214_implies_Equation2 (G : Type*) [Magma G] (h : Equation32214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32216_implies_Equation2 (G : Type*) [Magma G] (h : Equation32216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq31 eq14


@[equational_result]
theorem Equation32217_implies_Equation2 (G : Type*) [Magma G] (h : Equation32217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X3))) = X2 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq67 eq21


@[equational_result]
theorem Equation32218_implies_Equation2 (G : Type*) [Magma G] (h : Equation32218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ ((X0 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X2)) = ((X1 ◇ (X0 ◇ X1)) ◇ X5) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 X5 : G) : (X2 ◇ ((X0 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X2)) = X5 := superpose eq11 eq10
  have eq15 (X2 X5 : G) : (X2 ◇ X2) = X5 := superpose eq11 eq13
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq15 eq15
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq28 eq16


@[equational_result]
theorem Equation32219_implies_Equation2 (G : Type*) [Magma G] (h : Equation32219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32221_implies_Equation2 (G : Type*) [Magma G] (h : Equation32221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ ((X0 ◇ (X4 ◇ X5)) ◇ X4))) = X1 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X3 ◇ X4)) = X0 := superpose eq7 eq11
  have eq35 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq22 eq12
  have eq36 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq35 eq7
  have eq48 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq35 eq36
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq48 eq48
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq51 eq49


@[equational_result]
theorem Equation32222_implies_Equation2 (G : Type*) [Magma G] (h : Equation32222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq76 eq12


@[equational_result]
theorem Equation32223_implies_Equation2 (G : Type*) [Magma G] (h : Equation32223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation32224_implies_Equation2 (G : Type*) [Magma G] (h : Equation32224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32226_implies_Equation2 (G : Type*) [Magma G] (h : Equation32226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation32227_implies_Equation2 (G : Type*) [Magma G] (h : Equation32227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq54 eq13


@[equational_result]
theorem Equation32228_implies_Equation2 (G : Type*) [Magma G] (h : Equation32228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32229_implies_Equation2 (G : Type*) [Magma G] (h : Equation32229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32231_implies_Equation2 (G : Type*) [Magma G] (h : Equation32231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation32232_implies_Equation2 (G : Type*) [Magma G] (h : Equation32232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq56 eq13


@[equational_result]
theorem Equation32233_implies_Equation2 (G : Type*) [Magma G] (h : Equation32233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32234_implies_Equation2 (G : Type*) [Magma G] (h : Equation32234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32235_implies_Equation2 (G : Type*) [Magma G] (h : Equation32235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X9 : G) : (X0 ◇ X9) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32238_implies_Equation2 (G : Type*) [Magma G] (h : Equation32238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation32241_implies_Equation2 (G : Type*) [Magma G] (h : Equation32241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq68 eq13


@[equational_result]
theorem Equation32243_implies_Equation2 (G : Type*) [Magma G] (h : Equation32243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2)) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X0) = X1 := superpose eq10 eq7
  have eq43 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ X0) = X1 := superpose eq10 eq14
  have eq44 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq9 eq14
  have eq45 (X0 X1 X2 : G) : ((X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0) = X1 := superpose eq10 eq14
  have eq51 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) := superpose eq10 eq44
  have eq75 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := superpose eq10 eq43
  have eq93 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq14 eq75
  have eq96 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq93 eq51
  have eq136 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq93 eq96
  have eq137 (X0 X1 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0) = X1 := superpose eq136 eq45
  have eq142 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq136 eq137
  have eq257 (X0 X1 : G) : X0 = X1 := superpose eq136 eq142
  have eq262 (X0 : G) : sK0 ≠ X0 := superpose eq257 eq8
  subsumption eq262 eq257


@[equational_result]
theorem Equation32245_implies_Equation2 (G : Type*) [Magma G] (h : Equation32245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) ◇ (X0 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation32248_implies_Equation2 (G : Type*) [Magma G] (h : Equation32248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq62 eq14


@[equational_result]
theorem Equation32251_implies_Equation2 (G : Type*) [Magma G] (h : Equation32251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq76 eq14


@[equational_result]
theorem Equation32253_implies_Equation2 (G : Type*) [Magma G] (h : Equation32253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ X1)) = X0 := superpose eq7 eq10
  have eq79 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq13 eq13
  have eq117 (X0 X3 : G) : X0 = X3 := superpose eq13 eq79
  have eq204 (X0 : G) : sK0 ≠ X0 := superpose eq117 eq8
  subsumption eq204 eq117


@[equational_result]
theorem Equation32254_implies_Equation2 (G : Type*) [Magma G] (h : Equation32254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) = ((X1 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X3) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X1)) = X0 := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) ◇ X2) := superpose eq10 eq7
  have eq17 (X0 X1 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1)) = X0 := superpose eq10 eq13
  have eq18 (X0 X1 : G) : (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1))) = X0 := superpose eq10 eq17
  have eq39 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2)) = X0 := superpose eq7 eq9
  have eq45 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2)) ◇ X4)) ◇ X4) = X3 := superpose eq9 eq7
  have eq48 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) ◇ X2) := superpose eq9 eq7
  have eq70 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq7 eq18
  have eq75 (X0 : G) : (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose eq10 eq18
  have eq84 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq70 eq75
  have eq85 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := superpose eq10 eq84
  have eq96 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1)) = X0 := superpose eq10 eq39
  have eq101 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq39 eq39
  have eq112 (X0 X1 X2 : G) : (X0 ◇ X1) = (X1 ◇ (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) ◇ X1)) := superpose eq39 eq10
  have eq159 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq10 eq101
  have eq179 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq159 eq85
  have eq206 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X3) = ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2))) ◇ X4)) ◇ X4) := superpose eq9 eq16
  have eq207 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) ◇ X1) = ((((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) ◇ ((((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) ◇ (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) ◇ X0)) ◇ X3)) ◇ X3) := superpose eq39 eq16
  have eq213 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq101 eq16
  have eq226 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq16 eq7
  have eq243 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq179 eq213
  have eq244 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq179 eq243
  have eq301 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = ((X2 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))) ◇ X2) := superpose eq9 eq48
  have eq320 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)))) = ((X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3)) ◇ X3) := superpose eq48 eq16
  have eq335 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq244 eq244
  have eq363 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) := superpose eq226 eq335
  have eq364 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq363 eq96
  have eq365 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X3) = (X0 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)))) := superpose eq364 eq320
  have eq373 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)))) = X0 := superpose eq244 eq365
  have eq375 (X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = (X2 ◇ X2) := superpose eq373 eq301
  have eq377 (X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = X2 := superpose eq179 eq375
  have eq381 (X0 X1 X3 X4 : G) : (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X3) = ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X4)) ◇ X4) := superpose eq377 eq206
  have eq383 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) ◇ X1) = ((((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) ◇ (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) ◇ X3)) ◇ X3) := superpose eq377 eq207
  have eq441 (X0 X1 X3 X4 : G) : (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X3) = (((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X4) := superpose eq377 eq381
  have eq443 (X0 X1 X3 X4 : G) : ((((X3 ◇ (X1 ◇ X3)) ◇ X0) ◇ X3) ◇ X4) = X3 := superpose eq441 eq45
  have eq450 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) ◇ X1) = ((((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) ◇ X1) ◇ X3) := superpose eq441 eq383
  have eq451 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X2) ◇ X1) = X1 := superpose eq443 eq450
  have eq452 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq451 eq112
  have eq453 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq179 eq452
  have eq464 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose eq453 eq18
  have eq556 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq453 eq464
  have eq557 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq179 eq556
  have eq582 (X0 X2 : G) : X0 = X2 := superpose eq557 eq557
  have eq602 (X0 : G) : sK0 ≠ X0 := superpose eq582 eq8
  subsumption eq602 eq582


@[equational_result]
theorem Equation32255_implies_Equation2 (G : Type*) [Magma G] (h : Equation32255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (X0 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq79 eq14


@[equational_result]
theorem Equation32257_implies_Equation2 (G : Type*) [Magma G] (h : Equation32257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X0)) = ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X0)))) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0)) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X2)) = (((X2 ◇ ((X2 ◇ (X0 ◇ X4)) ◇ X0)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X2)))) ◇ (X2 ◇ ((X2 ◇ (X0 ◇ X4)) ◇ X0))) := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0)) ◇ (X0 ◇ X1)) = ((X4 ◇ ((X4 ◇ X1) ◇ (((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0)) ◇ (X0 ◇ X1)))) ◇ X4) := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) = ((((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ X4) ◇ (((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ X4) ◇ ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0)) ◇ X5)) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0)))) ◇ X0) ◇ ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ X4) ◇ (((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ X4) ◇ ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0)) ◇ X5)) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0))))) := superpose eq10 eq10
  have eq22 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0))) = X0 := superpose eq7 eq10
  have eq43 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) = X0 := superpose eq22 eq7
  have eq74 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq22 eq11
  have eq91 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)) = ((X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)))) ◇ X0) := superpose eq22 eq43
  have eq107 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)) = ((X0 ◇ X0) ◇ X0) := superpose eq22 eq91
  have eq111 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq107 eq22
  have eq112 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq111 eq43
  have eq137 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)))) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq112 eq74
  have eq138 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq112 eq107
  have eq154 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)))) ◇ (X0 ◇ X0)) := superpose eq112 eq137
  have eq155 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)))) ◇ X0) := superpose eq112 eq154
  have eq156 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq112 eq138
  have eq205 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ X4) ◇ (((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ X4) ◇ (X5 ◇ X6)) ◇ X5)) ◇ (X5 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)))) = (((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0)) ◇ (X0 ◇ (((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ X4) ◇ (((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ X4) ◇ (X5 ◇ X6)) ◇ X5)) ◇ (X5 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)))))) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0))) := superpose eq10 eq15
  have eq242 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ ((X4 ◇ ((X4 ◇ X0) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0)))) ◇ X6)) ◇ (X4 ◇ ((X4 ◇ X0) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0)))))) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0))) ◇ ((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ ((X4 ◇ ((X4 ◇ X0) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0)))) ◇ X6)) ◇ (X4 ◇ ((X4 ◇ X0) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0))))))) = X4 := superpose eq15 eq10
  have eq255 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X4 ◇ X0) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0)))) = ((X4 ◇ ((X4 ◇ X0) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0)))) ◇ (((X4 ◇ ((X4 ◇ X0) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0)))) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0))) ◇ (X4 ◇ ((X4 ◇ X0) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2)) ◇ (X2 ◇ X0)))))) := superpose eq15 eq156
  have eq281 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) ◇ X0) := superpose eq156 eq43
  have eq295 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq156 eq281
  have eq296 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq112 eq295
  have eq297 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq112 eq296
  have eq298 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X0 := superpose eq297 eq155
  have eq318 (X0 X1 X4 : G) : (X0 ◇ (X0 ◇ X1)) = ((X4 ◇ ((X4 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X4) := superpose eq298 eq15
  have eq319 (X0 X2 X4 X5 : G) : ((((X2 ◇ X4) ◇ (((X2 ◇ X4) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X5)) ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X0) ◇ ((X2 ◇ X4) ◇ (((X2 ◇ X4) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X5)) ◇ (X2 ◇ (X2 ◇ X0))))) = X2 := superpose eq298 eq21
  have eq336 (X0 X2 X4 X5 X6 : G) : (((X2 ◇ X4) ◇ (((X2 ◇ X4) ◇ (X5 ◇ X6)) ◇ X5)) ◇ (X5 ◇ X2)) = (((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (((X2 ◇ X4) ◇ (((X2 ◇ X4) ◇ (X5 ◇ X6)) ◇ X5)) ◇ (X5 ◇ X2)))) ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq298 eq205
  have eq347 (X0 X2 X4 X5 X6 : G) : ((((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ ((X4 ◇ ((X4 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X6)) ◇ (X4 ◇ ((X4 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0)))))) ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X4 ◇ X5) ◇ (((X4 ◇ X5) ◇ ((X4 ◇ ((X4 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X6)) ◇ (X4 ◇ ((X4 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0))))))) = X4 := superpose eq298 eq242
  have eq354 (X0 X2 X4 : G) : (X4 ◇ ((X4 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0)))) = ((X4 ◇ ((X4 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (((X4 ◇ ((X4 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X4 ◇ ((X4 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0)))))) := superpose eq298 eq255
  have eq425 (X0 X2 : G) : (((X2 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq298 eq319
  have eq435 (X0 X2 X5 : G) : (X5 ◇ (X5 ◇ X2)) = (((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X5 ◇ (X5 ◇ X2)))) ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq298 eq336
  have eq440 (X0 X2 X4 : G) : (((X4 ◇ ((X4 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0)))) ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X4 ◇ ((X4 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0))))) = X4 := superpose eq298 eq347
  have eq445 (X0 X2 X4 : G) : (X4 ◇ ((X4 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0)))) = ((X4 ◇ ((X4 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X4) := superpose eq440 eq354
  have eq446 (X0 X2 X4 : G) : (X2 ◇ (X2 ◇ X0)) = (X4 ◇ ((X4 ◇ X0) ◇ (X2 ◇ (X2 ◇ X0)))) := superpose eq318 eq445
  have eq453 (X0 X1 X4 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X4) := superpose eq446 eq318
  have eq469 (X0 X2 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq453 eq425
  have eq477 (X0 X2 X5 : G) : (X5 ◇ (X5 ◇ X2)) = ((X2 ◇ (X2 ◇ X0)) ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq453 eq435
  have eq484 (X2 X5 : G) : (X5 ◇ (X5 ◇ X2)) = X2 := superpose eq469 eq477
  have eq497 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq484 eq469
  have eq613 (X0 X2 : G) : X0 = X2 := superpose eq497 eq497
  have eq618 (X0 : G) : sK0 ≠ X0 := superpose eq613 eq8
  subsumption eq618 eq613


@[equational_result]
theorem Equation32259_implies_Equation2 (G : Type*) [Magma G] (h : Equation32259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ (X0 ◇ X3)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq62 eq14


@[equational_result]
theorem Equation32261_implies_Equation2 (G : Type*) [Magma G] (h : Equation32261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq11
  have eq29 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X1) = X0 := superpose eq15 eq7
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq29 eq29
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq45 eq37


@[equational_result]
theorem Equation32263_implies_Equation2 (G : Type*) [Magma G] (h : Equation32263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq76 eq14


@[equational_result]
theorem Equation32265_implies_Equation2 (G : Type*) [Magma G] (h : Equation32265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ X0) = X1 := superpose eq11 eq7
  have eq33 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = (((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq11 eq9
  have eq39 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X3 ◇ ((X1 ◇ X3) ◇ X4)) ◇ X4)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) ◇ X2) := superpose eq9 eq9
  have eq40 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2)) = X0 := superpose eq7 eq9
  have eq47 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2))) ◇ X0) := superpose eq9 eq7
  have eq58 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X3 ◇ ((X1 ◇ X3) ◇ X4)) ◇ X4)) = ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X2) := superpose eq11 eq39
  have eq59 (X0 X1 X2 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X2) = X1 := superpose eq40 eq58
  have eq145 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) = X0 := superpose eq11 eq15
  have eq221 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq59 eq59
  have eq319 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) ◇ X0)) = X0 := superpose eq145 eq40
  have eq322 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) := superpose eq145 eq7
  have eq330 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq145 eq15
  have eq333 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) ◇ X1) = X0 := superpose eq145 eq59
  have eq338 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X0)) = X0 := superpose eq221 eq319
  have eq339 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq7 eq338
  have eq341 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq339 eq330
  have eq343 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq341 eq145
  have eq344 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) = X0 := superpose eq341 eq322
  have eq379 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X1) = X0 := superpose eq343 eq333
  have eq380 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) = X0 := superpose eq343 eq379
  have eq381 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) ◇ X1) = X0 := superpose eq343 eq380
  have eq382 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X0 := superpose eq343 eq381
  have eq383 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X0 := superpose eq11 eq382
  have eq427 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ X0) := superpose eq11 eq47
  have eq614 (X0 X1 : G) : (((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) = X1 := superpose eq15 eq344
  have eq656 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) = X1 := superpose eq383 eq614
  have eq657 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq656 eq427
  have eq660 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq343 eq657
  have eq662 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq660 eq33
  have eq955 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq660 eq662
  have eq956 (X0 X2 X3 : G) : (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = (X0 ◇ X0) := superpose eq660 eq955
  have eq957 (X0 X2 X3 : G) : (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = X0 := superpose eq343 eq956
  have eq958 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ X3))) = X0 := superpose eq660 eq957
  have eq959 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq660 eq958
  have eq1045 (X0 X2 : G) : X0 = X2 := superpose eq959 eq959
  have eq1050 (X0 : G) : sK0 ≠ X0 := superpose eq1045 eq8
  subsumption eq1050 eq1045


@[equational_result]
theorem Equation32266_implies_Equation2 (G : Type*) [Magma G] (h : Equation32266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = ((X1 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X3) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X3) = (X2 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3))) := superpose eq11 eq9
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X2) = X0 := superpose eq11 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X3) = (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) := superpose eq11 eq12
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) = ((X1 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X3) := superpose eq11 eq15
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X2) = X0 := superpose eq11 eq13
  have eq29 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) ◇ X3) = X2 := superpose eq11 eq17
  have eq32 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X2)) = X1 := superpose eq11 eq17
  have eq36 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))))) ◇ X3) = X2 := superpose eq11 eq29
  have eq46 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X2))) = X1 := superpose eq11 eq32
  have eq47 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2)))) = X1 := superpose eq11 eq46
  have eq48 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) = X1 := superpose eq11 eq47
  have eq54 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq48 eq48
  have eq67 (X0 X2 X3 : G) : (X0 ◇ X3) = (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) := superpose eq54 eq16
  have eq75 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq54 eq67
  have eq79 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X3) = X2 := superpose eq75 eq36
  have eq84 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq75 eq79
  have eq85 (X0 X3 : G) : X0 = X3 := superpose eq84 eq84
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq90 eq85


@[equational_result]
theorem Equation32267_implies_Equation2 (G : Type*) [Magma G] (h : Equation32267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ (X0 ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation32269_implies_Equation2 (G : Type*) [Magma G] (h : Equation32269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ X0) = X1 := superpose eq11 eq7
  have eq23 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X0) = X1 := superpose eq11 eq7
  have eq28 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X0) ◇ X0) = X1 := superpose eq11 eq23
  have eq29 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq28
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) = X1 := superpose eq29 eq21
  have eq46 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq29 eq31
  have eq74 (X0 X1 : G) : X0 = X1 := superpose eq29 eq46
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq79 eq74


@[equational_result]
theorem Equation32270_implies_Equation2 (G : Type*) [Magma G] (h : Equation32270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) ◇ X2) ◇ X5) = X0 := superpose eq7 eq11
  have eq21 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X4)) = X0 := superpose eq7 eq11
  have eq27 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X4)) ◇ X2) = X1 := superpose eq11 eq7
  have eq34 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq21 eq27
  have eq35 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) ◇ X5) = X0 := superpose eq34 eq15
  have eq53 (X0 X1 X5 : G) : (X1 ◇ X5) = X0 := superpose eq34 eq35
  have eq54 (X0 X3 : G) : X0 = X3 := superpose eq53 eq53
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq59 eq54


@[equational_result]
theorem Equation32271_implies_Equation2 (G : Type*) [Magma G] (h : Equation32271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4))) ◇ (X0 ◇ X5)) ◇ X5) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ X3) := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X4)) = X0 := superpose eq7 eq11
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X4)) ◇ (X3 ◇ X5)) = X1 := superpose eq11 eq7
  have eq34 (X1 X3 X5 : G) : (X1 ◇ (X3 ◇ X5)) = X1 := superpose eq21 eq27
  have eq35 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4))) ◇ X5) = X3 := superpose eq34 eq10
  have eq52 (X1 X3 X5 : G) : (X1 ◇ X5) = X3 := superpose eq34 eq35
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq52 eq52
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq55 eq53


@[equational_result]
theorem Equation32272_implies_Equation2 (G : Type*) [Magma G] (h : Equation32272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X6 X7 : G) : (((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ (X0 ◇ X6)) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq79 eq14


@[equational_result]
theorem Equation32275_implies_Equation2 (G : Type*) [Magma G] (h : Equation32275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation32278_implies_Equation2 (G : Type*) [Magma G] (h : Equation32278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (((X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation32282_implies_Equation2 (G : Type*) [Magma G] (h : Equation32282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (((X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X0) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation32285_implies_Equation2 (G : Type*) [Magma G] (h : Equation32285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X0) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation32287_implies_Equation2 (G : Type*) [Magma G] (h : Equation32287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation32288_implies_Equation2 (G : Type*) [Magma G] (h : Equation32288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32290_implies_Equation2 (G : Type*) [Magma G] (h : Equation32290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation32291_implies_Equation2 (G : Type*) [Magma G] (h : Equation32291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation32292_implies_Equation2 (G : Type*) [Magma G] (h : Equation32292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32296_implies_Equation2 (G : Type*) [Magma G] (h : Equation32296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ (((X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X0) ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation32298_implies_Equation2 (G : Type*) [Magma G] (h : Equation32298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32299_implies_Equation2 (G : Type*) [Magma G] (h : Equation32299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32300_implies_Equation2 (G : Type*) [Magma G] (h : Equation32300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32302_implies_Equation2 (G : Type*) [Magma G] (h : Equation32302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32303_implies_Equation2 (G : Type*) [Magma G] (h : Equation32303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32304_implies_Equation2 (G : Type*) [Magma G] (h : Equation32304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32306_implies_Equation2 (G : Type*) [Magma G] (h : Equation32306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32307_implies_Equation2 (G : Type*) [Magma G] (h : Equation32307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32308_implies_Equation2 (G : Type*) [Magma G] (h : Equation32308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32309_implies_Equation2 (G : Type*) [Magma G] (h : Equation32309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32311_implies_Equation2 (G : Type*) [Magma G] (h : Equation32311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq7 eq9
  have eq27 (X0 X1 : G) : X0 = X1 := superpose eq7 eq17
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq69 eq27


@[equational_result]
theorem Equation32312_implies_Equation2 (G : Type*) [Magma G] (h : Equation32312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X3)) ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X0))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq15 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq11 eq11
  have eq33 (X0 X1 X2 X3 : G) : (X3 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) = (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X3 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) ◇ (X3 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2))))) := superpose eq9 eq11
  have eq36 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq15 eq7
  have eq45 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq36 eq15
  have eq47 (X0 X1 X2 X3 : G) : (X3 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) = (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X3 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)))) := superpose eq45 eq33
  have eq61 (X0 X2 X3 : G) : (X0 ◇ X0) = (X3 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) := superpose eq9 eq47
  have eq62 (X0 X2 X3 : G) : (X3 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := superpose eq45 eq61
  have eq63 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq62 eq7
  have eq78 (X0 X2 : G) : X0 = X2 := superpose eq63 eq63
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq80 eq78


@[equational_result]
theorem Equation32313_implies_Equation2 (G : Type*) [Magma G] (h : Equation32313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation32315_implies_Equation2 (G : Type*) [Magma G] (h : Equation32315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq11 eq7
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq19 eq16


@[equational_result]
theorem Equation32316_implies_Equation2 (G : Type*) [Magma G] (h : Equation32316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ X1)))) ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq11
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq13 eq9
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0)))) ◇ X2) = X3 := superpose eq13 eq10
  have eq20 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X0))) = X3 := superpose eq13 eq17
  have eq21 (X1 X2 X3 : G) : (X1 ◇ X2) = X3 := superpose eq20 eq19
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq11 eq21
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq65 eq27


@[equational_result]
theorem Equation32317_implies_Equation2 (G : Type*) [Magma G] (h : Equation32317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation32320_implies_Equation2 (G : Type*) [Magma G] (h : Equation32320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3)))) ◇ (X2 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X2)) ◇ X2) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ ((X4 ◇ (X2 ◇ X0)) ◇ X2)))) ◇ (X2 ◇ X3))) ◇ X0) ◇ X2) = X3 := superpose eq7 eq10
  have eq145 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X1)) ◇ X1) = X2 := superpose eq7 eq18
  have eq266 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X4 ◇ (X0 ◇ X3)) ◇ X0)) = ((X1 ◇ ((X1 ◇ ((X2 ◇ ((X2 ◇ X3) ◇ (X4 ◇ ((X4 ◇ (X0 ◇ X3)) ◇ X0)))) ◇ X0)) ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X4 ◇ ((X4 ◇ (X0 ◇ X3)) ◇ X0)))))) ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X4 ◇ ((X4 ◇ (X0 ◇ X3)) ◇ X0))))) := superpose eq9 eq145
  have eq308 (X0 X3 X4 : G) : (X4 ◇ ((X4 ◇ (X0 ◇ X3)) ◇ X0)) = X0 := superpose eq7 eq266
  have eq319 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq308 eq7
  have eq561 (X0 X2 : G) : X0 = X2 := superpose eq319 eq319
  have eq566 (X0 : G) : sK0 ≠ X0 := superpose eq561 eq8
  subsumption eq566 eq561


@[equational_result]
theorem Equation32321_implies_Equation2 (G : Type*) [Magma G] (h : Equation32321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2)) ◇ (X0 ◇ X3)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq77 eq14


@[equational_result]
theorem Equation32323_implies_Equation2 (G : Type*) [Magma G] (h : Equation32323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq57 eq15


@[equational_result]
theorem Equation32324_implies_Equation2 (G : Type*) [Magma G] (h : Equation32324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) = X3 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq65 eq21


@[equational_result]
theorem Equation32325_implies_Equation2 (G : Type*) [Magma G] (h : Equation32325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ X3) = X0 := superpose eq11 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32326_implies_Equation2 (G : Type*) [Magma G] (h : Equation32326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 X6 X7 : G) : (((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) ◇ (X0 ◇ X6)) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation32328_implies_Equation2 (G : Type*) [Magma G] (h : Equation32328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X1) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq7 eq9
  have eq24 (X0 X1 : G) : X0 = X1 := superpose eq7 eq15
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation32330_implies_Equation2 (G : Type*) [Magma G] (h : Equation32330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ (X0 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation32332_implies_Equation2 (G : Type*) [Magma G] (h : Equation32332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32333_implies_Equation2 (G : Type*) [Magma G] (h : Equation32333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32334_implies_Equation2 (G : Type*) [Magma G] (h : Equation32334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32336_implies_Equation2 (G : Type*) [Magma G] (h : Equation32336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32337_implies_Equation2 (G : Type*) [Magma G] (h : Equation32337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32338_implies_Equation2 (G : Type*) [Magma G] (h : Equation32338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32340_implies_Equation2 (G : Type*) [Magma G] (h : Equation32340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32341_implies_Equation2 (G : Type*) [Magma G] (h : Equation32341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32342_implies_Equation2 (G : Type*) [Magma G] (h : Equation32342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32343_implies_Equation2 (G : Type*) [Magma G] (h : Equation32343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32346_implies_Equation2 (G : Type*) [Magma G] (h : Equation32346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ X0)) ◇ (X0 ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq7
  have eq24 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq9
  have eq32 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := superpose eq24 eq14
  have eq41 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X2) = X0 := superpose eq24 eq7
  have eq42 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq24 eq10
  have eq50 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq24 eq32
  have eq51 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq24 eq50
  have eq81 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq24 eq41
  have eq91 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X1 := superpose eq51 eq42
  have eq92 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := superpose eq42 eq42
  have eq97 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq81 eq91
  have eq98 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq81 eq92
  have eq99 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq97 eq98
  have eq100 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = X0 := superpose eq99 eq41
  have eq119 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq99 eq100
  have eq120 (X0 X1 : G) : X0 = X1 := superpose eq24 eq119
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq120 eq8
  subsumption eq128 eq120


@[equational_result]
theorem Equation32347_implies_Equation2 (G : Type*) [Magma G] (h : Equation32347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0)) ◇ (X0 ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation32349_implies_Equation2 (G : Type*) [Magma G] (h : Equation32349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32350_implies_Equation2 (G : Type*) [Magma G] (h : Equation32350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32351_implies_Equation2 (G : Type*) [Magma G] (h : Equation32351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32353_implies_Equation2 (G : Type*) [Magma G] (h : Equation32353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32354_implies_Equation2 (G : Type*) [Magma G] (h : Equation32354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32355_implies_Equation2 (G : Type*) [Magma G] (h : Equation32355 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32357_implies_Equation2 (G : Type*) [Magma G] (h : Equation32357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32358_implies_Equation2 (G : Type*) [Magma G] (h : Equation32358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32359_implies_Equation2 (G : Type*) [Magma G] (h : Equation32359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32360_implies_Equation2 (G : Type*) [Magma G] (h : Equation32360 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32362_implies_Equation2 (G : Type*) [Magma G] (h : Equation32362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq31 eq14


@[equational_result]
theorem Equation32363_implies_Equation2 (G : Type*) [Magma G] (h : Equation32363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq49 eq18


@[equational_result]
theorem Equation32364_implies_Equation2 (G : Type*) [Magma G] (h : Equation32364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) ◇ (X0 ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq9 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation32365_implies_Equation2 (G : Type*) [Magma G] (h : Equation32365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X6 X7 : G) : (((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) ◇ (X0 ◇ X6)) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation32367_implies_Equation2 (G : Type*) [Magma G] (h : Equation32367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32368_implies_Equation2 (G : Type*) [Magma G] (h : Equation32368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32369_implies_Equation2 (G : Type*) [Magma G] (h : Equation32369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32370_implies_Equation2 (G : Type*) [Magma G] (h : Equation32370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32372_implies_Equation2 (G : Type*) [Magma G] (h : Equation32372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32373_implies_Equation2 (G : Type*) [Magma G] (h : Equation32373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32374_implies_Equation2 (G : Type*) [Magma G] (h : Equation32374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32375_implies_Equation2 (G : Type*) [Magma G] (h : Equation32375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32377_implies_Equation2 (G : Type*) [Magma G] (h : Equation32377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32378_implies_Equation2 (G : Type*) [Magma G] (h : Equation32378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32379_implies_Equation2 (G : Type*) [Magma G] (h : Equation32379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32380_implies_Equation2 (G : Type*) [Magma G] (h : Equation32380 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32382_implies_Equation2 (G : Type*) [Magma G] (h : Equation32382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32383_implies_Equation2 (G : Type*) [Magma G] (h : Equation32383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32384_implies_Equation2 (G : Type*) [Magma G] (h : Equation32384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32385_implies_Equation2 (G : Type*) [Magma G] (h : Equation32385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32386_implies_Equation2 (G : Type*) [Magma G] (h : Equation32386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32388_implies_Equation2 (G : Type*) [Magma G] (h : Equation32388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq9
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq97 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq97 eq38


@[equational_result]
theorem Equation32389_implies_Equation2 (G : Type*) [Magma G] (h : Equation32389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation32390_implies_Equation2 (G : Type*) [Magma G] (h : Equation32390 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq22 eq14


@[equational_result]
theorem Equation32392_implies_Equation2 (G : Type*) [Magma G] (h : Equation32392 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq38 eq15


@[equational_result]
theorem Equation32394_implies_Equation2 (G : Type*) [Magma G] (h : Equation32394 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation32397_implies_Equation2 (G : Type*) [Magma G] (h : Equation32397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq47 eq11


@[equational_result]
theorem Equation32398_implies_Equation2 (G : Type*) [Magma G] (h : Equation32398 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq67 eq12


@[equational_result]
theorem Equation32400_implies_Equation2 (G : Type*) [Magma G] (h : Equation32400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X1) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation32401_implies_Equation2 (G : Type*) [Magma G] (h : Equation32401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq56 eq12


@[equational_result]
theorem Equation32402_implies_Equation2 (G : Type*) [Magma G] (h : Equation32402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation32403_implies_Equation2 (G : Type*) [Magma G] (h : Equation32403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation32405_implies_Equation2 (G : Type*) [Magma G] (h : Equation32405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq103 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq103 eq40


@[equational_result]
theorem Equation32407_implies_Equation2 (G : Type*) [Magma G] (h : Equation32407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation32409_implies_Equation2 (G : Type*) [Magma G] (h : Equation32409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation32411_implies_Equation2 (G : Type*) [Magma G] (h : Equation32411 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation32413_implies_Equation2 (G : Type*) [Magma G] (h : Equation32413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq11 eq11
  have eq29 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X1) = X0 := superpose eq15 eq7
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq29 eq29
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq47 eq39


@[equational_result]
theorem Equation32415_implies_Equation2 (G : Type*) [Magma G] (h : Equation32415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation32417_implies_Equation2 (G : Type*) [Magma G] (h : Equation32417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X1) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq65 eq18


@[equational_result]
theorem Equation32418_implies_Equation2 (G : Type*) [Magma G] (h : Equation32418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ X2) := superpose eq7 eq7
  have eq15 (X0 X2 X3 X5 : G) : ((X5 ◇ X2) ◇ X3) = X0 := superpose eq7 eq11
  have eq94 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq211 (X0 : G) : sK0 ≠ X0 := superpose eq94 eq8
  subsumption eq211 eq94


@[equational_result]
theorem Equation32419_implies_Equation2 (G : Type*) [Magma G] (h : Equation32419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X5) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq65 eq18


@[equational_result]
theorem Equation32420_implies_Equation2 (G : Type*) [Magma G] (h : Equation32420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation32423_implies_Equation2 (G : Type*) [Magma G] (h : Equation32423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation32424_implies_Equation2 (G : Type*) [Magma G] (h : Equation32424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation32426_implies_Equation2 (G : Type*) [Magma G] (h : Equation32426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2)) = ((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X1)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq10 eq10
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X3) ◇ X1)) = X0 := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X0) ◇ X3) = X2 := superpose eq10 eq7
  have eq24 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X2) = X1 := superpose eq10 eq7
  have eq26 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = ((X2 ◇ ((X3 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) ◇ X2) := superpose eq10 eq7
  have eq28 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ ((X3 ◇ (X4 ◇ ((X0 ◇ X2) ◇ X4))) ◇ X5)) ◇ X5) = (X3 ◇ ((X4 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0))) ◇ X3)) := superpose eq9 eq9
  have eq35 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X4)) ◇ X4) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0))) := superpose eq9 eq9
  have eq41 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ ((X3 ◇ (X1 ◇ X3)) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)))) = ((X4 ◇ (X0 ◇ X4)) ◇ X4) := superpose eq7 eq9
  have eq45 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X3 ◇ (((X4 ◇ (X2 ◇ X4)) ◇ X1) ◇ X3)) ◇ X1)) = ((X5 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X5)) ◇ X5) := superpose eq9 eq9
  have eq69 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X4 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0))) ◇ X3)) = (X3 ◇ (X0 ◇ X2)) := superpose eq26 eq28
  have eq75 (X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X3 ◇ (((X4 ◇ (X2 ◇ X4)) ◇ X1) ◇ X3)) ◇ X1)) = ((X1 ◇ X2) ◇ X5) := superpose eq18 eq45
  have eq76 (X1 X2 X5 : G) : (X1 ◇ (X2 ◇ X1)) = ((X1 ◇ X2) ◇ X5) := superpose eq18 eq75
  have eq79 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X3) = X2 := superpose eq76 eq21
  have eq89 (X0 X4 : G) : ((X4 ◇ (X0 ◇ X4)) ◇ X4) = X0 := superpose eq79 eq41
  have eq90 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X2)) = (X3 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0))) := superpose eq89 eq35
  have eq97 (X0 X2 X3 X4 : G) : (X3 ◇ (X0 ◇ X2)) = (X3 ◇ ((X4 ◇ (X0 ◇ X2)) ◇ X3)) := superpose eq90 eq69
  have eq99 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X0 := superpose eq97 eq7
  have eq104 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X2 := superpose eq99 eq12
  have eq106 (X1 X2 : G) : (X2 ◇ X2) = X1 := superpose eq104 eq24
  have eq130 (X0 X2 : G) : X0 = X2 := superpose eq106 eq106
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq130 eq8
  subsumption eq135 eq130


@[equational_result]
theorem Equation32427_implies_Equation2 (G : Type*) [Magma G] (h : Equation32427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X2) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1)) = X0 := superpose eq7 eq10
  have eq30 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq10 eq17
  have eq34 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X2) = X0 := superpose eq30 eq7
  have eq35 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := superpose eq30 eq19
  have eq36 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq30 eq35
  have eq37 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq36 eq34
  have eq48 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq37 eq36
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq48 eq48
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq61 eq56


@[equational_result]
theorem Equation32428_implies_Equation2 (G : Type*) [Magma G] (h : Equation32428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation32430_implies_Equation2 (G : Type*) [Magma G] (h : Equation32430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X3)) = ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X3 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2))) ◇ X3) := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X3)) ◇ X2) = X1 := superpose eq10 eq7
  have eq46 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ (((X0 ◇ X2) ◇ X0) ◇ X4)) ◇ X4)) = ((X5 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) ◇ X5) := superpose eq9 eq9
  have eq76 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = (X3 ◇ ((X4 ◇ (((X0 ◇ X2) ◇ X0) ◇ X4)) ◇ X4)) := superpose eq12 eq46
  have eq77 (X0 X2 X3 : G) : (X0 ◇ X2) = (X3 ◇ X2) := superpose eq21 eq76
  have eq82 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq7 eq77
  have eq177 (X0 X3 : G) : X0 = X3 := superpose eq7 eq82
  have eq323 (X0 : G) : sK0 ≠ X0 := superpose eq177 eq8
  subsumption eq323 eq177


@[equational_result]
theorem Equation32431_implies_Equation2 (G : Type*) [Magma G] (h : Equation32431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq30 eq15


@[equational_result]
theorem Equation32432_implies_Equation2 (G : Type*) [Magma G] (h : Equation32432 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq57 eq13


@[equational_result]
theorem Equation32434_implies_Equation2 (G : Type*) [Magma G] (h : Equation32434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ ((X4 ◇ (X0 ◇ X4)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq185 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq7 eq11
  have eq208 (X0 X4 : G) : X0 = X4 := superpose eq7 eq185
  have eq360 (X0 : G) : sK0 ≠ X0 := superpose eq208 eq8
  subsumption eq360 eq208


@[equational_result]
theorem Equation32435_implies_Equation2 (G : Type*) [Magma G] (h : Equation32435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq55 eq12


@[equational_result]
theorem Equation32436_implies_Equation2 (G : Type*) [Magma G] (h : Equation32436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq55 eq12


@[equational_result]
theorem Equation32437_implies_Equation2 (G : Type*) [Magma G] (h : Equation32437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation32439_implies_Equation2 (G : Type*) [Magma G] (h : Equation32439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X2 := superpose eq10 eq10
  have eq34 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = X0 := superpose eq10 eq11
  have eq57 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X1) = X0 := superpose eq34 eq7
  have eq59 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq57 eq16
  have eq62 (X0 X3 : G) : X0 = X3 := superpose eq10 eq59
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq100 eq62


@[equational_result]
theorem Equation32440_implies_Equation2 (G : Type*) [Magma G] (h : Equation32440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation32441_implies_Equation2 (G : Type*) [Magma G] (h : Equation32441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation32442_implies_Equation2 (G : Type*) [Magma G] (h : Equation32442 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation32444_implies_Equation2 (G : Type*) [Magma G] (h : Equation32444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq62 eq16


@[equational_result]
theorem Equation32445_implies_Equation2 (G : Type*) [Magma G] (h : Equation32445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ X2) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X4)) ◇ X1)) ◇ X2) ◇ X5) = X0 := superpose eq7 eq11
  have eq24 (X0 X1 X2 X3 : G) : ((X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ X0) = X1 := superpose eq11 eq7
  have eq34 (X0 X3 X5 : G) : (X3 ◇ X5) = X0 := superpose eq24 eq15
  have eq86 (X0 X4 : G) : X0 = X4 := superpose eq7 eq34
  have eq200 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq200 eq86


@[equational_result]
theorem Equation32446_implies_Equation2 (G : Type*) [Magma G] (h : Equation32446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X5) = X4 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq66 eq17


@[equational_result]
theorem Equation32447_implies_Equation2 (G : Type*) [Magma G] (h : Equation32447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation32449_implies_Equation2 (G : Type*) [Magma G] (h : Equation32449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 : G) : (X3 ◇ (X0 ◇ X4)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq16 (X0 X1 X5 : G) : ((X5 ◇ X1) ◇ X5) = X0 := superpose eq7 eq11
  have eq102 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq215 (X0 : G) : sK0 ≠ X0 := superpose eq102 eq8
  subsumption eq215 eq102


@[equational_result]
theorem Equation32450_implies_Equation2 (G : Type*) [Magma G] (h : Equation32450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation32451_implies_Equation2 (G : Type*) [Magma G] (h : Equation32451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation32452_implies_Equation2 (G : Type*) [Magma G] (h : Equation32452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation32454_implies_Equation2 (G : Type*) [Magma G] (h : Equation32454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation32455_implies_Equation2 (G : Type*) [Magma G] (h : Equation32455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq55 eq13


@[equational_result]
theorem Equation32456_implies_Equation2 (G : Type*) [Magma G] (h : Equation32456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation32457_implies_Equation2 (G : Type*) [Magma G] (h : Equation32457 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation32459_implies_Equation2 (G : Type*) [Magma G] (h : Equation32459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : ((X1 ◇ (X0 ◇ X7)) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation32460_implies_Equation2 (G : Type*) [Magma G] (h : Equation32460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation32461_implies_Equation2 (G : Type*) [Magma G] (h : Equation32461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation32462_implies_Equation2 (G : Type*) [Magma G] (h : Equation32462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation32463_implies_Equation2 (G : Type*) [Magma G] (h : Equation32463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X9 : G) : (X0 ◇ X9) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation32465_implies_Equation2 (G : Type*) [Magma G] (h : Equation32465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X3 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq23 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq10 eq11
  have eq29 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ ((X3 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose eq23 eq9
  have eq37 (X0 X1 X3 : G) : ((X0 ◇ ((X3 ◇ X0) ◇ X1)) ◇ X0) = X1 := superpose eq23 eq29
  have eq38 (X0 X1 X3 : G) : (((X3 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq23 eq37
  have eq39 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq23 eq38
  have eq44 (X0 X1 : G) : X0 = X1 := superpose eq39 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq46 eq44


@[equational_result]
theorem Equation32467_implies_Equation2 (G : Type*) [Magma G] (h : Equation32467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation32469_implies_Equation2 (G : Type*) [Magma G] (h : Equation32469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation32471_implies_Equation2 (G : Type*) [Magma G] (h : Equation32471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) ◇ ((X3 ◇ X0) ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation32473_implies_Equation2 (G : Type*) [Magma G] (h : Equation32473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X2 ◇ X0))) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq11 eq7
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq7 eq17
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq125 eq42


@[equational_result]
theorem Equation32474_implies_Equation2 (G : Type*) [Magma G] (h : Equation32474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) = X1 := superpose eq7 eq7
  have eq28 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ (X1 ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X3))) ◇ X2)) ◇ X0) ◇ X3) = X2 := superpose eq7 eq9
  have eq30 (X0 X2 : G) : (X0 ◇ X2) = ((X2 ◇ X0) ◇ X2) := superpose eq7 eq9
  have eq45 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) = X0 := superpose eq30 eq7
  have eq50 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X3)) ◇ X2)) ◇ X0) ◇ X3) = X2 := superpose eq30 eq28
  have eq68 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X2)) ◇ X0) ◇ X3) = X2 := superpose eq30 eq50
  have eq69 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X2)) ◇ X0) ◇ X3) = X2 := superpose eq30 eq68
  have eq86 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X1 := superpose eq11 eq45
  have eq92 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := superpose eq30 eq86
  have eq93 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X1 := superpose eq30 eq92
  have eq97 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := superpose eq30 eq93
  have eq113 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq93 eq97
  have eq134 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq113 eq69
  have eq173 (X0 X3 : G) : X0 = X3 := superpose eq134 eq134
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq173 eq8
  subsumption eq175 eq173


@[equational_result]
theorem Equation32475_implies_Equation2 (G : Type*) [Magma G] (h : Equation32475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation32477_implies_Equation2 (G : Type*) [Magma G] (h : Equation32477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X1) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq62 eq18


@[equational_result]
theorem Equation32478_implies_Equation2 (G : Type*) [Magma G] (h : Equation32478 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X2) = X3 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq63 eq21


@[equational_result]
theorem Equation32479_implies_Equation2 (G : Type*) [Magma G] (h : Equation32479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X5) = X4 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq51 eq18


@[equational_result]
theorem Equation32480_implies_Equation2 (G : Type*) [Magma G] (h : Equation32480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) ◇ ((X4 ◇ X0) ◇ X6)) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation32482_implies_Equation2 (G : Type*) [Magma G] (h : Equation32482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq20 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq9 eq10
  have eq26 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq20 eq10
  have eq29 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq20 eq26
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq9 eq29
  have eq47 (X0 X2 : G) : X0 = X2 := superpose eq34 eq34
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq55 eq47


@[equational_result]
theorem Equation32484_implies_Equation2 (G : Type*) [Magma G] (h : Equation32484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation32486_implies_Equation2 (G : Type*) [Magma G] (h : Equation32486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32487_implies_Equation2 (G : Type*) [Magma G] (h : Equation32487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32488_implies_Equation2 (G : Type*) [Magma G] (h : Equation32488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32490_implies_Equation2 (G : Type*) [Magma G] (h : Equation32490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32491_implies_Equation2 (G : Type*) [Magma G] (h : Equation32491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32492_implies_Equation2 (G : Type*) [Magma G] (h : Equation32492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32494_implies_Equation2 (G : Type*) [Magma G] (h : Equation32494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32495_implies_Equation2 (G : Type*) [Magma G] (h : Equation32495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32496_implies_Equation2 (G : Type*) [Magma G] (h : Equation32496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32497_implies_Equation2 (G : Type*) [Magma G] (h : Equation32497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32501_implies_Equation2 (G : Type*) [Magma G] (h : Equation32501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) ◇ ((X3 ◇ X0) ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation32503_implies_Equation2 (G : Type*) [Magma G] (h : Equation32503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32504_implies_Equation2 (G : Type*) [Magma G] (h : Equation32504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32505_implies_Equation2 (G : Type*) [Magma G] (h : Equation32505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32507_implies_Equation2 (G : Type*) [Magma G] (h : Equation32507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32508_implies_Equation2 (G : Type*) [Magma G] (h : Equation32508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32509_implies_Equation2 (G : Type*) [Magma G] (h : Equation32509 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32511_implies_Equation2 (G : Type*) [Magma G] (h : Equation32511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32512_implies_Equation2 (G : Type*) [Magma G] (h : Equation32512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32513_implies_Equation2 (G : Type*) [Magma G] (h : Equation32513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32514_implies_Equation2 (G : Type*) [Magma G] (h : Equation32514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32516_implies_Equation2 (G : Type*) [Magma G] (h : Equation32516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X1 ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation32517_implies_Equation2 (G : Type*) [Magma G] (h : Equation32517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X2) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq48 eq18


@[equational_result]
theorem Equation32518_implies_Equation2 (G : Type*) [Magma G] (h : Equation32518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ X3) = X0 := superpose eq10 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32519_implies_Equation2 (G : Type*) [Magma G] (h : Equation32519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X6 X7 : G) : (((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X0)) ◇ ((X4 ◇ X0) ◇ X6)) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation32521_implies_Equation2 (G : Type*) [Magma G] (h : Equation32521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32522_implies_Equation2 (G : Type*) [Magma G] (h : Equation32522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32523_implies_Equation2 (G : Type*) [Magma G] (h : Equation32523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32524_implies_Equation2 (G : Type*) [Magma G] (h : Equation32524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32526_implies_Equation2 (G : Type*) [Magma G] (h : Equation32526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32527_implies_Equation2 (G : Type*) [Magma G] (h : Equation32527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32528_implies_Equation2 (G : Type*) [Magma G] (h : Equation32528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32529_implies_Equation2 (G : Type*) [Magma G] (h : Equation32529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32531_implies_Equation2 (G : Type*) [Magma G] (h : Equation32531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32532_implies_Equation2 (G : Type*) [Magma G] (h : Equation32532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32533_implies_Equation2 (G : Type*) [Magma G] (h : Equation32533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32534_implies_Equation2 (G : Type*) [Magma G] (h : Equation32534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32536_implies_Equation2 (G : Type*) [Magma G] (h : Equation32536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32537_implies_Equation2 (G : Type*) [Magma G] (h : Equation32537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32538_implies_Equation2 (G : Type*) [Magma G] (h : Equation32538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32539_implies_Equation2 (G : Type*) [Magma G] (h : Equation32539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32540_implies_Equation2 (G : Type*) [Magma G] (h : Equation32540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32543_implies_Equation2 (G : Type*) [Magma G] (h : Equation32543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq37 eq12


@[equational_result]
theorem Equation32544_implies_Equation2 (G : Type*) [Magma G] (h : Equation32544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation32547_implies_Equation2 (G : Type*) [Magma G] (h : Equation32547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X2)) ◇ X0) ◇ X1)) ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq10 eq10
  have eq13 (X0 X1 : G) : (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) = X1 := superpose eq10 eq7
  have eq16 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq10 eq12
  have eq17 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = X1 := superpose eq16 eq13
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) = X0 := superpose eq7 eq9
  have eq44 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq17 eq7
  have eq77 (X0 X1 : G) : (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := superpose eq7 eq44
  have eq97 (X0 X1 : G) : (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := superpose eq44 eq77
  have eq98 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq97 eq17
  have eq107 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq98 eq19
  have eq146 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = X0 := superpose eq98 eq107
  have eq147 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq98 eq146
  have eq148 (X0 X3 : G) : X0 = X3 := superpose eq147 eq147
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq148 eq8
  subsumption eq153 eq148


@[equational_result]
theorem Equation32548_implies_Equation2 (G : Type*) [Magma G] (h : Equation32548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq54 eq14


@[equational_result]
theorem Equation32550_implies_Equation2 (G : Type*) [Magma G] (h : Equation32550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq50 eq15


@[equational_result]
theorem Equation32551_implies_Equation2 (G : Type*) [Magma G] (h : Equation32551 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation32552_implies_Equation2 (G : Type*) [Magma G] (h : Equation32552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation32554_implies_Equation2 (G : Type*) [Magma G] (h : Equation32554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq58 eq15


@[equational_result]
theorem Equation32555_implies_Equation2 (G : Type*) [Magma G] (h : Equation32555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation32556_implies_Equation2 (G : Type*) [Magma G] (h : Equation32556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation32557_implies_Equation2 (G : Type*) [Magma G] (h : Equation32557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation32559_implies_Equation2 (G : Type*) [Magma G] (h : Equation32559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X0) ◇ X3)) ◇ X1) = X3 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq9
  have eq18 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq12 eq7
  have eq22 (X0 X2 : G) : X0 = X2 := superpose eq18 eq18
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq65 eq22


@[equational_result]
theorem Equation32561_implies_Equation2 (G : Type*) [Magma G] (h : Equation32561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation32563_implies_Equation2 (G : Type*) [Magma G] (h : Equation32563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32564_implies_Equation2 (G : Type*) [Magma G] (h : Equation32564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32565_implies_Equation2 (G : Type*) [Magma G] (h : Equation32565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32567_implies_Equation2 (G : Type*) [Magma G] (h : Equation32567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32568_implies_Equation2 (G : Type*) [Magma G] (h : Equation32568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32569_implies_Equation2 (G : Type*) [Magma G] (h : Equation32569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32571_implies_Equation2 (G : Type*) [Magma G] (h : Equation32571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32572_implies_Equation2 (G : Type*) [Magma G] (h : Equation32572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32573_implies_Equation2 (G : Type*) [Magma G] (h : Equation32573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32574_implies_Equation2 (G : Type*) [Magma G] (h : Equation32574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32577_implies_Equation2 (G : Type*) [Magma G] (h : Equation32577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq36 eq11


@[equational_result]
theorem Equation32578_implies_Equation2 (G : Type*) [Magma G] (h : Equation32578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation32580_implies_Equation2 (G : Type*) [Magma G] (h : Equation32580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32581_implies_Equation2 (G : Type*) [Magma G] (h : Equation32581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32582_implies_Equation2 (G : Type*) [Magma G] (h : Equation32582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32584_implies_Equation2 (G : Type*) [Magma G] (h : Equation32584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32585_implies_Equation2 (G : Type*) [Magma G] (h : Equation32585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation32586_implies_Equation2 (G : Type*) [Magma G] (h : Equation32586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32588_implies_Equation2 (G : Type*) [Magma G] (h : Equation32588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32589_implies_Equation2 (G : Type*) [Magma G] (h : Equation32589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32590_implies_Equation2 (G : Type*) [Magma G] (h : Equation32590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32591_implies_Equation2 (G : Type*) [Magma G] (h : Equation32591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32593_implies_Equation2 (G : Type*) [Magma G] (h : Equation32593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq7 eq10
  have eq65 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq159 eq65


@[equational_result]
theorem Equation32594_implies_Equation2 (G : Type*) [Magma G] (h : Equation32594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq45 eq12


@[equational_result]
theorem Equation32595_implies_Equation2 (G : Type*) [Magma G] (h : Equation32595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq44 eq12


@[equational_result]
theorem Equation32596_implies_Equation2 (G : Type*) [Magma G] (h : Equation32596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation32598_implies_Equation2 (G : Type*) [Magma G] (h : Equation32598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32599_implies_Equation2 (G : Type*) [Magma G] (h : Equation32599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32600_implies_Equation2 (G : Type*) [Magma G] (h : Equation32600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32601_implies_Equation2 (G : Type*) [Magma G] (h : Equation32601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32603_implies_Equation2 (G : Type*) [Magma G] (h : Equation32603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32604_implies_Equation2 (G : Type*) [Magma G] (h : Equation32604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32605_implies_Equation2 (G : Type*) [Magma G] (h : Equation32605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32606_implies_Equation2 (G : Type*) [Magma G] (h : Equation32606 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32608_implies_Equation2 (G : Type*) [Magma G] (h : Equation32608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32609_implies_Equation2 (G : Type*) [Magma G] (h : Equation32609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32610_implies_Equation2 (G : Type*) [Magma G] (h : Equation32610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32611_implies_Equation2 (G : Type*) [Magma G] (h : Equation32611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32613_implies_Equation2 (G : Type*) [Magma G] (h : Equation32613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32614_implies_Equation2 (G : Type*) [Magma G] (h : Equation32614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32615_implies_Equation2 (G : Type*) [Magma G] (h : Equation32615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32616_implies_Equation2 (G : Type*) [Magma G] (h : Equation32616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32617_implies_Equation2 (G : Type*) [Magma G] (h : Equation32617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32619_implies_Equation2 (G : Type*) [Magma G] (h : Equation32619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X1) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq7 eq7
  have eq30 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq11 eq10
  have eq34 (X1 X3 : G) : ((X1 ◇ X3) ◇ X1) = X3 := superpose eq30 eq9
  have eq41 (X1 X3 : G) : (X3 ◇ X1) = X3 := superpose eq30 eq34
  have eq44 (X0 X1 : G) : X0 = X1 := superpose eq41 eq30
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq46 eq44


@[equational_result]
theorem Equation32620_implies_Equation2 (G : Type*) [Magma G] (h : Equation32620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq27 eq16


@[equational_result]
theorem Equation32621_implies_Equation2 (G : Type*) [Magma G] (h : Equation32621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation32622_implies_Equation2 (G : Type*) [Magma G] (h : Equation32622 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq23 eq15


@[equational_result]
theorem Equation32624_implies_Equation2 (G : Type*) [Magma G] (h : Equation32624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq41 eq14


@[equational_result]
theorem Equation32625_implies_Equation2 (G : Type*) [Magma G] (h : Equation32625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X0 := superpose eq11 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq20 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq20 eq18


@[equational_result]
theorem Equation32626_implies_Equation2 (G : Type*) [Magma G] (h : Equation32626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X4) = X5 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation32627_implies_Equation2 (G : Type*) [Magma G] (h : Equation32627 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32629_implies_Equation2 (G : Type*) [Magma G] (h : Equation32629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation32630_implies_Equation2 (G : Type*) [Magma G] (h : Equation32630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq29 eq17


@[equational_result]
theorem Equation32631_implies_Equation2 (G : Type*) [Magma G] (h : Equation32631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation32632_implies_Equation2 (G : Type*) [Magma G] (h : Equation32632 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32634_implies_Equation2 (G : Type*) [Magma G] (h : Equation32634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation32635_implies_Equation2 (G : Type*) [Magma G] (h : Equation32635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq55 eq12


@[equational_result]
theorem Equation32636_implies_Equation2 (G : Type*) [Magma G] (h : Equation32636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq52 eq12


@[equational_result]
theorem Equation32637_implies_Equation2 (G : Type*) [Magma G] (h : Equation32637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32639_implies_Equation2 (G : Type*) [Magma G] (h : Equation32639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X5 : G) : ((X1 ◇ X0) ◇ X1) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation32640_implies_Equation2 (G : Type*) [Magma G] (h : Equation32640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32641_implies_Equation2 (G : Type*) [Magma G] (h : Equation32641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation32642_implies_Equation2 (G : Type*) [Magma G] (h : Equation32642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation32643_implies_Equation2 (G : Type*) [Magma G] (h : Equation32643 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X7 X9 : G) : (X0 ◇ X9) = X7 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32645_implies_Equation2 (G : Type*) [Magma G] (h : Equation32645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq37 eq13


@[equational_result]
theorem Equation32646_implies_Equation2 (G : Type*) [Magma G] (h : Equation32646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq43 eq14


@[equational_result]
theorem Equation32647_implies_Equation2 (G : Type*) [Magma G] (h : Equation32647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X3) = X0 := superpose eq10 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32648_implies_Equation2 (G : Type*) [Magma G] (h : Equation32648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation32650_implies_Equation2 (G : Type*) [Magma G] (h : Equation32650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32651_implies_Equation2 (G : Type*) [Magma G] (h : Equation32651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32652_implies_Equation2 (G : Type*) [Magma G] (h : Equation32652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32653_implies_Equation2 (G : Type*) [Magma G] (h : Equation32653 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32655_implies_Equation2 (G : Type*) [Magma G] (h : Equation32655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32656_implies_Equation2 (G : Type*) [Magma G] (h : Equation32656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32657_implies_Equation2 (G : Type*) [Magma G] (h : Equation32657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32658_implies_Equation2 (G : Type*) [Magma G] (h : Equation32658 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32660_implies_Equation2 (G : Type*) [Magma G] (h : Equation32660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32661_implies_Equation2 (G : Type*) [Magma G] (h : Equation32661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32662_implies_Equation2 (G : Type*) [Magma G] (h : Equation32662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32663_implies_Equation2 (G : Type*) [Magma G] (h : Equation32663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32665_implies_Equation2 (G : Type*) [Magma G] (h : Equation32665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32666_implies_Equation2 (G : Type*) [Magma G] (h : Equation32666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32667_implies_Equation2 (G : Type*) [Magma G] (h : Equation32667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32668_implies_Equation2 (G : Type*) [Magma G] (h : Equation32668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32669_implies_Equation2 (G : Type*) [Magma G] (h : Equation32669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32671_implies_Equation2 (G : Type*) [Magma G] (h : Equation32671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X5)) ◇ X1) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ ((X4 ◇ (X5 ◇ X4)) ◇ X0))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq10
  have eq14 (X0 X2 X3 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ X0) = X0 := superpose eq7 eq10
  have eq20 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X2 ◇ X3) ◇ ((X4 ◇ (X5 ◇ X4)) ◇ X0))) = X3 := superpose eq13 eq11
  have eq22 (X0 X2 X3 X5 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (X5 ◇ X0))) = X3 := superpose eq13 eq20
  have eq23 (X0 X3 : G) : (X3 ◇ X0) = X0 := superpose eq13 eq14
  have eq24 (X1 X5 : G) : ((X1 ◇ X5) ◇ X1) = X5 := superpose eq23 eq9
  have eq25 (X0 X3 X5 : G) : (X0 ◇ (X5 ◇ X0)) = X3 := superpose eq23 eq22
  have eq30 (X1 X5 : G) : (X5 ◇ X1) = X5 := superpose eq23 eq24
  have eq31 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq23 eq25
  have eq39 (X0 X1 : G) : X0 = X1 := superpose eq30 eq31
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq44 eq39


@[equational_result]
theorem Equation32672_implies_Equation2 (G : Type*) [Magma G] (h : Equation32672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq44 eq12


@[equational_result]
theorem Equation32673_implies_Equation2 (G : Type*) [Magma G] (h : Equation32673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq45 eq12


@[equational_result]
theorem Equation32674_implies_Equation2 (G : Type*) [Magma G] (h : Equation32674 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation32676_implies_Equation2 (G : Type*) [Magma G] (h : Equation32676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32677_implies_Equation2 (G : Type*) [Magma G] (h : Equation32677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32678_implies_Equation2 (G : Type*) [Magma G] (h : Equation32678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32679_implies_Equation2 (G : Type*) [Magma G] (h : Equation32679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32681_implies_Equation2 (G : Type*) [Magma G] (h : Equation32681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32682_implies_Equation2 (G : Type*) [Magma G] (h : Equation32682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32683_implies_Equation2 (G : Type*) [Magma G] (h : Equation32683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32684_implies_Equation2 (G : Type*) [Magma G] (h : Equation32684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32686_implies_Equation2 (G : Type*) [Magma G] (h : Equation32686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32687_implies_Equation2 (G : Type*) [Magma G] (h : Equation32687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32688_implies_Equation2 (G : Type*) [Magma G] (h : Equation32688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32689_implies_Equation2 (G : Type*) [Magma G] (h : Equation32689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32691_implies_Equation2 (G : Type*) [Magma G] (h : Equation32691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32692_implies_Equation2 (G : Type*) [Magma G] (h : Equation32692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32693_implies_Equation2 (G : Type*) [Magma G] (h : Equation32693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32694_implies_Equation2 (G : Type*) [Magma G] (h : Equation32694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32695_implies_Equation2 (G : Type*) [Magma G] (h : Equation32695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32697_implies_Equation2 (G : Type*) [Magma G] (h : Equation32697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2) = X3 := superpose eq7 eq7
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq48 eq29


@[equational_result]
theorem Equation32698_implies_Equation2 (G : Type*) [Magma G] (h : Equation32698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ X2) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq45 eq12


@[equational_result]
theorem Equation32699_implies_Equation2 (G : Type*) [Magma G] (h : Equation32699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq25 eq13


@[equational_result]
theorem Equation32700_implies_Equation2 (G : Type*) [Magma G] (h : Equation32700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation32702_implies_Equation2 (G : Type*) [Magma G] (h : Equation32702 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32703_implies_Equation2 (G : Type*) [Magma G] (h : Equation32703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32704_implies_Equation2 (G : Type*) [Magma G] (h : Equation32704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32705_implies_Equation2 (G : Type*) [Magma G] (h : Equation32705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32707_implies_Equation2 (G : Type*) [Magma G] (h : Equation32707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32708_implies_Equation2 (G : Type*) [Magma G] (h : Equation32708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32709_implies_Equation2 (G : Type*) [Magma G] (h : Equation32709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32710_implies_Equation2 (G : Type*) [Magma G] (h : Equation32710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32712_implies_Equation2 (G : Type*) [Magma G] (h : Equation32712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32713_implies_Equation2 (G : Type*) [Magma G] (h : Equation32713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32714_implies_Equation2 (G : Type*) [Magma G] (h : Equation32714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation32715_implies_Equation2 (G : Type*) [Magma G] (h : Equation32715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32717_implies_Equation2 (G : Type*) [Magma G] (h : Equation32717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32718_implies_Equation2 (G : Type*) [Magma G] (h : Equation32718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32719_implies_Equation2 (G : Type*) [Magma G] (h : Equation32719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32720_implies_Equation2 (G : Type*) [Magma G] (h : Equation32720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32721_implies_Equation2 (G : Type*) [Magma G] (h : Equation32721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32723_implies_Equation2 (G : Type*) [Magma G] (h : Equation32723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation32724_implies_Equation2 (G : Type*) [Magma G] (h : Equation32724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X5 : G) : (X0 ◇ X2) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32725_implies_Equation2 (G : Type*) [Magma G] (h : Equation32725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X6 : G) : (X0 ◇ X4) = X6 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq27 eq15


@[equational_result]
theorem Equation32726_implies_Equation2 (G : Type*) [Magma G] (h : Equation32726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X7 : G) : (X0 ◇ X6) = X7 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation32727_implies_Equation2 (G : Type*) [Magma G] (h : Equation32727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X0)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X8 X9 : G) : (X0 ◇ X9) = X8 := superpose eq7 eq7
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq26 eq14


@[equational_result]
theorem Equation32729_implies_Equation2 (G : Type*) [Magma G] (h : Equation32729 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32730_implies_Equation2 (G : Type*) [Magma G] (h : Equation32730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32731_implies_Equation2 (G : Type*) [Magma G] (h : Equation32731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32732_implies_Equation2 (G : Type*) [Magma G] (h : Equation32732 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32733_implies_Equation2 (G : Type*) [Magma G] (h : Equation32733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32735_implies_Equation2 (G : Type*) [Magma G] (h : Equation32735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32736_implies_Equation2 (G : Type*) [Magma G] (h : Equation32736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32737_implies_Equation2 (G : Type*) [Magma G] (h : Equation32737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32738_implies_Equation2 (G : Type*) [Magma G] (h : Equation32738 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32739_implies_Equation2 (G : Type*) [Magma G] (h : Equation32739 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X2)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32741_implies_Equation2 (G : Type*) [Magma G] (h : Equation32741 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32742_implies_Equation2 (G : Type*) [Magma G] (h : Equation32742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32743_implies_Equation2 (G : Type*) [Magma G] (h : Equation32743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32744_implies_Equation2 (G : Type*) [Magma G] (h : Equation32744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation32745_implies_Equation2 (G : Type*) [Magma G] (h : Equation32745 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X3)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32747_implies_Equation2 (G : Type*) [Magma G] (h : Equation32747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32748_implies_Equation2 (G : Type*) [Magma G] (h : Equation32748 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32749_implies_Equation2 (G : Type*) [Magma G] (h : Equation32749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32750_implies_Equation2 (G : Type*) [Magma G] (h : Equation32750 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32751_implies_Equation2 (G : Type*) [Magma G] (h : Equation32751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32753_implies_Equation2 (G : Type*) [Magma G] (h : Equation32753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32754_implies_Equation2 (G : Type*) [Magma G] (h : Equation32754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32755_implies_Equation2 (G : Type*) [Magma G] (h : Equation32755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32756_implies_Equation2 (G : Type*) [Magma G] (h : Equation32756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32757_implies_Equation2 (G : Type*) [Magma G] (h : Equation32757 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32758_implies_Equation2 (G : Type*) [Magma G] (h : Equation32758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5)) ◇ X6) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation32964_implies_Equation2 (G : Type*) [Magma G] (h : Equation32964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation32967_implies_Equation2 (G : Type*) [Magma G] (h : Equation32967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation32969_implies_Equation2 (G : Type*) [Magma G] (h : Equation32969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ X3))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X3 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ X3) = (X0 ◇ X2) := superpose eq7 eq10
  have eq30 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq7 eq13
  have eq32 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X1) ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ X3))) = X1 := superpose eq30 eq11
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ X2) := superpose eq30 eq10
  have eq40 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X2)) = X1 := superpose eq30 eq32
  have eq41 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq30 eq40
  have eq42 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq30 eq41
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (X0 ◇ X2) := superpose eq30 eq33
  have eq44 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq30 eq43
  have eq45 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq30 eq44
  have eq78 (X0 X1 : G) : X0 = X1 := superpose eq42 eq45
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq83 eq78


@[equational_result]
theorem Equation32970_implies_Equation2 (G : Type*) [Magma G] (h : Equation32970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation32971_implies_Equation2 (G : Type*) [Magma G] (h : Equation32971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq59 eq13


@[equational_result]
theorem Equation32974_implies_Equation2 (G : Type*) [Magma G] (h : Equation32974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq44 eq12


@[equational_result]
theorem Equation32977_implies_Equation2 (G : Type*) [Magma G] (h : Equation32977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq44 eq12


@[equational_result]
theorem Equation32979_implies_Equation2 (G : Type*) [Magma G] (h : Equation32979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X2)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) ◇ X0) = X1 := superpose eq9 eq9
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq9
  have eq13 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X1 := superpose eq11 eq9
  have eq14 (X0 X1 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0))) ◇ X0) = X1 := superpose eq11 eq10
  have eq21 (X0 X1 : G) : (X0 ◇ X0) = ((((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq11 eq13
  have eq25 (X0 X1 : G) : (((X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ X0) ◇ (X0 ◇ X0)) = X1 := superpose eq11 eq7
  have eq28 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq13 eq21
  have eq30 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X1)) := superpose eq28 eq11
  have eq31 (X0 X1 : G) : ((X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq28 eq14
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq28 eq30
  have eq39 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X1 := superpose eq36 eq13
  have eq40 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) = X1 := superpose eq36 eq31
  have eq41 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq28 eq40
  have eq55 (X0 X1 : G) : (((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) ◇ X0) = X1 := superpose eq28 eq25
  have eq56 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq41 eq55
  have eq57 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq28 eq56
  have eq58 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X1 := superpose eq57 eq39
  have eq68 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq57 eq58
  have eq69 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq57 eq68
  have eq79 (X0 X2 : G) : X0 = X2 := superpose eq69 eq69
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq81 eq79


@[equational_result]
theorem Equation32981_implies_Equation2 (G : Type*) [Magma G] (h : Equation32981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation32983_implies_Equation2 (G : Type*) [Magma G] (h : Equation32983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ (((X0 ◇ X0) ◇ X3) ◇ X0))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq10 eq7
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq15
  have eq71 (X0 X3 : G) : X0 = X3 := superpose eq7 eq26
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq158 eq71


@[equational_result]
theorem Equation32984_implies_Equation2 (G : Type*) [Magma G] (h : Equation32984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation32985_implies_Equation2 (G : Type*) [Magma G] (h : Equation32985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32987_implies_Equation2 (G : Type*) [Magma G] (h : Equation32987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : X0 = X1 := superpose eq7 eq9
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq15 eq11


@[equational_result]
theorem Equation32989_implies_Equation2 (G : Type*) [Magma G] (h : Equation32989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation32992_implies_Equation2 (G : Type*) [Magma G] (h : Equation32992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq55 eq11


@[equational_result]
theorem Equation32993_implies_Equation2 (G : Type*) [Magma G] (h : Equation32993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation32995_implies_Equation2 (G : Type*) [Magma G] (h : Equation32995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq67 eq15


@[equational_result]
theorem Equation32996_implies_Equation2 (G : Type*) [Magma G] (h : Equation32996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation32997_implies_Equation2 (G : Type*) [Magma G] (h : Equation32997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation32998_implies_Equation2 (G : Type*) [Magma G] (h : Equation32998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33001_implies_Equation2 (G : Type*) [Magma G] (h : Equation33001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation33004_implies_Equation2 (G : Type*) [Magma G] (h : Equation33004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation33006_implies_Equation2 (G : Type*) [Magma G] (h : Equation33006 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = ((X1 ◇ ((X0 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) ◇ X3)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = (((X0 ◇ X3) ◇ (X1 ◇ X4)) ◇ (X0 ◇ X3)) := superpose eq7 eq10
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ X3) = (((X0 ◇ X4) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X5)) ◇ (X0 ◇ X4)) := superpose eq10 eq10
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2))) ◇ X3))) ◇ X4)) = ((X0 ◇ (((X0 ◇ ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2))) ◇ X3)) ◇ (X0 ◇ (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2))) ◇ X3))) ◇ X4))) ◇ X5)) ◇ X0) := superpose eq9 eq9
  have eq60 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) = X0 := superpose eq10 eq15
  have eq72 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X2) ◇ X0) = ((X4 ◇ (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X5)) ◇ X4) := superpose eq15 eq7
  have eq73 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X5)) = ((X4 ◇ ((((X0 ◇ X2) ◇ X0) ◇ (X4 ◇ (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X5))) ◇ X6)) ◇ X4) := superpose eq15 eq9
  have eq130 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X4) = (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) ◇ X0) ◇ X3) := superpose eq15 eq16
  have eq168 (X1 X3 X4 : G) : (X1 ◇ X3) = (X1 ◇ X4) := superpose eq7 eq130
  have eq170 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) = X0 := superpose eq7 eq168
  have eq171 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) = ((X0 ◇ ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2))) ◇ X3)) ◇ X4) := superpose eq9 eq168
  have eq266 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X1 ◇ X4)) = ((X0 ◇ (((X0 ◇ ((X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2))) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X4))) ◇ X5)) ◇ X0) := superpose eq170 eq20
  have eq272 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X1 ◇ X4)) = ((X0 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) ◇ X5)) ◇ X0) := superpose eq171 eq266
  have eq275 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X4)) := superpose eq170 eq272
  have eq278 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X5)) = ((X4 ◇ (((((X0 ◇ X2) ◇ X0) ◇ X4) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X6)) ◇ X4) := superpose eq275 eq73
  have eq297 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X2) ◇ X0) = (X4 ◇ (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X5)) := superpose eq7 eq278
  have eq298 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X4) := superpose eq297 eq72
  have eq299 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) = X0 := superpose eq298 eq60
  have eq371 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq298 eq299
  have eq372 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq371 eq298
  have eq376 (X0 X1 X4 : G) : (X0 ◇ (X1 ◇ X4)) = X1 := superpose eq372 eq275
  have eq377 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq372 eq371
  have eq387 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq377 eq376
  have eq391 (X0 X1 : G) : X0 = X1 := superpose eq387 eq377
  have eq401 (X0 : G) : sK0 ≠ X0 := superpose eq391 eq8
  subsumption eq401 eq391


@[equational_result]
theorem Equation33007_implies_Equation2 (G : Type*) [Magma G] (h : Equation33007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X2) ◇ X0) ◇ X1)) = ((X1 ◇ ((X0 ◇ (X2 ◇ (((X0 ◇ X2) ◇ X0) ◇ X1))) ◇ X3)) ◇ X3) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) ◇ X2) = X1 := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ X2)) = ((X2 ◇ X0) ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ X2)) := superpose eq7 eq9
  have eq433 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X2 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X2) ◇ X0)) ◇ X0) = X2 := superpose eq25 eq7
  have eq609 (X0 X1 : G) : X0 = X1 := superpose eq10 eq433
  have eq712 (X0 : G) : sK0 ≠ X0 := superpose eq609 eq8
  subsumption eq712 eq609


@[equational_result]
theorem Equation33008_implies_Equation2 (G : Type*) [Magma G] (h : Equation33008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq49 eq12


@[equational_result]
theorem Equation33011_implies_Equation2 (G : Type*) [Magma G] (h : Equation33011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq44 eq12


@[equational_result]
theorem Equation33014_implies_Equation2 (G : Type*) [Magma G] (h : Equation33014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq69 eq12


@[equational_result]
theorem Equation33016_implies_Equation2 (G : Type*) [Magma G] (h : Equation33016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = ((X1 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X1) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X2)) = X0 := superpose eq7 eq9
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq19 eq19
  have eq43 (X0 X3 : G) : X0 = X3 := superpose eq7 eq33
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq113 eq43


@[equational_result]
theorem Equation33018_implies_Equation2 (G : Type*) [Magma G] (h : Equation33018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation33022_implies_Equation2 (G : Type*) [Magma G] (h : Equation33022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33024_implies_Equation2 (G : Type*) [Magma G] (h : Equation33024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = ((X1 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) = X1 := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X1)) = X0 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ X1)) ◇ X1) = X0 := superpose eq9 eq7
  have eq67 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X2)) = X2 := superpose eq25 eq10
  have eq77 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X1) = X0 := superpose eq67 eq29
  have eq84 (X0 X2 : G) : X0 = X2 := superpose eq77 eq77
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq84 eq8
  subsumption eq120 eq84


@[equational_result]
theorem Equation33025_implies_Equation2 (G : Type*) [Magma G] (h : Equation33025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X2) ◇ X1) ◇ X2)) = ((X1 ◇ ((X0 ◇ X3) ◇ X1)) ◇ X3) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1))) ◇ X2) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq20 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq7
  have eq32 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X0 := superpose eq11 eq9
  have eq81 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) = X0 := superpose eq20 eq10
  have eq108 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X1) := superpose eq32 eq32
  have eq121 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X1) := superpose eq32 eq10
  have eq139 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq121 eq108
  have eq140 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) := superpose eq139 eq121
  have eq141 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X0 := superpose eq139 eq81
  have eq143 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose eq139 eq140
  have eq144 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq20 eq143
  have eq147 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = X0 := superpose eq20 eq141
  have eq148 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq147 eq144
  have eq149 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq148 eq147
  have eq160 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) = X0 := superpose eq149 eq7
  have eq239 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq149 eq160
  have eq240 (X0 X1 : G) : X0 = X1 := superpose eq20 eq239
  have eq245 (X0 : G) : sK0 ≠ X0 := superpose eq240 eq8
  subsumption eq245 eq240


@[equational_result]
theorem Equation33026_implies_Equation2 (G : Type*) [Magma G] (h : Equation33026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33028_implies_Equation2 (G : Type*) [Magma G] (h : Equation33028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) = ((X1 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X1) := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X3) ◇ X3)) = (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0) ◇ X0) := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2)) = X0 := superpose eq7 eq9
  have eq39 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X0) ◇ X0) = X1 := superpose eq26 eq25
  have eq67 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ X3) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2)))) = X0 := superpose eq9 eq26
  have eq83 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X1) = X0 := superpose eq7 eq67
  have eq139 (X0 X2 : G) : X0 = X2 := superpose eq39 eq83
  have eq262 (X0 : G) : sK0 ≠ X0 := superpose eq139 eq8
  subsumption eq262 eq139


@[equational_result]
theorem Equation33030_implies_Equation2 (G : Type*) [Magma G] (h : Equation33030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33032_implies_Equation2 (G : Type*) [Magma G] (h : Equation33032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq74 eq15


@[equational_result]
theorem Equation33033_implies_Equation2 (G : Type*) [Magma G] (h : Equation33033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) ◇ X2) = X1 := superpose eq7 eq7
  have eq21 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq48 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq169 eq48


@[equational_result]
theorem Equation33034_implies_Equation2 (G : Type*) [Magma G] (h : Equation33034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ X4) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation33035_implies_Equation2 (G : Type*) [Magma G] (h : Equation33035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33037_implies_Equation2 (G : Type*) [Magma G] (h : Equation33037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq106 eq37


@[equational_result]
theorem Equation33038_implies_Equation2 (G : Type*) [Magma G] (h : Equation33038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq45 eq12


@[equational_result]
theorem Equation33039_implies_Equation2 (G : Type*) [Magma G] (h : Equation33039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (((X0 ◇ X3) ◇ X0) ◇ X0)) = ((X1 ◇ ((X0 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X0) ◇ X0))) ◇ (X2 ◇ (((X0 ◇ X3) ◇ X0) ◇ X0)))) ◇ X5) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X4) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (((X0 ◇ X3) ◇ X0) ◇ X0)) = ((X1 ◇ (((X0 ◇ X3) ◇ X0) ◇ X0)) ◇ X5) := superpose eq10 eq9
  have eq14 (X0 X2 X3 : G) : (X2 ◇ (((X0 ◇ X3) ◇ X0) ◇ X0)) = X0 := superpose eq7 eq13
  have eq15 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq14 eq7
  have eq17 (X1 X2 X4 : G) : (X1 ◇ X4) = X2 := superpose eq15 eq10
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq25 eq20


@[equational_result]
theorem Equation33041_implies_Equation2 (G : Type*) [Magma G] (h : Equation33041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation33043_implies_Equation2 (G : Type*) [Magma G] (h : Equation33043 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation33045_implies_Equation2 (G : Type*) [Magma G] (h : Equation33045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (((X0 ◇ X3) ◇ X0) ◇ X3))) ◇ X1) = X2 := superpose eq7 eq7
  have eq23 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq54 eq23


@[equational_result]
theorem Equation33046_implies_Equation2 (G : Type*) [Magma G] (h : Equation33046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq55 eq13


@[equational_result]
theorem Equation33047_implies_Equation2 (G : Type*) [Magma G] (h : Equation33047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation33049_implies_Equation2 (G : Type*) [Magma G] (h : Equation33049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq73 eq19


@[equational_result]
theorem Equation33050_implies_Equation2 (G : Type*) [Magma G] (h : Equation33050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq63 eq13


@[equational_result]
theorem Equation33051_implies_Equation2 (G : Type*) [Magma G] (h : Equation33051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation33052_implies_Equation2 (G : Type*) [Magma G] (h : Equation33052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X0) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation33054_implies_Equation2 (G : Type*) [Magma G] (h : Equation33054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq7 eq10
  have eq34 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq63 eq34


@[equational_result]
theorem Equation33056_implies_Equation2 (G : Type*) [Magma G] (h : Equation33056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq49 eq14


@[equational_result]
theorem Equation33058_implies_Equation2 (G : Type*) [Magma G] (h : Equation33058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation33059_implies_Equation2 (G : Type*) [Magma G] (h : Equation33059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X3) ◇ X2) ◇ X2)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X3) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := superpose eq10 eq7
  have eq27 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ ((X2 ◇ X4) ◇ X4)) ◇ X3) = (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ (X0 ◇ (((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) ◇ X0) ◇ X0))) := superpose eq9 eq9
  have eq37 (X0 X1 X2 X3 : G) : (X2 ◇ ((((X1 ◇ X0) ◇ X3) ◇ X2) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq10 eq9
  have eq38 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((((X1 ◇ X2) ◇ X4) ◇ X3) ◇ X3)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X4) := superpose eq9 eq9
  have eq39 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X1) ◇ X1)) = X0 := superpose eq7 eq9
  have eq43 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X2) = X1 := superpose eq9 eq7
  have eq75 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X2) ◇ X3) = ((X1 ◇ X2) ◇ X3) := superpose eq9 eq17
  have eq88 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X4) = (X3 ◇ ((((X1 ◇ X2) ◇ X4) ◇ X3) ◇ X3)) := superpose eq75 eq38
  have eq97 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := superpose eq88 eq37
  have eq98 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X2) = X1 := superpose eq97 eq43
  have eq106 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq98 eq39
  have eq112 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ (X0 ◇ (((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) ◇ X0) ◇ X0))) = ((X4 ◇ X4) ◇ X3) := superpose eq106 eq27
  have eq149 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ (X0 ◇ (((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) ◇ X0) ◇ X0))) = X3 := superpose eq106 eq112
  have eq150 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ (((X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) ◇ X0) ◇ X0)) = X3 := superpose eq106 eq149
  have eq151 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq106 eq150
  have eq152 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = X3 := superpose eq106 eq151
  have eq153 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq106 eq152
  have eq163 (X0 X1 : G) : X0 = X1 := superpose eq106 eq153
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq163 eq8
  subsumption eq173 eq163


@[equational_result]
theorem Equation33060_implies_Equation2 (G : Type*) [Magma G] (h : Equation33060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation33062_implies_Equation2 (G : Type*) [Magma G] (h : Equation33062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X3) ◇ X2) ◇ X3)) = ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (((X0 ◇ X2) ◇ X1) ◇ X2))) ◇ X1) = X1 := superpose eq7 eq7
  have eq35 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2)) = X0 := superpose eq7 eq9
  have eq56 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ X2)) = X2 := superpose eq7 eq35
  have eq58 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) ◇ X0)) = X0 := superpose eq10 eq35
  have eq72 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ X0) = X0 := superpose eq10 eq58
  have eq73 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X2) = X2 := superpose eq72 eq56
  have eq76 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq73 eq35
  have eq77 (X0 X3 : G) : X0 = X3 := superpose eq7 eq76
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq77 eq8
  subsumption eq121 eq77


@[equational_result]
theorem Equation33064_implies_Equation2 (G : Type*) [Magma G] (h : Equation33064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation33066_implies_Equation2 (G : Type*) [Magma G] (h : Equation33066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ X1) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation33067_implies_Equation2 (G : Type*) [Magma G] (h : Equation33067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq38 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq7 eq11
  have eq48 (X0 X4 : G) : X0 = X4 := superpose eq7 eq38
  have eq170 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq170 eq48


@[equational_result]
theorem Equation33068_implies_Equation2 (G : Type*) [Magma G] (h : Equation33068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ X4) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq58 eq18


@[equational_result]
theorem Equation33069_implies_Equation2 (G : Type*) [Magma G] (h : Equation33069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X1) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation33072_implies_Equation2 (G : Type*) [Magma G] (h : Equation33072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq45 eq12


@[equational_result]
theorem Equation33073_implies_Equation2 (G : Type*) [Magma G] (h : Equation33073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33075_implies_Equation2 (G : Type*) [Magma G] (h : Equation33075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X3) ◇ X3) ◇ X2)) = ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ ((X2 ◇ X3) ◇ X5)) ◇ X5) = (X3 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ (((X1 ◇ X4) ◇ X4) ◇ X2)) ◇ X3)) := superpose eq9 eq9
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : ((X5 ◇ ((X2 ◇ (((X1 ◇ X4) ◇ X4) ◇ ((X2 ◇ X3) ◇ X3))) ◇ X5)) ◇ X5) = ((((X1 ◇ X4) ◇ X4) ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X0)) := superpose eq9 eq9
  have eq14 (X0 X1 X2 X4 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) = ((X4 ◇ ((X1 ◇ X2) ◇ X4)) ◇ X4) := superpose eq9 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((((X1 ◇ X3) ◇ X4) ◇ X4) ◇ X3)) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X2) := superpose eq9 eq9
  have eq22 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X1)) = X0 := superpose eq7 eq9
  have eq26 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X4) ◇ X4) ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X0)) ◇ (((X1 ◇ X4) ◇ X4) ◇ ((X2 ◇ X3) ◇ X3))) = X2 := superpose eq9 eq7
  have eq29 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X2) = X1 := superpose eq22 eq21
  have eq52 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) = X1 := superpose eq7 eq29
  have eq67 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X3 ◇ ((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) ◇ X3)) ◇ X3) := superpose eq7 eq14
  have eq68 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4)) ◇ X4) = ((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0)) ◇ X3) := superpose eq14 eq14
  have eq103 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X1 ◇ X2) ◇ X4)) = (((X3 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X3)) ◇ X3) ◇ X4) := superpose eq14 eq29
  have eq146 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = ((((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X0) := superpose eq52 eq52
  have eq155 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = ((X2 ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X2)) ◇ X2) := superpose eq52 eq9
  have eq163 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq67 eq155
  have eq164 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X0) := superpose eq163 eq146
  have eq165 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = (X0 ◇ X0) := superpose eq52 eq164
  have eq281 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq165 eq52
  have eq284 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ X1) := superpose eq165 eq7
  have eq305 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq7 eq284
  have eq308 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq305 eq7
  have eq309 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) = (X2 ◇ (X0 ◇ X2)) := superpose eq305 eq9
  have eq312 (X0 X1 X2 X3 X5 : G) : ((X5 ◇ ((X2 ◇ X3) ◇ X5)) ◇ X5) = (X3 ◇ ((((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) := superpose eq305 eq12
  have eq313 (X0 X1 X2 X3 X5 : G) : ((X5 ◇ ((X2 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))) ◇ X5)) ◇ X5) = ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X0)) := superpose eq305 eq13
  have eq322 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0)) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))) = X2 := superpose eq305 eq26
  have eq404 (X0 X1 X2 X4 : G) : (X4 ◇ ((X1 ◇ X2) ◇ X4)) = (((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0) ◇ X4) := superpose eq308 eq103
  have eq410 (X1 X2 X3 X4 : G) : ((X4 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X4)) ◇ X4) = ((X3 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq308 eq68
  have eq418 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X4) = (X4 ◇ ((X1 ◇ X2) ◇ X4)) := superpose eq308 eq404
  have eq422 (X1 X2 X3 : G) : (X3 ◇ ((X1 ◇ X2) ◇ X3)) = ((X3 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq308 eq410
  have eq423 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = ((X3 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq418 eq422
  have eq424 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X1 := superpose eq423 eq281
  have eq433 (X0 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X0 ◇ X2)) := superpose eq308 eq309
  have eq442 (X0 X1 X2 X3 X5 : G) : ((X5 ◇ ((X2 ◇ X3) ◇ X5)) ◇ X5) = (X3 ◇ (((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) := superpose eq423 eq312
  have eq443 (X1 X2 X3 X5 : G) : ((X5 ◇ ((X2 ◇ X3) ◇ X5)) ◇ X5) = (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3)) := superpose eq305 eq442
  have eq444 (X1 X2 X3 X5 : G) : (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3)) = (((X2 ◇ X3) ◇ X5) ◇ X5) := superpose eq418 eq443
  have eq445 (X1 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3)) := superpose eq305 eq444
  have eq446 (X0 X1 X2 X3 X5 : G) : ((X5 ◇ ((X2 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))) ◇ X5)) ◇ X5) = ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ X0) ◇ X0)) := superpose eq423 eq313
  have eq447 (X1 X2 X3 X5 : G) : ((X5 ◇ ((X2 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))) ◇ X5)) ◇ X5) = ((X1 ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))) := superpose eq305 eq446
  have eq448 (X1 X2 X5 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = ((X5 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X5)) ◇ X5) := superpose eq305 eq447
  have eq449 (X1 X2 X5 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = (((X2 ◇ (X1 ◇ X2)) ◇ X5) ◇ X5) := superpose eq418 eq448
  have eq450 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X2)) := superpose eq305 eq449
  have eq451 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq433 eq450
  have eq452 (X1 X2 X3 : G) : (X2 ◇ X3) = (X3 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq451 eq445
  have eq453 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X4) = (X2 ◇ X4) := superpose eq452 eq418
  have eq454 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq453 eq424
  have eq459 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq454 eq451
  have eq480 (X0 X2 X3 : G) : ((((X2 ◇ X3) ◇ X3) ◇ ((X0 ◇ (((X2 ◇ X3) ◇ X3) ◇ X0)) ◇ X0)) ◇ ((X2 ◇ X3) ◇ X3)) = X2 := superpose eq459 eq322
  have eq481 (X0 X2 X3 : G) : ((X3 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X0)) ◇ X3) = X2 := superpose eq459 eq480
  have eq482 (X0 X2 X3 : G) : (((X0 ◇ (X3 ◇ X0)) ◇ X0) ◇ X3) = X2 := superpose eq459 eq481
  have eq483 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq459 eq482
  have eq484 (X0 X3 : G) : X0 = X3 := superpose eq483 eq483
  have eq489 (X0 : G) : sK0 ≠ X0 := superpose eq484 eq8
  subsumption eq489 eq484


@[equational_result]
theorem Equation33077_implies_Equation2 (G : Type*) [Magma G] (h : Equation33077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation33080_implies_Equation2 (G : Type*) [Magma G] (h : Equation33080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq60 eq11


@[equational_result]
theorem Equation33081_implies_Equation2 (G : Type*) [Magma G] (h : Equation33081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33083_implies_Equation2 (G : Type*) [Magma G] (h : Equation33083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation33084_implies_Equation2 (G : Type*) [Magma G] (h : Equation33084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation33085_implies_Equation2 (G : Type*) [Magma G] (h : Equation33085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq47 eq12


@[equational_result]
theorem Equation33086_implies_Equation2 (G : Type*) [Magma G] (h : Equation33086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33088_implies_Equation2 (G : Type*) [Magma G] (h : Equation33088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq118 eq41


@[equational_result]
theorem Equation33089_implies_Equation2 (G : Type*) [Magma G] (h : Equation33089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33090_implies_Equation2 (G : Type*) [Magma G] (h : Equation33090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation33091_implies_Equation2 (G : Type*) [Magma G] (h : Equation33091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33093_implies_Equation2 (G : Type*) [Magma G] (h : Equation33093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation33094_implies_Equation2 (G : Type*) [Magma G] (h : Equation33094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation33095_implies_Equation2 (G : Type*) [Magma G] (h : Equation33095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X4) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation33096_implies_Equation2 (G : Type*) [Magma G] (h : Equation33096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33098_implies_Equation2 (G : Type*) [Magma G] (h : Equation33098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (((X0 ◇ X3) ◇ X4) ◇ X3))) ◇ X1) = X2 := superpose eq7 eq7
  have eq23 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq88 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq88 eq23


@[equational_result]
theorem Equation33099_implies_Equation2 (G : Type*) [Magma G] (h : Equation33099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33100_implies_Equation2 (G : Type*) [Magma G] (h : Equation33100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation33101_implies_Equation2 (G : Type*) [Magma G] (h : Equation33101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33103_implies_Equation2 (G : Type*) [Magma G] (h : Equation33103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq55 eq17


@[equational_result]
theorem Equation33104_implies_Equation2 (G : Type*) [Magma G] (h : Equation33104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation33105_implies_Equation2 (G : Type*) [Magma G] (h : Equation33105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq51 eq12


@[equational_result]
theorem Equation33106_implies_Equation2 (G : Type*) [Magma G] (h : Equation33106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33108_implies_Equation2 (G : Type*) [Magma G] (h : Equation33108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation33109_implies_Equation2 (G : Type*) [Magma G] (h : Equation33109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33110_implies_Equation2 (G : Type*) [Magma G] (h : Equation33110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq53 eq13


@[equational_result]
theorem Equation33111_implies_Equation2 (G : Type*) [Magma G] (h : Equation33111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33112_implies_Equation2 (G : Type*) [Magma G] (h : Equation33112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X0 ◇ X2) ◇ X3) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X9 : G) : (X0 ◇ X9) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33115_implies_Equation2 (G : Type*) [Magma G] (h : Equation33115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation33118_implies_Equation2 (G : Type*) [Magma G] (h : Equation33118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation33120_implies_Equation2 (G : Type*) [Magma G] (h : Equation33120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) ◇ X3)) ◇ (X0 ◇ X4)) ◇ (X1 ◇ (((X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) ◇ X3))) = X1 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) = ((((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) ◇ X4)) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X3))) := superpose eq7 eq9
  have eq46 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2))) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2))) ◇ X3))) := superpose eq7 eq10
  have eq55 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2)) = ((((X0 ◇ (((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2)) ◇ (X0 ◇ X3)) ◇ (((X0 ◇ (((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2)) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2))) ◇ X4)) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2)) ◇ (X0 ◇ X3))) := superpose eq10 eq9
  have eq56 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2)) = (((X0 ◇ (((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2)) ◇ (X0 ◇ X3)) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2))) := superpose eq10 eq7
  have eq65 (X0 X1 X2 : G) : (X0 ◇ (((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2)) = X0 := superpose eq10 eq56
  have eq66 (X0 X3 X4 : G) : (((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X0) ◇ X4)) ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq65 eq55
  have eq70 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2)) = ((((X0 ◇ (((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2)) ◇ X3)) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2)) ◇ ((X0 ◇ (((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2)) ◇ X3))) := superpose eq10 eq66
  have eq87 (X0 X3 : G) : (((X0 ◇ (X0 ◇ X3)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X3))) = X0 := superpose eq65 eq70
  have eq123 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) = (((((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3))) ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X0)) := superpose eq9 eq87
  have eq143 (X0 X1 X2 : G) : (((X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) = X0 := superpose eq87 eq9
  have eq146 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) = X0 := superpose eq7 eq143
  have eq215 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq146 eq87
  have eq221 (X0 X1 X2 X3 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = ((((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq146 eq14
  have eq223 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq87 eq215
  have eq224 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) = ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X0)) := superpose eq221 eq123
  have eq294 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X0) = (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) ◇ ((((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)))) := superpose eq9 eq223
  have eq345 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) = (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X0) := superpose eq221 eq294
  have eq346 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) ◇ X0) = X0 := superpose eq9 eq345
  have eq347 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ X0) = ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq346 eq224
  have eq352 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X3)) = X1 := superpose eq7 eq347
  have eq364 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) = X1 := superpose eq352 eq9
  have eq432 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ X2)) = X0 := superpose eq364 eq65
  have eq433 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq364 eq432
  have eq451 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2))) ◇ X3))) := superpose eq433 eq46
  have eq600 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3))) := superpose eq433 eq451
  have eq601 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq433 eq600
  have eq602 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq7 eq601
  have eq618 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X0 := superpose eq602 eq7
  have eq717 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq602 eq618
  have eq992 (X0 X2 : G) : X0 = X2 := superpose eq717 eq717
  have eq994 (X0 : G) : sK0 ≠ X0 := superpose eq992 eq8
  subsumption eq994 eq992


@[equational_result]
theorem Equation33121_implies_Equation2 (G : Type*) [Magma G] (h : Equation33121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X2) ◇ X3)) ◇ ((X2 ◇ X3) ◇ X4)) ◇ X4) = X3 := superpose eq7 eq9
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X1 ◇ (X2 ◇ (((X2 ◇ X0) ◇ X0) ◇ X3))) ◇ (X2 ◇ (((X2 ◇ X0) ◇ X0) ◇ X3))) ◇ X3)) ◇ (X0 ◇ X4)) ◇ X4) = X3 := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (((X1 ◇ (((X1 ◇ (X2 ◇ (((X2 ◇ X3) ◇ X3) ◇ X0))) ◇ (X2 ◇ (((X2 ◇ X3) ◇ X3) ◇ X0))) ◇ ((X3 ◇ X0) ◇ X4))) ◇ X0) ◇ X4) := superpose eq9 eq9
  have eq37 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ X0) := superpose eq10 eq7
  have eq41 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq7 eq37
  have eq46 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) = X0 := superpose eq41 eq7
  have eq52 (X0 X1 : G) : (((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ X1) = X0 := superpose eq41 eq7
  have eq58 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) = X0 := superpose eq41 eq52
  have eq89 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0)) = ((((X1 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0)) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0)) := superpose eq9 eq46
  have eq91 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq41 eq46
  have eq103 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0)) = (X1 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X0)) := superpose eq7 eq89
  have eq244 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X2))) ◇ X2) := superpose eq7 eq12
  have eq279 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq91 eq58
  have eq316 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq279 eq46
  have eq531 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1)) = X1 := superpose eq279 eq9
  have eq549 (X0 X1 : G) : ((X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1)) = X1 := superpose eq103 eq531
  have eq683 (X0 X1 X2 X3 : G) : (((X2 ◇ (((X2 ◇ (X3 ◇ (((X3 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)))) ◇ (X3 ◇ (((X3 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)))) ◇ X0)) ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq316 eq15
  have eq704 (X0 X1 X2 X3 : G) : ((X3 ◇ (((X3 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) ◇ X0)) ◇ X2) = X0 := superpose eq7 eq244
  have eq744 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq704 eq683
  have eq746 (X0 X1 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = X1 := superpose eq744 eq549
  have eq1072 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq744 eq746
  have eq1073 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := superpose eq744 eq1072
  have eq1074 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = X1 := superpose eq744 eq1073
  have eq1075 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq279 eq1074
  have eq1079 (X0 X2 : G) : X0 = X2 := superpose eq1075 eq1075
  have eq1087 (X0 : G) : sK0 ≠ X0 := superpose eq1079 eq8
  subsumption eq1087 eq1079


@[equational_result]
theorem Equation33122_implies_Equation2 (G : Type*) [Magma G] (h : Equation33122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X3) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation33125_implies_Equation2 (G : Type*) [Magma G] (h : Equation33125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0))) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation33128_implies_Equation2 (G : Type*) [Magma G] (h : Equation33128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1))) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation33130_implies_Equation2 (G : Type*) [Magma G] (h : Equation33130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = ((X1 ◇ (X0 ◇ X3)) ◇ X1) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X1) ◇ ((X1 ◇ X2) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ X3))) ◇ X4) = (X0 ◇ ((X1 ◇ X2) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq7 eq10
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X2) = X0 := superpose eq7 eq10
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X0) = X1 := superpose eq10 eq7
  have eq67 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = (((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X0) ◇ X4) := superpose eq10 eq25
  have eq91 (X1 X3 X4 : G) : (X1 ◇ X4) = (X1 ◇ X3) := superpose eq7 eq67
  have eq109 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X2)) := superpose eq29 eq29
  have eq120 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X4)) ◇ X1) := superpose eq29 eq10
  have eq132 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = (((((X1 ◇ X2) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ X3)) ◇ X1) ◇ ((X1 ◇ X2) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ X3))) ◇ X4) := superpose eq109 eq22
  have eq172 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) ◇ X3) = X0 := superpose eq7 eq91
  have eq228 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = ((X0 ◇ ((X1 ◇ X2) ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ X3))) ◇ X4) := superpose eq172 eq132
  have eq243 (X0 X1 X2 X4 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X4) := superpose eq109 eq228
  have eq246 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ X1) := superpose eq243 eq120
  have eq259 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq29 eq246
  have eq260 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X2) = X0 := superpose eq259 eq25
  have eq314 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq259 eq260
  have eq315 (X0 X3 : G) : X0 = X3 := superpose eq314 eq314
  have eq317 (X0 : G) : sK0 ≠ X0 := superpose eq315 eq8
  subsumption eq317 eq315


@[equational_result]
theorem Equation33131_implies_Equation2 (G : Type*) [Magma G] (h : Equation33131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = ((X0 ◇ (X1 ◇ X3)) ◇ X3) := superpose eq10 eq10
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) ◇ X0) = X1 := superpose eq10 eq7
  have eq67 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq20 eq20
  have eq78 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) ◇ X2) = X0 := superpose eq67 eq7
  have eq164 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X3) = (X2 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) := superpose eq78 eq78
  have eq202 (X0 X1 X2 X3 X4 : G) : (X4 ◇ ((X4 ◇ ((X1 ◇ X3) ◇ X4)) ◇ X3)) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ X0) := superpose eq164 eq164
  have eq203 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1)) = X0 := superpose eq20 eq164
  have eq244 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X2) ◇ X0) = X1 := superpose eq203 eq202
  have eq257 (X0 X1 X2 : G) : ((((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ X1) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq244 eq244
  have eq346 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := superpose eq203 eq203
  have eq507 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq67 eq346
  have eq520 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ X1) = X0 := superpose eq346 eq20
  have eq528 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ X2)) ◇ X2) ◇ X0) := superpose eq346 eq244
  have eq701 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq507 eq15
  have eq704 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) = X0 := superpose eq507 eq20
  have eq727 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq507 eq704
  have eq728 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq727 eq701
  have eq732 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq727 eq728
  have eq733 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq727 eq732
  have eq734 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ X0) := superpose eq733 eq528
  have eq736 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq727 eq734
  have eq739 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X1) = X0 := superpose eq736 eq520
  have eq753 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq736 eq739
  have eq756 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X2 := superpose eq753 eq257
  have eq1018 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq753 eq756
  have eq1019 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq753 eq1018
  have eq1038 (X0 X2 : G) : X0 = X2 := superpose eq1019 eq1019
  have eq1040 (X0 : G) : sK0 ≠ X0 := superpose eq1038 eq8
  subsumption eq1040 eq1038


@[equational_result]
theorem Equation33132_implies_Equation2 (G : Type*) [Magma G] (h : Equation33132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X2))) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation33134_implies_Equation2 (G : Type*) [Magma G] (h : Equation33134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) ◇ ((X0 ◇ X3) ◇ X1)) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X0))) = X1 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (((X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X1)) ◇ X0) ◇ (X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X1))) = X1 := superpose eq7 eq9
  have eq36 (X0 X1 : G) : X0 = X1 := superpose eq7 eq20
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq70 eq36


@[equational_result]
theorem Equation33136_implies_Equation2 (G : Type*) [Magma G] (h : Equation33136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) ◇ ((X0 ◇ X4) ◇ X3)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation33138_implies_Equation2 (G : Type*) [Magma G] (h : Equation33138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) ◇ ((X0 ◇ X3) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)))) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1))) = (((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) ◇ (X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)))) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1))) := superpose eq7 eq10
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1))) ◇ X3) ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq10
  have eq33 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) = ((((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) ◇ ((X0 ◇ X3) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)))) ◇ ((X1 ◇ X4) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) ◇ ((X0 ◇ X3) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)))))) ◇ ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) ◇ ((X0 ◇ X3) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1))))) := superpose eq7 eq9
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) = (((((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) ◇ ((X0 ◇ X4) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))))) ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X5) ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) ◇ ((X0 ◇ X4) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))))))) ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) ◇ ((X0 ◇ X4) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))))))) := superpose eq9 eq9
  have eq43 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) = (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) := superpose eq9 eq10
  have eq46 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))))) ◇ X4) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) = (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) := superpose eq9 eq10
  have eq47 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))))) = ((((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))))) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))))) := superpose eq9 eq10
  have eq49 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))))) ◇ X4) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) = (X1 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) := superpose eq7 eq46
  have eq50 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) = ((X0 ◇ X4) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))))) := superpose eq33 eq47
  have eq51 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) = (((((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X5) ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))))) ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) := superpose eq50 eq36
  have eq53 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) = (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X4) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) := superpose eq50 eq49
  have eq54 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) = ((X0 ◇ (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ X5) ◇ X0)) ◇ X0) := superpose eq9 eq51
  have eq55 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) := superpose eq7 eq54
  have eq58 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1))) = X1 := superpose eq55 eq9
  have eq60 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1))) = (X0 ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1))) := superpose eq53 eq11
  have eq62 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) = (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) := superpose eq60 eq43
  have eq63 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (X1 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) := superpose eq60 eq55
  have eq64 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) = (((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (X1 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)))) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) := superpose eq60 eq62
  have eq65 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) = ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) := superpose eq63 eq64
  have eq66 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) = X0 := superpose eq58 eq65
  have eq68 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X3) ◇ X1) := superpose eq66 eq16
  have eq78 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ X1) = X0 := superpose eq7 eq68
  have eq142 (X0 X3 : G) : X0 = X3 := superpose eq7 eq78
  have eq205 (X0 : G) : sK0 ≠ X0 := superpose eq142 eq8
  subsumption eq205 eq142


@[equational_result]
theorem Equation33139_implies_Equation2 (G : Type*) [Magma G] (h : Equation33139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) ◇ ((X0 ◇ X3) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ (X1 ◇ X2))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1)) ◇ X2) := superpose eq7 eq10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ (X1 ◇ X2))) = X0 := superpose eq7 eq10
  have eq18 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq10 eq10
  have eq22 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X2) ◇ X1) = X0 := superpose eq7 eq10
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X2) = X1 := superpose eq10 eq7
  have eq32 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := superpose eq18 eq17
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := superpose eq18 eq11
  have eq55 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X2))) ◇ X3) = ((X0 ◇ X3) ◇ (X1 ◇ X2)) := superpose eq33 eq10
  have eq67 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X0) ◇ (X0 ◇ X1)) = X2 := superpose eq10 eq22
  have eq80 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (X0 ◇ X1)) = X2 := superpose eq10 eq67
  have eq95 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0)) ◇ (((X1 ◇ X0) ◇ X3) ◇ (X0 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X0)))) ◇ X3) = X2 := superpose eq10 eq9
  have eq96 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X0))) = (((X1 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X3) := superpose eq33 eq9
  have eq135 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq26 eq26
  have eq230 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X2))) := superpose eq33 eq135
  have eq267 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq230 eq55
  have eq274 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = X0 := superpose eq267 eq22
  have eq339 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1) = (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq15 eq274
  have eq349 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))) ◇ X3) := superpose eq274 eq9
  have eq367 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq267 eq339
  have eq368 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ X1) = ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq135 eq367
  have eq370 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0))) ◇ (((X1 ◇ X0) ◇ X3) ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X0))))) ◇ X3) = X2 := superpose eq368 eq95
  have eq410 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X0))) := superpose eq349 eq96
  have eq415 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) = X0 := superpose eq410 eq32
  have eq439 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq415 eq80
  have eq443 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ (((X1 ◇ X0) ◇ X3) ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0))))) ◇ X3) = X2 := superpose eq439 eq370
  have eq585 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3) = X2 := superpose eq439 eq443
  have eq586 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq439 eq585
  have eq587 (X0 X3 : G) : X0 = X3 := superpose eq586 eq586
  have eq599 (X0 : G) : sK0 ≠ X0 := superpose eq587 eq8
  subsumption eq599 eq587


@[equational_result]
theorem Equation33140_implies_Equation2 (G : Type*) [Magma G] (h : Equation33140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) ◇ ((X0 ◇ X4) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation33143_implies_Equation2 (G : Type*) [Magma G] (h : Equation33143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) ◇ ((X0 ◇ X3) ◇ X3)) ◇ X3) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X2) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ ((X0 ◇ X3) ◇ X3)) ◇ X3) = X2 := superpose eq10 eq9
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X2) = X0 := superpose eq10 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := superpose eq12 eq12
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2)) ◇ (X0 ◇ (X3 ◇ X3))) ◇ X3) = X2 := superpose eq15 eq11
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) ◇ X2) = X0 := superpose eq15 eq12
  have eq21 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X0 ◇ (X3 ◇ X3)))) ◇ X3) = X2 := superpose eq15 eq16
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3))))) ◇ X3) = X2 := superpose eq15 eq21
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))))) ◇ X3) = X2 := superpose eq15 eq22
  have eq24 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3))))))) ◇ X3) = X2 := superpose eq15 eq23
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X2) = X0 := superpose eq15 eq18
  have eq48 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X2)) = X0 := superpose eq27 eq15
  have eq56 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2))) = X0 := superpose eq15 eq48
  have eq57 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2)))) = X0 := superpose eq15 eq56
  have eq58 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2))))) = X0 := superpose eq15 eq57
  have eq104 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq58 eq58
  have eq121 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq104 eq24
  have eq136 (X0 X3 : G) : X0 = X3 := superpose eq58 eq121
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq136 eq8
  subsumption eq159 eq136


@[equational_result]
theorem Equation33144_implies_Equation2 (G : Type*) [Magma G] (h : Equation33144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) ◇ ((X0 ◇ X4) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation33146_implies_Equation2 (G : Type*) [Magma G] (h : Equation33146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation33147_implies_Equation2 (G : Type*) [Magma G] (h : Equation33147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = ((X1 ◇ (X0 ◇ X4)) ◇ X2) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X4)) = X2 := superpose eq7 eq7
  have eq33 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X0 ◇ X1) ◇ X3) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X5) ◇ X6)) ◇ X5) = X4 := superpose eq10 eq7
  have eq51 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ X4) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X5) ◇ X6)) = X3 := superpose eq10 eq11
  have eq72 (X3 X4 X5 : G) : (X3 ◇ X5) = X4 := superpose eq51 eq33
  have eq73 (X0 X4 : G) : X0 = X4 := superpose eq7 eq72
  have eq177 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq177 eq73


@[equational_result]
theorem Equation33148_implies_Equation2 (G : Type*) [Magma G] (h : Equation33148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ X4) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq71 eq15


@[equational_result]
theorem Equation33149_implies_Equation2 (G : Type*) [Magma G] (h : Equation33149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) ◇ ((X0 ◇ X5) ◇ X6)) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation33152_implies_Equation2 (G : Type*) [Magma G] (h : Equation33152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation33155_implies_Equation2 (G : Type*) [Magma G] (h : Equation33155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X2) ◇ (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)))) ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation33157_implies_Equation2 (G : Type*) [Magma G] (h : Equation33157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) ◇ X2) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X3)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) = X2 := superpose eq9 eq7
  have eq23 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) = X2 := superpose eq9 eq17
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq118 eq57


@[equational_result]
theorem Equation33159_implies_Equation2 (G : Type*) [Magma G] (h : Equation33159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X3) ◇ X4)) ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation33162_implies_Equation2 (G : Type*) [Magma G] (h : Equation33162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0))) ◇ X2)) ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq25 eq12


@[equational_result]
theorem Equation33164_implies_Equation2 (G : Type*) [Magma G] (h : Equation33164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation33165_implies_Equation2 (G : Type*) [Magma G] (h : Equation33165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33167_implies_Equation2 (G : Type*) [Magma G] (h : Equation33167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation33168_implies_Equation2 (G : Type*) [Magma G] (h : Equation33168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation33169_implies_Equation2 (G : Type*) [Magma G] (h : Equation33169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33171_implies_Equation2 (G : Type*) [Magma G] (h : Equation33171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq16 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq29 eq16


@[equational_result]
theorem Equation33172_implies_Equation2 (G : Type*) [Magma G] (h : Equation33172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq9 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq40 eq19


@[equational_result]
theorem Equation33173_implies_Equation2 (G : Type*) [Magma G] (h : Equation33173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) ◇ ((X0 ◇ X3) ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation33175_implies_Equation2 (G : Type*) [Magma G] (h : Equation33175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation33176_implies_Equation2 (G : Type*) [Magma G] (h : Equation33176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33177_implies_Equation2 (G : Type*) [Magma G] (h : Equation33177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33179_implies_Equation2 (G : Type*) [Magma G] (h : Equation33179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation33180_implies_Equation2 (G : Type*) [Magma G] (h : Equation33180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation33181_implies_Equation2 (G : Type*) [Magma G] (h : Equation33181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33183_implies_Equation2 (G : Type*) [Magma G] (h : Equation33183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33184_implies_Equation2 (G : Type*) [Magma G] (h : Equation33184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33185_implies_Equation2 (G : Type*) [Magma G] (h : Equation33185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33186_implies_Equation2 (G : Type*) [Magma G] (h : Equation33186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X1) ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33188_implies_Equation2 (G : Type*) [Magma G] (h : Equation33188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq7 eq10
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq66 eq32


@[equational_result]
theorem Equation33189_implies_Equation2 (G : Type*) [Magma G] (h : Equation33189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X3) ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ (X3 ◇ X2)) ◇ ((X0 ◇ X3) ◇ X3)) = X2 := superpose eq7 eq10
  have eq20 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ X3) ◇ X3)) ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) = X3 := superpose eq10 eq7
  have eq32 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X2)) = X2 := superpose eq7 eq9
  have eq41 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ (X0 ◇ X2)) = X2 := superpose eq7 eq32
  have eq105 (X0 X1 X2 : G) : (X0 ◇ ((((X1 ◇ (((X1 ◇ X0) ◇ X2) ◇ X2)) ◇ X0) ◇ X2) ◇ X2)) = X0 := superpose eq41 eq10
  have eq113 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X2) ◇ X2)) = X0 := superpose eq7 eq105
  have eq147 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ X2) ◇ X0) := superpose eq15 eq9
  have eq167 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := superpose eq41 eq113
  have eq188 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1))) := superpose eq113 eq41
  have eq203 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X2))) ◇ (((X2 ◇ X2) ◇ X2) ◇ X1)) = X1 := superpose eq113 eq41
  have eq234 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X2) := superpose eq113 eq188
  have eq235 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X1) := superpose eq32 eq234
  have eq246 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (((X2 ◇ X2) ◇ X2) ◇ X1)) = X1 := superpose eq113 eq203
  have eq357 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) = X2 := superpose eq235 eq10
  have eq368 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X1)) = X3 := superpose eq235 eq20
  have eq389 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X2 := superpose eq235 eq9
  have eq420 (X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) = X2 := superpose eq113 eq357
  have eq421 (X0 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ X0) := superpose eq420 eq147
  have eq422 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X0 := superpose eq421 eq113
  have eq426 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X2) ◇ X1)) = X1 := superpose eq421 eq246
  have eq440 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq422 eq167
  have eq443 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X0 := superpose eq422 eq440
  have eq448 (X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X1)) = X1 := superpose eq443 eq426
  have eq472 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X1)) = X3 := superpose eq421 eq368
  have eq499 (X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ X1) = X2 := superpose eq448 eq389
  have eq500 (X1 X2 : G) : (X2 ◇ X1) = X2 := superpose eq32 eq499
  have eq501 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X1)) = X3 := superpose eq500 eq472
  have eq714 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ ((X1 ◇ X2) ◇ X2)) = X3 := superpose eq500 eq501
  have eq715 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ (X1 ◇ X2)) = X3 := superpose eq500 eq714
  have eq716 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ ((X2 ◇ X3) ◇ X3)) ◇ X1) = X3 := superpose eq500 eq715
  have eq717 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ X1) = X3 := superpose eq500 eq716
  have eq718 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq500 eq717
  have eq719 (X0 X3 : G) : X0 = X3 := superpose eq718 eq718
  have eq738 (X0 : G) : sK0 ≠ X0 := superpose eq719 eq8
  subsumption eq738 eq719


@[equational_result]
theorem Equation33190_implies_Equation2 (G : Type*) [Magma G] (h : Equation33190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ ((X0 ◇ X4) ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation33192_implies_Equation2 (G : Type*) [Magma G] (h : Equation33192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq31 eq13


@[equational_result]
theorem Equation33194_implies_Equation2 (G : Type*) [Magma G] (h : Equation33194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X4) ◇ (X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)))) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation33198_implies_Equation2 (G : Type*) [Magma G] (h : Equation33198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X4) ◇ X3)) ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation33200_implies_Equation2 (G : Type*) [Magma G] (h : Equation33200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X4 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ X1) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq32 eq16


@[equational_result]
theorem Equation33201_implies_Equation2 (G : Type*) [Magma G] (h : Equation33201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X4) = ((X1 ◇ X0) ◇ X2) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ (X4 ◇ X5)) ◇ ((X0 ◇ X4) ◇ X6)) = X2 := superpose eq7 eq10
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X4) ◇ X5)) ◇ X0) = X2 := superpose eq7 eq10
  have eq28 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X4) ◇ X3)) ◇ X0) = X2 := superpose eq11 eq20
  have eq29 (X0 X2 X4 X6 : G) : (X2 ◇ ((X0 ◇ X4) ◇ X6)) = X2 := superpose eq28 eq16
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq29 eq28
  have eq50 (X0 X5 : G) : X0 = X5 := superpose eq10 eq32
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq108 eq50


@[equational_result]
theorem Equation33202_implies_Equation2 (G : Type*) [Magma G] (h : Equation33202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ X4) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation33203_implies_Equation2 (G : Type*) [Magma G] (h : Equation33203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) ◇ ((X0 ◇ X5) ◇ X6)) ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation33205_implies_Equation2 (G : Type*) [Magma G] (h : Equation33205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq10
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq101 eq37


@[equational_result]
theorem Equation33206_implies_Equation2 (G : Type*) [Magma G] (h : Equation33206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0))) ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (((X2 ◇ X3) ◇ X2) ◇ X0)))) = X3 := superpose eq7 eq10
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ X2) ◇ X2) ◇ X3) = ((X1 ◇ X0) ◇ (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ (X3 ◇ X0)))) := superpose eq10 eq10
  have eq16 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X2) := superpose eq10 eq7
  have eq24 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) ◇ X2) = X1 := superpose eq7 eq9
  have eq82 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := superpose eq11 eq12
  have eq87 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ (X3 ◇ X1))))) = X4 := superpose eq12 eq10
  have eq112 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) ◇ ((((((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) ◇ X3)) ◇ X1) = X3 := superpose eq12 eq9
  have eq141 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) := superpose eq82 eq82
  have eq150 (X0 X1 : G) : (X0 ◇ (((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ X0))) = X1 := superpose eq82 eq10
  have eq156 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ X2) = (X0 ◇ (((((X3 ◇ X3) ◇ X3) ◇ ((X3 ◇ X3) ◇ X3)) ◇ ((X3 ◇ X3) ◇ X3)) ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))))) := superpose eq82 eq12
  have eq164 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) := superpose eq82 eq141
  have eq166 (X0 X1 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X1 ◇ X0))) = X1 := superpose eq82 eq150
  have eq168 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X1) ◇ X2) = (X0 ◇ ((X3 ◇ ((X3 ◇ X3) ◇ X3)) ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))))) := superpose eq82 eq156
  have eq226 (X0 X1 X2 : G) : (X2 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = (X1 ◇ (((X2 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) ◇ (((X2 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) ◇ (X2 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0))) ◇ (X2 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)))) ◇ X0)) := superpose eq7 eq166
  have eq235 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) ◇ X0) := superpose eq166 eq166
  have eq239 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = ((X2 ◇ (X0 ◇ X1)) ◇ (((X2 ◇ X2) ◇ X2) ◇ X0)) := superpose eq166 eq12
  have eq244 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X3)) = ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X1) ◇ (X3 ◇ ((X0 ◇ X3) ◇ X2)))) := superpose eq166 eq11
  have eq250 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = ((((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq166 eq12
  have eq263 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) ◇ X0) := superpose eq164 eq235
  have eq264 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) := superpose eq168 eq263
  have eq265 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) := superpose eq16 eq264
  have eq267 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq10 eq239
  have eq273 (X0 X1 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X0) := superpose eq164 eq250
  have eq274 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) := superpose eq267 eq273
  have eq276 (X0 X1 X2 : G) : (X2 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := superpose eq274 eq226
  have eq282 (X0 X1 X2 : G) : (((X2 ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0)) ◇ X2) = X1 := superpose eq276 eq24
  have eq355 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ (((((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X1)))) ◇ X3) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X1))))) ◇ (X2 ◇ X2))) ◇ X3) = X2 := superpose eq12 eq282
  have eq357 (X0 X1 X2 X3 : G) : (((((X2 ◇ X3) ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X2 ◇ X3) ◇ X2) ◇ (X2 ◇ X1))))) ◇ ((X2 ◇ X3) ◇ X2)) = X3 := superpose eq12 eq282
  have eq379 (X2 X3 : G) : (X2 ◇ ((X2 ◇ X3) ◇ X2)) = X3 := superpose eq87 eq357
  have eq403 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X1) ◇ X1) ◇ (X3 ◇ ((X0 ◇ X3) ◇ X2)))) = (X0 ◇ (X0 ◇ X3)) := superpose eq379 eq244
  have eq413 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq379 eq265
  have eq414 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X0) = X1 := superpose eq379 eq267
  have eq420 (X2 X3 : G) : (((X3 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ ((((X2 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2))) ◇ X3) = X2 := superpose eq403 eq355
  have eq425 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) ◇ (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X3)) ◇ X1) = X3 := superpose eq414 eq112
  have eq426 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq414 eq413
  have eq542 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X3)) ◇ X1) = X3 := superpose eq414 eq425
  have eq543 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X3)) ◇ X1) = X3 := superpose eq379 eq542
  have eq544 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X1) = X3 := superpose eq414 eq543
  have eq546 (X2 X3 : G) : (((X3 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2))) ◇ X3) = X2 := superpose eq544 eq420
  have eq547 (X2 X3 : G) : (((X3 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq544 eq546
  have eq549 (X2 X3 : G) : (((X3 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) ◇ X3) = X2 := superpose eq426 eq547
  have eq556 (X0 X1 X2 : G) : (X1 ◇ X0) = (X2 ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) := superpose eq426 eq276
  have eq569 (X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X3) = X2 := superpose eq426 eq549
  have eq575 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq556 eq7
  have eq580 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq575 eq379
  have eq585 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq580 eq569
  have eq610 (X0 X1 : G) : X0 = X1 := superpose eq580 eq585
  have eq612 (X0 : G) : sK0 ≠ X0 := superpose eq610 eq8
  subsumption eq612 eq610


@[equational_result]
theorem Equation33207_implies_Equation2 (G : Type*) [Magma G] (h : Equation33207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0))) ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation33209_implies_Equation2 (G : Type*) [Magma G] (h : Equation33209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33210_implies_Equation2 (G : Type*) [Magma G] (h : Equation33210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33211_implies_Equation2 (G : Type*) [Magma G] (h : Equation33211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33213_implies_Equation2 (G : Type*) [Magma G] (h : Equation33213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33214_implies_Equation2 (G : Type*) [Magma G] (h : Equation33214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33215_implies_Equation2 (G : Type*) [Magma G] (h : Equation33215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33217_implies_Equation2 (G : Type*) [Magma G] (h : Equation33217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33218_implies_Equation2 (G : Type*) [Magma G] (h : Equation33218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33219_implies_Equation2 (G : Type*) [Magma G] (h : Equation33219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33220_implies_Equation2 (G : Type*) [Magma G] (h : Equation33220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X1) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33223_implies_Equation2 (G : Type*) [Magma G] (h : Equation33223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X3)) ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (((X3 ◇ X2) ◇ X2) ◇ X0)))) ◇ (X0 ◇ X4)) ◇ X2) = X4 := superpose eq7 eq9
  have eq18 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose eq9 eq7
  have eq19 (X0 X1 X2 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq18
  have eq31 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq7 eq19
  have eq79 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq31 eq7
  have eq85 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0)) := superpose eq31 eq18
  have eq95 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) = X1 := superpose eq31 eq79
  have eq98 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq31 eq85
  have eq134 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X3 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2)))) ◇ ((X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X3 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2)))) ◇ (X2 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X3 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2)))) ◇ (X2 ◇ X0)))) := superpose eq13 eq18
  have eq155 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X3 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2)))) ◇ (X3 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2))) ◇ (X0 ◇ (X3 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2)))) := superpose eq7 eq134
  have eq159 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq18 eq95
  have eq160 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq95 eq95
  have eq286 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ (((X3 ◇ X2) ◇ X2) ◇ (X0 ◇ X0))))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2) := superpose eq98 eq13
  have eq297 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq13 eq286
  have eq309 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq297 eq160
  have eq310 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := superpose eq297 eq159
  have eq376 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq297 eq309
  have eq377 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq297 eq376
  have eq378 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq297 eq377
  have eq379 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq297 eq310
  have eq380 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq378 eq379
  have eq587 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X3 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2)))) = (X0 ◇ ((X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X3 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2)))) ◇ (X2 ◇ X0))) := superpose eq13 eq380
  have eq630 (X0 X1 X2 X3 : G) : (X1 ◇ (((X1 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ (X3 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2)))) = (X0 ◇ (X3 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2))) := superpose eq7 eq587
  have eq637 (X0 X2 X3 : G) : (X2 ◇ X0) = (((X0 ◇ (X3 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2))) ◇ (X3 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2))) ◇ (X0 ◇ (X3 ◇ (((X3 ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0)) ◇ X2)))) := superpose eq630 eq155
  have eq639 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq380 eq637
  have eq640 (X0 X1 X2 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X0) ◇ X0) = X2 := superpose eq639 eq19
  have eq870 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq639 eq640
  have eq899 (X0 X2 : G) : X0 = X2 := superpose eq870 eq870
  have eq907 (X0 : G) : sK0 ≠ X0 := superpose eq899 eq8
  subsumption eq907 eq899


@[equational_result]
theorem Equation33224_implies_Equation2 (G : Type*) [Magma G] (h : Equation33224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X0)) ◇ ((X0 ◇ X3) ◇ X4)) ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq26 eq13


@[equational_result]
theorem Equation33226_implies_Equation2 (G : Type*) [Magma G] (h : Equation33226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33227_implies_Equation2 (G : Type*) [Magma G] (h : Equation33227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33228_implies_Equation2 (G : Type*) [Magma G] (h : Equation33228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33230_implies_Equation2 (G : Type*) [Magma G] (h : Equation33230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33231_implies_Equation2 (G : Type*) [Magma G] (h : Equation33231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33232_implies_Equation2 (G : Type*) [Magma G] (h : Equation33232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33234_implies_Equation2 (G : Type*) [Magma G] (h : Equation33234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33235_implies_Equation2 (G : Type*) [Magma G] (h : Equation33235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33236_implies_Equation2 (G : Type*) [Magma G] (h : Equation33236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation33237_implies_Equation2 (G : Type*) [Magma G] (h : Equation33237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33239_implies_Equation2 (G : Type*) [Magma G] (h : Equation33239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq24 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq124 eq41


@[equational_result]
theorem Equation33240_implies_Equation2 (G : Type*) [Magma G] (h : Equation33240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq55 eq15


@[equational_result]
theorem Equation33241_implies_Equation2 (G : Type*) [Magma G] (h : Equation33241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) ◇ ((X0 ◇ X4) ◇ X5)) ◇ X4) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X3 X4 : G) : ((X1 ◇ (X0 ◇ X4)) ◇ X3) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq10 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation33242_implies_Equation2 (G : Type*) [Magma G] (h : Equation33242 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 X6 X7 : G) : (((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) ◇ ((X0 ◇ X5) ◇ X6)) ◇ X7) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ X7) = X6 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation33244_implies_Equation2 (G : Type*) [Magma G] (h : Equation33244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33245_implies_Equation2 (G : Type*) [Magma G] (h : Equation33245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33246_implies_Equation2 (G : Type*) [Magma G] (h : Equation33246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33247_implies_Equation2 (G : Type*) [Magma G] (h : Equation33247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33249_implies_Equation2 (G : Type*) [Magma G] (h : Equation33249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33250_implies_Equation2 (G : Type*) [Magma G] (h : Equation33250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33251_implies_Equation2 (G : Type*) [Magma G] (h : Equation33251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33252_implies_Equation2 (G : Type*) [Magma G] (h : Equation33252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33254_implies_Equation2 (G : Type*) [Magma G] (h : Equation33254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33255_implies_Equation2 (G : Type*) [Magma G] (h : Equation33255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33256_implies_Equation2 (G : Type*) [Magma G] (h : Equation33256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation33257_implies_Equation2 (G : Type*) [Magma G] (h : Equation33257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33259_implies_Equation2 (G : Type*) [Magma G] (h : Equation33259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33260_implies_Equation2 (G : Type*) [Magma G] (h : Equation33260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33261_implies_Equation2 (G : Type*) [Magma G] (h : Equation33261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33262_implies_Equation2 (G : Type*) [Magma G] (h : Equation33262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation33263_implies_Equation2 (G : Type*) [Magma G] (h : Equation33263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X1 ◇ X2) ◇ X3) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation33265_implies_Equation2 (G : Type*) [Magma G] (h : Equation33265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (((X3 ◇ X0) ◇ X0) ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq9 eq9
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ ((X3 ◇ X0) ◇ X0))) = X2 := superpose eq9 eq9
  have eq32 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := superpose eq9 eq11
  have eq33 (X0 X1 X2 : G) : ((((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2))) = X2 := superpose eq11 eq11
  have eq49 (X0 X1 X2 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ ((X0 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X2))) = X2 := superpose eq32 eq33
  have eq50 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2))) = X2 := superpose eq32 eq49
  have eq53 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ X0))) = X2 := superpose eq9 eq12
  have eq70 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) = X0 := superpose eq9 eq15
  have eq88 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq70 eq50
  have eq91 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ X0) := superpose eq88 eq15
  have eq97 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq88 eq91
  have eq102 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X0))) = X2 := superpose eq97 eq17
  have eq105 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq97 eq53
  have eq115 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq97 eq102
  have eq122 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq115 eq12
  have eq130 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq122 eq105
  have eq138 (X0 X2 : G) : X0 = X2 := superpose eq130 eq130
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq138 eq8
  subsumption eq146 eq138


@[equational_result]
theorem Equation33266_implies_Equation2 (G : Type*) [Magma G] (h : Equation33266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation33267_implies_Equation2 (G : Type*) [Magma G] (h : Equation33267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation33269_implies_Equation2 (G : Type*) [Magma G] (h : Equation33269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X2 := superpose eq7 eq9
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq38 eq20


@[equational_result]
theorem Equation33270_implies_Equation2 (G : Type*) [Magma G] (h : Equation33270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X3) ◇ X1)) ◇ (X2 ◇ (((X3 ◇ X0) ◇ X0) ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X4 ◇ (((X3 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X0) ◇ X2))) ◇ (X2 ◇ (((X3 ◇ X0) ◇ X0) ◇ X2))) ◇ X4))) = X3 := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ X3) = (((X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) ◇ X0) ◇ (X4 ◇ (((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ X3) ◇ X4))) := superpose eq9 eq9
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X3 ◇ X0) ◇ X4)) = ((X1 ◇ (((X2 ◇ (((X0 ◇ X3) ◇ X3) ◇ X2)) ◇ (X4 ◇ ((X3 ◇ X0) ◇ X4))) ◇ X1)) ◇ (X5 ◇ ((X0 ◇ (X2 ◇ (((X0 ◇ X3) ◇ X3) ◇ X2))) ◇ X5))) := superpose eq9 eq9
  have eq20 (X0 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ X3) = (X2 ◇ (X4 ◇ (((((X2 ◇ X0) ◇ X3) ◇ X3) ◇ X3) ◇ X4))) := superpose eq7 eq13
  have eq24 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ (((X0 ◇ X2) ◇ X2) ◇ X3))) = X0 := superpose eq7 eq20
  have eq35 (X0 X1 X3 X4 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X3 ◇ X4))) = X3 := superpose eq24 eq10
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X3 ◇ X0) ◇ X4)) = ((X1 ◇ (((X2 ◇ (((X0 ◇ X3) ◇ X3) ◇ X2)) ◇ (X4 ◇ ((X3 ◇ X0) ◇ X4))) ◇ X1)) ◇ (X5 ◇ (X0 ◇ X5))) := superpose eq24 eq16
  have eq42 (X0 X3 X4 : G) : (X4 ◇ ((X3 ◇ X0) ◇ X4)) = X0 := superpose eq35 eq36
  have eq43 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq42 eq7
  have eq54 (X0 X3 X4 : G) : (X4 ◇ (X3 ◇ X0)) = X0 := superpose eq43 eq42
  have eq59 (X0 X3 X4 : G) : (X4 ◇ X3) = X0 := superpose eq43 eq54
  have eq60 (X0 X3 : G) : X0 = X3 := superpose eq59 eq59
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq65 eq60


@[equational_result]
theorem Equation33271_implies_Equation2 (G : Type*) [Magma G] (h : Equation33271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation33274_implies_Equation2 (G : Type*) [Magma G] (h : Equation33274 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation33275_implies_Equation2 (G : Type*) [Magma G] (h : Equation33275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq63 eq13


@[equational_result]
theorem Equation33277_implies_Equation2 (G : Type*) [Magma G] (h : Equation33277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X5)) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X5 : G) : ((X1 ◇ (X0 ◇ X5)) ◇ X1) = X2 := superpose eq7 eq9
  have eq73 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq189 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq189 eq73


@[equational_result]
theorem Equation33278_implies_Equation2 (G : Type*) [Magma G] (h : Equation33278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq61 eq12


@[equational_result]
theorem Equation33279_implies_Equation2 (G : Type*) [Magma G] (h : Equation33279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation33280_implies_Equation2 (G : Type*) [Magma G] (h : Equation33280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation33282_implies_Equation2 (G : Type*) [Magma G] (h : Equation33282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = X3 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq9 eq9
  have eq52 (X0 X2 : G) : X0 = X2 := superpose eq11 eq14
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq62 eq52


@[equational_result]
theorem Equation33284_implies_Equation2 (G : Type*) [Magma G] (h : Equation33284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation33286_implies_Equation2 (G : Type*) [Magma G] (h : Equation33286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq9
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation33287_implies_Equation2 (G : Type*) [Magma G] (h : Equation33287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) = (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq10 eq10
  have eq20 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X2) ◇ X2) = X0 := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X0) = X1 := superpose eq10 eq7
  have eq22 (X0 X1 X2 : G) : ((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2)) ◇ (X0 ◇ X1)) = X2 := superpose eq10 eq7
  have eq50 (X0 X1 X2 X3 : G) : (((X3 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X2 := superpose eq10 eq20
  have eq56 (X0 X1 X2 : G) : (((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X2 := superpose eq10 eq20
  have eq76 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ X1)) := superpose eq21 eq21
  have eq98 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) := superpose eq76 eq16
  have eq106 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ (X0 ◇ X1)) = X2 := superpose eq98 eq22
  have eq109 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq106 eq56
  have eq111 (X0 X1 X2 X3 : G) : ((X3 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) = X2 := superpose eq109 eq50
  have eq162 (X0 X1 X2 X3 : G) : ((X3 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X3)) ◇ X0) = X2 := superpose eq109 eq111
  have eq163 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq109 eq162
  have eq164 (X0 X3 : G) : X0 = X3 := superpose eq163 eq163
  have eq180 (X0 : G) : sK0 ≠ X0 := superpose eq164 eq8
  subsumption eq180 eq164


@[equational_result]
theorem Equation33288_implies_Equation2 (G : Type*) [Magma G] (h : Equation33288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation33292_implies_Equation2 (G : Type*) [Magma G] (h : Equation33292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq67 eq13


@[equational_result]
theorem Equation33294_implies_Equation2 (G : Type*) [Magma G] (h : Equation33294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X5)) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq77 eq19


@[equational_result]
theorem Equation33295_implies_Equation2 (G : Type*) [Magma G] (h : Equation33295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X4) ◇ X0) ◇ X2) = X3 := superpose eq7 eq7
  have eq57 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq7 eq11
  have eq70 (X0 X4 : G) : X0 = X4 := superpose eq7 eq57
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq175 eq70


@[equational_result]
theorem Equation33296_implies_Equation2 (G : Type*) [Magma G] (h : Equation33296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X5)) ◇ X5) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq77 eq19


@[equational_result]
theorem Equation33297_implies_Equation2 (G : Type*) [Magma G] (h : Equation33297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X1) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation33300_implies_Equation2 (G : Type*) [Magma G] (h : Equation33300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq49 eq13


@[equational_result]
theorem Equation33301_implies_Equation2 (G : Type*) [Magma G] (h : Equation33301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33303_implies_Equation2 (G : Type*) [Magma G] (h : Equation33303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X3) ◇ X2) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ ((X3 ◇ X1) ◇ X3)) ◇ X2) ◇ X4) = ((X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X5) := superpose eq10 eq10
  have eq22 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X1) ◇ X3) = X0 := superpose eq7 eq10
  have eq31 (X0 X1 X5 : G) : ((X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X5) = X1 := superpose eq22 eq20
  have eq108 (X0 X2 : G) : X0 = X2 := superpose eq22 eq31
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq108 eq8
  subsumption eq125 eq108


@[equational_result]
theorem Equation33304_implies_Equation2 (G : Type*) [Magma G] (h : Equation33304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X2) = ((X1 ◇ (X0 ◇ X1)) ◇ X2) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X2 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X2) ◇ X2) = ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X2) := superpose eq10 eq10
  have eq18 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3) ◇ X3) = ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3) := superpose eq10 eq10
  have eq19 (X0 X1 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) ◇ X1) = X0 := superpose eq7 eq10
  have eq20 (X0 X1 X2 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X2) = X1 := superpose eq10 eq7
  have eq58 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X2)) := superpose eq20 eq20
  have eq79 (X0 X1 X2 X3 : G) : (X3 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X1) ◇ X3)) = X0 := superpose eq20 eq58
  have eq84 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = ((X1 ◇ (X2 ◇ (((X3 ◇ X0) ◇ X3) ◇ X2))) ◇ X1) := superpose eq7 eq58
  have eq92 (X0 X1 X2 : G) : (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) ◇ X2) = X1 := superpose eq58 eq19
  have eq95 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3) = X1 := superpose eq58 eq7
  have eq104 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ X1)) ◇ X2)) ◇ (X3 ◇ X1)) = X3 := superpose eq58 eq7
  have eq131 (X0 X1 X2 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X2) = X1 := superpose eq92 eq17
  have eq134 (X1 X2 X3 : G) : (((X3 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X3) ◇ X3) = X1 := superpose eq95 eq18
  have eq138 (X1 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X3 := superpose eq79 eq104
  have eq142 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = X1 := superpose eq138 eq131
  have eq152 (X0 X1 X3 : G) : (X3 ◇ X0) = ((X1 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X1) := superpose eq138 eq84
  have eq219 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = X1 := superpose eq152 eq134
  have eq222 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq219 eq142
  have eq231 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq222 eq219
  have eq232 (X0 X3 : G) : X0 = X3 := superpose eq231 eq231
  have eq237 (X0 : G) : sK0 ≠ X0 := superpose eq232 eq8
  subsumption eq237 eq232


@[equational_result]
theorem Equation33305_implies_Equation2 (G : Type*) [Magma G] (h : Equation33305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq62 eq12


@[equational_result]
theorem Equation33307_implies_Equation2 (G : Type*) [Magma G] (h : Equation33307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X3 ◇ X0) ◇ X3) ◇ X3) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (((X3 ◇ X0) ◇ X3) ◇ X3))) = X2 := superpose eq7 eq7
  have eq49 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ X1) ◇ X1) = (X0 ◇ X3) := superpose eq11 eq10
  have eq53 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq7 eq49
  have eq57 (X0 X1 X4 : G) : (X1 ◇ X4) = X0 := superpose eq11 eq53
  have eq154 (X0 X3 : G) : X0 = X3 := superpose eq7 eq57
  have eq311 (X0 : G) : sK0 ≠ X0 := superpose eq154 eq8
  subsumption eq311 eq154


@[equational_result]
theorem Equation33308_implies_Equation2 (G : Type*) [Magma G] (h : Equation33308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation33309_implies_Equation2 (G : Type*) [Magma G] (h : Equation33309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33311_implies_Equation2 (G : Type*) [Magma G] (h : Equation33311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X1) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq73 eq16


@[equational_result]
theorem Equation33312_implies_Equation2 (G : Type*) [Magma G] (h : Equation33312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation33313_implies_Equation2 (G : Type*) [Magma G] (h : Equation33313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33314_implies_Equation2 (G : Type*) [Magma G] (h : Equation33314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X2) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33316_implies_Equation2 (G : Type*) [Magma G] (h : Equation33316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ ((X0 ◇ X5) ◇ X2)) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq9
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq116 eq47


@[equational_result]
theorem Equation33317_implies_Equation2 (G : Type*) [Magma G] (h : Equation33317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X0)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33318_implies_Equation2 (G : Type*) [Magma G] (h : Equation33318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X0)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation33319_implies_Equation2 (G : Type*) [Magma G] (h : Equation33319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X0)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33321_implies_Equation2 (G : Type*) [Magma G] (h : Equation33321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X1)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ ((X0 ◇ X5) ◇ X1)) ◇ X1) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation33322_implies_Equation2 (G : Type*) [Magma G] (h : Equation33322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X1)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq71 eq15


@[equational_result]
theorem Equation33323_implies_Equation2 (G : Type*) [Magma G] (h : Equation33323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X1)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((X1 ◇ ((X0 ◇ X5) ◇ X1)) ◇ X5) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq9
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq77 eq19


@[equational_result]
theorem Equation33324_implies_Equation2 (G : Type*) [Magma G] (h : Equation33324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X1)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33326_implies_Equation2 (G : Type*) [Magma G] (h : Equation33326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X2)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X0 ◇ X5) ◇ (X2 ◇ (((X3 ◇ X0) ◇ X4) ◇ X3)))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X0) ◇ X4) ◇ X3) = ((X1 ◇ (X0 ◇ X2)) ◇ X1) := superpose eq7 eq7
  have eq58 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X5 := superpose eq10 eq9
  have eq88 (X0 X5 : G) : X0 = X5 := superpose eq58 eq58
  have eq181 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq181 eq88


@[equational_result]
theorem Equation33327_implies_Equation2 (G : Type*) [Magma G] (h : Equation33327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X2)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33328_implies_Equation2 (G : Type*) [Magma G] (h : Equation33328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X2)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq61 eq13


@[equational_result]
theorem Equation33329_implies_Equation2 (G : Type*) [Magma G] (h : Equation33329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X2)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33331_implies_Equation2 (G : Type*) [Magma G] (h : Equation33331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation33332_implies_Equation2 (G : Type*) [Magma G] (h : Equation33332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq65 eq12


@[equational_result]
theorem Equation33333_implies_Equation2 (G : Type*) [Magma G] (h : Equation33333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq54 eq12


@[equational_result]
theorem Equation33334_implies_Equation2 (G : Type*) [Magma G] (h : Equation33334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33336_implies_Equation2 (G : Type*) [Magma G] (h : Equation33336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation33337_implies_Equation2 (G : Type*) [Magma G] (h : Equation33337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33338_implies_Equation2 (G : Type*) [Magma G] (h : Equation33338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq58 eq13


@[equational_result]
theorem Equation33339_implies_Equation2 (G : Type*) [Magma G] (h : Equation33339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X7 : G) : (X0 ◇ X7) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33340_implies_Equation2 (G : Type*) [Magma G] (h : Equation33340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X4)) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X6 X9 : G) : (X0 ◇ X9) = X6 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq48 eq13


@[equational_result]
theorem Equation33342_implies_Equation2 (G : Type*) [Magma G] (h : Equation33342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (((X2 ◇ X1) ◇ X0) ◇ X0)) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((X1 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X1) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X2 := superpose eq7 eq9
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq7 eq11
  have eq117 (X0 X3 : G) : X0 = X3 := superpose eq7 eq33
  have eq216 (X0 : G) : sK0 ≠ X0 := superpose eq117 eq8
  subsumption eq216 eq117


