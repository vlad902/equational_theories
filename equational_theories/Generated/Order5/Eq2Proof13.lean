import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation27486_implies_Equation2 (G : Type*) [Magma G] (h : Equation27486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27487_implies_Equation2 (G : Type*) [Magma G] (h : Equation27487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27488_implies_Equation2 (G : Type*) [Magma G] (h : Equation27488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27489_implies_Equation2 (G : Type*) [Magma G] (h : Equation27489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27491_implies_Equation2 (G : Type*) [Magma G] (h : Equation27491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X5 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27492_implies_Equation2 (G : Type*) [Magma G] (h : Equation27492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X5 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27493_implies_Equation2 (G : Type*) [Magma G] (h : Equation27493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X5 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27494_implies_Equation2 (G : Type*) [Magma G] (h : Equation27494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X5 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27495_implies_Equation2 (G : Type*) [Magma G] (h : Equation27495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X5 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27496_implies_Equation2 (G : Type*) [Magma G] (h : Equation27496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X5 ◇ X6)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27705_implies_Equation2 (G : Type*) [Magma G] (h : Equation27705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X2 ◇ X2)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 : G) : (X0 ◇ (((X2 ◇ (((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X0 ◇ X0)) ◇ X0) ◇ ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X0 ◇ X0)) ◇ X0))) ◇ ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X0 ◇ X0)) ◇ X0)) ◇ X3)) = X2 := superpose eq11 eq9
  have eq37 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq17
  have eq44 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X1) := superpose eq17 eq11
  have eq51 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X0 ◇ X0)) ◇ X0) ◇ X2))) = X2 := superpose eq37 eq34
  have eq54 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq51
  have eq55 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2) = X1 := superpose eq54 eq37
  have eq70 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := superpose eq55 eq44
  have eq71 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq70 eq7
  have eq94 (X0 X1 : G) : X0 = X1 := superpose eq71 eq54
  have eq116 (X0 : G) : sK0 ≠ X0 := superpose eq94 eq8
  subsumption eq116 eq94


@[equational_result]
theorem Equation27707_implies_Equation2 (G : Type*) [Magma G] (h : Equation27707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq7 eq12
  have eq33 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq17 eq17
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq17 eq33
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq41 eq34


@[equational_result]
theorem Equation27708_implies_Equation2 (G : Type*) [Magma G] (h : Equation27708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X3)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9
  have eq20 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq13
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq9 eq20
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation27709_implies_Equation2 (G : Type*) [Magma G] (h : Equation27709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq45 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq16 eq16
  have eq95 (X0 X4 : G) : X0 = X4 := superpose eq10 eq45
  have eq185 (X0 : G) : sK0 ≠ X0 := superpose eq95 eq8
  subsumption eq185 eq95


@[equational_result]
theorem Equation27712_implies_Equation2 (G : Type*) [Magma G] (h : Equation27712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ X2) = (((X1 ◇ (((X2 ◇ (X0 ◇ X0)) ◇ X2) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2))) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = ((((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq15 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) ◇ X0) := superpose eq10 eq7
  have eq18 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose eq10 eq17
  have eq53 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X1) ◇ X0) := superpose eq10 eq11
  have eq66 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose eq15 eq53
  have eq67 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq18 eq66
  have eq81 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq10 eq67
  have eq83 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq67 eq7
  have eq90 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq81 eq83
  have eq91 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq90 eq67
  have eq92 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) := superpose eq91 eq13
  have eq102 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := superpose eq91 eq18
  have eq108 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose eq91 eq92
  have eq112 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq102 eq108
  have eq135 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq90 eq112
  have eq136 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq91 eq135
  have eq138 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq136 eq112
  have eq141 (X0 X2 : G) : X0 = X2 := superpose eq138 eq138
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq141 eq8
  subsumption eq146 eq141


@[equational_result]
theorem Equation27715_implies_Equation2 (G : Type*) [Magma G] (h : Equation27715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq89 eq25


@[equational_result]
theorem Equation27717_implies_Equation2 (G : Type*) [Magma G] (h : Equation27717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq11
  have eq18 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq14 eq12
  have eq24 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq14 eq18
  have eq25 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq14 eq24
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation27718_implies_Equation2 (G : Type*) [Magma G] (h : Equation27718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X3 ◇ X3)) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ X3)) = X2 := superpose eq10 eq9
  have eq13 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X2 := superpose eq10 eq11
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation27719_implies_Equation2 (G : Type*) [Magma G] (h : Equation27719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X1 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27721_implies_Equation2 (G : Type*) [Magma G] (h : Equation27721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq10
  have eq15 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq10 eq10
  have eq49 (X0 X1 : G) : X0 = X1 := superpose eq12 eq15
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq55 eq49


@[equational_result]
theorem Equation27722_implies_Equation2 (G : Type*) [Magma G] (h : Equation27722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X2)))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ X1) := superpose eq9 eq9
  have eq21 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X2 := superpose eq14 eq10
  have eq33 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq21 eq9
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq9 eq33
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq101 eq48


@[equational_result]
theorem Equation27723_implies_Equation2 (G : Type*) [Magma G] (h : Equation27723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq10 eq15
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq53 eq21


@[equational_result]
theorem Equation27725_implies_Equation2 (G : Type*) [Magma G] (h : Equation27725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation27726_implies_Equation2 (G : Type*) [Magma G] (h : Equation27726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X2)) ◇ X0) = X3 := superpose eq9 eq7
  have eq33 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq17 eq21
  have eq34 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq17 eq33
  have eq37 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq34 eq11
  have eq48 (X0 X1 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ (X3 ◇ X3)) ◇ X0) = X3 := superpose eq34 eq37
  have eq49 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X3 := superpose eq34 eq48
  have eq50 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq34 eq49
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq50 eq50
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq53 eq51


@[equational_result]
theorem Equation27727_implies_Equation2 (G : Type*) [Magma G] (h : Equation27727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X4)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq54 eq19


@[equational_result]
theorem Equation27730_implies_Equation2 (G : Type*) [Magma G] (h : Equation27730 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ (X3 ◇ X3)) = X2 := superpose eq7 eq7
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation27731_implies_Equation2 (G : Type*) [Magma G] (h : Equation27731 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation27733_implies_Equation2 (G : Type*) [Magma G] (h : Equation27733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ (X0 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq56 eq21


@[equational_result]
theorem Equation27734_implies_Equation2 (G : Type*) [Magma G] (h : Equation27734 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation27735_implies_Equation2 (G : Type*) [Magma G] (h : Equation27735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation27736_implies_Equation2 (G : Type*) [Magma G] (h : Equation27736 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation27742_implies_Equation2 (G : Type*) [Magma G] (h : Equation27742 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2)) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ X2) ◇ X0) = X2 := superpose eq10 eq7
  have eq37 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq16 eq16
  have eq62 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X2 := superpose eq37 eq19
  have eq132 (X0 X1 : G) : X0 = X1 := superpose eq62 eq37
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq132 eq8
  subsumption eq163 eq132


@[equational_result]
theorem Equation27744_implies_Equation2 (G : Type*) [Magma G] (h : Equation27744 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq10 eq10
  have eq25 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq15 eq25
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq43 eq26


@[equational_result]
theorem Equation27746_implies_Equation2 (G : Type*) [Magma G] (h : Equation27746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X2 := superpose eq15 eq11
  have eq25 (X0 X1 : G) : X0 = X1 := superpose eq10 eq21
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq29 eq25


@[equational_result]
theorem Equation27749_implies_Equation2 (G : Type*) [Magma G] (h : Equation27749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ X2) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ X2) = (((X1 ◇ (((X2 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1)) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = (((X3 ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)) := superpose eq7 eq11
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = ((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq11
  have eq52 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) = (((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) ◇ ((X2 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) ◇ X2)) ◇ X2)) ◇ X0) := superpose eq14 eq10
  have eq121 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = ((((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq26
  have eq125 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2))) = ((((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq9 eq26
  have eq133 (X0 X1 X2 X3 : G) : ((X2 ◇ ((((X1 ◇ X3) ◇ X1) ◇ (X1 ◇ X3)) ◇ X2)) ◇ X2) = (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ X3) ◇ X1) ◇ (X1 ◇ X3))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (((X1 ◇ X3) ◇ X1) ◇ (X1 ◇ X3))) := superpose eq9 eq26
  have eq135 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2)) ◇ X2) = (((((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X3 ◇ (X0 ◇ X3))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq26 eq26
  have eq137 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ X0) := superpose eq7 eq26
  have eq146 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ X2) = ((((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X3 ◇ (X0 ◇ X3))) ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X2) ◇ X4)) := superpose eq26 eq9
  have eq152 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (((X2 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X3)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq26 eq10
  have eq175 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2))) := superpose eq10 eq137
  have eq180 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq137 eq137
  have eq234 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq175
  have eq239 (X0 X2 X3 : G) : (((X3 ◇ (X0 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X2)) = X0 := superpose eq234 eq21
  have eq279 (X0 X1 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = (X0 ◇ X0) := superpose eq234 eq121
  have eq283 (X0 X1 X3 : G) : ((((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) := superpose eq234 eq125
  have eq286 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ X2) = (((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X1) := superpose eq234 eq133
  have eq287 (X0 X2 X3 : G) : ((X2 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X2)) ◇ X2) = ((((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X3))) ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq234 eq135
  have eq294 (X0 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ X2) = (((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X3))) ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X2) ◇ X4)) := superpose eq234 eq146
  have eq300 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X2)) = (((X2 ◇ (X0 ◇ X2)) ◇ ((X3 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X3)) ◇ (X0 ◇ X0)) := superpose eq234 eq152
  have eq339 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) = (((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)))) ◇ X0) := superpose eq279 eq52
  have eq344 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq279 eq10
  have eq345 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := superpose eq279 eq14
  have eq391 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq279 eq339
  have eq399 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq345 eq391
  have eq508 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) := superpose eq234 eq283
  have eq509 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) = X1 := superpose eq239 eq508
  have eq530 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X1) := superpose eq509 eq286
  have eq531 (X1 X2 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ X2) = ((X1 ◇ X1) ◇ X1) := superpose eq279 eq530
  have eq540 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (((X2 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X2))) ◇ (X0 ◇ X0)) := superpose eq279 eq300
  have eq573 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (((X2 ◇ (X0 ◇ X0)) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq180 eq540
  have eq665 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq344 eq399
  have eq673 (X1 X2 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ X2) = X1 := superpose eq665 eq531
  have eq675 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq673 eq7
  have eq681 (X0 X3 X4 : G) : (((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X3))) ◇ (X3 ◇ X4)) = X3 := superpose eq673 eq294
  have eq690 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X3))) ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq673 eq287
  have eq693 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq675 eq399
  have eq694 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := superpose eq693 eq180
  have eq702 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (((X2 ◇ X0) ◇ X2) ◇ X0) := superpose eq693 eq573
  have eq704 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := superpose eq693 eq694
  have eq710 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X2 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq704 eq702
  have eq713 (X0 X3 X4 : G) : ((X0 ◇ (X3 ◇ (X0 ◇ X3))) ◇ (X3 ◇ X4)) = X3 := superpose eq693 eq681
  have eq724 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = (((X0 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X0))) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq704 eq690
  have eq725 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X0 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X0)) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq693 eq724
  have eq726 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X0 ◇ (X3 ◇ (X0 ◇ X3))) ◇ (X3 ◇ (X0 ◇ X3))) := superpose eq710 eq725
  have eq727 (X0 X3 : G) : (X3 ◇ (X0 ◇ X3)) = X3 := superpose eq713 eq726
  have eq728 (X1 X2 : G) : (X2 ◇ X2) = X1 := superpose eq727 eq673
  have eq744 (X0 X2 : G) : X0 = X2 := superpose eq728 eq728
  have eq752 (X0 : G) : sK0 ≠ X0 := superpose eq744 eq8
  subsumption eq752 eq744


@[equational_result]
theorem Equation27752_implies_Equation2 (G : Type*) [Magma G] (h : Equation27752 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = ((X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X2)) := superpose eq7 eq10
  have eq16 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X0) = X1 := superpose eq7 eq10
  have eq19 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = ((((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2)) ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) ◇ X3)) := superpose eq10 eq7
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) ◇ X1)) ◇ X1) = ((X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X3)) := superpose eq10 eq9
  have eq32 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X1) = X0 := superpose eq7 eq9
  have eq39 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) = (((((X0 ◇ X2) ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X3)) ◇ (((X0 ◇ X2) ◇ X3) ◇ X4)) := superpose eq9 eq7
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) ◇ X1)) ◇ X1) := superpose eq14 eq22
  have eq145 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ X3)) = X1 := superpose eq32 eq10
  have eq158 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) := superpose eq145 eq39
  have eq160 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) ◇ X3)) := superpose eq158 eq19
  have eq202 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = (X1 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) ◇ X3)) := superpose eq7 eq160
  have eq203 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X1) := superpose eq202 eq41
  have eq204 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq16 eq203
  have eq205 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq204 eq7
  have eq208 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq204 eq16
  have eq234 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq208 eq158
  have eq238 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq234 eq204
  have eq243 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq238 eq205
  have eq249 (X0 X3 : G) : X0 = X3 := superpose eq243 eq243
  have eq251 (X0 : G) : sK0 ≠ X0 := superpose eq249 eq8
  subsumption eq251 eq249


@[equational_result]
theorem Equation27754_implies_Equation2 (G : Type*) [Magma G] (h : Equation27754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : (((X0 ◇ (X3 ◇ X0)) ◇ X0) ◇ X4) = X3 := superpose eq7 eq10
  have eq23 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) = (((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) ◇ (X2 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq9 eq9
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X1) = X0 := superpose eq10 eq9
  have eq39 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq14 eq23
  have eq58 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X2)) = X3 := superpose eq7 eq30
  have eq84 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq58 eq39
  have eq86 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) = X0 := superpose eq84 eq7
  have eq103 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = X0 := superpose eq84 eq86
  have eq104 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq84 eq103
  have eq105 (X0 X3 : G) : X0 = X3 := superpose eq104 eq104
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq105 eq8
  subsumption eq107 eq105


@[equational_result]
theorem Equation27756_implies_Equation2 (G : Type*) [Magma G] (h : Equation27756 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq37 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq56 eq37


@[equational_result]
theorem Equation27758_implies_Equation2 (G : Type*) [Magma G] (h : Equation27758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq9
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X2 := superpose eq9 eq7
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq7
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq16
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq22 eq34
  have eq88 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq88 eq39


@[equational_result]
theorem Equation27760_implies_Equation2 (G : Type*) [Magma G] (h : Equation27760 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq55 eq23


@[equational_result]
theorem Equation27762_implies_Equation2 (G : Type*) [Magma G] (h : Equation27762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq61 eq16


@[equational_result]
theorem Equation27764_implies_Equation2 (G : Type*) [Magma G] (h : Equation27764 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X4)) = X2 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq63 eq22


@[equational_result]
theorem Equation27768_implies_Equation2 (G : Type*) [Magma G] (h : Equation27768 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation27770_implies_Equation2 (G : Type*) [Magma G] (h : Equation27770 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation27771_implies_Equation2 (G : Type*) [Magma G] (h : Equation27771 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X3 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X4)) ◇ X0) = X2 := superpose eq7 eq7
  have eq36 (X0 X6 : G) : X0 = X6 := superpose eq11 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq44 eq36


@[equational_result]
theorem Equation27772_implies_Equation2 (G : Type*) [Magma G] (h : Equation27772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27773_implies_Equation2 (G : Type*) [Magma G] (h : Equation27773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation27779_implies_Equation2 (G : Type*) [Magma G] (h : Equation27779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X0) = (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (X0 ◇ ((((X1 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ (((X1 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)))) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (((X2 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq10 eq10
  have eq20 (X0 X1 X2 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq10 eq7
  have eq33 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq9 eq7
  have eq43 (X0 X1 X3 : G) : (((X3 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X3 ◇ X3)) = X0 := superpose eq7 eq20
  have eq82 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X3 := superpose eq10 eq43
  have eq89 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq10 eq43
  have eq108 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)))) := superpose eq89 eq12
  have eq151 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2)) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2))) = ((X0 ◇ X0) ◇ ((X3 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X3 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq11 eq82
  have eq158 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq82
  have eq187 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq158 eq33
  have eq188 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X2))) = X1 := superpose eq187 eq10
  have eq195 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq187 eq108
  have eq205 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X0)) = X2 := superpose eq187 eq15
  have eq215 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ ((X3 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X3 ◇ ((X0 ◇ X0) ◇ X1)))) = X0 := superpose eq187 eq151
  have eq232 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X1) = X3 := superpose eq187 eq82
  have eq239 (X0 X3 : G) : ((X0 ◇ X0) ◇ X3) = X0 := superpose eq187 eq215
  have eq244 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq239 eq195
  have eq258 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq232 eq205
  have eq266 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq244 eq244
  have eq280 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq188 eq266
  have eq285 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq258 eq266
  have eq312 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq285 eq280
  have eq327 (X0 X3 : G) : X0 = X3 := superpose eq312 eq312
  have eq370 (X0 : G) : sK0 ≠ X0 := superpose eq327 eq8
  subsumption eq370 eq327


@[equational_result]
theorem Equation27780_implies_Equation2 (G : Type*) [Magma G] (h : Equation27780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X0) = (((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X0)) ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (((X2 ◇ X0) ◇ (X1 ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X3)) ◇ X1) ◇ X3))) = X2 := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq10
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2)) := superpose eq10 eq10
  have eq21 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ (((X0 ◇ (X1 ◇ X3)) ◇ X1) ◇ X3))) ◇ X2) ◇ X0) = X2 := superpose eq10 eq7
  have eq32 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X0) ◇ (X2 ◇ (((X0 ◇ (X1 ◇ X3)) ◇ X1) ◇ X3))) ◇ X2) ◇ (X4 ◇ X0)) ◇ X4) ◇ X2) = X4 := superpose eq10 eq12
  have eq34 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X0) = (((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X0)) ◇ X2) := superpose eq7 eq12
  have eq40 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) = ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2))) ◇ X0) := superpose eq12 eq10
  have eq50 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ ((((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X0 ◇ (X1 ◇ X3))) ◇ X0) ◇ ((X0 ◇ X4) ◇ X2)) ◇ X4)) = X0 := superpose eq12 eq11
  have eq52 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2))) := superpose eq10 eq11
  have eq55 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq11
  have eq87 (X0 X1 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1))) := superpose eq10 eq9
  have eq101 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) := superpose eq9 eq10
  have eq103 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (((X3 ◇ X1) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) ◇ (X3 ◇ (X0 ◇ X2)))) := superpose eq9 eq11
  have eq122 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq55 eq10
  have eq123 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq55 eq11
  have eq128 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq55 eq10
  have eq168 (X0 X1 : G) : (X1 ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq10 eq21
  have eq178 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = (X0 ◇ (((X3 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ (X0 ◇ (((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X3 ◇ X4)) ◇ X3) ◇ X4))) ◇ (X1 ◇ X2))) := superpose eq21 eq9
  have eq231 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq7 eq52
  have eq236 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq55 eq52
  have eq241 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0))) := superpose eq9 eq52
  have eq245 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2))) = (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)))) ◇ X0)) := superpose eq12 eq52
  have eq268 (X0 X1 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq9 eq168
  have eq271 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq7 eq168
  have eq277 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X2) = X0 := superpose eq12 eq168
  have eq287 (X0 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq168 eq7
  have eq315 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq277 eq287
  have eq316 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := superpose eq315 eq55
  have eq319 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq315 eq122
  have eq320 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0)) := superpose eq315 eq123
  have eq361 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq316 eq241
  have eq364 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq316 eq101
  have eq375 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) := superpose eq316 eq168
  have eq404 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq375 eq320
  have eq405 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := superpose eq404 eq375
  have eq406 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq316 eq405
  have eq409 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq406 eq128
  have eq411 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq406 eq236
  have eq426 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq406 eq404
  have eq430 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq426 eq411
  have eq431 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq409 eq430
  have eq432 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq426 eq431
  have eq467 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq315 eq168
  have eq468 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq315 eq11
  have eq493 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq467 eq468
  have eq494 (X0 X1 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) = ((((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq493 eq268
  have eq496 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq493 eq319
  have eq515 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq9 eq494
  have eq516 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2))) = (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2))) ◇ X0)) := superpose eq515 eq245
  have eq517 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2))) = (((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2))) := superpose eq40 eq516
  have eq518 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) = (X0 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2))) := superpose eq515 eq517
  have eq530 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq496 eq361
  have eq531 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq406 eq530
  have eq532 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq426 eq531
  have eq533 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq432 eq532
  have eq536 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq533 eq364
  have eq539 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq536 eq426
  have eq551 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq539 eq406
  have eq574 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq315 eq551
  have eq578 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq574 eq231
  have eq579 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X2)))) := superpose eq574 eq103
  have eq653 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq17 eq578
  have eq654 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq574 eq653
  have eq656 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X2)) := superpose eq654 eq18
  have eq662 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq9 eq579
  have eq663 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = ((X3 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq574 eq662
  have eq668 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X0) = (((X1 ◇ (X0 ◇ X3)) ◇ X0) ◇ X2) := superpose eq663 eq34
  have eq716 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1))) := superpose eq668 eq87
  have eq720 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (((X2 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X1))) = X2 := superpose eq668 eq16
  have eq724 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X1))) ◇ X2) ◇ (X4 ◇ X0)) ◇ X4) ◇ X2) = X4 := superpose eq668 eq32
  have eq744 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq668 eq656
  have eq767 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = (X0 ◇ (((X3 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ (X0 ◇ ((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X3 ◇ X4)) ◇ X3))) ◇ (X1 ◇ X2))) := superpose eq668 eq178
  have eq775 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X0) ◇ ((X0 ◇ X4) ◇ X2)) ◇ X4)) = X0 := superpose eq668 eq50
  have eq799 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X1))) ◇ X2) ◇ X4) ◇ X2) = X4 := superpose eq668 eq724
  have eq800 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ X1))) ◇ X2) ◇ X2) = X4 := superpose eq668 eq799
  have eq820 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq668 eq744
  have eq821 (X0 X1 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := superpose eq820 eq515
  have eq822 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X0 ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq821 eq518
  have eq833 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1))) := superpose eq822 eq716
  have eq840 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq277 eq833
  have eq841 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq822 eq840
  have eq894 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = (X0 ◇ (((X3 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ (X0 ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X3))) ◇ (X1 ◇ X2))) := superpose eq668 eq767
  have eq895 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = (X0 ◇ (((X3 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) ◇ (X1 ◇ X2))) := superpose eq668 eq894
  have eq901 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X4) ◇ X2)) ◇ X4)) = X0 := superpose eq668 eq775
  have eq902 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X4)) = X0 := superpose eq668 eq901
  have eq903 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X2)) = X0 := superpose eq668 eq902
  have eq905 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ X0)) = X2 := superpose eq903 eq720
  have eq922 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq905 eq841
  have eq923 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq922 eq271
  have eq941 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = (X0 ◇ ((X3 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)))) := superpose eq923 eq895
  have eq959 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ X2) = X4 := superpose eq923 eq800
  have eq989 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq923 eq941
  have eq990 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq923 eq989
  have eq1037 (X2 X4 : G) : (X2 ◇ X2) = X4 := superpose eq990 eq959
  have eq1047 (X0 X2 : G) : X0 = X2 := superpose eq1037 eq1037
  have eq1054 (X0 : G) : sK0 ≠ X0 := superpose eq1047 eq8
  subsumption eq1054 eq1047


@[equational_result]
theorem Equation27781_implies_Equation2 (G : Type*) [Magma G] (h : Equation27781 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ X4)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X3 ◇ X4)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq20 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq10
  have eq40 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ ((((X2 ◇ (X0 ◇ X3)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X4)) ◇ X5)) = X0 := superpose eq12 eq7
  have eq43 (X0 X1 X2 X3 X4 X5 X6 : G) : (X0 ◇ (((X2 ◇ (((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X0 ◇ X4)) ◇ X0) ◇ X5)) ◇ ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X0 ◇ X4)) ◇ X0)) ◇ X6)) = X2 := superpose eq12 eq10
  have eq46 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X2 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) ◇ (X0 ◇ X5)) ◇ X0) = ((X1 ◇ ((((X2 ◇ ((X1 ◇ X3) ◇ X4)) ◇ (X1 ◇ X3)) ◇ (X0 ◇ X5)) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X6)) := superpose eq12 eq10
  have eq49 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) = (X0 ◇ (X1 ◇ X0)) := superpose eq10 eq20
  have eq61 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X1 ◇ X0)) ◇ X3)) = X1 := superpose eq20 eq10
  have eq64 (X0 X1 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X3 ◇ X4)) ◇ X3) ◇ X1) = X3 := superpose eq20 eq12
  have eq67 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X2 ◇ (((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X0 ◇ X4)) ◇ X0) ◇ X2))) = X2 := superpose eq49 eq43
  have eq69 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq12 eq67
  have eq70 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) = X1 := superpose eq69 eq49
  have eq79 (X0 X1 X3 X6 : G) : ((X1 ◇ X3) ◇ X0) = ((X1 ◇ ((X1 ◇ X3) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X6)) := superpose eq70 eq46
  have eq80 (X0 X1 X5 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X5)) = X0 := superpose eq70 eq40
  have eq99 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X3)) = X1 := superpose eq80 eq61
  have eq104 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X1 ◇ X3) ◇ X0) := superpose eq99 eq79
  have eq117 (X0 X1 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X1) = X3 := superpose eq104 eq64
  have eq118 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq99 eq117
  have eq123 (X0 X2 : G) : X0 = X2 := superpose eq20 eq118
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq123 eq8
  subsumption eq147 eq123


@[equational_result]
theorem Equation27784_implies_Equation2 (G : Type*) [Magma G] (h : Equation27784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X2)) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq7 eq10
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X2) ◇ X0) = X2 := superpose eq10 eq7
  have eq19 (X0 X2 : G) : (X0 ◇ X2) = (X2 ◇ X2) := superpose eq10 eq13
  have eq24 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X2 := superpose eq19 eq18
  have eq73 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq19 eq24
  have eq125 (X0 X1 : G) : X0 = X1 := superpose eq10 eq73
  have eq187 (X0 : G) : sK0 ≠ X0 := superpose eq125 eq8
  subsumption eq187 eq125


@[equational_result]
theorem Equation27785_implies_Equation2 (G : Type*) [Magma G] (h : Equation27785 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq24 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X3)) = X0 := superpose eq16 eq7
  have eq30 (X0 X1 : G) : X0 = X1 := superpose eq10 eq24
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq34 eq30


@[equational_result]
theorem Equation27787_implies_Equation2 (G : Type*) [Magma G] (h : Equation27787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 X6 : G) : (((X0 ◇ (X4 ◇ X5)) ◇ X4) ◇ X6) = X4 := superpose eq7 eq12
  have eq17 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq12
  have eq26 (X4 X5 X6 : G) : ((X4 ◇ X5) ◇ X6) = X4 := superpose eq17 eq13
  have eq56 (X0 X1 : G) : X0 = X1 := superpose eq17 eq26
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq59 eq56


@[equational_result]
theorem Equation27788_implies_Equation2 (G : Type*) [Magma G] (h : Equation27788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X2)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq23 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X2)) = X0 := superpose eq16 eq7
  have eq30 (X0 X1 : G) : X0 = X1 := superpose eq10 eq23
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq34 eq30


@[equational_result]
theorem Equation27789_implies_Equation2 (G : Type*) [Magma G] (h : Equation27789 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq20 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X3)) = X0 := superpose eq14 eq7
  have eq26 (X0 X1 : G) : X0 = X1 := superpose eq10 eq20
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq30 eq26


@[equational_result]
theorem Equation27790_implies_Equation2 (G : Type*) [Magma G] (h : Equation27790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : ((X0 ◇ X3) ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq22 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = X2 := superpose eq16 eq12
  have eq27 (X0 X1 : G) : X0 = X1 := superpose eq10 eq22
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq31 eq27


@[equational_result]
theorem Equation27792_implies_Equation2 (G : Type*) [Magma G] (h : Equation27792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X2) = (((X1 ◇ X0) ◇ X1) ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = ((((X0 ◇ X1) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X3)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)))) = X0 := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1))))) = X0 := superpose eq10 eq10
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2)) = (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2)) ◇ X1)) := superpose eq10 eq7
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X1) = (((X4 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2)) ◇ X4) ◇ (((X1 ◇ X0) ◇ X1) ◇ X4)) := superpose eq7 eq9
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq9
  have eq48 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = ((X0 ◇ (X1 ◇ X3)) ◇ X0) := superpose eq28 eq28
  have eq51 (X0 X1 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq28 eq7
  have eq61 (X0 X1 X2 X3 : G) : ((((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) = X1 := superpose eq28 eq7
  have eq62 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X0)) = ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0)) := superpose eq28 eq9
  have eq79 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)) ◇ X2) = (((((X1 ◇ (X0 ◇ X3)) ◇ X2) ◇ (((X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)) ◇ X2) ◇ X4)) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X2)) ◇ (X1 ◇ (X0 ◇ X3))) := superpose eq28 eq11
  have eq117 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X4)) ◇ X1) := superpose eq7 eq48
  have eq122 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)) ◇ X2) = ((X2 ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X4)) ◇ X2) := superpose eq28 eq48
  have eq126 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)) = ((((X3 ◇ X1) ◇ X3) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X4)) ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq9 eq48
  have eq128 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X4)) ◇ (X0 ◇ X5)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X4))) = ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X4))) := superpose eq48 eq48
  have eq130 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X4)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) := superpose eq28 eq48
  have eq163 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X4)) ◇ X2) = (((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq48 eq28
  have eq165 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) = (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq48 eq9
  have eq171 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3) = (((((X0 ◇ (X1 ◇ X4)) ◇ X3) ◇ (((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3) ◇ X5)) ◇ ((X0 ◇ (X1 ◇ X4)) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X4))) := superpose eq48 eq11
  have eq176 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X4)))) ◇ (X0 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X4))))) = X0 := superpose eq48 eq10
  have eq213 (X0 X1 X2 X3 : G) : ((X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)) ◇ X2) = (((((X1 ◇ (X0 ◇ X3)) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X2)) ◇ (X1 ◇ (X0 ◇ X3))) := superpose eq117 eq79
  have eq242 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3) = (((((X0 ◇ (X1 ◇ X4)) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X4)) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X4))) := superpose eq117 eq171
  have eq289 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq48 eq51
  have eq372 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((((X0 ◇ X1) ◇ X2) ◇ ((X4 ◇ (X2 ◇ X5)) ◇ X4)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq48 eq22
  have eq411 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2)))) ◇ X1) = ((X1 ◇ (((X4 ◇ X0) ◇ X4) ◇ X5)) ◇ X1) := superpose eq14 eq117
  have eq412 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X4))) ◇ X3) = ((X3 ◇ (((X5 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X5) ◇ X6)) ◇ X3) := superpose eq48 eq117
  have eq433 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ X4) = ((X4 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0)) ◇ X4) := superpose eq9 eq117
  have eq439 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)) = ((((X3 ◇ X1) ◇ X3) ◇ X1) ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq9 eq117
  have eq444 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X4)) ◇ X3))) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X4)) ◇ X3)))) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X4)) ◇ X3)))) := superpose eq14 eq117
  have eq471 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ X4)) = (((X0 ◇ ((X0 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ X4)) ◇ X5)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq117 eq7
  have eq515 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)))) = (((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3))) ◇ X1) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)))) := superpose eq117 eq444
  have eq537 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X2 ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X3)) ◇ X2) ◇ ((X5 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X5)) = (((X6 ◇ ((X2 ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X3)) ◇ X2)) ◇ X6) ◇ ((((X2 ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X3)) ◇ X2) ◇ ((X5 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X5)) ◇ X6)) := superpose eq22 eq18
  have eq565 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) ◇ X0)) := superpose eq48 eq18
  have eq593 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ ((X4 ◇ X0) ◇ X4)) ◇ X3) = ((X3 ◇ (((X5 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1))) ◇ X5) ◇ X6)) ◇ X3) := superpose eq18 eq117
  have eq598 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X2 ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X3)) ◇ X2) ◇ ((X5 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X5)) = (((X6 ◇ X3) ◇ X6) ◇ ((((X2 ◇ ((X3 ◇ (X1 ◇ X4)) ◇ X3)) ◇ X2) ◇ ((X5 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X5)) ◇ X6)) := superpose eq433 eq537
  have eq601 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X3) = ((X3 ◇ ((X4 ◇ X0) ◇ X4)) ◇ X3) := superpose eq117 eq593
  have eq609 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ (X1 ◇ X4)) ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X4)) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X4))) = ((X3 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq601 eq242
  have eq626 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ (X0 ◇ (X1 ◇ X4))) ◇ X3) = ((X3 ◇ (((X5 ◇ (X1 ◇ X2)) ◇ X5) ◇ X6)) ◇ X3) := superpose eq601 eq412
  have eq637 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X2 ◇ (X1 ◇ X4)) ◇ X2) ◇ ((X5 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X5)) = (((X6 ◇ X3) ◇ X6) ◇ ((((X2 ◇ (X1 ◇ X4)) ◇ X2) ◇ ((X5 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X5)) ◇ X6)) := superpose eq601 eq598
  have eq666 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X5)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq601 eq372
  have eq668 (X0 X1 X2 X3 : G) : ((X2 ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0)) ◇ X2) = (((((X1 ◇ (X0 ◇ X3)) ◇ X2) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X2)) ◇ (X1 ◇ (X0 ◇ X3))) := superpose eq601 eq213
  have eq681 (X0 X1 X3 X4 : G) : ((X3 ◇ X1) ◇ X3) = ((X3 ◇ (X0 ◇ (X1 ◇ X4))) ◇ X3) := superpose eq117 eq626
  have eq693 (X0 X1 X4 X5 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ (((X4 ◇ X0) ◇ X4) ◇ X5)) ◇ X1) := superpose eq681 eq411
  have eq708 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X1 ◇ X2)) ◇ X3) = (((((X0 ◇ (X1 ◇ X4)) ◇ X3) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X4)) ◇ X3)) ◇ (X0 ◇ (X1 ◇ X4))) := superpose eq681 eq609
  have eq720 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X4)) ◇ X2) = ((X2 ◇ X0) ◇ X2) := superpose eq693 eq122
  have eq733 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq720 eq565
  have eq737 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ X4)) = (((X0 ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq720 eq471
  have eq738 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ (X1 ◇ X3)) ◇ X2) ◇ X4)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq720 eq737
  have eq741 (X0 X2 : G) : ((((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) ◇ (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0))) = X0 := superpose eq738 eq176
  have eq763 (X1 X2 X3 X4 X5 X6 : G) : (((X2 ◇ (X1 ◇ X4)) ◇ X2) ◇ ((X5 ◇ X1) ◇ X5)) = (((X6 ◇ X3) ◇ X6) ◇ ((((X2 ◇ (X1 ◇ X4)) ◇ X2) ◇ ((X5 ◇ X1) ◇ X5)) ◇ X6)) := superpose eq601 eq637
  have eq799 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = (((((X1 ◇ (X0 ◇ X3)) ◇ X2) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X3)) ◇ X2)) ◇ (X1 ◇ (X0 ◇ X3))) := superpose eq720 eq668
  have eq800 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ X3) = ((X3 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq799 eq708
  have eq801 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq800 eq7
  have eq806 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) = X0 := superpose eq800 eq15
  have eq818 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) = X1 := superpose eq800 eq61
  have eq823 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)) = ((((X3 ◇ X1) ◇ X3) ◇ (((X0 ◇ X1) ◇ X0) ◇ X4)) ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq800 eq126
  have eq825 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X4)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) := superpose eq800 eq130
  have eq844 (X0 X1 X3 : G) : ((((X3 ◇ X1) ◇ X3) ◇ X1) ◇ ((X3 ◇ X1) ◇ X3)) = (((X0 ◇ X1) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq800 eq439
  have eq860 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)))) = (((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3))) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)))) := superpose eq800 eq515
  have eq901 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq800 eq733
  have eq903 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (((X2 ◇ X1) ◇ X2) ◇ X4)) := superpose eq800 eq738
  have eq914 (X1 X2 X3 X5 X6 : G) : (((X2 ◇ X1) ◇ X2) ◇ ((X5 ◇ X1) ◇ X5)) = (((X6 ◇ X3) ◇ X6) ◇ ((((X2 ◇ X1) ◇ X2) ◇ ((X5 ◇ X1) ◇ X5)) ◇ X6)) := superpose eq800 eq763
  have eq930 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X0)) = ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq800 eq62
  have eq932 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq800 eq163
  have eq938 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X4)) ◇ (X0 ◇ X5)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X4))) = ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X4))) := superpose eq800 eq128
  have eq939 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq800 eq165
  have eq947 (X0 X1 X2 X5 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X5)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq800 eq666
  have eq948 (X0 X1 X2 : G) : (X0 ◇ X1) = ((((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq800 eq289
  have eq1030 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X0)) = ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq800 eq930
  have eq1031 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) = ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq800 eq1030
  have eq1034 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X2) = (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq800 eq932
  have eq1035 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = (((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq800 eq1034
  have eq1043 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq800 eq939
  have eq1044 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq800 eq947
  have eq1045 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq1035 eq948
  have eq1046 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq1045 eq901
  have eq1050 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq1046 eq806
  have eq1090 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq801 eq801
  have eq1098 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1090 eq1050
  have eq1099 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := superpose eq1098 eq741
  have eq1133 (X0 X1 X2 X4 : G) : (X0 ◇ (((X2 ◇ X1) ◇ X2) ◇ X4)) = X0 := superpose eq1099 eq903
  have eq1135 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)) = (((X3 ◇ X1) ◇ X3) ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq1133 eq823
  have eq1139 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = (((((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3))) ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)))) := superpose eq1133 eq860
  have eq1169 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)) = X3 := superpose eq1099 eq1135
  have eq1172 (X1 X3 : G) : ((((X3 ◇ X1) ◇ X3) ◇ X1) ◇ ((X3 ◇ X1) ◇ X3)) = X3 := superpose eq1169 eq844
  have eq1173 (X3 X5 X6 : G) : (((X6 ◇ X3) ◇ X6) ◇ (X5 ◇ X6)) = X5 := superpose eq1169 eq914
  have eq1180 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := superpose eq1169 eq1031
  have eq1184 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq1173 eq1044
  have eq1186 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X4)) ◇ (X0 ◇ X5)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X4))) = ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X4))) := superpose eq1184 eq938
  have eq1192 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))) := superpose eq1184 eq1043
  have eq1199 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) := superpose eq1186 eq825
  have eq1202 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) = X1 := superpose eq1199 eq818
  have eq1206 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq1184 eq1192
  have eq1207 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq1184 eq1206
  have eq1219 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1133 eq1139
  have eq1220 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq1172 eq1219
  have eq1244 (X0 X2 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X0 := superpose eq1220 eq1133
  have eq1276 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq1244 eq1207
  have eq1277 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) = X1 := superpose eq1244 eq1202
  have eq1284 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X2) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0)) := superpose eq1244 eq1276
  have eq1285 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1244 eq1284
  have eq1286 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq1244 eq1285
  have eq1287 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)) = X0 := superpose eq1286 eq1180
  have eq1288 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X1) = X1 := superpose eq1244 eq1277
  have eq1289 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X1 := superpose eq1286 eq1288
  have eq1290 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq1289 eq1286
  have eq1292 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq1290 eq1287
  have eq1300 (X0 X2 : G) : X0 = X2 := superpose eq1292 eq1292
  have eq1305 (X0 : G) : sK0 ≠ X0 := superpose eq1300 eq8
  subsumption eq1305 eq1300


@[equational_result]
theorem Equation27793_implies_Equation2 (G : Type*) [Magma G] (h : Equation27793 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X2) = (((X1 ◇ X0) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X0) := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2)) := superpose eq9 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X1) = (((X4 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2))) ◇ X4) ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2))) := superpose eq9 eq10
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : (((X5 ◇ X2) ◇ X5) ◇ X2) = ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) := superpose eq10 eq10
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X1 ◇ X4)) ◇ X3) = ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X5 ◇ X1) ◇ X5)) ◇ X1) := superpose eq10 eq10
  have eq38 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ X4)) = (((X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) := superpose eq10 eq7
  have eq44 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq7 eq18
  have eq49 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) ◇ X0) := superpose eq44 eq13
  have eq51 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X3)) := superpose eq44 eq16
  have eq53 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X2) = (X0 ◇ X0) := superpose eq44 eq10
  have eq54 (X0 X2 : G) : (X0 ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq44 eq49
  have eq55 (X0 X2 : G) : (X0 ◇ X2) = (X2 ◇ X0) := superpose eq44 eq54
  have eq58 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = (X0 ◇ X0) := superpose eq44 eq51
  have eq75 (X0 X1 X2 X3 X4 X5 : G) : (((X5 ◇ X2) ◇ X5) ◇ X2) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) := superpose eq55 eq23
  have eq76 (X1 X2 X3 X4 X5 : G) : (((X5 ◇ X2) ◇ X5) ◇ X2) = ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) := superpose eq44 eq75
  have eq77 (X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) = (X2 ◇ X2) := superpose eq44 eq76
  have eq89 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X1 ◇ X4)) ◇ X3) = ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X1) ◇ X1) := superpose eq44 eq29
  have eq90 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X1 ◇ X4)) ◇ X3) = ((X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X1) := superpose eq55 eq89
  have eq91 (X1 X2 X3 X4 : G) : ((X3 ◇ (X1 ◇ X4)) ◇ X3) = ((X1 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq44 eq90
  have eq92 (X1 X3 X4 : G) : ((X3 ◇ (X1 ◇ X4)) ◇ X3) = ((X1 ◇ X1) ◇ X1) := superpose eq58 eq91
  have eq93 (X1 X3 X4 : G) : ((X3 ◇ (X1 ◇ X4)) ◇ X3) = X1 := superpose eq44 eq92
  have eq95 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq93 eq53
  have eq99 (X1 X2 X3 X4 : G) : (X2 ◇ X2) = (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) := superpose eq95 eq77
  have eq102 (X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) = X2 := superpose eq95 eq99
  have eq127 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ X4)) = (((X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X2) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq55 eq38
  have eq128 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ X4)) = (((X2 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X1 ◇ X1)) := superpose eq44 eq127
  have eq129 (X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ X4)) = (((X2 ◇ X1) ◇ X2) ◇ X1) := superpose eq95 eq128
  have eq130 (X1 X3 X4 : G) : (X3 ◇ (X1 ◇ X4)) = (X1 ◇ X1) := superpose eq44 eq129
  have eq131 (X1 X3 X4 : G) : (X3 ◇ (X1 ◇ X4)) = X1 := superpose eq95 eq130
  have eq132 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq131 eq102
  have eq145 (X0 X2 : G) : X0 = X2 := superpose eq132 eq132
  have eq150 (X0 : G) : sK0 ≠ X0 := superpose eq145 eq8
  subsumption eq150 eq145


@[equational_result]
theorem Equation27794_implies_Equation2 (G : Type*) [Magma G] (h : Equation27794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X3)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X2) = (((X1 ◇ (((X2 ◇ (X0 ◇ X3)) ◇ X2) ◇ X4)) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq11 eq11
  have eq40 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq11 eq14
  have eq88 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X0 := superpose eq11 eq40
  have eq122 (X0 X1 X2 X4 : G) : (((X1 ◇ (X2 ◇ X4)) ◇ X1) ◇ X0) = X2 := superpose eq88 eq12
  have eq145 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq88 eq122
  have eq156 (X0 X3 : G) : X0 = X3 := superpose eq11 eq145
  have eq176 (X0 : G) : sK0 ≠ X0 := superpose eq156 eq8
  subsumption eq176 eq156


@[equational_result]
theorem Equation27796_implies_Equation2 (G : Type*) [Magma G] (h : Equation27796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X2) = (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X1) = (((X4 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2)) ◇ X4) ◇ (X4 ◇ X4)) := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 X4 : G) : (((X4 ◇ X3) ◇ X4) ◇ (X4 ◇ X4)) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)) := superpose eq9 eq9
  have eq18 (X0 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ (X2 ◇ X2)) = X0 := superpose eq7 eq9
  have eq39 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ X1) ◇ X3)) = X3 := superpose eq18 eq16
  have eq42 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X2) = X0 := superpose eq18 eq9
  have eq46 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X1) = (((X4 ◇ X0) ◇ X4) ◇ (X4 ◇ X4)) := superpose eq42 eq12
  have eq48 (X1 X3 : G) : (X1 ◇ ((X3 ◇ X1) ◇ X3)) = X3 := superpose eq42 eq39
  have eq53 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq18 eq46
  have eq57 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq53 eq48
  have eq65 (X0 X2 : G) : X0 = X2 := superpose eq57 eq57
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq82 eq65


@[equational_result]
theorem Equation27798_implies_Equation2 (G : Type*) [Magma G] (h : Equation27798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4)) = X1 := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq149 eq67


@[equational_result]
theorem Equation27802_implies_Equation2 (G : Type*) [Magma G] (h : Equation27802 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X1 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq56 eq16


@[equational_result]
theorem Equation27804_implies_Equation2 (G : Type*) [Magma G] (h : Equation27804 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq11
  have eq21 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X3 := superpose eq16 eq12
  have eq29 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq16 eq21
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq16 eq29
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq30 eq30
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq33 eq31


@[equational_result]
theorem Equation27805_implies_Equation2 (G : Type*) [Magma G] (h : Equation27805 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X4 ◇ X2)) = X3 := superpose eq7 eq7
  have eq42 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq62 eq42


@[equational_result]
theorem Equation27806_implies_Equation2 (G : Type*) [Magma G] (h : Equation27806 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X0 := superpose eq7 eq11
  have eq19 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ (X4 ◇ X4)) = X3 := superpose eq13 eq10
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq36 eq29


@[equational_result]
theorem Equation27807_implies_Equation2 (G : Type*) [Magma G] (h : Equation27807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X1 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation27810_implies_Equation2 (G : Type*) [Magma G] (h : Equation27810 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X3) = (((X1 ◇ X0) ◇ (X0 ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq9 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = ((X2 ◇ (X0 ◇ X3)) ◇ X3) := superpose eq14 eq10
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq15 eq9
  have eq22 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq9 eq20
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq22 eq22
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq9 eq30
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq79 eq38


@[equational_result]
theorem Equation27811_implies_Equation2 (G : Type*) [Magma G] (h : Equation27811 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq55 eq23


@[equational_result]
theorem Equation27815_implies_Equation2 (G : Type*) [Magma G] (h : Equation27815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X4)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X4)) = X2 := superpose eq7 eq7
  have eq39 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq11
  have eq48 (X0 X4 : G) : X0 = X4 := superpose eq7 eq39
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq135 eq48


@[equational_result]
theorem Equation27818_implies_Equation2 (G : Type*) [Magma G] (h : Equation27818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X3) = (((X1 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X2)) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ X3) = (X3 ◇ X3) := superpose eq10 eq9
  have eq12 (X0 X2 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X2)) = X0 := superpose eq11 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27819_implies_Equation2 (G : Type*) [Magma G] (h : Equation27819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq79 eq18


@[equational_result]
theorem Equation27821_implies_Equation2 (G : Type*) [Magma G] (h : Equation27821 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X4 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0) = X3 := superpose eq7 eq7
  have eq44 (X0 X6 : G) : X0 = X6 := superpose eq12 eq10
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq64 eq44


@[equational_result]
theorem Equation27822_implies_Equation2 (G : Type*) [Magma G] (h : Equation27822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X4 ◇ X2)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation27823_implies_Equation2 (G : Type*) [Magma G] (h : Equation27823 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation27824_implies_Equation2 (G : Type*) [Magma G] (h : Equation27824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation27826_implies_Equation2 (G : Type*) [Magma G] (h : Equation27826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq11 eq11
  have eq23 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq14 eq11
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq37 eq24


@[equational_result]
theorem Equation27827_implies_Equation2 (G : Type*) [Magma G] (h : Equation27827 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq20 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq66 eq20


@[equational_result]
theorem Equation27828_implies_Equation2 (G : Type*) [Magma G] (h : Equation27828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 : G) : ((X0 ◇ X4) ◇ (X0 ◇ X4)) = X0 := superpose eq7 eq7
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X4)))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq10 eq10
  have eq19 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X3 := superpose eq14 eq11
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq19 eq10
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq10 eq26
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq98 eq32


@[equational_result]
theorem Equation27829_implies_Equation2 (G : Type*) [Magma G] (h : Equation27829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X6 : G) : (X0 ◇ (X3 ◇ X6)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq55 eq23


@[equational_result]
theorem Equation27831_implies_Equation2 (G : Type*) [Magma G] (h : Equation27831 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq75 eq19


@[equational_result]
theorem Equation27832_implies_Equation2 (G : Type*) [Magma G] (h : Equation27832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X4)) = X3 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq60 eq22


@[equational_result]
theorem Equation27833_implies_Equation2 (G : Type*) [Magma G] (h : Equation27833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ X4)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X1 ◇ (X3 ◇ X4)))) = X3 := superpose eq7 eq7
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq10 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq50 eq39


@[equational_result]
theorem Equation27834_implies_Equation2 (G : Type*) [Magma G] (h : Equation27834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X6 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X6)) = X3 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq63 eq22


@[equational_result]
theorem Equation27836_implies_Equation2 (G : Type*) [Magma G] (h : Equation27836 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq62 eq22


@[equational_result]
theorem Equation27837_implies_Equation2 (G : Type*) [Magma G] (h : Equation27837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation27838_implies_Equation2 (G : Type*) [Magma G] (h : Equation27838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation27839_implies_Equation2 (G : Type*) [Magma G] (h : Equation27839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X6 : G) : (X0 ◇ (X4 ◇ X6)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation27841_implies_Equation2 (G : Type*) [Magma G] (h : Equation27841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (X4 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X3 ◇ X4) ◇ X1) ◇ (X1 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X5))) = X5 := superpose eq7 eq10
  have eq27 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq17 eq11
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq7 eq27
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq54 eq28


@[equational_result]
theorem Equation27842_implies_Equation2 (G : Type*) [Magma G] (h : Equation27842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (X4 ◇ X2)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation27843_implies_Equation2 (G : Type*) [Magma G] (h : Equation27843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq83 eq19


@[equational_result]
theorem Equation27844_implies_Equation2 (G : Type*) [Magma G] (h : Equation27844 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : ((X0 ◇ X5) ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation27846_implies_Equation2 (G : Type*) [Magma G] (h : Equation27846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X6 : G) : (X0 ◇ (X6 ◇ (X1 ◇ (X0 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq59 eq22


@[equational_result]
theorem Equation27847_implies_Equation2 (G : Type*) [Magma G] (h : Equation27847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X6 : G) : (X0 ◇ (X6 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation27848_implies_Equation2 (G : Type*) [Magma G] (h : Equation27848 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : ((X0 ◇ X5) ◇ (X6 ◇ X5)) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation27849_implies_Equation2 (G : Type*) [Magma G] (h : Equation27849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X6 : G) : (X0 ◇ (X6 ◇ X6)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation27850_implies_Equation2 (G : Type*) [Magma G] (h : Equation27850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X3) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X7 X8 : G) : (X0 ◇ (X7 ◇ X8)) = X3 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation27856_implies_Equation2 (G : Type*) [Magma G] (h : Equation27856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X2) = (((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : (((((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0)) ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq103 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq10 eq14
  have eq117 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq103 eq7
  have eq118 (X0 X1 : G) : ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) ◇ X0) = X1 := superpose eq103 eq7
  have eq129 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq103 eq117
  have eq130 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq129 eq118
  have eq187 (X0 X1 X2 : G) : (X0 ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0)) ◇ X0)) = X2 := superpose eq10 eq130
  have eq189 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) = ((X0 ◇ X1) ◇ ((((X0 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2) ◇ (X0 ◇ X1))) := superpose eq9 eq130
  have eq190 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((((X0 ◇ (X0 ◇ X2)) ◇ X2) ◇ X2) ◇ (X0 ◇ X1))) = X2 := superpose eq13 eq130
  have eq206 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) ◇ X1) := superpose eq130 eq10
  have eq224 (X0 X2 X3 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ X2) ◇ X3) = X2 := superpose eq190 eq189
  have eq283 (X0 X1 X2 : G) : (X0 ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) ◇ X0)) = X2 := superpose eq224 eq187
  have eq336 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq224 eq283
  have eq346 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (X1 ◇ X1) := superpose eq224 eq206
  have eq347 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq346 eq7
  have eq394 (X0 X1 : G) : X0 = X1 := superpose eq347 eq336
  have eq454 (X0 : G) : sK0 ≠ X0 := superpose eq394 eq8
  subsumption eq454 eq394


@[equational_result]
theorem Equation27858_implies_Equation2 (G : Type*) [Magma G] (h : Equation27858 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) = X1 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq38 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq18 eq18
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq18 eq38
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq67 eq39


@[equational_result]
theorem Equation27860_implies_Equation2 (G : Type*) [Magma G] (h : Equation27860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ X3) = (((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 X4 X5 : G) : (X2 ◇ X3) = (X0 ◇ (X4 ◇ X5)) := superpose eq10 eq9
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq12
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq10 eq29
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq71 eq38


@[equational_result]
theorem Equation27866_implies_Equation2 (G : Type*) [Magma G] (h : Equation27866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (((((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X0) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) ◇ (((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3)) = X2 := superpose eq10 eq7
  have eq39 (X0 X1 X2 X3 X4 : G) : (((((((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X2) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = X4 := superpose eq9 eq10
  have eq45 (X0 X1 X4 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1) = X4 := superpose eq16 eq39
  have eq173 (X0 X3 : G) : X0 = X3 := superpose eq45 eq45
  have eq188 (X0 : G) : sK0 ≠ X0 := superpose eq173 eq8
  subsumption eq188 eq173


@[equational_result]
theorem Equation27868_implies_Equation2 (G : Type*) [Magma G] (h : Equation27868 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3) := superpose eq7 eq11
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X2) = X1 := superpose eq7 eq11
  have eq16 (X0 X3 X4 : G) : (((X0 ◇ (X0 ◇ X3)) ◇ X0) ◇ X4) = X3 := superpose eq7 eq11
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X3) := superpose eq16 eq12
  have eq24 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq14 eq22
  have eq25 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq24 eq16
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq25 eq25
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq36 eq31


@[equational_result]
theorem Equation27870_implies_Equation2 (G : Type*) [Magma G] (h : Equation27870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq40 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq58 eq40


@[equational_result]
theorem Equation27872_implies_Equation2 (G : Type*) [Magma G] (h : Equation27872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) ◇ X3) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq10 eq10
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X2 := superpose eq10 eq7
  have eq23 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) ◇ X3) ◇ (X1 ◇ (X1 ◇ X0))) := superpose eq20 eq9
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq20 eq23
  have eq36 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq34 eq16
  have eq40 (X0 X1 : G) : X0 = X1 := superpose eq34 eq36
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq50 eq40


@[equational_result]
theorem Equation27873_implies_Equation2 (G : Type*) [Magma G] (h : Equation27873 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) ◇ X3) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X3) = (((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3))) ◇ (X0 ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X2)) ◇ X0)))) ◇ X0) = X2 := superpose eq10 eq7
  have eq58 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) = ((X0 ◇ X3) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) ◇ X3)) := superpose eq19 eq9
  have eq69 (X0 X3 : G) : ((X0 ◇ X3) ◇ (X0 ◇ X3)) = X0 := superpose eq10 eq58
  have eq85 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1)))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1))))) ◇ X1) := superpose eq10 eq11
  have eq100 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ X0) := superpose eq7 eq69
  have eq130 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1)))) = ((X1 ◇ X1) ◇ X1) := superpose eq100 eq85
  have eq136 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X2 := superpose eq100 eq19
  have eq183 (X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X1) := superpose eq100 eq130
  have eq188 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq136 eq183
  have eq195 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = X0 := superpose eq188 eq100
  have eq205 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq195 eq7
  have eq233 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq205 eq195
  have eq241 (X0 X2 : G) : X0 = X2 := superpose eq69 eq233
  have eq256 (X0 : G) : sK0 ≠ X0 := superpose eq241 eq8
  subsumption eq256 eq241


@[equational_result]
theorem Equation27874_implies_Equation2 (G : Type*) [Magma G] (h : Equation27874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X4 : G) : (X0 ◇ (X2 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq10 eq16
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq45 eq30


@[equational_result]
theorem Equation27876_implies_Equation2 (G : Type*) [Magma G] (h : Equation27876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation27878_implies_Equation2 (G : Type*) [Magma G] (h : Equation27878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X4)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation27882_implies_Equation2 (G : Type*) [Magma G] (h : Equation27882 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X3) ◇ X4)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X4)) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ (X2 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq19 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq10 eq10
  have eq26 (X0 X1 X2 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X4)) ◇ X0) = X2 := superpose eq18 eq11
  have eq31 (X0 X2 X4 : G) : ((X2 ◇ (X0 ◇ X4)) ◇ X0) = X2 := superpose eq18 eq26
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq31 eq19
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq59 eq34


@[equational_result]
theorem Equation27884_implies_Equation2 (G : Type*) [Magma G] (h : Equation27884 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq63 eq22


@[equational_result]
theorem Equation27885_implies_Equation2 (G : Type*) [Magma G] (h : Equation27885 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation27886_implies_Equation2 (G : Type*) [Magma G] (h : Equation27886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X2 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation27887_implies_Equation2 (G : Type*) [Magma G] (h : Equation27887 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X2 := superpose eq7 eq7
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation27893_implies_Equation2 (G : Type*) [Magma G] (h : Equation27893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0))) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ X1) := superpose eq9 eq9
  have eq35 (X0 X1 X2 X3 : G) : (((((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)))))) ◇ (((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))))) ◇ X2)) ◇ X1) = X3 := superpose eq9 eq10
  have eq43 (X0 X1 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ X3) = X0 := superpose eq7 eq17
  have eq96 (X0 X1 X3 : G) : (((((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)))))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))))) ◇ X1) = X3 := superpose eq43 eq35
  have eq98 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq43 eq10
  have eq105 (X0 X1 X3 : G) : (((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))))) ◇ X1) = X3 := superpose eq7 eq96
  have eq106 (X1 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X1) = X3 := superpose eq43 eq105
  have eq159 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq98 eq98
  have eq164 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq159 eq106
  have eq188 (X0 X2 : G) : X0 = X2 := superpose eq164 eq164
  have eq193 (X0 : G) : sK0 ≠ X0 := superpose eq188 eq8
  subsumption eq193 eq188


@[equational_result]
theorem Equation27895_implies_Equation2 (G : Type*) [Magma G] (h : Equation27895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X3) ◇ X4) = X3 := superpose eq7 eq11
  have eq14 (X0 X1 X2 : G) : (((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ X1) ◇ X2) = X1 := superpose eq7 eq11
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq12 eq14
  have eq30 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq24 eq24
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq24 eq30
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq54 eq31


@[equational_result]
theorem Equation27896_implies_Equation2 (G : Type*) [Magma G] (h : Equation27896 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X3)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X2)) = X0 := superpose eq17 eq7
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq10 eq24
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq40 eq31


@[equational_result]
theorem Equation27897_implies_Equation2 (G : Type*) [Magma G] (h : Equation27897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq17 eq12
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq10 eq23
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation27900_implies_Equation2 (G : Type*) [Magma G] (h : Equation27900 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq10
  have eq14 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq13
  have eq24 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq14
  have eq40 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq24 eq24
  have eq69 (X0 X3 : G) : X0 = X3 := superpose eq24 eq40
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq125 eq69


@[equational_result]
theorem Equation27902_implies_Equation2 (G : Type*) [Magma G] (h : Equation27902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation27903_implies_Equation2 (G : Type*) [Magma G] (h : Equation27903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27905_implies_Equation2 (G : Type*) [Magma G] (h : Equation27905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27906_implies_Equation2 (G : Type*) [Magma G] (h : Equation27906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27907_implies_Equation2 (G : Type*) [Magma G] (h : Equation27907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27909_implies_Equation2 (G : Type*) [Magma G] (h : Equation27909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X3) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X2) = (X1 ◇ X0) := superpose eq7 eq10
  have eq19 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq10 eq7
  have eq24 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq19 eq11
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X2) := superpose eq19 eq15
  have eq31 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (X1 ◇ X3) := superpose eq19 eq24
  have eq41 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = (X2 ◇ (X0 ◇ X1)) := superpose eq31 eq19
  have eq50 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ X4) = X0 := superpose eq19 eq41
  have eq53 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq50 eq25
  have eq57 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq53 eq19
  have eq63 (X0 X3 : G) : X0 = X3 := superpose eq57 eq57
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq82 eq63


@[equational_result]
theorem Equation27910_implies_Equation2 (G : Type*) [Magma G] (h : Equation27910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2) ◇ (X3 ◇ X2)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X3)) ◇ X2) = (((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X3 ◇ X3)))))) ◇ X0) = X2 := superpose eq10 eq7
  have eq47 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X4 ◇ X4)) = (X2 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X3)) ◇ (X3 ◇ (X3 ◇ X3)))))) ◇ X1)) := superpose eq11 eq10
  have eq55 (X2 X4 : G) : (X2 ◇ X2) = (X4 ◇ (X4 ◇ X4)) := superpose eq17 eq47
  have eq71 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) = X2 := superpose eq55 eq7
  have eq81 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq55 eq10
  have eq84 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) = X2 := superpose eq55 eq7
  have eq91 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X2)) = X3 := superpose eq71 eq9
  have eq93 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq91 eq10
  have eq127 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1)) = X2 := superpose eq55 eq91
  have eq161 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq127 eq84
  have eq173 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq161 eq81
  have eq194 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq161 eq173
  have eq196 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X2 := superpose eq194 eq93
  have eq204 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq194 eq196
  have eq205 (X0 X3 : G) : X0 = X3 := superpose eq204 eq204
  have eq207 (X0 : G) : sK0 ≠ X0 := superpose eq205 eq8
  subsumption eq207 eq205


@[equational_result]
theorem Equation27911_implies_Equation2 (G : Type*) [Magma G] (h : Equation27911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation27913_implies_Equation2 (G : Type*) [Magma G] (h : Equation27913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27914_implies_Equation2 (G : Type*) [Magma G] (h : Equation27914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27915_implies_Equation2 (G : Type*) [Magma G] (h : Equation27915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27917_implies_Equation2 (G : Type*) [Magma G] (h : Equation27917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27918_implies_Equation2 (G : Type*) [Magma G] (h : Equation27918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27919_implies_Equation2 (G : Type*) [Magma G] (h : Equation27919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27921_implies_Equation2 (G : Type*) [Magma G] (h : Equation27921 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27922_implies_Equation2 (G : Type*) [Magma G] (h : Equation27922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27923_implies_Equation2 (G : Type*) [Magma G] (h : Equation27923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27924_implies_Equation2 (G : Type*) [Magma G] (h : Equation27924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27930_implies_Equation2 (G : Type*) [Magma G] (h : Equation27930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) ◇ X3) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)))) := superpose eq10 eq10
  have eq14 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X0)) ◇ X3) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X0)))) := superpose eq10 eq10
  have eq15 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq10 eq7
  have eq16 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X0)) ◇ X3) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) = X3 := superpose eq10 eq7
  have eq18 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X2 ◇ X3) ◇ (X2 ◇ X2)) := superpose eq7 eq14
  have eq19 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) = X3 := superpose eq7 eq16
  have eq26 (X0 X1 X2 X3 X4 : G) : (((((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X0)) ◇ X3) ◇ X3) ◇ X4) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X0)) ◇ X3) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X0)) ◇ X3))) = X4 := superpose eq10 eq9
  have eq36 (X2 X3 X4 : G) : ((((X2 ◇ X3) ◇ X3) ◇ X4) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))) = X4 := superpose eq7 eq26
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq7 eq36
  have eq47 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq36 eq36
  have eq48 (X0 X1 X3 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X3) ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq36
  have eq71 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) = X3 := superpose eq7 eq19
  have eq102 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq7 eq48
  have eq123 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq102 eq15
  have eq125 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq123 eq12
  have eq132 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq123 eq44
  have eq136 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq123 eq125
  have eq145 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X2 ◇ X2) := superpose eq132 eq18
  have eq148 (X2 X3 : G) : ((X2 ◇ X3) ◇ (X2 ◇ X2)) = X3 := superpose eq145 eq19
  have eq151 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ (X2 ◇ X2)) = X3 := superpose eq145 eq71
  have eq161 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq148 eq136
  have eq163 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq161 eq47
  have eq172 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq161 eq123
  have eq182 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq161 eq163
  have eq190 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ X2) = X3 := superpose eq161 eq151
  have eq191 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq161 eq190
  have eq194 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq191 eq182
  have eq205 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq161 eq194
  have eq207 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq205 eq172
  have eq212 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq205 eq207
  have eq214 (X0 X2 : G) : X0 = X2 := superpose eq212 eq212
  have eq219 (X0 : G) : sK0 ≠ X0 := superpose eq214 eq8
  subsumption eq219 eq214


@[equational_result]
theorem Equation27931_implies_Equation2 (G : Type*) [Magma G] (h : Equation27931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 X4 : G) : (((((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) ◇ X3) ◇ X2) ◇ X4) ◇ X2) = X4 := superpose eq10 eq10
  have eq20 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq13
  have eq21 (X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X2) = X4 := superpose eq10 eq14
  have eq25 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq21 eq9
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = X0 := superpose eq21 eq7
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq20 eq25
  have eq31 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq27 eq26
  have eq35 (X0 X2 : G) : X0 = X2 := superpose eq31 eq31
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq37 eq35


@[equational_result]
theorem Equation27932_implies_Equation2 (G : Type*) [Magma G] (h : Equation27932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) ◇ X4) ◇ (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X4)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq10 eq10
  have eq42 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) ◇ X3)) ◇ X4) ◇ (((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) ◇ ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X2) ◇ X3)) ◇ X5)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X7)) = X6 := superpose eq10 eq9
  have eq67 (X0 X1 X2 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ X4) = X0 := superpose eq7 eq25
  have eq117 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X2 ◇ (X2 ◇ X3)) ◇ X4) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X5)) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X7)) = X6 := superpose eq67 eq42
  have eq150 (X2 X3 X4 X5 X6 : G) : ((((X2 ◇ (X2 ◇ X3)) ◇ X4) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X5)) ◇ X2) = X6 := superpose eq67 eq117
  have eq151 (X2 X4 X6 : G) : (X4 ◇ X2) = X6 := superpose eq67 eq150
  have eq168 (X0 X4 : G) : X0 = X4 := superpose eq7 eq151
  have eq242 (X0 : G) : sK0 ≠ X0 := superpose eq168 eq8
  subsumption eq242 eq168


@[equational_result]
theorem Equation27936_implies_Equation2 (G : Type*) [Magma G] (h : Equation27936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ (X2 ◇ X4)) := superpose eq7 eq7
  have eq25 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq7 eq10
  have eq38 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X3)) = X0 := superpose eq25 eq7
  have eq55 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X2) = X0 := superpose eq25 eq38
  have eq56 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq25 eq55
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq56 eq56
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq59 eq57


@[equational_result]
theorem Equation27938_implies_Equation2 (G : Type*) [Magma G] (h : Equation27938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0))) = X3 := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq28 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X1)) = X0 := superpose eq21 eq7
  have eq43 (X0 X4 : G) : X0 = X4 := superpose eq28 eq28
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq47 eq43


@[equational_result]
theorem Equation27939_implies_Equation2 (G : Type*) [Magma G] (h : Equation27939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X2)) = X0 := superpose eq15 eq7
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq10 eq23
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq40 eq31


@[equational_result]
theorem Equation27940_implies_Equation2 (G : Type*) [Magma G] (h : Equation27940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq24 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X3)) = X0 := superpose eq16 eq7
  have eq31 (X0 X4 : G) : X0 = X4 := superpose eq24 eq24
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq40 eq31


@[equational_result]
theorem Equation27941_implies_Equation2 (G : Type*) [Magma G] (h : Equation27941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : ((X0 ◇ X4) ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq16 eq12
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq10 eq22
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation27943_implies_Equation2 (G : Type*) [Magma G] (h : Equation27943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X3)) ◇ X1) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) = X2 := superpose eq7 eq10
  have eq13 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ (X3 ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)))) = X3 := superpose eq7 eq12
  have eq15 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X2 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)))) = X2 := superpose eq7 eq12
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq12
  have eq20 (X0 X1 X2 X3 : G) : (X1 ◇ (X1 ◇ X2)) = ((((X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X3)) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) ◇ X0) := superpose eq12 eq7
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq15
  have eq23 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) = ((((X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ ((X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X4)) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) ◇ X3) := superpose eq7 eq11
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = ((((X3 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X4)) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3) := superpose eq12 eq11
  have eq28 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X2) := superpose eq12 eq11
  have eq36 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X4)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X3)) ◇ X1)) := superpose eq7 eq11
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq11 eq11
  have eq43 (X0 X1 X2 X4 : G) : (((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X4 ◇ X1)) = X4 := superpose eq11 eq7
  have eq52 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq20 eq23
  have eq53 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) = X3 := superpose eq52 eq13
  have eq57 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X2))) = ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq28 eq24
  have eq95 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) = X3 := superpose eq41 eq12
  have eq101 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X0) = (((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X4)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq41 eq11
  have eq132 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq52 eq101
  have eq142 (X0 X1 X2 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X2)))) = X3 := superpose eq41 eq22
  have eq242 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = ((((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq95 eq22
  have eq289 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq57 eq242
  have eq338 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) = X3 := superpose eq17 eq12
  have eq468 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = (((X0 ◇ (X0 ◇ X5)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X4)) ◇ X1)) := superpose eq142 eq11
  have eq553 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq53
  have eq618 (X0 X1 X4 X5 : G) : (((X0 ◇ (X0 ◇ X5)) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X4)) ◇ X1)) = X0 := superpose eq553 eq468
  have eq622 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) = X3 := superpose eq553 eq338
  have eq627 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) = X0 := superpose eq618 eq36
  have eq633 (X0 X1 X4 : G) : ((X0 ◇ X0) ◇ (X4 ◇ X1)) = X4 := superpose eq627 eq43
  have eq649 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq633 eq289
  have eq664 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq649 eq52
  have eq667 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X3))) := superpose eq649 eq132
  have eq690 (X0 X1 X5 : G) : (((X0 ◇ (X0 ◇ X5)) ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq649 eq618
  have eq704 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X0) = X0 := superpose eq649 eq667
  have eq705 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq649 eq704
  have eq706 (X0 X1 X4 : G) : (X0 ◇ (X4 ◇ X1)) = X4 := superpose eq705 eq633
  have eq708 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq705 eq664
  have eq719 (X0 X1 X5 : G) : (((X0 ◇ (X0 ◇ X5)) ◇ X0) ◇ X1) = X0 := superpose eq705 eq690
  have eq720 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq708 eq719
  have eq723 (X0 X4 : G) : (X0 ◇ X4) = X4 := superpose eq720 eq706
  have eq749 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X0) = X3 := superpose eq720 eq622
  have eq750 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq720 eq749
  have eq885 (X0 X1 : G) : X0 = X1 := superpose eq723 eq750
  have eq928 (X0 : G) : sK0 ≠ X0 := superpose eq885 eq8
  subsumption eq928 eq885


@[equational_result]
theorem Equation27944_implies_Equation2 (G : Type*) [Magma G] (h : Equation27944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X2 ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X2)) ◇ X3) = (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X1) = (((((X3 ◇ (X3 ◇ X2)) ◇ X3) ◇ X0) ◇ ((X3 ◇ (X3 ◇ X2)) ◇ X3)) ◇ X0) := superpose eq7 eq11
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X2 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq11 eq11
  have eq26 (X0 X1 X2 X4 : G) : ((((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) ◇ X1) ◇ (X4 ◇ X2)) = X4 := superpose eq11 eq7
  have eq38 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq10
  have eq59 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X0)) = X1 := superpose eq38 eq7
  have eq63 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) ◇ X0) = (X2 ◇ (X2 ◇ X2)) := superpose eq38 eq7
  have eq65 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1)) ◇ X0) = (X2 ◇ (X2 ◇ X2)) := superpose eq38 eq10
  have eq93 (X0 X1 X2 X3 X4 : G) : ((((X4 ◇ (X4 ◇ X3)) ◇ X4) ◇ X2) ◇ ((X4 ◇ (X4 ◇ X3)) ◇ X4)) = (((((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1)) ◇ X0) := superpose eq9 eq9
  have eq153 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = ((X2 ◇ (X2 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq25 eq38
  have eq209 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = X2 := superpose eq26 eq9
  have eq234 (X0 X1 X2 : G) : ((((((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) ◇ ((((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0))) ◇ (X2 ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ X1))) = X2 := superpose eq26 eq59
  have eq270 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0))) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) = X2 := superpose eq63 eq234
  have eq271 (X1 X2 : G) : (((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) = X2 := superpose eq153 eq270
  have eq272 (X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) = X2 := superpose eq209 eq271
  have eq418 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X1) ◇ X2) := superpose eq272 eq11
  have eq428 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2))))) ◇ X1) ◇ X0) = X2 := superpose eq272 eq7
  have eq473 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq428 eq418
  have eq494 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) ◇ X0) = (X2 ◇ (X2 ◇ X2)) := superpose eq473 eq65
  have eq583 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) ◇ X0) = (X2 ◇ X2) := superpose eq473 eq494
  have eq584 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1) ◇ X0) = X2 := superpose eq473 eq583
  have eq585 (X2 X3 : G) : ((X3 ◇ (X3 ◇ X2)) ◇ X3) = X2 := superpose eq584 eq11
  have eq641 (X0 X2 X3 : G) : (((((X3 ◇ (X3 ◇ X2)) ◇ X3) ◇ X0) ◇ ((X3 ◇ (X3 ◇ X2)) ◇ X3)) ◇ X0) = X2 := superpose eq585 eq20
  have eq655 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1)) ◇ X0) = ((X3 ◇ X2) ◇ X3) := superpose eq585 eq93
  have eq719 (X0 X2 : G) : (((X2 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq585 eq641
  have eq739 (X0 X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = ((((X2 ◇ X3) ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) := superpose eq585 eq655
  have eq740 (X2 X3 : G) : (X2 ◇ X3) = ((X3 ◇ X2) ◇ X3) := superpose eq719 eq739
  have eq742 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq740 eq719
  have eq750 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq742 eq740
  have eq752 (X2 X3 : G) : ((X3 ◇ X3) ◇ X3) = X2 := superpose eq750 eq585
  have eq759 (X2 X3 : G) : (X3 ◇ X3) = X2 := superpose eq473 eq752
  have eq769 (X0 X2 : G) : X0 = X2 := superpose eq759 eq759
  have eq771 (X0 : G) : sK0 ≠ X0 := superpose eq769 eq8
  subsumption eq771 eq769


@[equational_result]
theorem Equation27945_implies_Equation2 (G : Type*) [Magma G] (h : Equation27945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X3 X4 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq10
  have eq19 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq12 eq7
  have eq41 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq19 eq19
  have eq70 (X0 X3 : G) : X0 = X3 := superpose eq19 eq41
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq70 eq8
  subsumption eq126 eq70


@[equational_result]
theorem Equation27947_implies_Equation2 (G : Type*) [Magma G] (h : Equation27947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27948_implies_Equation2 (G : Type*) [Magma G] (h : Equation27948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27949_implies_Equation2 (G : Type*) [Magma G] (h : Equation27949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27951_implies_Equation2 (G : Type*) [Magma G] (h : Equation27951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27952_implies_Equation2 (G : Type*) [Magma G] (h : Equation27952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27953_implies_Equation2 (G : Type*) [Magma G] (h : Equation27953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27955_implies_Equation2 (G : Type*) [Magma G] (h : Equation27955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27956_implies_Equation2 (G : Type*) [Magma G] (h : Equation27956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27957_implies_Equation2 (G : Type*) [Magma G] (h : Equation27957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27958_implies_Equation2 (G : Type*) [Magma G] (h : Equation27958 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27962_implies_Equation2 (G : Type*) [Magma G] (h : Equation27962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq10 eq9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq12 eq12
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq46 eq31


@[equational_result]
theorem Equation27964_implies_Equation2 (G : Type*) [Magma G] (h : Equation27964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27965_implies_Equation2 (G : Type*) [Magma G] (h : Equation27965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation27966_implies_Equation2 (G : Type*) [Magma G] (h : Equation27966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27968_implies_Equation2 (G : Type*) [Magma G] (h : Equation27968 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27969_implies_Equation2 (G : Type*) [Magma G] (h : Equation27969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27970_implies_Equation2 (G : Type*) [Magma G] (h : Equation27970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27972_implies_Equation2 (G : Type*) [Magma G] (h : Equation27972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27973_implies_Equation2 (G : Type*) [Magma G] (h : Equation27973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27974_implies_Equation2 (G : Type*) [Magma G] (h : Equation27974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27975_implies_Equation2 (G : Type*) [Magma G] (h : Equation27975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27977_implies_Equation2 (G : Type*) [Magma G] (h : Equation27977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := superpose eq11 eq11
  have eq23 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq14 eq11
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq37 eq24


@[equational_result]
theorem Equation27978_implies_Equation2 (G : Type*) [Magma G] (h : Equation27978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq11 eq18
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq47 eq32


@[equational_result]
theorem Equation27979_implies_Equation2 (G : Type*) [Magma G] (h : Equation27979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ X3) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) = X4 := superpose eq7 eq7
  have eq17 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq10
  have eq19 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq10
  have eq44 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X0 ◇ (X4 ◇ ((X5 ◇ (X5 ◇ X6)) ◇ X7)))) ◇ X0) = X4 := superpose eq11 eq10
  have eq119 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq19
  have eq155 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq119 eq44
  have eq188 (X0 X2 : G) : X0 = X2 := superpose eq17 eq155
  have eq197 (X0 : G) : sK0 ≠ X0 := superpose eq188 eq8
  subsumption eq197 eq188


@[equational_result]
theorem Equation27980_implies_Equation2 (G : Type*) [Magma G] (h : Equation27980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq11 eq18
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq47 eq32


@[equational_result]
theorem Equation27982_implies_Equation2 (G : Type*) [Magma G] (h : Equation27982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27983_implies_Equation2 (G : Type*) [Magma G] (h : Equation27983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation27984_implies_Equation2 (G : Type*) [Magma G] (h : Equation27984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27985_implies_Equation2 (G : Type*) [Magma G] (h : Equation27985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27987_implies_Equation2 (G : Type*) [Magma G] (h : Equation27987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27988_implies_Equation2 (G : Type*) [Magma G] (h : Equation27988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation27989_implies_Equation2 (G : Type*) [Magma G] (h : Equation27989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27990_implies_Equation2 (G : Type*) [Magma G] (h : Equation27990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27992_implies_Equation2 (G : Type*) [Magma G] (h : Equation27992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27993_implies_Equation2 (G : Type*) [Magma G] (h : Equation27993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27994_implies_Equation2 (G : Type*) [Magma G] (h : Equation27994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27995_implies_Equation2 (G : Type*) [Magma G] (h : Equation27995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation27997_implies_Equation2 (G : Type*) [Magma G] (h : Equation27997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27998_implies_Equation2 (G : Type*) [Magma G] (h : Equation27998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation27999_implies_Equation2 (G : Type*) [Magma G] (h : Equation27999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28000_implies_Equation2 (G : Type*) [Magma G] (h : Equation28000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28001_implies_Equation2 (G : Type*) [Magma G] (h : Equation28001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28007_implies_Equation2 (G : Type*) [Magma G] (h : Equation28007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X0) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq7 eq10
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq9 eq10
  have eq30 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq10 eq9
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq15 eq29
  have eq37 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq30 eq10
  have eq73 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq37 eq15
  have eq75 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq15 eq15
  have eq76 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq15
  have eq93 (X0 X2 : G) : (X0 ◇ X0) = ((X2 ◇ X2) ◇ (X0 ◇ X0)) := superpose eq76 eq75
  have eq95 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = ((X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq76 eq25
  have eq103 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq93 eq73
  have eq105 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X2 ◇ X2)) := superpose eq103 eq30
  have eq108 (X1 X2 : G) : (X2 ◇ X2) = ((X2 ◇ X2) ◇ (X1 ◇ X1)) := superpose eq105 eq9
  have eq115 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = (X0 ◇ X0) := superpose eq105 eq95
  have eq116 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq115 eq7
  have eq118 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq116 eq108
  have eq119 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq118 eq34
  have eq122 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X0 := superpose eq118 eq93
  have eq128 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq118 eq122
  have eq129 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq128 eq119
  have eq149 (X0 X1 : G) : X0 = X1 := superpose eq129 eq128
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq149 eq8
  subsumption eq151 eq149


@[equational_result]
theorem Equation28008_implies_Equation2 (G : Type*) [Magma G] (h : Equation28008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0))) = X2 := superpose eq7 eq10
  have eq43 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ ((((X3 ◇ (X4 ◇ (X2 ◇ X1))) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X4) ◇ X0)) ◇ X0))) = X2 := superpose eq12 eq10
  have eq83 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))) := superpose eq7 eq9
  have eq85 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) = (X0 ◇ (X2 ◇ ((((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq10 eq9
  have eq119 (X0 X1 X2 : G) : (((X1 ◇ (X0 ◇ X2)) ◇ X2) ◇ X1) = (X0 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq7 eq85
  have eq132 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ (X4 ◇ X3))) = ((X0 ◇ X4) ◇ ((((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X3 ◇ X4)) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0)) := superpose eq12 eq119
  have eq146 (X0 X1 X2 : G) : (((X2 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1) ◇ X2) = ((X1 ◇ X1) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0)) := superpose eq119 eq119
  have eq196 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) = X2 := superpose eq132 eq43
  have eq206 (X1 X2 : G) : (((X2 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X1) ◇ X2) = X1 := superpose eq10 eq146
  have eq296 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X0))) := superpose eq119 eq196
  have eq309 (X0 X1 : G) : ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq196 eq119
  have eq315 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) ◇ (((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X2)) := superpose eq196 eq10
  have eq323 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X0)))) = (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X1) := superpose eq196 eq119
  have eq327 (X1 : G) : (X1 ◇ X1) = ((X1 ◇ (X1 ◇ X1)) ◇ X1) := superpose eq10 eq296
  have eq331 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq83 eq309
  have eq337 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X2)) := superpose eq331 eq315
  have eq343 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X1) := superpose eq83 eq323
  have eq344 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq343 eq337
  have eq358 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := superpose eq196 eq83
  have eq361 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ X1) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0) ◇ (X2 ◇ X1)))) := superpose eq119 eq83
  have eq406 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ X0) := superpose eq327 eq119
  have eq414 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1)) := superpose eq327 eq10
  have eq420 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) = X1 := superpose eq327 eq17
  have eq421 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq327 eq83
  have eq423 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq327 eq119
  have eq425 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0)) = X1 := superpose eq327 eq7
  have eq436 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1)) := superpose eq406 eq414
  have eq440 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) = X1 := superpose eq406 eq420
  have eq441 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq83 eq421
  have eq447 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq441 eq406
  have eq449 (X1 X2 : G) : (((X2 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2) = X1 := superpose eq447 eq206
  have eq453 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1)) := superpose eq447 eq436
  have eq454 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0))) = X1 := superpose eq447 eq440
  have eq456 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq453
  have eq463 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq344 eq454
  have eq464 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq456 eq463
  have eq467 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ X1) := superpose eq358 eq423
  have eq468 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq449 eq467
  have eq469 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq468 eq447
  have eq481 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq469 eq344
  have eq489 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq469 eq464
  have eq501 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq481 eq489
  have eq506 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0)) = X1 := superpose eq481 eq425
  have eq507 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq501 eq506
  have eq508 (X0 X1 : G) : (X1 ◇ (X1 ◇ X0)) = X1 := superpose eq469 eq507
  have eq513 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X2 ◇ X1) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X0)) := superpose eq508 eq361
  have eq653 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq10 eq513
  have eq654 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) = X2 := superpose eq653 eq10
  have eq767 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X1 ◇ (X2 ◇ X0))) = X2 := superpose eq653 eq654
  have eq768 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X2 := superpose eq653 eq767
  have eq769 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq653 eq768
  have eq770 (X0 X3 : G) : X0 = X3 := superpose eq769 eq769
  have eq772 (X0 : G) : sK0 ≠ X0 := superpose eq770 eq8
  subsumption eq772 eq770


@[equational_result]
theorem Equation28009_implies_Equation2 (G : Type*) [Magma G] (h : Equation28009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X2 ◇ X4) = (((X1 ◇ X0) ◇ (X2 ◇ X4)) ◇ (X1 ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ X4)) = X3 := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X2 ◇ (X3 ◇ X1)) ◇ X1) ◇ X4) = (X0 ◇ (((X5 ◇ (X6 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) ◇ X7)) := superpose eq10 eq10
  have eq37 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq10
  have eq40 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X4) = (X0 ◇ (X3 ◇ X5)) := superpose eq10 eq9
  have eq62 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) ◇ X4)) = X1 := superpose eq37 eq10
  have eq67 (X1 X2 X3 X4 : G) : (((X2 ◇ (X3 ◇ X1)) ◇ X1) ◇ X4) = X1 := superpose eq62 eq27
  have eq68 (X0 X3 X5 : G) : (X0 ◇ (X3 ◇ X5)) = X3 := superpose eq67 eq40
  have eq90 (X0 X1 : G) : X0 = X1 := superpose eq37 eq68
  have eq93 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq93 eq90


@[equational_result]
theorem Equation28012_implies_Equation2 (G : Type*) [Magma G] (h : Equation28012 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X2)) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq7 eq10
  have eq17 (X0 X1 X2 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X2) ◇ X0) = X2 := superpose eq10 eq7
  have eq18 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X2) := superpose eq10 eq12
  have eq23 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X2 := superpose eq18 eq17
  have eq73 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq18 eq23
  have eq124 (X0 X1 : G) : X0 = X1 := superpose eq10 eq73
  have eq206 (X0 : G) : sK0 ≠ X0 := superpose eq124 eq8
  subsumption eq206 eq124


@[equational_result]
theorem Equation28013_implies_Equation2 (G : Type*) [Magma G] (h : Equation28013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq26 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq16 eq16
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq10 eq26
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq73 eq29


@[equational_result]
theorem Equation28015_implies_Equation2 (G : Type*) [Magma G] (h : Equation28015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X4) = X1 := superpose eq7 eq12
  have eq40 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq17 eq17
  have eq72 (X0 X3 : G) : X0 = X3 := superpose eq40 eq40
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq140 eq72


@[equational_result]
theorem Equation28016_implies_Equation2 (G : Type*) [Magma G] (h : Equation28016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq26 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq16 eq16
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq10 eq26
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq73 eq29


@[equational_result]
theorem Equation28017_implies_Equation2 (G : Type*) [Magma G] (h : Equation28017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X4 ◇ X4) = (((X1 ◇ X0) ◇ (X4 ◇ X4)) ◇ (X5 ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X4 ◇ X4) = (X0 ◇ (X5 ◇ X5)) := superpose eq10 eq9
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq10 eq12
  have eq36 (X0 X1 : G) : X0 = X1 := superpose eq10 eq27
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq69 eq36


@[equational_result]
theorem Equation28018_implies_Equation2 (G : Type*) [Magma G] (h : Equation28018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 X6 X7 : G) : (X4 ◇ X5) = (((X1 ◇ X0) ◇ (X4 ◇ X5)) ◇ (X6 ◇ X7)) := superpose eq7 eq7
  have eq10 (X0 X4 X5 X6 : G) : ((X0 ◇ X4) ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X5 X6 X7 : G) : (X4 ◇ X5) = (X0 ◇ (X6 ◇ X7)) := superpose eq10 eq9
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq10 eq13
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq10 eq30
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq72 eq39


@[equational_result]
theorem Equation28020_implies_Equation2 (G : Type*) [Magma G] (h : Equation28020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X2) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X0)) ◇ X1) = ((((X0 ◇ X1) ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X0)) ◇ X1))) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (((X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X3) ◇ (X0 ◇ X3)) = X0 := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X3 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = ((((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq9
  have eq18 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) = X2 := superpose eq9 eq7
  have eq30 (X0 X1 X2 X3 : G) : (((X3 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X0))) ◇ X3) ◇ (X0 ◇ X3)) = X0 := superpose eq10 eq9
  have eq145 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))))) = X1 := superpose eq18 eq14
  have eq148 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq14
  have eq150 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq18 eq7
  have eq170 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) := superpose eq7 eq148
  have eq178 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq148 eq148
  have eq179 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq18 eq148
  have eq193 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq148 eq15
  have eq196 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq148 eq9
  have eq198 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq148 eq9
  have eq202 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose eq148 eq7
  have eq260 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X0))) ◇ X1) = ((((X0 ◇ X1) ◇ ((X4 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X0)))) ◇ X4)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq30 eq15
  have eq285 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq178
  have eq287 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0)) := superpose eq10 eq178
  have eq298 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X2 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X0) ◇ X0) := superpose eq178 eq11
  have eq304 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq178 eq18
  have eq312 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq148 eq285
  have eq329 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) ◇ X1) := superpose eq148 eq16
  have eq334 (X0 : G) : (X0 ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq178 eq16
  have eq346 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0) := superpose eq11 eq16
  have eq361 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X0)) = (((X2 ◇ X3) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X0)))) ◇ ((((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X0)) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X0))))) := superpose eq16 eq18
  have eq376 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq312 eq334
  have eq377 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq9 eq376
  have eq380 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = ((X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq346 eq287
  have eq383 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq18 eq377
  have eq414 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq383 eq193
  have eq416 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) = X1 := superpose eq383 eq145
  have eq428 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X0)) = (((X2 ◇ X3) ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq414 eq361
  have eq436 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X1 := superpose eq383 eq416
  have eq437 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := superpose eq383 eq436
  have eq438 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq437 eq179
  have eq446 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq438 eq150
  have eq456 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq178 eq446
  have eq459 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq456 eq196
  have eq462 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = (((X0 ◇ (X2 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)))) ◇ X0) ◇ X0) := superpose eq456 eq298
  have eq465 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq456 eq304
  have eq495 (X0 X1 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0)) = X1 := superpose eq459 eq202
  have eq497 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) := superpose eq459 eq329
  have eq499 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ (X1 ◇ (X2 ◇ X0))) = X1 := superpose eq459 eq10
  have eq516 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq459 eq380
  have eq532 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (((X0 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) ◇ X0) ◇ X0) := superpose eq456 eq462
  have eq535 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq456 eq465
  have eq536 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq535 eq532
  have eq537 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq536 eq516
  have eq540 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq536 eq537
  have eq555 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq540 eq437
  have eq558 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq555 eq497
  have eq559 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq540 eq558
  have eq573 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq559 eq495
  have eq580 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq573 eq198
  have eq581 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := superpose eq540 eq580
  have eq612 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq581 eq170
  have eq630 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))) ◇ X1) = ((((X0 ◇ X1) ◇ ((X4 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2))))) ◇ X4)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq581 eq260
  have eq658 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X0)) = (((X2 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq581 eq428
  have eq665 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0))) = X1 := superpose eq581 eq499
  have eq875 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))) ◇ X1) = (((X0 ◇ X1) ◇ ((X4 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2))))) ◇ X4)) ◇ X0) := superpose eq581 eq630
  have eq876 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))) ◇ X1) = (((X0 ◇ X1) ◇ (X4 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))))) ◇ X0) := superpose eq581 eq875
  have eq877 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))) = (((X0 ◇ X1) ◇ (X4 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))))) ◇ X0) := superpose eq581 eq876
  have eq941 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = (((X2 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))))) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq581 eq658
  have eq942 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = (((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq540 eq941
  have eq943 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq555 eq942
  have eq944 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq943 eq612
  have eq988 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq665 eq944
  have eq991 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := superpose eq988 eq877
  have eq1044 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X3 ◇ X2))) = X0 := superpose eq988 eq991
  have eq1045 (X0 X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X2)) = X0 := superpose eq988 eq1044
  have eq1046 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq988 eq1045
  have eq1047 (X0 X1 : G) : X0 = X1 := superpose eq456 eq1046
  have eq1052 (X0 : G) : sK0 ≠ X0 := superpose eq1047 eq8
  subsumption eq1052 eq1047


@[equational_result]
theorem Equation28021_implies_Equation2 (G : Type*) [Magma G] (h : Equation28021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X0)) ◇ X3) = (((X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X3))) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X2)))) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq10
  have eq14 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X3) = (((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) := superpose eq7 eq10
  have eq19 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X4))) := superpose eq7 eq9
  have eq133 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) = (((((X3 ◇ (X1 ◇ X0)) ◇ X3) ◇ (X0 ◇ X1)) ◇ ((X4 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X4)) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq9 eq14
  have eq159 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X2))) ◇ X0)) ◇ X1) := superpose eq13 eq14
  have eq160 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = ((X3 ◇ (X1 ◇ X2)) ◇ X3) := superpose eq14 eq14
  have eq183 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X0))) = (((X5 ◇ ((X4 ◇ X3) ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X0))))) ◇ X5) ◇ X4) := superpose eq14 eq11
  have eq185 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ (X3 ◇ ((((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) ◇ ((X4 ◇ X3) ◇ (X1 ◇ X0)))))) ◇ (X4 ◇ X3)) = X4 := superpose eq14 eq13
  have eq205 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) = ((X0 ◇ ((X4 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)) ◇ X4)) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq7 eq133
  have eq258 (X0 X1 X2 X3 X4 : G) : (X3 ◇ (X1 ◇ X2)) = ((X3 ◇ ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X4)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq160 eq10
  have eq308 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ X0)) := superpose eq258 eq205
  have eq375 (X0 X1 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X0))) = (((X5 ◇ ((X4 ◇ X3) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X0))))) ◇ X5) ◇ X4) := superpose eq308 eq183
  have eq377 (X0 X1 X3 X4 : G) : ((X3 ◇ (X4 ◇ (X3 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X4 ◇ X3) ◇ (X1 ◇ X0)))))) ◇ (X4 ◇ X3)) = X4 := superpose eq308 eq185
  have eq769 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X0)) := superpose eq10 eq308
  have eq775 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X0))) = X2 := superpose eq308 eq7
  have eq1734 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq308 eq769
  have eq1751 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1))) = X0 := superpose eq769 eq7
  have eq1934 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq308 eq775
  have eq1973 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq775 eq1934
  have eq1977 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2))) ◇ X0)) ◇ X1) := superpose eq1973 eq159
  have eq1983 (X0 X1 : G) : (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq1973 eq1734
  have eq1988 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1))) = X0 := superpose eq1973 eq1751
  have eq1997 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) ◇ X0)) ◇ X1) = X0 := superpose eq1973 eq1977
  have eq2004 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose eq1973 eq1988
  have eq2006 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq2004 eq1997
  have eq2008 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq1973 eq2006
  have eq2018 (X0 X1 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X0))) = (((X5 ◇ ((X4 ◇ X3) ◇ ((X1 ◇ X0) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X0))))) ◇ X5) ◇ X4) := superpose eq2008 eq375
  have eq2020 (X0 X1 X3 X4 : G) : ((X3 ◇ (X4 ◇ (X3 ◇ ((X1 ◇ X0) ◇ ((X4 ◇ X3) ◇ (X1 ◇ X0)))))) ◇ (X4 ◇ X3)) = X4 := superpose eq2008 eq377
  have eq2025 (X0 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq2008 eq7
  have eq2031 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X4 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X4))) := superpose eq2008 eq19
  have eq2449 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X0))) = (((X4 ◇ X3) ◇ ((X1 ◇ X0) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X0)))) ◇ X4) := superpose eq2008 eq2018
  have eq2468 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq2008 eq2031
  have eq2469 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq2025 eq2468
  have eq2473 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq2469 eq1983
  have eq2477 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq1973 eq2473
  have eq2478 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq2008 eq2477
  have eq2482 (X0 X1 X3 X4 : G) : ((X3 ◇ (X4 ◇ (X3 ◇ ((X1 ◇ X0) ◇ (X4 ◇ X3))))) ◇ (X4 ◇ X3)) = X4 := superpose eq2478 eq2020
  have eq2484 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ (X3 ◇ X4)) = (((X4 ◇ X3) ◇ ((X1 ◇ X0) ◇ (X3 ◇ X4))) ◇ X4) := superpose eq2478 eq2449
  have eq2501 (X0 X1 X3 X4 : G) : ((X3 ◇ (X4 ◇ (X3 ◇ ((X1 ◇ X0) ◇ X4)))) ◇ X4) = X4 := superpose eq2478 eq2482
  have eq2502 (X3 X4 : G) : (X3 ◇ X4) = X4 := superpose eq2478 eq2501
  have eq2504 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ (X3 ◇ X4)) = X4 := superpose eq2502 eq2484
  have eq2505 (X0 X1 X3 X4 : G) : ((X1 ◇ X0) ◇ X3) = X4 := superpose eq2478 eq2504
  have eq2506 (X1 X3 X4 : G) : (X1 ◇ X3) = X4 := superpose eq2478 eq2505
  have eq2507 (X0 X3 : G) : X0 = X3 := superpose eq2506 eq2506
  have eq2512 (X0 : G) : sK0 ≠ X0 := superpose eq2507 eq8
  subsumption eq2512 eq2507


@[equational_result]
theorem Equation28022_implies_Equation2 (G : Type*) [Magma G] (h : Equation28022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (X0 ◇ X4) = (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X4) ◇ X5)) := superpose eq7 eq7
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X3)) = X1 := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X1) ◇ X0) := superpose eq11 eq7
  have eq30 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) ◇ X0) := superpose eq7 eq9
  have eq31 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X2) = (((X3 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq34 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) ◇ (X3 ◇ X4)) = X3 := superpose eq9 eq7
  have eq39 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq19 eq30
  have eq49 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq39 eq31
  have eq50 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq11 eq49
  have eq54 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ X4)) = X3 := superpose eq50 eq34
  have eq55 (X1 X3 X4 : G) : (X1 ◇ (X3 ◇ X4)) = X3 := superpose eq50 eq54
  have eq67 (X0 X1 : G) : X0 = X1 := superpose eq50 eq55
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq72 eq67


@[equational_result]
theorem Equation28024_implies_Equation2 (G : Type*) [Magma G] (h : Equation28024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X1)) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq92 eq40


@[equational_result]
theorem Equation28026_implies_Equation2 (G : Type*) [Magma G] (h : Equation28026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X2 ◇ X4) = (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X5)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq9
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq163 eq61


@[equational_result]
theorem Equation28030_implies_Equation2 (G : Type*) [Magma G] (h : Equation28030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X3)) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq69 eq16


@[equational_result]
theorem Equation28032_implies_Equation2 (G : Type*) [Magma G] (h : Equation28032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X2) = (((X1 ◇ X0) ◇ X1) ◇ (X5 ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq9
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq136 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq136 eq56


@[equational_result]
theorem Equation28033_implies_Equation2 (G : Type*) [Magma G] (h : Equation28033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ X1) ◇ X0) = X4 := superpose eq7 eq7
  have eq18 (X0 X3 X6 : G) : (X0 ◇ X6) = X3 := superpose eq11 eq11
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq161 eq45


@[equational_result]
theorem Equation28034_implies_Equation2 (G : Type*) [Magma G] (h : Equation28034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X0 := superpose eq7 eq11
  have eq19 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ (X4 ◇ X4)) = X3 := superpose eq13 eq10
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq35 eq28


@[equational_result]
theorem Equation28035_implies_Equation2 (G : Type*) [Magma G] (h : Equation28035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation28038_implies_Equation2 (G : Type*) [Magma G] (h : Equation28038 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = (((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3)) ◇ ((X0 ◇ X3) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq10 eq10
  have eq13 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq14 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ X1) := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ X1) := superpose eq14 eq13
  have eq20 (X0 X1 X3 : G) : (X0 ◇ X3) = (((X1 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X0 ◇ X3) ◇ (X3 ◇ X3))) := superpose eq18 eq9
  have eq29 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (((X2 ◇ X1) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq10 eq20
  have eq35 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (((X2 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq18 eq29
  have eq43 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq20 eq12
  have eq49 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq43
  have eq51 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq49 eq35
  have eq57 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq51 eq12
  have eq80 (X0 X1 : G) : X0 = X1 := superpose eq10 eq57
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq107 eq80


@[equational_result]
theorem Equation28039_implies_Equation2 (G : Type*) [Magma G] (h : Equation28039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation28043_implies_Equation2 (G : Type*) [Magma G] (h : Equation28043 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ X4)) = X3 := superpose eq7 eq7
  have eq27 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq62 eq27


@[equational_result]
theorem Equation28046_implies_Equation2 (G : Type*) [Magma G] (h : Equation28046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X2)) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq34 eq14


@[equational_result]
theorem Equation28047_implies_Equation2 (G : Type*) [Magma G] (h : Equation28047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq54 eq18


@[equational_result]
theorem Equation28049_implies_Equation2 (G : Type*) [Magma G] (h : Equation28049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X2))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X3) ◇ X0) = X4 := superpose eq7 eq7
  have eq40 (X0 X5 : G) : X0 = X5 := superpose eq12 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq50 eq40


@[equational_result]
theorem Equation28050_implies_Equation2 (G : Type*) [Magma G] (h : Equation28050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation28051_implies_Equation2 (G : Type*) [Magma G] (h : Equation28051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation28052_implies_Equation2 (G : Type*) [Magma G] (h : Equation28052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation28054_implies_Equation2 (G : Type*) [Magma G] (h : Equation28054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq15
  have eq65 (X0 X3 : G) : X0 = X3 := superpose eq36 eq36
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq129 eq65


@[equational_result]
theorem Equation28055_implies_Equation2 (G : Type*) [Magma G] (h : Equation28055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq11 eq19
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq63 eq30


@[equational_result]
theorem Equation28056_implies_Equation2 (G : Type*) [Magma G] (h : Equation28056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ (X3 ◇ X4)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq10
  have eq27 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq11 eq11
  have eq38 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq10 eq27
  have eq61 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq38 eq13
  have eq95 (X0 X2 : G) : X0 = X2 := superpose eq10 eq61
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq95 eq8
  subsumption eq125 eq95


@[equational_result]
theorem Equation28057_implies_Equation2 (G : Type*) [Magma G] (h : Equation28057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X6 : G) : (X0 ◇ (X4 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq66 eq22


@[equational_result]
theorem Equation28059_implies_Equation2 (G : Type*) [Magma G] (h : Equation28059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq59 eq42


@[equational_result]
theorem Equation28060_implies_Equation2 (G : Type*) [Magma G] (h : Equation28060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = X4 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq60 eq22


@[equational_result]
theorem Equation28061_implies_Equation2 (G : Type*) [Magma G] (h : Equation28061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X2 ◇ X4) = (((X1 ◇ X0) ◇ X5) ◇ (X1 ◇ X5)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq9
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq155 eq67


@[equational_result]
theorem Equation28062_implies_Equation2 (G : Type*) [Magma G] (h : Equation28062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X6 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X6)) = X4 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq74 eq22


@[equational_result]
theorem Equation28064_implies_Equation2 (G : Type*) [Magma G] (h : Equation28064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq62 eq22


@[equational_result]
theorem Equation28065_implies_Equation2 (G : Type*) [Magma G] (h : Equation28065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X3)) = X4 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation28066_implies_Equation2 (G : Type*) [Magma G] (h : Equation28066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation28067_implies_Equation2 (G : Type*) [Magma G] (h : Equation28067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X6 : G) : (X0 ◇ (X3 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation28069_implies_Equation2 (G : Type*) [Magma G] (h : Equation28069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X2) = (((X1 ◇ X0) ◇ X5) ◇ (X5 ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq9
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq159 eq67


@[equational_result]
theorem Equation28070_implies_Equation2 (G : Type*) [Magma G] (h : Equation28070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (X4 ◇ X3)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation28071_implies_Equation2 (G : Type*) [Magma G] (h : Equation28071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq73 eq19


@[equational_result]
theorem Equation28072_implies_Equation2 (G : Type*) [Magma G] (h : Equation28072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : ((X0 ◇ X5) ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation28074_implies_Equation2 (G : Type*) [Magma G] (h : Equation28074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X6 : G) : (X0 ◇ (X6 ◇ (X1 ◇ (X2 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq74 eq22


@[equational_result]
theorem Equation28075_implies_Equation2 (G : Type*) [Magma G] (h : Equation28075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X6 : G) : (X0 ◇ (X6 ◇ X3)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation28076_implies_Equation2 (G : Type*) [Magma G] (h : Equation28076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : ((X0 ◇ X5) ◇ (X6 ◇ X5)) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation28077_implies_Equation2 (G : Type*) [Magma G] (h : Equation28077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X6 : G) : (X0 ◇ (X6 ◇ X6)) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation28078_implies_Equation2 (G : Type*) [Magma G] (h : Equation28078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X7 X8 : G) : (X0 ◇ (X7 ◇ X8)) = X4 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation28084_implies_Equation2 (G : Type*) [Magma G] (h : Equation28084 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X3) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1)))) := superpose eq7 eq7
  have eq21 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := superpose eq7 eq10
  have eq30 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq21 eq10
  have eq31 (X0 X1 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq21 eq7
  have eq38 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq9 eq21
  have eq42 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq30 eq38
  have eq49 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq21 eq31
  have eq54 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := superpose eq31 eq49
  have eq55 (X0 X1 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X3) ◇ (X1 ◇ X1)) = X3 := superpose eq54 eq9
  have eq60 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq54 eq42
  have eq65 (X1 X3 : G) : (((X1 ◇ X1) ◇ X3) ◇ (X1 ◇ X1)) = X3 := superpose eq60 eq55
  have eq68 (X1 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X3 := superpose eq60 eq65
  have eq77 (X0 X2 : G) : X0 = X2 := superpose eq68 eq68
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq77 eq8
  subsumption eq82 eq77


@[equational_result]
theorem Equation28086_implies_Equation2 (G : Type*) [Magma G] (h : Equation28086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0))) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq37 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq10
  have eq51 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq37 eq37
  have eq63 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ X0) = X4 := superpose eq51 eq12
  have eq86 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq37 eq63
  have eq89 (X0 X2 : G) : X0 = X2 := superpose eq37 eq86
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq8
  subsumption eq123 eq89


@[equational_result]
theorem Equation28088_implies_Equation2 (G : Type*) [Magma G] (h : Equation28088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X2 ◇ X1)) = X0 := superpose eq14 eq7
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation28090_implies_Equation2 (G : Type*) [Magma G] (h : Equation28090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq23 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X2 ◇ X3)) = X0 := superpose eq15 eq7
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq10 eq23
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq41 eq30


@[equational_result]
theorem Equation28092_implies_Equation2 (G : Type*) [Magma G] (h : Equation28092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2))) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq29 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq11 eq11
  have eq50 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq29 eq29
  have eq71 (X0 X3 : G) : X0 = X3 := superpose eq29 eq50
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq124 eq71


@[equational_result]
theorem Equation28093_implies_Equation2 (G : Type*) [Magma G] (h : Equation28093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X3) ◇ X1)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X4) ◇ X5) = X4 := superpose eq7 eq11
  have eq15 (X0 X1 X5 X6 : G) : (((X1 ◇ X0) ◇ X5) ◇ X6) = X5 := superpose eq11 eq11
  have eq23 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq15 eq14
  have eq63 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq134 eq63


@[equational_result]
theorem Equation28094_implies_Equation2 (G : Type*) [Magma G] (h : Equation28094 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq22 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X3 ◇ X3)) = X0 := superpose eq16 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq22 eq22
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq39 eq30


@[equational_result]
theorem Equation28095_implies_Equation2 (G : Type*) [Magma G] (h : Equation28095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : ((X0 ◇ X4) ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X0) = X3 := superpose eq15 eq12
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq10 eq21
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq36 eq27


@[equational_result]
theorem Equation28097_implies_Equation2 (G : Type*) [Magma G] (h : Equation28097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ X1) = ((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X0) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) = ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) := superpose eq9 eq9
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) = ((((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) := superpose eq9 eq7
  have eq31 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq10 eq10
  have eq32 (X0 X1 X2 X4 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X4 ◇ X1)) = X4 := superpose eq10 eq7
  have eq37 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X4 ◇ (X1 ◇ X2))) = ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) := superpose eq10 eq9
  have eq44 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X4 ◇ (X1 ◇ X2))) = ((((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X2) ◇ X1) ◇ (X1 ◇ X2))) := superpose eq15 eq37
  have eq45 (X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X1) = ((X1 ◇ X2) ◇ (X4 ◇ (X1 ◇ X2))) := superpose eq9 eq44
  have eq53 (X0 X1 X4 : G) : (((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X4 ◇ X1)) = X4 := superpose eq45 eq32
  have eq94 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) = (X0 ◇ (X3 ◇ X0)) := superpose eq7 eq45
  have eq129 (X0 X1 X4 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X4 ◇ X0)) := superpose eq94 eq94
  have eq131 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2)) := superpose eq7 eq94
  have eq145 (X0 X1 X2 X3 : G) : (((((X2 ◇ (X3 ◇ X2)) ◇ X2) ◇ (X2 ◇ (X3 ◇ X2))) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq94 eq9
  have eq188 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) ◇ (X3 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0))) = X3 := superpose eq7 eq11
  have eq220 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X3 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0))) = X3 := superpose eq131 eq188
  have eq265 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X2) = ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq129 eq45
  have eq363 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X2 ◇ (X3 ◇ X2)) ◇ X2) ◇ (X4 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2)))) := superpose eq94 eq265
  have eq402 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq265 eq53
  have eq426 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X2 ◇ X1))) = (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq265 eq31
  have eq441 (X0 X1 X4 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X4) := superpose eq220 eq363
  have eq448 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X3 ◇ X0)) = X3 := superpose eq14 eq402
  have eq450 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq448 eq145
  have eq461 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ (X2 ◇ X1))) = X1 := superpose eq450 eq426
  have eq462 (X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X2 ◇ X1))) = X1 := superpose eq441 eq461
  have eq463 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X0)) = X3 := superpose eq462 eq448
  have eq470 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) = X1 := superpose eq463 eq14
  have eq592 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq463 eq470
  have eq606 (X0 X2 : G) : X0 = X2 := superpose eq592 eq592
  have eq608 (X0 : G) : sK0 ≠ X0 := superpose eq606 eq8
  subsumption eq608 eq606


@[equational_result]
theorem Equation28099_implies_Equation2 (G : Type*) [Magma G] (h : Equation28099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq9
  have eq38 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq16 eq16
  have eq65 (X0 X3 : G) : X0 = X3 := superpose eq38 eq38
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq129 eq65


@[equational_result]
theorem Equation28101_implies_Equation2 (G : Type*) [Magma G] (h : Equation28101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28102_implies_Equation2 (G : Type*) [Magma G] (h : Equation28102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28103_implies_Equation2 (G : Type*) [Magma G] (h : Equation28103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28105_implies_Equation2 (G : Type*) [Magma G] (h : Equation28105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation28106_implies_Equation2 (G : Type*) [Magma G] (h : Equation28106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28107_implies_Equation2 (G : Type*) [Magma G] (h : Equation28107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28109_implies_Equation2 (G : Type*) [Magma G] (h : Equation28109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28110_implies_Equation2 (G : Type*) [Magma G] (h : Equation28110 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28111_implies_Equation2 (G : Type*) [Magma G] (h : Equation28111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28112_implies_Equation2 (G : Type*) [Magma G] (h : Equation28112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28114_implies_Equation2 (G : Type*) [Magma G] (h : Equation28114 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2)) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ X3) = ((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq26 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (((X0 ◇ (X4 ◇ X0)) ◇ X4) ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X3)) := superpose eq7 eq10
  have eq35 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = ((X0 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq10 eq10
  have eq43 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X3 ◇ X4) ◇ X1)) = ((((X3 ◇ X4) ◇ X3) ◇ ((X4 ◇ (X5 ◇ X4)) ◇ X5)) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) ◇ X0)) := superpose eq10 eq9
  have eq44 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((X2 ◇ X0) ◇ (X3 ◇ (X2 ◇ X0))) ◇ X3)) ◇ ((X2 ◇ (X4 ◇ X2)) ◇ X4)) ◇ (X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) = X5 := superpose eq10 eq9
  have eq49 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2)) = (((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) ◇ X3) := superpose eq7 eq35
  have eq73 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X0)) = (((X2 ◇ (X3 ◇ X2)) ◇ X3) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq35 eq7
  have eq93 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) = (X1 ◇ (X0 ◇ X1)) := superpose eq73 eq26
  have eq94 (X0 X1 X2 X4 X5 : G) : ((((X2 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ ((X2 ◇ (X4 ◇ X2)) ◇ X4)) ◇ (X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) = X5 := superpose eq73 eq44
  have eq113 (X0 X1 X3 X4 X5 : G) : (X1 ◇ ((X3 ◇ X4) ◇ X1)) = ((((X3 ◇ X4) ◇ X3) ◇ ((X4 ◇ (X5 ◇ X4)) ◇ X5)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq93 eq43
  have eq115 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2)) = (X1 ◇ (X0 ◇ X1)) := superpose eq93 eq49
  have eq132 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq115 eq9
  have eq138 (X0 X1 X3 X4 : G) : (X1 ◇ ((X3 ◇ X4) ◇ X1)) = ((X4 ◇ (X3 ◇ X4)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq115 eq113
  have eq153 (X0 X1 X2 X5 : G) : ((X2 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X2)) ◇ (X5 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) = X5 := superpose eq138 eq94
  have eq164 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq132
  have eq185 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq164 eq164
  have eq188 (X0 X1 X2 X3 : G) : ((X1 ◇ (X3 ◇ X1)) ◇ X3) = ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq164
  have eq189 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ X3) ◇ X1) := superpose eq164 eq164
  have eq211 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = (((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0)))) := superpose eq93 eq93
  have eq231 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq164 eq185
  have eq233 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ X0) := superpose eq7 eq185
  have eq236 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq132 eq185
  have eq237 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = (X0 ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq35 eq185
  have eq240 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) := superpose eq185 eq93
  have eq260 (X1 X3 X4 : G) : (X1 ◇ ((X3 ◇ X4) ◇ X1)) = ((X4 ◇ (X3 ◇ X4)) ◇ (X1 ◇ X1)) := superpose eq233 eq138
  have eq262 (X0 X2 X5 : G) : ((X2 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X2)) ◇ (X5 ◇ (X0 ◇ X0))) = X5 := superpose eq233 eq153
  have eq265 (X0 X1 X2 : G) : (X1 ◇ X1) = ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq233 eq188
  have eq277 (X0 X2 X5 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ (X5 ◇ (X0 ◇ X0))) = X5 := superpose eq233 eq262
  have eq278 (X1 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X3) ◇ X1) := superpose eq265 eq189
  have eq283 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq278 eq231
  have eq295 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = (X0 ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq233 eq237
  have eq297 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ X1) := superpose eq278 eq240
  have eq298 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq283 eq297
  have eq299 (X0 X2 : G) : (X0 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := superpose eq298 eq295
  have eq308 (X0 X2 X5 : G) : ((X0 ◇ X2) ◇ (X5 ◇ (X0 ◇ X0))) = X5 := superpose eq299 eq277
  have eq311 (X0 X2 X5 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X5)) = X5 := superpose eq299 eq308
  have eq312 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq311 eq236
  have eq317 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = (((X2 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq312 eq211
  have eq322 (X1 X3 X4 : G) : (X1 ◇ ((X3 ◇ X4) ◇ X1)) = (X4 ◇ (X1 ◇ X1)) := superpose eq312 eq260
  have eq330 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X3)) = (((X2 ◇ X3) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq312 eq317
  have eq331 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X0) ◇ (X1 ◇ X0)) = X3 := superpose eq312 eq330
  have eq332 (X1 X3 X4 : G) : (X1 ◇ ((X3 ◇ X4) ◇ X1)) = (X1 ◇ X4) := superpose eq299 eq322
  have eq333 (X1 X4 : G) : (X1 ◇ X4) = X1 := superpose eq312 eq332
  have eq334 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ X0)) = X3 := superpose eq333 eq331
  have eq348 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = X3 := superpose eq333 eq334
  have eq349 (X1 X2 X3 : G) : (X2 ◇ X1) = X3 := superpose eq333 eq348
  have eq350 (X0 X3 : G) : X0 = X3 := superpose eq349 eq349
  have eq369 (X0 : G) : sK0 ≠ X0 := superpose eq350 eq8
  subsumption eq369 eq350


@[equational_result]
theorem Equation28116_implies_Equation2 (G : Type*) [Magma G] (h : Equation28116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X3)) ◇ X4) = (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq21 (X0 X1 X2 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ X0) = (X4 ◇ X4) := superpose eq13 eq11
  have eq23 (X0 X2 X4 : G) : (X4 ◇ X4) = ((X2 ◇ X2) ◇ X0) := superpose eq13 eq21
  have eq32 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq10 eq23
  have eq41 (X0 X1 : G) : X0 = X1 := superpose eq10 eq32
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq74 eq41


@[equational_result]
theorem Equation28118_implies_Equation2 (G : Type*) [Magma G] (h : Equation28118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28119_implies_Equation2 (G : Type*) [Magma G] (h : Equation28119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28120_implies_Equation2 (G : Type*) [Magma G] (h : Equation28120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28122_implies_Equation2 (G : Type*) [Magma G] (h : Equation28122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation28123_implies_Equation2 (G : Type*) [Magma G] (h : Equation28123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28124_implies_Equation2 (G : Type*) [Magma G] (h : Equation28124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28126_implies_Equation2 (G : Type*) [Magma G] (h : Equation28126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28127_implies_Equation2 (G : Type*) [Magma G] (h : Equation28127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28128_implies_Equation2 (G : Type*) [Magma G] (h : Equation28128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28129_implies_Equation2 (G : Type*) [Magma G] (h : Equation28129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28131_implies_Equation2 (G : Type*) [Magma G] (h : Equation28131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X4) ◇ (X5 ◇ (X0 ◇ X1))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X1)))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq24 (X0 X1 X4 X5 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X4) ◇ X0) = X5 := superpose eq14 eq9
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq24 eq24
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq71 eq57


@[equational_result]
theorem Equation28132_implies_Equation2 (G : Type*) [Magma G] (h : Equation28132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq10 eq16
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq50 eq33


@[equational_result]
theorem Equation28133_implies_Equation2 (G : Type*) [Magma G] (h : Equation28133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X4) ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))))) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X4 ◇ X3))) ◇ (X5 ◇ X0)) = X5 := superpose eq7 eq10
  have eq31 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X0)) = X3 := superpose eq10 eq10
  have eq43 (X0 X3 X5 : G) : (X3 ◇ (X5 ◇ X0)) = X5 := superpose eq31 eq29
  have eq52 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq43 eq16
  have eq58 (X0 X2 : G) : X0 = X2 := superpose eq52 eq52
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq80 eq58


@[equational_result]
theorem Equation28134_implies_Equation2 (G : Type*) [Magma G] (h : Equation28134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq66 eq22


@[equational_result]
theorem Equation28136_implies_Equation2 (G : Type*) [Magma G] (h : Equation28136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28137_implies_Equation2 (G : Type*) [Magma G] (h : Equation28137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28138_implies_Equation2 (G : Type*) [Magma G] (h : Equation28138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28139_implies_Equation2 (G : Type*) [Magma G] (h : Equation28139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28141_implies_Equation2 (G : Type*) [Magma G] (h : Equation28141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28142_implies_Equation2 (G : Type*) [Magma G] (h : Equation28142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28143_implies_Equation2 (G : Type*) [Magma G] (h : Equation28143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28144_implies_Equation2 (G : Type*) [Magma G] (h : Equation28144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28146_implies_Equation2 (G : Type*) [Magma G] (h : Equation28146 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28147_implies_Equation2 (G : Type*) [Magma G] (h : Equation28147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28148_implies_Equation2 (G : Type*) [Magma G] (h : Equation28148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28149_implies_Equation2 (G : Type*) [Magma G] (h : Equation28149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28151_implies_Equation2 (G : Type*) [Magma G] (h : Equation28151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28152_implies_Equation2 (G : Type*) [Magma G] (h : Equation28152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28153_implies_Equation2 (G : Type*) [Magma G] (h : Equation28153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28154_implies_Equation2 (G : Type*) [Magma G] (h : Equation28154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28155_implies_Equation2 (G : Type*) [Magma G] (h : Equation28155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28161_implies_Equation2 (G : Type*) [Magma G] (h : Equation28161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2)))) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) := superpose eq7 eq10
  have eq57 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X3 ◇ X3)) ◇ X4) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) = X4 := superpose eq16 eq7
  have eq66 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X5) ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4))) = X5 := superpose eq16 eq9
  have eq68 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X4) ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)))) = X4 := superpose eq16 eq9
  have eq90 (X0 X1 X3 X4 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X4) ◇ (X3 ◇ X3)) = X4 := superpose eq57 eq68
  have eq91 (X2 X4 X5 : G) : ((X2 ◇ X5) ◇ (X2 ◇ (X4 ◇ X4))) = X5 := superpose eq90 eq66
  have eq96 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq91 eq10
  have eq115 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq9 eq96
  have eq153 (X0 X2 : G) : X0 = X2 := superpose eq115 eq115
  have eq261 (X0 : G) : sK0 ≠ X0 := superpose eq153 eq8
  subsumption eq261 eq153


@[equational_result]
theorem Equation28163_implies_Equation2 (G : Type*) [Magma G] (h : Equation28163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X4)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X3) = ((X0 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X4)) := superpose eq7 eq7
  have eq18 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq9
  have eq41 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq10 eq10
  have eq47 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) ◇ (((X5 ◇ (X6 ◇ X6)) ◇ X1) ◇ X7)) = X4 := superpose eq10 eq9
  have eq71 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ (X3 ◇ X3)) ◇ X1) ◇ X4) = (X0 ◇ (X1 ◇ X0)) := superpose eq9 eq18
  have eq73 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq18 eq18
  have eq88 (X1 X2 X3 X4 : G) : (((X2 ◇ (X3 ◇ X3)) ◇ X1) ◇ X4) = X1 := superpose eq73 eq71
  have eq90 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) ◇ X1) = X4 := superpose eq88 eq47
  have eq98 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq18 eq41
  have eq147 (X0 X1 X2 X4 : G) : (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ X1) = X4 := superpose eq98 eq90
  have eq157 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq98 eq147
  have eq158 (X0 X2 : G) : X0 = X2 := superpose eq18 eq157
  have eq201 (X0 : G) : sK0 ≠ X0 := superpose eq158 eq8
  subsumption eq201 eq158


@[equational_result]
theorem Equation28166_implies_Equation2 (G : Type*) [Magma G] (h : Equation28166 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ (X2 ◇ X2)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq9 eq9
  have eq17 (X0 X2 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X2)) = X0 := superpose eq13 eq7
  have eq21 (X0 X1 : G) : X0 = X1 := superpose eq9 eq17
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq30 eq21


@[equational_result]
theorem Equation28167_implies_Equation2 (G : Type*) [Magma G] (h : Equation28167 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X2 ◇ X4)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq9
  have eq21 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X3)) = X0 := superpose eq15 eq7
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq9 eq21
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq40 eq29


@[equational_result]
theorem Equation28169_implies_Equation2 (G : Type*) [Magma G] (h : Equation28169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 X4 : G) : (((X1 ◇ X0) ◇ X3) ◇ (X4 ◇ X1)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq29 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq7 eq12
  have eq47 (X0 X1 X3 X4 : G) : (X0 ◇ (X4 ◇ X1)) = X3 := superpose eq29 eq9
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq47 eq47
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq81 eq51


@[equational_result]
theorem Equation28170_implies_Equation2 (G : Type*) [Magma G] (h : Equation28170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X2)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq23 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ X2)) = X0 := superpose eq16 eq7
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq10 eq23
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq40 eq31


@[equational_result]
theorem Equation28171_implies_Equation2 (G : Type*) [Magma G] (h : Equation28171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ X5)) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq22 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ (X3 ◇ X3)) = X0 := superpose eq16 eq7
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq10 eq22
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq39 eq30


@[equational_result]
theorem Equation28172_implies_Equation2 (G : Type*) [Magma G] (h : Equation28172 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : ((X0 ◇ X4) ◇ (X5 ◇ X6)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq21 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ X0) = X3 := superpose eq15 eq12
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq10 eq21
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq36 eq27


@[equational_result]
theorem Equation28174_implies_Equation2 (G : Type*) [Magma G] (h : Equation28174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2) ◇ (X3 ◇ X2)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ (X4 ◇ (X5 ◇ X5))) ◇ X1) := superpose eq9 eq9
  have eq32 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq11 eq9
  have eq35 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((((X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ X0) := superpose eq11 eq9
  have eq46 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq15 eq15
  have eq48 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X3 ◇ (X4 ◇ X4))) ◇ X1) = ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq9 eq15
  have eq49 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ X3) ◇ X1) := superpose eq15 eq15
  have eq96 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X0) = (X0 ◇ X0) := superpose eq7 eq46
  have eq108 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = X1 := superpose eq46 eq15
  have eq112 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq96 eq7
  have eq133 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq112 eq35
  have eq138 (X1 X4 X5 : G) : (X1 ◇ X1) = ((X1 ◇ (X4 ◇ (X5 ◇ X5))) ◇ X1) := superpose eq133 eq22
  have eq142 (X0 X1 X2 : G) : (X1 ◇ X1) = ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq138 eq48
  have eq146 (X1 X3 : G) : (X1 ◇ X1) = ((X1 ◇ X3) ◇ X1) := superpose eq142 eq49
  have eq179 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = X1 := superpose eq146 eq108
  have eq180 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq32 eq179
  have eq190 (X0 X1 : G) : X0 = X1 := superpose eq112 eq180
  have eq221 (X0 : G) : sK0 ≠ X0 := superpose eq190 eq8
  subsumption eq221 eq190


@[equational_result]
theorem Equation28176_implies_Equation2 (G : Type*) [Magma G] (h : Equation28176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X4 ◇ X4)) ◇ X3) = (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq11 eq11
  have eq22 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ X0) = (X4 ◇ X3) := superpose eq14 eq12
  have eq26 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X3) = ((X2 ◇ X1) ◇ X0) := superpose eq14 eq22
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq26
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq11 eq33
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq75 eq42


@[equational_result]
theorem Equation28178_implies_Equation2 (G : Type*) [Magma G] (h : Equation28178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28179_implies_Equation2 (G : Type*) [Magma G] (h : Equation28179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28180_implies_Equation2 (G : Type*) [Magma G] (h : Equation28180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28182_implies_Equation2 (G : Type*) [Magma G] (h : Equation28182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28183_implies_Equation2 (G : Type*) [Magma G] (h : Equation28183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation28184_implies_Equation2 (G : Type*) [Magma G] (h : Equation28184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28186_implies_Equation2 (G : Type*) [Magma G] (h : Equation28186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28187_implies_Equation2 (G : Type*) [Magma G] (h : Equation28187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28188_implies_Equation2 (G : Type*) [Magma G] (h : Equation28188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28189_implies_Equation2 (G : Type*) [Magma G] (h : Equation28189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X1) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28192_implies_Equation2 (G : Type*) [Magma G] (h : Equation28192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) = X2 := superpose eq7 eq10
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq10 eq10
  have eq19 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X1 ◇ X1)) ◇ X1) := superpose eq15 eq14
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq19 eq12
  have eq28 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = X1 := superpose eq13 eq10
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq21 eq28
  have eq30 (X0 X1 : G) : X0 = X1 := superpose eq10 eq29
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq53 eq30


@[equational_result]
theorem Equation28193_implies_Equation2 (G : Type*) [Magma G] (h : Equation28193 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation28195_implies_Equation2 (G : Type*) [Magma G] (h : Equation28195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28196_implies_Equation2 (G : Type*) [Magma G] (h : Equation28196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28197_implies_Equation2 (G : Type*) [Magma G] (h : Equation28197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28199_implies_Equation2 (G : Type*) [Magma G] (h : Equation28199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28200_implies_Equation2 (G : Type*) [Magma G] (h : Equation28200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation28201_implies_Equation2 (G : Type*) [Magma G] (h : Equation28201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28203_implies_Equation2 (G : Type*) [Magma G] (h : Equation28203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28204_implies_Equation2 (G : Type*) [Magma G] (h : Equation28204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28205_implies_Equation2 (G : Type*) [Magma G] (h : Equation28205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28206_implies_Equation2 (G : Type*) [Magma G] (h : Equation28206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28208_implies_Equation2 (G : Type*) [Magma G] (h : Equation28208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X1))))) = X3 := superpose eq7 eq11
  have eq23 (X2 X3 X4 : G) : (X2 ◇ X4) = X3 := superpose eq11 eq13
  have eq46 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq126 eq46


@[equational_result]
theorem Equation28209_implies_Equation2 (G : Type*) [Magma G] (h : Equation28209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq71 eq23


@[equational_result]
theorem Equation28210_implies_Equation2 (G : Type*) [Magma G] (h : Equation28210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ (X3 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq28 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq11 eq11
  have eq35 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq10 eq28
  have eq108 (X0 X2 : G) : X0 = X2 := superpose eq10 eq35
  have eq253 (X0 : G) : sK0 ≠ X0 := superpose eq108 eq8
  subsumption eq253 eq108


@[equational_result]
theorem Equation28211_implies_Equation2 (G : Type*) [Magma G] (h : Equation28211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation28213_implies_Equation2 (G : Type*) [Magma G] (h : Equation28213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28214_implies_Equation2 (G : Type*) [Magma G] (h : Equation28214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28215_implies_Equation2 (G : Type*) [Magma G] (h : Equation28215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28216_implies_Equation2 (G : Type*) [Magma G] (h : Equation28216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28218_implies_Equation2 (G : Type*) [Magma G] (h : Equation28218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28219_implies_Equation2 (G : Type*) [Magma G] (h : Equation28219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28220_implies_Equation2 (G : Type*) [Magma G] (h : Equation28220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28221_implies_Equation2 (G : Type*) [Magma G] (h : Equation28221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28223_implies_Equation2 (G : Type*) [Magma G] (h : Equation28223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28224_implies_Equation2 (G : Type*) [Magma G] (h : Equation28224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28225_implies_Equation2 (G : Type*) [Magma G] (h : Equation28225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28226_implies_Equation2 (G : Type*) [Magma G] (h : Equation28226 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28228_implies_Equation2 (G : Type*) [Magma G] (h : Equation28228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28229_implies_Equation2 (G : Type*) [Magma G] (h : Equation28229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28230_implies_Equation2 (G : Type*) [Magma G] (h : Equation28230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28231_implies_Equation2 (G : Type*) [Magma G] (h : Equation28231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28232_implies_Equation2 (G : Type*) [Magma G] (h : Equation28232 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28239_implies_Equation2 (G : Type*) [Magma G] (h : Equation28239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X2) = ((X0 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ (X2 ◇ (X3 ◇ X4)))) := superpose eq7 eq7
  have eq29 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq41 (X0 X2 : G) : X0 = X2 := superpose eq29 eq29
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq107 eq41


@[equational_result]
theorem Equation28240_implies_Equation2 (G : Type*) [Magma G] (h : Equation28240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X1)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X3) = ((X0 ◇ X1) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ ((X1 ◇ X2) ◇ X4)) ◇ X5) ◇ X0) = X5 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X0))) = X2 := superpose eq7 eq10
  have eq25 (X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X4)) = X2 := superpose eq11 eq17
  have eq26 (X0 X5 : G) : ((X0 ◇ X5) ◇ X0) = X5 := superpose eq25 eq12
  have eq32 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq26 eq26
  have eq65 (X0 X2 : G) : X0 = X2 := superpose eq32 eq25
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq73 eq65


@[equational_result]
theorem Equation28241_implies_Equation2 (G : Type*) [Magma G] (h : Equation28241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ (X1 ◇ (X2 ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X3)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X4 ◇ (X1 ◇ X3))) ◇ X5) ◇ X0) = X5 := superpose eq7 eq7
  have eq37 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq9 eq10
  have eq39 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X4) = (X0 ◇ (X1 ◇ (X5 ◇ X6))) := superpose eq10 eq9
  have eq48 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X4) = (X0 ◇ (X1 ◇ X0)) := superpose eq10 eq37
  have eq49 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq37 eq37
  have eq62 (X1 X2 X3 X4 : G) : (((X2 ◇ (X3 ◇ X4)) ◇ X1) ◇ X4) = X1 := superpose eq49 eq48
  have eq63 (X0 X1 X5 X6 : G) : (X0 ◇ (X1 ◇ (X5 ◇ X6))) = X1 := superpose eq62 eq39
  have eq69 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ X0) = X5 := superpose eq63 eq12
  have eq87 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq37 eq69
  have eq90 (X0 X2 : G) : X0 = X2 := superpose eq37 eq87
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq130 eq90


@[equational_result]
theorem Equation28242_implies_Equation2 (G : Type*) [Magma G] (h : Equation28242 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X6 X7 : G) : (((X1 ◇ X0) ◇ X6) ◇ (X1 ◇ X7)) = X6 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X5 X6 : G) : ((X0 ◇ X5) ◇ (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ X6)) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 X6 : G) : (((((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X4 ◇ X5)) ◇ X6) ◇ X0) = X6 := superpose eq7 eq7
  have eq35 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq10
  have eq49 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq35 eq9
  have eq61 (X0 X4 X6 : G) : ((X4 ◇ X6) ◇ X0) = X6 := superpose eq49 eq12
  have eq78 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq35 eq61
  have eq81 (X0 X2 : G) : X0 = X2 := superpose eq35 eq78
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq81 eq8
  subsumption eq115 eq81


@[equational_result]
theorem Equation28244_implies_Equation2 (G : Type*) [Magma G] (h : Equation28244 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ (X4 ◇ X5)) ◇ X0) ◇ ((X6 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq10
  have eq37 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = (((X2 ◇ X3) ◇ X4) ◇ (X0 ◇ X1)) := superpose eq11 eq11
  have eq48 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X3)) = X2 := superpose eq37 eq15
  have eq58 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq11 eq48
  have eq118 (X0 X4 : G) : X0 = X4 := superpose eq7 eq58
  have eq252 (X0 : G) : sK0 ≠ X0 := superpose eq118 eq8
  subsumption eq252 eq118


@[equational_result]
theorem Equation28245_implies_Equation2 (G : Type*) [Magma G] (h : Equation28245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X4 : G) : ((X0 ◇ X4) ◇ (X2 ◇ X2)) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq20 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X2 ◇ X2)) = X0 := superpose eq14 eq7
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq10 eq20
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq38 eq27


@[equational_result]
theorem Equation28246_implies_Equation2 (G : Type*) [Magma G] (h : Equation28246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (X2 ◇ X3)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ X0) = X5 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq9
  have eq19 (X0 X5 : G) : (X0 ◇ X0) = X5 := superpose eq14 eq11
  have eq21 (X0 X2 : G) : X0 = X2 := superpose eq9 eq19
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq30 eq21


@[equational_result]
theorem Equation28247_implies_Equation2 (G : Type*) [Magma G] (h : Equation28247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X5 X6 : G) : ((X0 ◇ X5) ◇ (X2 ◇ X6)) = X5 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq23 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X2 ◇ X4)) = X0 := superpose eq15 eq7
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq10 eq23
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq42 eq31


@[equational_result]
theorem Equation28249_implies_Equation2 (G : Type*) [Magma G] (h : Equation28249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ ((X4 ◇ X2) ◇ X1)) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0))) = X4 := superpose eq7 eq7
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq9 eq10
  have eq66 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq37 eq37
  have eq78 (X0 X3 : G) : X0 = X3 := superpose eq37 eq66
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq124 eq78


@[equational_result]
theorem Equation28250_implies_Equation2 (G : Type*) [Magma G] (h : Equation28250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (X2 ◇ X3)) = X4 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq22 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X3 ◇ X2)) = X0 := superpose eq16 eq7
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq10 eq22
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq39 eq30


@[equational_result]
theorem Equation28251_implies_Equation2 (G : Type*) [Magma G] (h : Equation28251 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ (X3 ◇ X3)) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq20 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ (X3 ◇ X3)) = X0 := superpose eq15 eq7
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq10 eq20
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation28252_implies_Equation2 (G : Type*) [Magma G] (h : Equation28252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 X6 X7 : G) : (((X1 ◇ X0) ◇ X6) ◇ ((X4 ◇ X5) ◇ X7)) = X6 := superpose eq7 eq7
  have eq10 (X0 X4 X5 X6 : G) : ((X0 ◇ X5) ◇ (X4 ◇ X6)) = X5 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq21 (X0 X4 X5 X6 X7 : G) : (X0 ◇ ((X4 ◇ X5) ◇ X7)) = X6 := superpose eq15 eq9
  have eq24 (X0 X5 X6 : G) : (X0 ◇ X5) = X6 := superpose eq15 eq21
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq10 eq24
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq34 eq25


@[equational_result]
theorem Equation28254_implies_Equation2 (G : Type*) [Magma G] (h : Equation28254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X6 X7 : G) : (((X1 ◇ X0) ◇ X6) ◇ (X7 ◇ X1)) = X6 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X5) ◇ X0) = X5 := superpose eq7 eq7
  have eq29 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq44 (X0 X1 X6 X7 : G) : (X0 ◇ (X7 ◇ X1)) = X6 := superpose eq29 eq9
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq44 eq44
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq81 eq51


@[equational_result]
theorem Equation28255_implies_Equation2 (G : Type*) [Magma G] (h : Equation28255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 X6 : G) : ((X0 ◇ X5) ◇ (X6 ◇ X4)) = X5 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq23 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X4 ◇ X2)) = X0 := superpose eq15 eq7
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq10 eq23
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq42 eq31


@[equational_result]
theorem Equation28256_implies_Equation2 (G : Type*) [Magma G] (h : Equation28256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : ((X0 ◇ X5) ◇ (X6 ◇ X3)) = X5 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq22 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X4 ◇ X3)) = X0 := superpose eq15 eq7
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq10 eq22
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq39 eq30


@[equational_result]
theorem Equation28257_implies_Equation2 (G : Type*) [Magma G] (h : Equation28257 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ (X6 ◇ X6)) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq22 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X4 ◇ X4)) = X0 := superpose eq16 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq22 eq22
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq39 eq30


@[equational_result]
theorem Equation28258_implies_Equation2 (G : Type*) [Magma G] (h : Equation28258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X0) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X7 X8 X9 : G) : (((X1 ◇ X0) ◇ X7) ◇ (X8 ◇ X9)) = X7 := superpose eq7 eq7
  have eq10 (X0 X6 X7 X8 : G) : ((X0 ◇ X6) ◇ (X7 ◇ X8)) = X6 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq21 (X0 X7 X8 X9 : G) : (X0 ◇ (X8 ◇ X9)) = X7 := superpose eq15 eq9
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq10 eq21
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq36 eq27


@[equational_result]
theorem Equation28260_implies_Equation2 (G : Type*) [Magma G] (h : Equation28260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X5 ◇ X1)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq9 eq11
  have eq31 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq11 eq7
  have eq32 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) ◇ X0) := superpose eq11 eq9
  have eq39 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) ◇ X0) := superpose eq29 eq32
  have eq40 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X0) := superpose eq31 eq39
  have eq43 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq7 eq40
  have eq129 (X0 X2 : G) : X0 = X2 := superpose eq43 eq43
  have eq238 (X0 : G) : sK0 ≠ X0 := superpose eq129 eq8
  subsumption eq238 eq129


@[equational_result]
theorem Equation28261_implies_Equation2 (G : Type*) [Magma G] (h : Equation28261 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X5 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X2))) ◇ (X5 ◇ X1)) = X5 := superpose eq7 eq10
  have eq17 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X6 ◇ (X0 ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X3)))) = X6 := superpose eq10 eq10
  have eq26 (X0 X4 X5 X6 X7 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ (X6 ◇ X7)) ◇ X5))) = X4 := superpose eq9 eq9
  have eq48 (X0 X1 X2 X6 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = X6 := superpose eq26 eq17
  have eq50 (X0 X1 X5 : G) : (X0 ◇ (X5 ◇ X1)) = X5 := superpose eq26 eq14
  have eq62 (X0 X1 X6 : G) : (X1 ◇ X0) = X6 := superpose eq50 eq48
  have eq68 (X0 X3 : G) : X0 = X3 := superpose eq62 eq62
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq76 eq68


@[equational_result]
theorem Equation28262_implies_Equation2 (G : Type*) [Magma G] (h : Equation28262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X5 ◇ (X0 ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ (X5 ◇ (X3 ◇ X4))) = X5 := superpose eq9 eq10
  have eq34 (X0 X2 X4 : G) : (X0 ◇ (X4 ◇ X2)) = X4 := superpose eq10 eq7
  have eq53 (X0 X1 X2 X3 X5 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ X3) = X5 := superpose eq34 eq25
  have eq61 (X0 X3 X5 : G) : (X0 ◇ X3) = X5 := superpose eq34 eq53
  have eq62 (X0 X3 : G) : X0 = X3 := superpose eq61 eq61
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq77 eq62


@[equational_result]
theorem Equation28263_implies_Equation2 (G : Type*) [Magma G] (h : Equation28263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X0 ◇ X1) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X4 ◇ (X5 ◇ X6)) ◇ X4) = (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq11
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ X0) = (X5 ◇ X4) := superpose eq13 eq12
  have eq24 (X0 X1 X2 X4 X5 : G) : (X5 ◇ X4) = ((X2 ◇ X1) ◇ X0) := superpose eq13 eq21
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq24
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq11 eq31
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq85 eq40


@[equational_result]
theorem Equation28265_implies_Equation2 (G : Type*) [Magma G] (h : Equation28265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28266_implies_Equation2 (G : Type*) [Magma G] (h : Equation28266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28267_implies_Equation2 (G : Type*) [Magma G] (h : Equation28267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28268_implies_Equation2 (G : Type*) [Magma G] (h : Equation28268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28270_implies_Equation2 (G : Type*) [Magma G] (h : Equation28270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28271_implies_Equation2 (G : Type*) [Magma G] (h : Equation28271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28272_implies_Equation2 (G : Type*) [Magma G] (h : Equation28272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28273_implies_Equation2 (G : Type*) [Magma G] (h : Equation28273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28275_implies_Equation2 (G : Type*) [Magma G] (h : Equation28275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28276_implies_Equation2 (G : Type*) [Magma G] (h : Equation28276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28277_implies_Equation2 (G : Type*) [Magma G] (h : Equation28277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28278_implies_Equation2 (G : Type*) [Magma G] (h : Equation28278 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28280_implies_Equation2 (G : Type*) [Magma G] (h : Equation28280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28281_implies_Equation2 (G : Type*) [Magma G] (h : Equation28281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28282_implies_Equation2 (G : Type*) [Magma G] (h : Equation28282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28283_implies_Equation2 (G : Type*) [Magma G] (h : Equation28283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28284_implies_Equation2 (G : Type*) [Magma G] (h : Equation28284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X1) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28286_implies_Equation2 (G : Type*) [Magma G] (h : Equation28286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)))) = X4 := superpose eq7 eq7
  have eq33 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X0))) = X2 := superpose eq7 eq11
  have eq49 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq33 eq11
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq7 eq49
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq120 eq52


@[equational_result]
theorem Equation28287_implies_Equation2 (G : Type*) [Magma G] (h : Equation28287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 : G) : ((X0 ◇ X0) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) = X3 := superpose eq7 eq10
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq10 eq10
  have eq14 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X3)) ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq15 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = (X1 ◇ X1) := superpose eq10 eq10
  have eq19 (X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X3)) ◇ X1) = (X1 ◇ X1) := superpose eq15 eq14
  have eq20 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X1))) = X3 := superpose eq19 eq12
  have eq28 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = X1 := superpose eq13 eq10
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq20 eq28
  have eq30 (X0 X1 : G) : X0 = X1 := superpose eq10 eq29
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq55 eq30


@[equational_result]
theorem Equation28288_implies_Equation2 (G : Type*) [Magma G] (h : Equation28288 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation28289_implies_Equation2 (G : Type*) [Magma G] (h : Equation28289 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation28291_implies_Equation2 (G : Type*) [Magma G] (h : Equation28291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28292_implies_Equation2 (G : Type*) [Magma G] (h : Equation28292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28293_implies_Equation2 (G : Type*) [Magma G] (h : Equation28293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28294_implies_Equation2 (G : Type*) [Magma G] (h : Equation28294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28296_implies_Equation2 (G : Type*) [Magma G] (h : Equation28296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28297_implies_Equation2 (G : Type*) [Magma G] (h : Equation28297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28298_implies_Equation2 (G : Type*) [Magma G] (h : Equation28298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28299_implies_Equation2 (G : Type*) [Magma G] (h : Equation28299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28301_implies_Equation2 (G : Type*) [Magma G] (h : Equation28301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28302_implies_Equation2 (G : Type*) [Magma G] (h : Equation28302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28303_implies_Equation2 (G : Type*) [Magma G] (h : Equation28303 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28304_implies_Equation2 (G : Type*) [Magma G] (h : Equation28304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28306_implies_Equation2 (G : Type*) [Magma G] (h : Equation28306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28307_implies_Equation2 (G : Type*) [Magma G] (h : Equation28307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28308_implies_Equation2 (G : Type*) [Magma G] (h : Equation28308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28309_implies_Equation2 (G : Type*) [Magma G] (h : Equation28309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28310_implies_Equation2 (G : Type*) [Magma G] (h : Equation28310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28312_implies_Equation2 (G : Type*) [Magma G] (h : Equation28312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X5 ◇ X1)) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) = X3 := superpose eq7 eq9
  have eq25 (X0 X2 X4 : G) : (X0 ◇ (X4 ◇ X2)) = X4 := superpose eq17 eq11
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq25 eq25
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq25 eq36
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq65 eq37


@[equational_result]
theorem Equation28313_implies_Equation2 (G : Type*) [Magma G] (h : Equation28313 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq71 eq23


@[equational_result]
theorem Equation28314_implies_Equation2 (G : Type*) [Magma G] (h : Equation28314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X4)) ◇ (X5 ◇ (X0 ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq10
  have eq37 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq12
  have eq38 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq10 eq12
  have eq53 (X0 X2 X4 : G) : (X2 ◇ (X4 ◇ X0)) = X4 := superpose eq38 eq37
  have eq57 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq53 eq12
  have eq64 (X0 X2 : G) : X0 = X2 := superpose eq10 eq57
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq73 eq64


@[equational_result]
theorem Equation28315_implies_Equation2 (G : Type*) [Magma G] (h : Equation28315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X5 X6 X7 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X5)) ◇ (X6 ◇ X7)) = X6 := superpose eq7 eq7
  have eq10 (X0 X4 X5 X6 : G) : ((X0 ◇ X4) ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X6 := superpose eq10 eq9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq13 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation28317_implies_Equation2 (G : Type*) [Magma G] (h : Equation28317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28318_implies_Equation2 (G : Type*) [Magma G] (h : Equation28318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28319_implies_Equation2 (G : Type*) [Magma G] (h : Equation28319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28320_implies_Equation2 (G : Type*) [Magma G] (h : Equation28320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28322_implies_Equation2 (G : Type*) [Magma G] (h : Equation28322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28323_implies_Equation2 (G : Type*) [Magma G] (h : Equation28323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28324_implies_Equation2 (G : Type*) [Magma G] (h : Equation28324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28325_implies_Equation2 (G : Type*) [Magma G] (h : Equation28325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28327_implies_Equation2 (G : Type*) [Magma G] (h : Equation28327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28328_implies_Equation2 (G : Type*) [Magma G] (h : Equation28328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28329_implies_Equation2 (G : Type*) [Magma G] (h : Equation28329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28330_implies_Equation2 (G : Type*) [Magma G] (h : Equation28330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28332_implies_Equation2 (G : Type*) [Magma G] (h : Equation28332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28333_implies_Equation2 (G : Type*) [Magma G] (h : Equation28333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28334_implies_Equation2 (G : Type*) [Magma G] (h : Equation28334 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28335_implies_Equation2 (G : Type*) [Magma G] (h : Equation28335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28336_implies_Equation2 (G : Type*) [Magma G] (h : Equation28336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28338_implies_Equation2 (G : Type*) [Magma G] (h : Equation28338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X6 X7 : G) : (((X1 ◇ X0) ◇ X6) ◇ (X7 ◇ X1)) = X7 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X6 : G) : (X0 ◇ (X6 ◇ (X1 ◇ (X2 ◇ X3)))) = X6 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ X2))) = X4 := superpose eq9 eq9
  have eq23 (X0 X1 X6 : G) : (X0 ◇ X1) = X6 := superpose eq16 eq11
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation28339_implies_Equation2 (G : Type*) [Magma G] (h : Equation28339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X6 : G) : (X0 ◇ (X6 ◇ X4)) = X6 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq71 eq23


@[equational_result]
theorem Equation28340_implies_Equation2 (G : Type*) [Magma G] (h : Equation28340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X5 X6 : G) : (X0 ◇ (X6 ◇ X5)) = X6 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq11 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation28341_implies_Equation2 (G : Type*) [Magma G] (h : Equation28341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ (X6 ◇ X5)) = X6 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ (X5 ◇ (X0 ◇ X4))) = X5 := superpose eq7 eq10
  have eq39 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq13 eq13
  have eq56 (X0 X5 : G) : (X0 ◇ X0) = X5 := superpose eq39 eq13
  have eq65 (X0 X2 : G) : X0 = X2 := superpose eq10 eq56
  have eq82 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq82 eq65


@[equational_result]
theorem Equation28342_implies_Equation2 (G : Type*) [Magma G] (h : Equation28342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X0 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X7 X8 : G) : (X0 ◇ (X7 ◇ X8)) = X7 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq11 eq16
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq66 eq22


@[equational_result]
theorem Equation28344_implies_Equation2 (G : Type*) [Magma G] (h : Equation28344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28345_implies_Equation2 (G : Type*) [Magma G] (h : Equation28345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28346_implies_Equation2 (G : Type*) [Magma G] (h : Equation28346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28347_implies_Equation2 (G : Type*) [Magma G] (h : Equation28347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28348_implies_Equation2 (G : Type*) [Magma G] (h : Equation28348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X1 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28350_implies_Equation2 (G : Type*) [Magma G] (h : Equation28350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28351_implies_Equation2 (G : Type*) [Magma G] (h : Equation28351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28352_implies_Equation2 (G : Type*) [Magma G] (h : Equation28352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28353_implies_Equation2 (G : Type*) [Magma G] (h : Equation28353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28354_implies_Equation2 (G : Type*) [Magma G] (h : Equation28354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X2 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28356_implies_Equation2 (G : Type*) [Magma G] (h : Equation28356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28357_implies_Equation2 (G : Type*) [Magma G] (h : Equation28357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28358_implies_Equation2 (G : Type*) [Magma G] (h : Equation28358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28359_implies_Equation2 (G : Type*) [Magma G] (h : Equation28359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28360_implies_Equation2 (G : Type*) [Magma G] (h : Equation28360 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X3 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28362_implies_Equation2 (G : Type*) [Magma G] (h : Equation28362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28363_implies_Equation2 (G : Type*) [Magma G] (h : Equation28363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28364_implies_Equation2 (G : Type*) [Magma G] (h : Equation28364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28365_implies_Equation2 (G : Type*) [Magma G] (h : Equation28365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28366_implies_Equation2 (G : Type*) [Magma G] (h : Equation28366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28368_implies_Equation2 (G : Type*) [Magma G] (h : Equation28368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X5 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28369_implies_Equation2 (G : Type*) [Magma G] (h : Equation28369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X5 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28370_implies_Equation2 (G : Type*) [Magma G] (h : Equation28370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X5 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28371_implies_Equation2 (G : Type*) [Magma G] (h : Equation28371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X5 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28372_implies_Equation2 (G : Type*) [Magma G] (h : Equation28372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X5 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28373_implies_Equation2 (G : Type*) [Magma G] (h : Equation28373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X5 ◇ X6)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28582_implies_Equation2 (G : Type*) [Magma G] (h : Equation28582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X2) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X3)) := superpose eq11 eq11
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq11 eq11
  have eq22 (X0 X2 X3 : G) : ((((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X3) ◇ X3) ◇ X2) = X3 := superpose eq12 eq12
  have eq28 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2) = ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2)) ◇ X1) := superpose eq11 eq12
  have eq29 (X0 X2 : G) : (((X0 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq12 eq12
  have eq31 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq37 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2)) ◇ X1) := superpose eq11 eq28
  have eq38 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X2) := superpose eq11 eq37
  have eq40 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq31 eq14
  have eq44 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X2) := superpose eq40 eq38
  have eq51 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq31 eq7
  have eq52 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1) := superpose eq31 eq12
  have eq53 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq31 eq51
  have eq54 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq31 eq53
  have eq56 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq54 eq15
  have eq57 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X1) := superpose eq56 eq52
  have eq58 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = ((((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ X1) ◇ X1) := superpose eq44 eq57
  have eq59 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X1) = X1 := superpose eq22 eq58
  have eq62 (X0 X2 : G) : ((((X0 ◇ X2) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq59 eq12
  have eq74 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq59 eq62
  have eq75 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq74 eq29
  have eq83 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq74 eq75
  have eq89 (X0 X2 : G) : X0 = X2 := superpose eq83 eq83
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq8
  subsumption eq115 eq89


@[equational_result]
theorem Equation28584_implies_Equation2 (G : Type*) [Magma G] (h : Equation28584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : ((((X0 ◇ X3) ◇ X3) ◇ X3) ◇ X4) = X3 := superpose eq7 eq12
  have eq16 (X0 X3 X4 : G) : (((X0 ◇ X3) ◇ X3) ◇ X4) = X3 := superpose eq12 eq12
  have eq25 (X3 X4 : G) : (X3 ◇ X4) = X3 := superpose eq16 eq13
  have eq30 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = X3 := superpose eq25 eq16
  have eq33 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq25 eq30
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq33 eq33
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq39 eq34


@[equational_result]
theorem Equation28585_implies_Equation2 (G : Type*) [Magma G] (h : Equation28585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X2 ◇ X2) = (((X0 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq18 (X0 X1 X3 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ X3)) := superpose eq7 eq9
  have eq32 (X0 X1 X3 : G) : (X1 ◇ X1) = (X0 ◇ (X3 ◇ X3)) := superpose eq7 eq18
  have eq53 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq32
  have eq81 (X0 X2 : G) : X0 = X2 := superpose eq53 eq53
  have eq178 (X0 : G) : sK0 ≠ X0 := superpose eq81 eq8
  subsumption eq178 eq81


@[equational_result]
theorem Equation28586_implies_Equation2 (G : Type*) [Magma G] (h : Equation28586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X3 ◇ X4)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X0 := superpose eq7 eq11
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq11
  have eq26 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq17 eq12
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq17 eq26
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq28 eq11
  have eq31 (X0 X5 : G) : (X0 ◇ X5) = X0 := superpose eq29 eq15
  have eq38 (X0 X1 : G) : X0 = X1 := superpose eq29 eq31
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq52 eq38


@[equational_result]
theorem Equation28589_implies_Equation2 (G : Type*) [Magma G] (h : Equation28589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq11 eq9
  have eq14 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X0) := superpose eq7 eq11
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq16 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X0) = X0 := superpose eq11 eq7
  have eq18 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := superpose eq16 eq14
  have eq21 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ X0) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq18 eq13
  have eq24 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq15 eq21
  have eq29 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq11 eq24
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq29
  have eq35 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq32 eq18
  have eq41 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq32 eq35
  have eq43 (X0 X2 : G) : X0 = X2 := superpose eq41 eq41
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq51 eq43


@[equational_result]
theorem Equation28592_implies_Equation2 (G : Type*) [Magma G] (h : Equation28592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X0 ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X2) ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) ◇ (X0 ◇ X2)) := superpose eq10 eq7
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq10 eq14
  have eq24 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ ((((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X0) ◇ X0) ◇ (((X1 ◇ X2) ◇ X2) ◇ X1))) ◇ (((((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X0) ◇ X0) ◇ (((X1 ◇ X2) ◇ X2) ◇ X1)) ◇ X3)) = X2 := superpose eq11 eq7
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq7
  have eq33 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq12 eq29
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq33 eq15
  have eq44 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1)) := superpose eq12 eq9
  have eq57 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) := superpose eq34 eq44
  have eq58 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq34 eq57
  have eq59 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq34 eq58
  have eq60 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq12 eq59
  have eq61 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq60
  have eq62 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq61 eq34
  have eq65 (X0 X1 X2 X3 : G) : (((X0 ◇ X2) ◇ (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X0) ◇ (((X1 ◇ X2) ◇ X2) ◇ X1))) ◇ ((((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X0) ◇ (((X1 ◇ X2) ◇ X2) ◇ X1)) ◇ X3)) = X2 := superpose eq62 eq24
  have eq78 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X0) ◇ (((X1 ◇ X2) ◇ X2) ◇ X1))) ◇ (((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X0) ◇ (((X1 ◇ X2) ◇ X2) ◇ X1))) = X2 := superpose eq62 eq65
  have eq79 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X0)) ◇ ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X0)) = X2 := superpose eq62 eq78
  have eq80 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ (((X1 ◇ X2) ◇ X2) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X2) ◇ X1)) = X2 := superpose eq62 eq79
  have eq81 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = X2 := superpose eq62 eq80
  have eq82 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = X2 := superpose eq62 eq81
  have eq83 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X1) ◇ X1) = X2 := superpose eq62 eq82
  have eq84 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X2 := superpose eq62 eq83
  have eq85 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq62 eq84
  have eq86 (X0 X3 : G) : X0 = X3 := superpose eq85 eq85
  have eq91 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq91 eq86


@[equational_result]
theorem Equation28594_implies_Equation2 (G : Type*) [Magma G] (h : Equation28594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X2 ◇ X1)) = X0 := superpose eq13 eq7
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq13 eq19
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq13 eq25
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq13 eq26
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation28596_implies_Equation2 (G : Type*) [Magma G] (h : Equation28596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq11
  have eq24 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq16 eq12
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq16 eq24
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq16 eq28
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq29 eq29
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq32 eq30


@[equational_result]
theorem Equation28598_implies_Equation2 (G : Type*) [Magma G] (h : Equation28598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X3) ◇ ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq7
  have eq19 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X3) = (X0 ◇ (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X3) ◇ ((X3 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)))) := superpose eq7 eq10
  have eq54 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq17 eq7
  have eq58 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X3) ◇ ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) := superpose eq54 eq9
  have eq78 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq17 eq58
  have eq104 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq54
  have eq107 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq54 eq10
  have eq121 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq104 eq107
  have eq122 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ X0) := superpose eq121 eq78
  have eq131 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq121 eq122
  have eq142 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X3) ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq131 eq19
  have eq209 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = X0 := superpose eq131 eq142
  have eq210 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq131 eq209
  have eq211 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq131 eq210
  have eq212 (X0 X3 : G) : X0 = X3 := superpose eq211 eq211
  have eq217 (X0 : G) : sK0 ≠ X0 := superpose eq212 eq8
  subsumption eq217 eq212


@[equational_result]
theorem Equation28599_implies_Equation2 (G : Type*) [Magma G] (h : Equation28599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ (X0 ◇ X2)) ◇ X3) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq10 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := superpose eq10 eq9
  have eq21 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq10 eq9
  have eq28 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := superpose eq7 eq21
  have eq35 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq10 eq21
  have eq36 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq21 eq9
  have eq37 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X2) = ((((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ ((X0 ◇ X0) ◇ X2)) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq21 eq7
  have eq68 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) ◇ X0) := superpose eq35 eq21
  have eq70 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) ◇ X0) := superpose eq35 eq7
  have eq86 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) ◇ X0) := superpose eq12 eq21
  have eq101 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) = (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) ◇ X0)) := superpose eq35 eq15
  have eq104 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) = (X0 ◇ (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ X2))) ◇ (X0 ◇ X2))) := superpose eq7 eq15
  have eq136 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq35 eq36
  have eq171 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq136 eq101
  have eq172 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq136 eq68
  have eq178 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ (((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X2))) := superpose eq136 eq104
  have eq181 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) := superpose eq136 eq86
  have eq204 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = ((((X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ X0) := superpose eq172 eq70
  have eq209 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq172 eq171
  have eq210 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq209
  have eq211 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq210 eq10
  have eq230 (X0 X1 X2 : G) : (X0 ◇ X2) = ((((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq211 eq37
  have eq240 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) := superpose eq211 eq204
  have eq252 (X0 X1 : G) : (X0 ◇ X0) = ((((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) := superpose eq211 eq240
  have eq253 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq211 eq252
  have eq276 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq253 eq181
  have eq277 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq211 eq276
  have eq278 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq211 eq277
  have eq285 (X0 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ X0) := superpose eq278 eq230
  have eq287 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X2) = (X0 ◇ ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X0 ◇ X2))) := superpose eq285 eq178
  have eq297 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X2) = (X0 ◇ X0) := superpose eq7 eq287
  have eq298 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq211 eq297
  have eq299 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ X0) := superpose eq298 eq28
  have eq316 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq211 eq299
  have eq318 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq316 eq298
  have eq330 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq318 eq316
  have eq355 (X0 X1 : G) : X0 = X1 := superpose eq318 eq330
  have eq357 (X0 : G) : sK0 ≠ X0 := superpose eq355 eq8
  subsumption eq357 eq355


@[equational_result]
theorem Equation28600_implies_Equation2 (G : Type*) [Magma G] (h : Equation28600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = ((X0 ◇ X3) ◇ ((X0 ◇ X2) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X2) = ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) := superpose eq7 eq11
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq16 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq11 eq7
  have eq19 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X2) = X0 := superpose eq16 eq14
  have eq27 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X3)) = X0 := superpose eq11 eq10
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq10 eq10
  have eq32 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq27 eq29
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq32 eq19
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq32 eq37
  have eq50 (X0 X1 : G) : X0 = X1 := superpose eq15 eq49
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq58 eq50


@[equational_result]
theorem Equation28602_implies_Equation2 (G : Type*) [Magma G] (h : Equation28602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq7 eq7
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X2 := superpose eq10 eq7
  have eq90 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq121 eq90


@[equational_result]
theorem Equation28604_implies_Equation2 (G : Type*) [Magma G] (h : Equation28604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X3)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ X3) ◇ X3) ◇ X4) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq11
  have eq20 (X0 X1 X3 X4 : G) : ((((((X1 ◇ X0) ◇ X0) ◇ X3) ◇ X3) ◇ X4) ◇ X0) = X3 := superpose eq15 eq12
  have eq26 (X0 X1 X3 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq15 eq20
  have eq27 (X0 X1 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X3) ◇ X0) = X3 := superpose eq15 eq26
  have eq28 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X3 := superpose eq15 eq27
  have eq29 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X0) = X3 := superpose eq15 eq28
  have eq30 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq15 eq29
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq30 eq30
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq33 eq31


@[equational_result]
theorem Equation28607_implies_Equation2 (G : Type*) [Magma G] (h : Equation28607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X2 ◇ X2) = (((X0 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))))) = X1 := superpose eq10 eq7
  have eq16 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq7 eq15
  have eq17 (X0 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ (X3 ◇ X3)) = X0 := superpose eq7 eq9
  have eq22 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq7 eq9
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq17 eq22
  have eq35 (X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X1 := superpose eq32 eq16
  have eq38 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq35 eq10
  have eq39 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ (X3 ◇ X3)) = X2 := superpose eq38 eq9
  have eq42 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq38 eq32
  have eq44 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ X3) = X2 := superpose eq38 eq39
  have eq46 (X2 X3 : G) : ((X2 ◇ X3) ◇ X3) = X2 := superpose eq42 eq44
  have eq47 (X2 X3 : G) : (X3 ◇ X3) = X2 := superpose eq42 eq46
  have eq58 (X0 X2 : G) : X0 = X2 := superpose eq47 eq47
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq63 eq58


@[equational_result]
theorem Equation28608_implies_Equation2 (G : Type*) [Magma G] (h : Equation28608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X2 ◇ X3) = (((X0 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X4 ◇ X5)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (((X3 ◇ X0) ◇ X0) ◇ X4)) ◇ X0) = X2 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X4 X5 : G) : (X1 ◇ X2) = (X0 ◇ (((X1 ◇ X2) ◇ X4) ◇ X5)) := superpose eq7 eq9
  have eq36 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X0) = X2 := superpose eq25 eq11
  have eq43 (X0 X3 : G) : X0 = X3 := superpose eq36 eq36
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq68 eq43


@[equational_result]
theorem Equation28610_implies_Equation2 (G : Type*) [Magma G] (h : Equation28610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X0))) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq11
  have eq21 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X3 ◇ X1)) = X0 := superpose eq15 eq7
  have eq29 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = X0 := superpose eq15 eq21
  have eq30 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq15 eq29
  have eq31 (X0 X1 X3 : G) : (X1 ◇ X3) = X0 := superpose eq15 eq30
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation28611_implies_Equation2 (G : Type*) [Magma G] (h : Equation28611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X2 ◇ X0))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X3 ◇ X0)) := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq12 eq11
  have eq20 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = X0 := superpose eq19 eq7
  have eq21 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq20 eq10
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq21 eq19
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq21 eq23
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq32 eq27


@[equational_result]
theorem Equation28612_implies_Equation2 (G : Type*) [Magma G] (h : Equation28612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq11
  have eq22 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq14 eq12
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq14 eq22
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq26
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation28613_implies_Equation2 (G : Type*) [Magma G] (h : Equation28613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq7 eq11
  have eq22 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq14 eq12
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq14 eq22
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq26
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation28619_implies_Equation2 (G : Type*) [Magma G] (h : Equation28619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ (X1 ◇ X2)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq7 eq10
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ ((((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X2)) ◇ X0)) ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq20 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2) = ((((X1 ◇ X3) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ (X1 ◇ X3))) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X2)) ◇ (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ (X1 ◇ X3)) ◇ X4)) := superpose eq7 eq9
  have eq36 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ ((X2 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) ◇ X2) ◇ (((X2 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3)) = X2 := superpose eq11 eq7
  have eq41 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ (X1 ◇ X2))) ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq7 eq12
  have eq61 (X0 : G) : (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X0))) ◇ (X0 ◇ ((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X0))) = X0 := superpose eq11 eq41
  have eq311 (X0 X1 : G) : (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X0))) ◇ (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X0))) ◇ X1)) = X0 := superpose eq11 eq36
  have eq1076 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = ((((X0 ◇ ((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X0)))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1)) ◇ X0) := superpose eq61 eq20
  have eq1077 (X0 : G) : ((((X0 ◇ ((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X0)))) ◇ X0) ◇ X0) = X0 := superpose eq61 eq36
  have eq1079 (X0 : G) : (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (X0 ◇ ((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X0))) ◇ X0) = X0 := superpose eq11 eq1077
  have eq1083 (X0 : G) : (X0 ◇ ((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X0)) = X0 := superpose eq11 eq1079
  have eq1092 (X0 : G) : (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq1083 eq61
  have eq1094 (X0 X1 : G) : (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ X1)) = X0 := superpose eq1083 eq311
  have eq1096 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = (((X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1)) ◇ X0) := superpose eq1083 eq1076
  have eq1179 (X0 X1 X2 : G) : ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X1) = ((X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X1)) ◇ (((((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) ◇ X2)) := superpose eq1083 eq9
  have eq1192 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq1083 eq7
  have eq1571 (X0 X1 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = X1 := superpose eq1192 eq1192
  have eq1587 (X0 X1 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ X1) ◇ X0) = X1 := superpose eq1192 eq10
  have eq1679 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X0) := superpose eq1083 eq1587
  have eq1719 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq1571 eq7
  have eq1744 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) := superpose eq1719 eq1679
  have eq1745 (X0 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) = X0 := superpose eq1192 eq1744
  have eq1747 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq1745 eq1092
  have eq1748 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq1745 eq1094
  have eq1750 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) = (((X0 ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1)) ◇ X0) := superpose eq1745 eq1096
  have eq1755 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X2)) := superpose eq1745 eq1179
  have eq1777 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq1747 eq1719
  have eq1779 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq1747 eq1750
  have eq1780 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq1777 eq1779
  have eq1781 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq1748 eq1780
  have eq1783 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq1781 eq1748
  have eq1800 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq1747 eq1755
  have eq1801 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq1781 eq1800
  have eq1802 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq1777 eq1801
  have eq1803 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1783 eq1802
  have eq1811 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq1803 eq7
  have eq2085 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq1803 eq1811
  have eq2086 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq1803 eq2085
  have eq2087 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq1803 eq2086
  have eq2099 (X0 X2 : G) : X0 = X2 := superpose eq2087 eq2087
  have eq2101 (X0 : G) : sK0 ≠ X0 := superpose eq2099 eq8
  subsumption eq2101 eq2099


@[equational_result]
theorem Equation28621_implies_Equation2 (G : Type*) [Magma G] (h : Equation28621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq7 eq10
  have eq23 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) ◇ X0)) ◇ X3) ◇ X4) = X3 := superpose eq11 eq11
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ X0) := superpose eq7 eq16
  have eq49 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq16 eq36
  have eq53 (X0 X3 X4 : G) : (((X0 ◇ X0) ◇ X3) ◇ X4) = X3 := superpose eq49 eq23
  have eq59 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq16 eq53
  have eq60 (X0 X3 : G) : X0 = X3 := superpose eq7 eq59
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq100 eq60


@[equational_result]
theorem Equation28623_implies_Equation2 (G : Type*) [Magma G] (h : Equation28623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ X3) = (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X3)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ X2)) := superpose eq10 eq10
  have eq19 (X0 X2 X3 X4 X5 : G) : (X2 ◇ X3) = (((X0 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)) := superpose eq13 eq9
  have eq20 (X0 X2 X3 X4 X5 : G) : (X2 ◇ X3) = (X0 ◇ (X4 ◇ X5)) := superpose eq10 eq19
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq20
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq29
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq108 eq49


@[equational_result]
theorem Equation28629_implies_Equation2 (G : Type*) [Magma G] (h : Equation28629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ X2) ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X0) ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (((X0 ◇ ((((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1))) ◇ ((((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1))) ◇ (((((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ X3)) = X2 := superpose eq10 eq7
  have eq33 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ ((((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1))) ◇ ((((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1))) ◇ (((((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ X3)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ X2) = X4 := superpose eq9 eq10
  have eq39 (X1 X2 X4 : G) : (((X2 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ X2) = X4 := superpose eq16 eq33
  have eq138 (X0 X3 : G) : X0 = X3 := superpose eq39 eq39
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq138 eq8
  subsumption eq153 eq138


@[equational_result]
theorem Equation28631_implies_Equation2 (G : Type*) [Magma G] (h : Equation28631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X2)) ◇ X0) = X2 := superpose eq7 eq10
  have eq43 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq7 eq17
  have eq85 (X0 X3 : G) : X0 = X3 := superpose eq7 eq43
  have eq202 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq202 eq85


@[equational_result]
theorem Equation28633_implies_Equation2 (G : Type*) [Magma G] (h : Equation28633 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X2 ◇ X3)) = X1 := superpose eq7 eq7
  have eq25 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq10
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq109 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq109 eq45


@[equational_result]
theorem Equation28635_implies_Equation2 (G : Type*) [Magma G] (h : Equation28635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X0)) := superpose eq7 eq10
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X2 := superpose eq10 eq7
  have eq23 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq17 eq10
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq23 eq12
  have eq30 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq23 eq25
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq23 eq30
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq37 eq32


@[equational_result]
theorem Equation28637_implies_Equation2 (G : Type*) [Magma G] (h : Equation28637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X3)) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq145 eq55


@[equational_result]
theorem Equation28639_implies_Equation2 (G : Type*) [Magma G] (h : Equation28639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = X2 := superpose eq10 eq7
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq83 eq30


@[equational_result]
theorem Equation28641_implies_Equation2 (G : Type*) [Magma G] (h : Equation28641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X3)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X3) ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) ◇ X4) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) = X1 := superpose eq10 eq10
  have eq19 (X0 X2 X3 X4 : G) : ((X2 ◇ X4) ◇ X0) = X3 := superpose eq13 eq11
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq44 eq24


@[equational_result]
theorem Equation28645_implies_Equation2 (G : Type*) [Magma G] (h : Equation28645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X3)) = X1 := superpose eq7 eq7
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq46
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq118 eq56


@[equational_result]
theorem Equation28647_implies_Equation2 (G : Type*) [Magma G] (h : Equation28647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ ((X1 ◇ X0) ◇ X1))) = X2 := superpose eq7 eq7
  have eq34 (X0 X5 : G) : X0 = X5 := superpose eq10 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq51 eq34


@[equational_result]
theorem Equation28648_implies_Equation2 (G : Type*) [Magma G] (h : Equation28648 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X2)) = X1 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq50 eq19


@[equational_result]
theorem Equation28649_implies_Equation2 (G : Type*) [Magma G] (h : Equation28649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X1 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation28650_implies_Equation2 (G : Type*) [Magma G] (h : Equation28650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X1 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation28656_implies_Equation2 (G : Type*) [Magma G] (h : Equation28656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) = X2 := superpose eq11 eq7
  have eq21 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq10
  have eq23 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq11 eq10
  have eq30 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq21 eq23
  have eq33 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = X2 := superpose eq30 eq15
  have eq79 (X0 X2 : G) : X0 = X2 := superpose eq30 eq33
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq100 eq79


@[equational_result]
theorem Equation28658_implies_Equation2 (G : Type*) [Magma G] (h : Equation28658 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X3) ◇ X4) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X3) := superpose eq7 eq11
  have eq34 (X0 X3 X4 : G) : (((((X0 ◇ X0) ◇ X3) ◇ X4) ◇ X3) ◇ X0) = X3 := superpose eq19 eq12
  have eq38 (X0 X3 : G) : ((X3 ◇ X3) ◇ X0) = X3 := superpose eq19 eq34
  have eq48 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq11 eq38
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq48 eq48
  have eq102 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq102 eq57


@[equational_result]
theorem Equation28661_implies_Equation2 (G : Type*) [Magma G] (h : Equation28661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X2 ◇ X2) = (((X0 ◇ X3) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq18 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq11
  have eq19 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq18 eq10
  have eq22 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq19 eq19
  have eq32 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (X2 ◇ X2)) = X1 := superpose eq22 eq7
  have eq40 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = X1 := superpose eq19 eq32
  have eq42 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ (X3 ◇ X3)) := superpose eq40 eq9
  have eq54 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq19 eq42
  have eq64 (X0 X1 : G) : X0 = X1 := superpose eq19 eq54
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq113 eq64


@[equational_result]
theorem Equation28662_implies_Equation2 (G : Type*) [Magma G] (h : Equation28662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ ((X2 ◇ X3) ◇ X4)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X4) ◇ X0)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq7 eq10
  have eq38 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq10 eq15
  have eq39 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq15 eq15
  have eq77 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X1) ◇ X1) = X1 := superpose eq15 eq11
  have eq108 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (X2 ◇ X3)) = X1 := superpose eq39 eq7
  have eq131 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X1 := superpose eq15 eq108
  have eq132 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq131 eq38
  have eq143 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq132 eq77
  have eq146 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = X0 := superpose eq132 eq7
  have eq166 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq143 eq146
  have eq167 (X0 X3 : G) : X0 = X3 := superpose eq166 eq166
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq167 eq8
  subsumption eq169 eq167


@[equational_result]
theorem Equation28664_implies_Equation2 (G : Type*) [Magma G] (h : Equation28664 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : ((X0 ◇ X0) ◇ (X4 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X0 ◇ (X3 ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 X5 : G) : (X4 ◇ (X5 ◇ ((X3 ◇ X1) ◇ X4))) = X0 := superpose eq7 eq11
  have eq46 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq11 eq10
  have eq57 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq46 eq13
  have eq72 (X0 X2 : G) : X0 = X2 := superpose eq7 eq57
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq106 eq72


@[equational_result]
theorem Equation28665_implies_Equation2 (G : Type*) [Magma G] (h : Equation28665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X4 ◇ (X3 ◇ X2))) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq7 eq10
  have eq25 (X0 X1 X2 X6 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X6) = X2 := superpose eq7 eq11
  have eq44 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq16 eq11
  have eq55 (X0 X2 X6 : G) : (X0 ◇ X6) = X2 := superpose eq44 eq25
  have eq64 (X0 X4 : G) : X0 = X4 := superpose eq10 eq55
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq80 eq64


@[equational_result]
theorem Equation28666_implies_Equation2 (G : Type*) [Magma G] (h : Equation28666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 : G) : ((X0 ◇ X0) ◇ (X4 ◇ X4)) = X0 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq24 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq42 (X0 X1 : G) : X0 = X1 := superpose eq10 eq24
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq107 eq42


@[equational_result]
theorem Equation28667_implies_Equation2 (G : Type*) [Magma G] (h : Equation28667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 X5 : G) : (X2 ◇ X3) = (X0 ◇ (X4 ◇ X5)) := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq29
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq112 eq49


@[equational_result]
theorem Equation28669_implies_Equation2 (G : Type*) [Magma G] (h : Equation28669 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = (((((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X2) ◇ X1)) ◇ X3) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq11 eq11
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ X2) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) := superpose eq11 eq7
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = X2 := superpose eq11 eq7
  have eq18 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = (((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq17 eq12
  have eq53 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq10 eq18
  have eq62 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X1) = (X0 ◇ X0) := superpose eq7 eq18
  have eq76 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ (X2 ◇ X1)) ◇ X2) := superpose eq62 eq53
  have eq81 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ X2) ◇ X1) ◇ (X1 ◇ X1)) := superpose eq76 eq16
  have eq117 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq17 eq81
  have eq118 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq117 eq11
  have eq123 (X0 X1 : G) : X0 = X1 := superpose eq14 eq118
  have eq138 (X0 : G) : sK0 ≠ X0 := superpose eq123 eq8
  subsumption eq138 eq123


@[equational_result]
theorem Equation28671_implies_Equation2 (G : Type*) [Magma G] (h : Equation28671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq146 eq56


@[equational_result]
theorem Equation28673_implies_Equation2 (G : Type*) [Magma G] (h : Equation28673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq37 eq14


@[equational_result]
theorem Equation28675_implies_Equation2 (G : Type*) [Magma G] (h : Equation28675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X3)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq49 eq19


@[equational_result]
theorem Equation28679_implies_Equation2 (G : Type*) [Magma G] (h : Equation28679 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq43 eq18


@[equational_result]
theorem Equation28681_implies_Equation2 (G : Type*) [Magma G] (h : Equation28681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq52 eq18


@[equational_result]
theorem Equation28682_implies_Equation2 (G : Type*) [Magma G] (h : Equation28682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X4 ◇ (X3 ◇ X2))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X4) = X1 := superpose eq11 eq10
  have eq15 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq11 eq14
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq42 eq16


@[equational_result]
theorem Equation28683_implies_Equation2 (G : Type*) [Magma G] (h : Equation28683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X1 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq47 eq14


@[equational_result]
theorem Equation28684_implies_Equation2 (G : Type*) [Magma G] (h : Equation28684 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X1) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation28687_implies_Equation2 (G : Type*) [Magma G] (h : Equation28687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ X2) = (((X0 ◇ X3) ◇ X3) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X2))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X2 ◇ X0) ◇ X3) ◇ X3) = ((((X1 ◇ (((X2 ◇ X0) ◇ X3) ◇ X3)) ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = (((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq7 eq10
  have eq20 (X0 X1 X2 X3 : G) : ((((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X3) ◇ X3) ◇ (X0 ◇ X3)) = X0 := superpose eq7 eq9
  have eq21 (X0 X1 X2 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq10 eq9
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq45 (X0 X1 X2 : G) : (X0 ◇ X2) = (((((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq21 eq10
  have eq86 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq20
  have eq88 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ (X2 ◇ (X0 ◇ X3))) = X2 := superpose eq20 eq20
  have eq90 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X1)) := superpose eq11 eq20
  have eq135 (X0 X1 X2 : G) : ((((X2 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = ((((((X2 ◇ X0) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq12 eq9
  have eq210 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = (((((((X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) ◇ X4) ◇ X4) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) := superpose eq11 eq22
  have eq234 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose eq86 eq88
  have eq242 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X2) ◇ X2) ◇ X3) ◇ X3) ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X1))) = X4 := superpose eq22 eq88
  have eq244 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq86 eq88
  have eq245 (X0 X1 X2 : G) : (((X2 ◇ X0) ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq88
  have eq286 (X0 X1 X2 : G) : ((((X2 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = (((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq245 eq135
  have eq288 (X0 X1 X2 : G) : ((((X2 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X0 := superpose eq234 eq286
  have eq293 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X2) = (X1 ◇ X1) := superpose eq288 eq90
  have eq318 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq293 eq22
  have eq331 (X0 X1 X2 X4 : G) : (((X2 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X0 ◇ X1))) = X4 := superpose eq293 eq242
  have eq333 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) = ((X4 ◇ X4) ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) := superpose eq293 eq210
  have eq334 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X3)) = X0 := superpose eq293 eq20
  have eq355 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X2) = ((X2 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq293 eq25
  have eq378 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (((X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq318 eq333
  have eq385 (X0 X1 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ X1))) = X4 := superpose eq334 eq331
  have eq390 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq385 eq244
  have eq406 (X0 X1 X2 : G) : (X0 ◇ X2) = (((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq390 eq45
  have eq441 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq293 eq406
  have eq472 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq334 eq355
  have eq473 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq472 eq7
  have eq474 (X0 X2 : G) : ((X2 ◇ X0) ◇ X0) = X0 := superpose eq472 eq288
  have eq475 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X2) = (((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq472 eq378
  have eq495 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X1 ◇ X2) := superpose eq474 eq475
  have eq498 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) := superpose eq495 eq441
  have eq499 (X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = (X1 ◇ X1) := superpose eq495 eq293
  have eq507 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq495 eq498
  have eq508 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq472 eq499
  have eq509 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X0 := superpose eq508 eq334
  have eq515 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq509 eq507
  have eq519 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq515 eq472
  have eq520 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq515 eq473
  have eq523 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq515 eq520
  have eq524 (X0 X1 : G) : X0 = X1 := superpose eq523 eq519
  have eq538 (X0 : G) : sK0 ≠ X0 := superpose eq524 eq8
  subsumption eq538 eq524


@[equational_result]
theorem Equation28688_implies_Equation2 (G : Type*) [Magma G] (h : Equation28688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (X0 ◇ X3) = (((X0 ◇ X4) ◇ X4) ◇ ((X0 ◇ X3) ◇ X5)) := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ (X2 ◇ X4)) = X2 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : (((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X0) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq10
  have eq19 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X3)) = X1 := superpose eq10 eq7
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X1 ◇ X2)) := superpose eq10 eq11
  have eq44 (X0 X1 X3 X4 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X3 ◇ X4)) = X3 := superpose eq19 eq10
  have eq62 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X2) = ((((X0 ◇ X2) ◇ X3) ◇ X3) ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq78 (X0 X2 : G) : ((X0 ◇ X2) ◇ X2) = X0 := superpose eq44 eq62
  have eq81 (X0 X1 X4 X5 : G) : (((X1 ◇ X0) ◇ X0) ◇ (X4 ◇ X5)) = X4 := superpose eq78 eq13
  have eq89 (X1 X4 X5 : G) : (X1 ◇ (X4 ◇ X5)) = X4 := superpose eq78 eq81
  have eq94 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq89 eq26
  have eq100 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X3)) = X1 := superpose eq94 eq19
  have eq106 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq94 eq100
  have eq108 (X0 X1 : G) : X0 = X1 := superpose eq94 eq106
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq108 eq8
  subsumption eq110 eq108


@[equational_result]
theorem Equation28692_implies_Equation2 (G : Type*) [Magma G] (h : Equation28692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X3) ◇ X4) ◇ X4) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X3) := superpose eq7 eq11
  have eq34 (X0 X2 X3 X4 : G) : (((((X2 ◇ X0) ◇ X3) ◇ X4) ◇ X4) ◇ X0) = X3 := superpose eq19 eq12
  have eq39 (X0 X3 X4 : G) : ((X4 ◇ X3) ◇ X0) = X3 := superpose eq19 eq34
  have eq40 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq39 eq19
  have eq48 (X0 X3 X4 : G) : (X4 ◇ X0) = X3 := superpose eq40 eq39
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq48 eq48
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq51 eq49


@[equational_result]
theorem Equation28695_implies_Equation2 (G : Type*) [Magma G] (h : Equation28695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X2 := superpose eq7 eq7
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq44 eq32


@[equational_result]
theorem Equation28696_implies_Equation2 (G : Type*) [Magma G] (h : Equation28696 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ X4)) = X2 := superpose eq7 eq7
  have eq46 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq57 eq46


@[equational_result]
theorem Equation28698_implies_Equation2 (G : Type*) [Magma G] (h : Equation28698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X4) ◇ X0) = X3 := superpose eq7 eq7
  have eq45 (X0 X3 X4 : G) : (X0 ◇ X4) = X3 := superpose eq12 eq12
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq45
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq143 eq57


@[equational_result]
theorem Equation28699_implies_Equation2 (G : Type*) [Magma G] (h : Equation28699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ (X3 ◇ X2)) ◇ (X4 ◇ (X3 ◇ X2))) = X2 := superpose eq7 eq7
  have eq46 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq57 eq46


@[equational_result]
theorem Equation28700_implies_Equation2 (G : Type*) [Magma G] (h : Equation28700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) = X2 := superpose eq7 eq7
  have eq40 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq61 eq40


@[equational_result]
theorem Equation28701_implies_Equation2 (G : Type*) [Magma G] (h : Equation28701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 X5 X6 : G) : ((X0 ◇ (X3 ◇ X4)) ◇ (X5 ◇ X6)) = X2 := superpose eq7 eq7
  have eq47 (X0 X6 : G) : X0 = X6 := superpose eq7 eq10
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq68 eq47


@[equational_result]
theorem Equation28703_implies_Equation2 (G : Type*) [Magma G] (h : Equation28703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq11
  have eq17 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X2 := superpose eq11 eq7
  have eq29 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq16 eq17
  have eq42 (X0 X3 : G) : X0 = X3 := superpose eq11 eq29
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq74 eq42


@[equational_result]
theorem Equation28704_implies_Equation2 (G : Type*) [Magma G] (h : Equation28704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X0) = X3 := superpose eq11 eq10
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq11 eq13
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq41 eq25


@[equational_result]
theorem Equation28705_implies_Equation2 (G : Type*) [Magma G] (h : Equation28705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X3))) = X2 := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq11
  have eq36 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq23 eq11
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq10 eq36
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq96 eq39


@[equational_result]
theorem Equation28706_implies_Equation2 (G : Type*) [Magma G] (h : Equation28706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X5 : G) : (X0 ◇ (X2 ◇ X5)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq31 (X0 X5 : G) : X0 = X5 := superpose eq7 eq15
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq90 eq31


@[equational_result]
theorem Equation28708_implies_Equation2 (G : Type*) [Magma G] (h : Equation28708 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq60 eq16


@[equational_result]
theorem Equation28709_implies_Equation2 (G : Type*) [Magma G] (h : Equation28709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X3)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq71 eq19


@[equational_result]
theorem Equation28710_implies_Equation2 (G : Type*) [Magma G] (h : Equation28710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X3))) = X2 := superpose eq7 eq7
  have eq20 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq71 eq20


@[equational_result]
theorem Equation28711_implies_Equation2 (G : Type*) [Magma G] (h : Equation28711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X5)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation28713_implies_Equation2 (G : Type*) [Magma G] (h : Equation28713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq71 eq19


@[equational_result]
theorem Equation28714_implies_Equation2 (G : Type*) [Magma G] (h : Equation28714 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq58 eq14


@[equational_result]
theorem Equation28715_implies_Equation2 (G : Type*) [Magma G] (h : Equation28715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq40 eq16


@[equational_result]
theorem Equation28716_implies_Equation2 (G : Type*) [Magma G] (h : Equation28716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X5 : G) : (X0 ◇ (X3 ◇ X5)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation28718_implies_Equation2 (G : Type*) [Magma G] (h : Equation28718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X1) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq74 eq22


@[equational_result]
theorem Equation28719_implies_Equation2 (G : Type*) [Magma G] (h : Equation28719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ X2) ◇ X3)) = X2 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq42 eq17


@[equational_result]
theorem Equation28720_implies_Equation2 (G : Type*) [Magma G] (h : Equation28720 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation28721_implies_Equation2 (G : Type*) [Magma G] (h : Equation28721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : ((X0 ◇ X5) ◇ (X5 ◇ X6)) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation28723_implies_Equation2 (G : Type*) [Magma G] (h : Equation28723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (X0 ◇ (X5 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation28724_implies_Equation2 (G : Type*) [Magma G] (h : Equation28724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X5 : G) : (X0 ◇ (X5 ◇ X3)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq63 eq16


@[equational_result]
theorem Equation28725_implies_Equation2 (G : Type*) [Magma G] (h : Equation28725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : ((X0 ◇ X5) ◇ (X6 ◇ X5)) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq63 eq19


@[equational_result]
theorem Equation28726_implies_Equation2 (G : Type*) [Magma G] (h : Equation28726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X5 : G) : (X0 ◇ (X5 ◇ X5)) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation28727_implies_Equation2 (G : Type*) [Magma G] (h : Equation28727 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X2 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation28733_implies_Equation2 (G : Type*) [Magma G] (h : Equation28733 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq9 eq9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq9 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq9 eq12
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq11 eq7
  have eq34 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq11 eq26
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq34 eq14
  have eq37 (X0 X1 X2 : G) : ((((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) ◇ X2) ◇ X0) = X2 := superpose eq35 eq10
  have eq40 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) ◇ X0) = X2 := superpose eq35 eq37
  have eq41 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) = X2 := superpose eq35 eq40
  have eq42 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X2 := superpose eq35 eq41
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq11 eq42
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq43 eq43
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq62 eq56


@[equational_result]
theorem Equation28735_implies_Equation2 (G : Type*) [Magma G] (h : Equation28735 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq10
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = X0 := superpose eq13 eq7
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X1)) = X0 := superpose eq13 eq18
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq39 eq31


@[equational_result]
theorem Equation28737_implies_Equation2 (G : Type*) [Magma G] (h : Equation28737 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq24 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq10
  have eq35 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq24 eq11
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq24 eq35
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq37 eq37
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq59 eq44


@[equational_result]
theorem Equation28743_implies_Equation2 (G : Type*) [Magma G] (h : Equation28743 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq9 eq9
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq9 eq7
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq7
  have eq23 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = X0 := superpose eq20 eq12
  have eq26 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ (((X1 ◇ X1) ◇ X0) ◇ X1)) ◇ X0) = X2 := superpose eq23 eq10
  have eq29 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X2 := superpose eq23 eq26
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq20 eq29
  have eq31 (X0 X1 : G) : X0 = X1 := superpose eq11 eq30
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq38 eq31


@[equational_result]
theorem Equation28745_implies_Equation2 (G : Type*) [Magma G] (h : Equation28745 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq7 eq10
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X1)) = X0 := superpose eq13 eq7
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq35 eq27


@[equational_result]
theorem Equation28746_implies_Equation2 (G : Type*) [Magma G] (h : Equation28746 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq9 eq9
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X2)) = X0 := superpose eq11 eq7
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq33 eq24


@[equational_result]
theorem Equation28747_implies_Equation2 (G : Type*) [Magma G] (h : Equation28747 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq14 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq10 eq21
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation28749_implies_Equation2 (G : Type*) [Magma G] (h : Equation28749 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ X2) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose eq7 eq10
  have eq13 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq27 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq7
  have eq29 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq27 eq13
  have eq32 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ X2) = ((((X0 ◇ X1) ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)) ◇ X3) ◇ X0) := superpose eq29 eq11
  have eq35 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq29 eq7
  have eq38 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq29 eq12
  have eq50 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = ((((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) ◇ X0) := superpose eq29 eq32
  have eq53 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq29 eq38
  have eq54 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq53 eq35
  have eq59 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X2) = (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) ◇ X0) := superpose eq53 eq50
  have eq62 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq53 eq54
  have eq63 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq53 eq62
  have eq67 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq63 eq59
  have eq68 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq53 eq67
  have eq69 (X0 X3 : G) : X0 = X3 := superpose eq68 eq68
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq74 eq69


@[equational_result]
theorem Equation28751_implies_Equation2 (G : Type*) [Magma G] (h : Equation28751 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = ((X0 ◇ X3) ◇ ((X0 ◇ X2) ◇ X4)) := superpose eq7 eq7
  have eq10 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X3)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq30 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq32 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq13 eq30
  have eq35 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq32 eq13
  have eq43 (X0 X1 : G) : X0 = X1 := superpose eq32 eq35
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq45 eq43


@[equational_result]
theorem Equation28753_implies_Equation2 (G : Type*) [Magma G] (h : Equation28753 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq36 eq13


@[equational_result]
theorem Equation28754_implies_Equation2 (G : Type*) [Magma G] (h : Equation28754 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X0)) = ((X0 ◇ X2) ◇ (((X1 ◇ X1) ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq10 eq7
  have eq36 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq9 eq10
  have eq58 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := superpose eq7 eq14
  have eq81 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) := superpose eq14 eq10
  have eq135 (X0 X1 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq58 eq58
  have eq174 (X0 X1 X2 : G) : (X0 ◇ X2) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq135 eq81
  have eq213 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X2) = (X0 ◇ X2) := superpose eq174 eq36
  have eq216 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = X0 := superpose eq213 eq7
  have eq291 (X0 X3 : G) : X0 = X3 := superpose eq216 eq216
  have eq311 (X0 : G) : sK0 ≠ X0 := superpose eq291 eq8
  subsumption eq311 eq291


@[equational_result]
theorem Equation28755_implies_Equation2 (G : Type*) [Magma G] (h : Equation28755 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X3)) = X1 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq62 eq16


@[equational_result]
theorem Equation28758_implies_Equation2 (G : Type*) [Magma G] (h : Equation28758 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X3) ◇ (X3 ◇ X3)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq34 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := superpose eq11 eq9
  have eq40 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq9 eq34
  have eq41 (X0 X2 : G) : X0 = X2 := superpose eq7 eq40
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq142 eq41


@[equational_result]
theorem Equation28759_implies_Equation2 (G : Type*) [Magma G] (h : Equation28759 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (((X0 ◇ X2) ◇ X3) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ (((X3 ◇ X3) ◇ X0) ◇ X4)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X4)) = X2 := superpose eq7 eq9
  have eq23 (X0 X2 X3 : G) : ((X3 ◇ X3) ◇ X0) = X2 := superpose eq15 eq12
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq7 eq23
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq52 eq30


@[equational_result]
theorem Equation28761_implies_Equation2 (G : Type*) [Magma G] (h : Equation28761 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq66 eq18


@[equational_result]
theorem Equation28762_implies_Equation2 (G : Type*) [Magma G] (h : Equation28762 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ X3) ◇ X4) ◇ (X5 ◇ X4)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X3 ◇ (X2 ◇ X1))) = X1 := superpose eq7 eq7
  have eq15 (X0 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X3 ◇ X2))) = X2 := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X2 ◇ (X3 ◇ X0)))) = X1 := superpose eq11 eq9
  have eq40 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq15 eq34
  have eq41 (X0 X3 : G) : X0 = X3 := superpose eq7 eq40
  have eq111 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq111 eq41


@[equational_result]
theorem Equation28763_implies_Equation2 (G : Type*) [Magma G] (h : Equation28763 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ (X3 ◇ X3)) = X1 := superpose eq7 eq7
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation28764_implies_Equation2 (G : Type*) [Magma G] (h : Equation28764 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X0) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : ((X0 ◇ X0) ◇ (X4 ◇ X5)) = X1 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation28772_implies_Equation2 (G : Type*) [Magma G] (h : Equation28772 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ X1) ◇ (X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq74 (X0 X1 X2 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ X1) ◇ X2) = X1 := superpose eq9 eq11
  have eq107 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq15 eq74
  have eq116 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq107 eq15
  have eq125 (X0 X3 : G) : X0 = X3 := superpose eq116 eq116
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq125 eq8
  subsumption eq133 eq125


@[equational_result]
theorem Equation28773_implies_Equation2 (G : Type*) [Magma G] (h : Equation28773 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) ◇ (X2 ◇ X2)) = X1 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ ((X0 ◇ X0) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) ◇ ((X2 ◇ X2) ◇ X2)) = X1 := superpose eq7 eq10
  have eq13 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = X2 := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X1) = ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq7 eq9
  have eq22 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = X2 := superpose eq9 eq9
  have eq53 (X0 X1 X2 X3 X4 : G) : ((((((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X1)) ◇ X2) ◇ ((((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X1)) ◇ X2) ◇ (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X1)) ◇ X2))) ◇ X3) ◇ (X4 ◇ X4)) = X3 := superpose eq19 eq9
  have eq78 (X0 X2 X3 X4 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ (((X0 ◇ X0) ◇ X0) ◇ X2))) ◇ X3) ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq53
  have eq79 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X4 ◇ X4)) = X3 := superpose eq7 eq78
  have eq81 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X2) ◇ X2)) = X1 := superpose eq79 eq11
  have eq82 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq79 eq13
  have eq83 (X0 X1 X2 : G) : (((((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1))) ◇ X2) ◇ X0) = X2 := superpose eq79 eq22
  have eq97 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq82 eq83
  have eq98 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq81 eq97
  have eq99 (X0 X3 : G) : X0 = X3 := superpose eq7 eq98
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq99 eq8
  subsumption eq125 eq99


@[equational_result]
theorem Equation28774_implies_Equation2 (G : Type*) [Magma G] (h : Equation28774 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) ◇ X2) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq25 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X5)) = X3 := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X0) ◇ X0) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (X3 ◇ X4)) = X2 := superpose eq11 eq9
  have eq40 (X0 X2 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X2 := superpose eq25 eq29
  have eq46 (X0 X4 : G) : X0 = X4 := superpose eq7 eq40
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq112 eq46


@[equational_result]
theorem Equation28777_implies_Equation2 (G : Type*) [Magma G] (h : Equation28777 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X2 ◇ X2) ◇ X2) ◇ X2) = ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq17 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ X1) = X0 := superpose eq7 eq10
  have eq36 (X0 X2 : G) : X0 = X2 := superpose eq17 eq17
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq57 eq36


@[equational_result]
theorem Equation28779_implies_Equation2 (G : Type*) [Magma G] (h : Equation28779 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation28780_implies_Equation2 (G : Type*) [Magma G] (h : Equation28780 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28782_implies_Equation2 (G : Type*) [Magma G] (h : Equation28782 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28783_implies_Equation2 (G : Type*) [Magma G] (h : Equation28783 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation28784_implies_Equation2 (G : Type*) [Magma G] (h : Equation28784 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28786_implies_Equation2 (G : Type*) [Magma G] (h : Equation28786 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)))) = X2 := superpose eq7 eq10
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))) = X2 := superpose eq10 eq10
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X2 := superpose eq10 eq7
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq12
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X2 := superpose eq22 eq13
  have eq29 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq20 eq23
  have eq47 (X0 X3 : G) : X0 = X3 := superpose eq29 eq29
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq61 eq47


@[equational_result]
theorem Equation28787_implies_Equation2 (G : Type*) [Magma G] (h : Equation28787 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ X2) ◇ (X3 ◇ X2)) = X3 := superpose eq7 eq7
  have eq31 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X2)))) = X3 := superpose eq7 eq9
  have eq89 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := superpose eq31 eq31
  have eq114 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X1) ◇ X1) ◇ (((X1 ◇ X1) ◇ X1) ◇ X2)) ◇ (X0 ◇ (X3 ◇ (((X4 ◇ X4) ◇ X4) ◇ X5)))) ◇ X0) = X3 := superpose eq31 eq9
  have eq125 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq89
  have eq172 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq125 eq114
  have eq272 (X0 X2 : G) : X0 = X2 := superpose eq172 eq172
  have eq356 (X0 : G) : sK0 ≠ X0 := superpose eq272 eq8
  subsumption eq356 eq272


@[equational_result]
theorem Equation28788_implies_Equation2 (G : Type*) [Magma G] (h : Equation28788 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X3) ◇ X3) ◇ X4) = ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq41 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X1) ◇ X2) = X0 := superpose eq7 eq11
  have eq97 (X0 X3 : G) : X0 = X3 := superpose eq10 eq41
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq97 eq8
  subsumption eq132 eq97


@[equational_result]
theorem Equation28790_implies_Equation2 (G : Type*) [Magma G] (h : Equation28790 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation28791_implies_Equation2 (G : Type*) [Magma G] (h : Equation28791 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28792_implies_Equation2 (G : Type*) [Magma G] (h : Equation28792 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28794_implies_Equation2 (G : Type*) [Magma G] (h : Equation28794 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28795_implies_Equation2 (G : Type*) [Magma G] (h : Equation28795 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28796_implies_Equation2 (G : Type*) [Magma G] (h : Equation28796 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28798_implies_Equation2 (G : Type*) [Magma G] (h : Equation28798 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28799_implies_Equation2 (G : Type*) [Magma G] (h : Equation28799 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28800_implies_Equation2 (G : Type*) [Magma G] (h : Equation28800 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28801_implies_Equation2 (G : Type*) [Magma G] (h : Equation28801 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28807_implies_Equation2 (G : Type*) [Magma G] (h : Equation28807 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq37 (X0 X2 : G) : X0 = X2 := superpose eq13 eq13
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq92 eq37


@[equational_result]
theorem Equation28809_implies_Equation2 (G : Type*) [Magma G] (h : Equation28809 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq62 (X0 X3 : G) : X0 = X3 := superpose eq29 eq29
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq78 eq62


@[equational_result]
theorem Equation28812_implies_Equation2 (G : Type*) [Magma G] (h : Equation28812 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq34 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ (X0 ◇ X0))) = X3 := superpose eq10 eq9
  have eq188 (X0 X2 X3 : G) : (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X3))) := superpose eq34 eq34
  have eq316 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq34 eq188
  have eq458 (X0 X2 : G) : X0 = X2 := superpose eq316 eq316
  have eq650 (X0 : G) : sK0 ≠ X0 := superpose eq458 eq8
  subsumption eq650 eq458


@[equational_result]
theorem Equation28813_implies_Equation2 (G : Type*) [Magma G] (h : Equation28813 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X3) ◇ ((X1 ◇ X2) ◇ X4)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X3) ◇ X0)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq31 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X3) ◇ (((X1 ◇ X2) ◇ X4) ◇ X5)) = X3 := superpose eq7 eq9
  have eq51 (X0 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = (X0 ◇ X2) := superpose eq9 eq10
  have eq75 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X0 ◇ X1) ◇ X4) ◇ ((((X2 ◇ X2) ◇ X3) ◇ X5) ◇ X6)) = X4 := superpose eq51 eq9
  have eq77 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ (((X2 ◇ X2) ◇ X3) ◇ X5)) = X4 := superpose eq51 eq7
  have eq118 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X2) ◇ (((X3 ◇ X3) ◇ X4) ◇ X5))) ◇ X6) ◇ X5) = X6 := superpose eq11 eq11
  have eq143 (X0 X2 X5 X6 : G) : ((((X0 ◇ X0) ◇ X2) ◇ X6) ◇ X5) = X6 := superpose eq77 eq118
  have eq144 (X0 X1 X4 X5 : G) : (((X0 ◇ X1) ◇ X4) ◇ X5) = X4 := superpose eq143 eq75
  have eq153 (X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X4) ◇ X5)) = X3 := superpose eq144 eq31
  have eq172 (X1 X3 X4 : G) : (X1 ◇ X4) = X3 := superpose eq144 eq153
  have eq176 (X0 X3 : G) : X0 = X3 := superpose eq172 eq172
  have eq228 (X0 : G) : sK0 ≠ X0 := superpose eq176 eq8
  subsumption eq228 eq176


@[equational_result]
theorem Equation28815_implies_Equation2 (G : Type*) [Magma G] (h : Equation28815 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X0 ◇ (X3 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq58 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq147 eq58


@[equational_result]
theorem Equation28816_implies_Equation2 (G : Type*) [Magma G] (h : Equation28816 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ X1)) = (X0 ◇ (X3 ◇ X0)) := superpose eq7 eq7
  have eq26 (X0 X3 X4 : G) : (X3 ◇ (X4 ◇ X3)) = X0 := superpose eq7 eq11
  have eq58 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq126 eq58


@[equational_result]
theorem Equation28817_implies_Equation2 (G : Type*) [Magma G] (h : Equation28817 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X2) = (X0 ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq63 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq147 eq63


@[equational_result]
theorem Equation28818_implies_Equation2 (G : Type*) [Magma G] (h : Equation28818 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 X5 : G) : (X2 ◇ X3) = (X0 ◇ (X4 ◇ X5)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation28820_implies_Equation2 (G : Type*) [Magma G] (h : Equation28820 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : (((((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = X1 := superpose eq10 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = X2 := superpose eq10 eq7
  have eq20 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq13 eq7
  have eq22 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = X1 := superpose eq13 eq15
  have eq24 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq16 eq22
  have eq30 (X0 X1 : G) : X0 = X1 := superpose eq20 eq24
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq66 eq30


@[equational_result]
theorem Equation28822_implies_Equation2 (G : Type*) [Magma G] (h : Equation28822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq54 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq142 eq54


@[equational_result]
theorem Equation28824_implies_Equation2 (G : Type*) [Magma G] (h : Equation28824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation28825_implies_Equation2 (G : Type*) [Magma G] (h : Equation28825 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28826_implies_Equation2 (G : Type*) [Magma G] (h : Equation28826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28828_implies_Equation2 (G : Type*) [Magma G] (h : Equation28828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28829_implies_Equation2 (G : Type*) [Magma G] (h : Equation28829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation28830_implies_Equation2 (G : Type*) [Magma G] (h : Equation28830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28832_implies_Equation2 (G : Type*) [Magma G] (h : Equation28832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28833_implies_Equation2 (G : Type*) [Magma G] (h : Equation28833 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28834_implies_Equation2 (G : Type*) [Magma G] (h : Equation28834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28835_implies_Equation2 (G : Type*) [Magma G] (h : Equation28835 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X1) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28838_implies_Equation2 (G : Type*) [Magma G] (h : Equation28838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) ◇ (X3 ◇ X2)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X2) ◇ X2) = ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X3) ◇ X3) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq9
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq9
  have eq31 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X1) = (((X2 ◇ X2) ◇ X1) ◇ X1) := superpose eq10 eq10
  have eq42 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) = (((X3 ◇ X3) ◇ X2) ◇ X2) := superpose eq7 eq31
  have eq69 (X0 X1 X2 X3 : G) : ((X3 ◇ X3) ◇ X1) = ((((X2 ◇ X2) ◇ X1) ◇ X1) ◇ (((X0 ◇ X0) ◇ X1) ◇ X1)) := superpose eq31 eq7
  have eq88 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X2) ◇ (X3 ◇ X2)) = X3 := superpose eq7 eq11
  have eq180 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X4) ◇ (X2 ◇ (X3 ◇ X3))) = ((X2 ◇ (X2 ◇ (X3 ◇ X3))) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X1)) := superpose eq10 eq13
  have eq193 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X3 ◇ X3))) = (((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X0) := superpose eq13 eq88
  have eq196 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3)))) = ((((X4 ◇ X4) ◇ X0) ◇ X0) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))) := superpose eq13 eq10
  have eq199 (X2 X3 X4 : G) : ((X4 ◇ X4) ◇ (X2 ◇ (X3 ◇ X3))) = ((X2 ◇ (X2 ◇ (X3 ◇ X3))) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))) := superpose eq193 eq180
  have eq200 (X2 X3 X4 : G) : ((X4 ◇ X4) ◇ (X2 ◇ (X3 ◇ X3))) = X2 := superpose eq13 eq199
  have eq216 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ (X3 ◇ X3))) = X2 := superpose eq13 eq200
  have eq273 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ X2) = ((((X4 ◇ X4) ◇ X0) ◇ X0) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))) := superpose eq216 eq196
  have eq274 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X3 ◇ X3))) = (((X1 ◇ X2) ◇ X2) ◇ X0) := superpose eq216 eq193
  have eq292 (X0 X1 X2 X4 : G) : (((X1 ◇ X1) ◇ X2) ◇ X2) = ((((X4 ◇ X4) ◇ X0) ◇ X0) ◇ X2) := superpose eq216 eq273
  have eq293 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq216 eq274
  have eq294 (X1 X3 : G) : ((X3 ◇ X3) ◇ X1) = X1 := superpose eq293 eq69
  have eq316 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X0) = (X2 ◇ X2) := superpose eq294 eq10
  have eq327 (X1 X2 X3 : G) : (((X3 ◇ X3) ◇ X2) ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq294 eq42
  have eq346 (X0 X2 X4 : G) : (X2 ◇ X2) = ((((X4 ◇ X4) ◇ X0) ◇ X0) ◇ X2) := superpose eq294 eq292
  have eq348 (X0 X2 : G) : (X2 ◇ X2) = (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq294 eq316
  have eq353 (X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq294 eq327
  have eq380 (X0 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X0) ◇ X2) := superpose eq353 eq346
  have eq381 (X2 : G) : (X2 ◇ X2) = X2 := superpose eq294 eq380
  have eq383 (X0 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X2) ◇ X0) := superpose eq381 eq348
  have eq387 (X1 X3 : G) : (X3 ◇ X1) = X1 := superpose eq381 eq294
  have eq392 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq381 eq383
  have eq397 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq387 eq392
  have eq399 (X0 X1 : G) : X0 = X1 := superpose eq397 eq387
  have eq401 (X0 : G) : sK0 ≠ X0 := superpose eq399 eq8
  subsumption eq401 eq399


@[equational_result]
theorem Equation28839_implies_Equation2 (G : Type*) [Magma G] (h : Equation28839 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq10 eq10
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq131 eq35


@[equational_result]
theorem Equation28841_implies_Equation2 (G : Type*) [Magma G] (h : Equation28841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation28842_implies_Equation2 (G : Type*) [Magma G] (h : Equation28842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28843_implies_Equation2 (G : Type*) [Magma G] (h : Equation28843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28845_implies_Equation2 (G : Type*) [Magma G] (h : Equation28845 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28846_implies_Equation2 (G : Type*) [Magma G] (h : Equation28846 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation28847_implies_Equation2 (G : Type*) [Magma G] (h : Equation28847 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28849_implies_Equation2 (G : Type*) [Magma G] (h : Equation28849 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28850_implies_Equation2 (G : Type*) [Magma G] (h : Equation28850 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28851_implies_Equation2 (G : Type*) [Magma G] (h : Equation28851 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28852_implies_Equation2 (G : Type*) [Magma G] (h : Equation28852 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28854_implies_Equation2 (G : Type*) [Magma G] (h : Equation28854 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X1))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq11
  have eq25 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq14 eq11
  have eq26 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq39 eq26


@[equational_result]
theorem Equation28855_implies_Equation2 (G : Type*) [Magma G] (h : Equation28855 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ (X0 ◇ X2))) = X4 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X0) = X4 := superpose eq11 eq10
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq11 eq13
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq42 eq26


@[equational_result]
theorem Equation28856_implies_Equation2 (G : Type*) [Magma G] (h : Equation28856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X3)) = X4 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq11
  have eq35 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq23 eq11
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq10 eq35
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq100 eq39


@[equational_result]
theorem Equation28857_implies_Equation2 (G : Type*) [Magma G] (h : Equation28857 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq30 (X0 X5 : G) : X0 = X5 := superpose eq7 eq14
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq95 eq30


@[equational_result]
theorem Equation28859_implies_Equation2 (G : Type*) [Magma G] (h : Equation28859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28860_implies_Equation2 (G : Type*) [Magma G] (h : Equation28860 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28861_implies_Equation2 (G : Type*) [Magma G] (h : Equation28861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28862_implies_Equation2 (G : Type*) [Magma G] (h : Equation28862 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28864_implies_Equation2 (G : Type*) [Magma G] (h : Equation28864 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28865_implies_Equation2 (G : Type*) [Magma G] (h : Equation28865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28866_implies_Equation2 (G : Type*) [Magma G] (h : Equation28866 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28867_implies_Equation2 (G : Type*) [Magma G] (h : Equation28867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28869_implies_Equation2 (G : Type*) [Magma G] (h : Equation28869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28870_implies_Equation2 (G : Type*) [Magma G] (h : Equation28870 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28871_implies_Equation2 (G : Type*) [Magma G] (h : Equation28871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28872_implies_Equation2 (G : Type*) [Magma G] (h : Equation28872 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28874_implies_Equation2 (G : Type*) [Magma G] (h : Equation28874 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28875_implies_Equation2 (G : Type*) [Magma G] (h : Equation28875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28876_implies_Equation2 (G : Type*) [Magma G] (h : Equation28876 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28877_implies_Equation2 (G : Type*) [Magma G] (h : Equation28877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28878_implies_Equation2 (G : Type*) [Magma G] (h : Equation28878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X1) ◇ X2) ◇ X3) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation28884_implies_Equation2 (G : Type*) [Magma G] (h : Equation28884 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq11 eq7
  have eq16 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq14
  have eq17 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (X0 ◇ (((X1 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)) ◇ ((X1 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X0)))) := superpose eq7 eq10
  have eq26 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq10
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq26 eq16
  have eq46 (X0 X1 X3 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) := superpose eq35 eq17
  have eq57 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq35 eq46
  have eq61 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq57
  have eq80 (X0 X2 : G) : X0 = X2 := superpose eq61 eq61
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq80 eq8
  subsumption eq113 eq80


@[equational_result]
theorem Equation28886_implies_Equation2 (G : Type*) [Magma G] (h : Equation28886 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ X3) ◇ X4) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X4 X5 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X4) ◇ X5)) := superpose eq11 eq11
  have eq16 (X0 X1 X2 X5 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X5)) := superpose eq11 eq11
  have eq18 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq11 eq11
  have eq20 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ X3)) ◇ (X0 ◇ X4)) := superpose eq11 eq7
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X2) ◇ X3) = ((X0 ◇ X1) ◇ (X0 ◇ X4)) := superpose eq14 eq20
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X3) := superpose eq18 eq24
  have eq26 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq25 eq16
  have eq29 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X4) ◇ X0) = X4 := superpose eq25 eq12
  have eq39 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq26 eq29
  have eq40 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X4 := superpose eq26 eq39
  have eq41 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq26 eq40
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq41 eq41
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq46 eq44


@[equational_result]
theorem Equation28889_implies_Equation2 (G : Type*) [Magma G] (h : Equation28889 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ X3) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X2 ◇ X2) = ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ ((((X2 ◇ X1) ◇ X0) ◇ X0) ◇ (((X2 ◇ X1) ◇ X0) ◇ X0))) := superpose eq7 eq10
  have eq27 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq10 eq9
  have eq213 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq27 eq13
  have eq227 (X0 X2 : G) : X0 = X2 := superpose eq213 eq213
  have eq367 (X0 : G) : sK0 ≠ X0 := superpose eq227 eq8
  subsumption eq367 eq227


@[equational_result]
theorem Equation28890_implies_Equation2 (G : Type*) [Magma G] (h : Equation28890 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ X4) ◇ ((X2 ◇ X3) ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X2 ◇ X3) = ((X0 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X4)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq9
  have eq28 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = (X0 ◇ ((((X3 ◇ X1) ◇ X0) ◇ X0) ◇ X4)) := superpose eq7 eq10
  have eq42 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X0) := superpose eq19 eq28
  have eq46 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq7 eq42
  have eq105 (X0 X2 : G) : X0 = X2 := superpose eq9 eq46
  have eq209 (X0 : G) : sK0 ≠ X0 := superpose eq105 eq8
  subsumption eq209 eq105


@[equational_result]
theorem Equation28892_implies_Equation2 (G : Type*) [Magma G] (h : Equation28892 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ X4) ◇ (X5 ◇ (((X1 ◇ X2) ◇ X0) ◇ X0))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq11
  have eq25 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ X4) ◇ (X5 ◇ ((X1 ◇ X2) ◇ X0))) = X4 := superpose eq17 eq9
  have eq30 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ X4) ◇ (X5 ◇ (X1 ◇ X2))) = X4 := superpose eq17 eq25
  have eq31 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ (X1 ◇ X2))) = X4 := superpose eq17 eq30
  have eq32 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq31 eq11
  have eq34 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq32 eq17
  have eq51 (X0 X1 : G) : X0 = X1 := superpose eq32 eq34
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq53 eq51


@[equational_result]
theorem Equation28893_implies_Equation2 (G : Type*) [Magma G] (h : Equation28893 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ X4) ◇ (X5 ◇ (X3 ◇ X2))) = X4 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : (X3 ◇ X2) = ((X0 ◇ (X3 ◇ X2)) ◇ (X4 ◇ X0)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq9
  have eq31 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = (((X3 ◇ X4) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq7 eq10
  have eq35 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X2)) := superpose eq10 eq7
  have eq42 (X0 X2 X3 X4 : G) : (X3 ◇ X2) = ((X0 ◇ (X3 ◇ X2)) ◇ X4) := superpose eq7 eq19
  have eq61 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq42 eq35
  have eq63 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq61 eq31
  have eq73 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X2)) = X0 := superpose eq63 eq7
  have eq74 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq63 eq19
  have eq76 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X2)) = X0 := superpose eq63 eq73
  have eq77 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq74 eq63
  have eq81 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = X0 := superpose eq77 eq76
  have eq83 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq77 eq81
  have eq111 (X0 X2 : G) : X0 = X2 := superpose eq83 eq83
  have eq113 (X0 : G) : sK0 ≠ X0 := superpose eq111 eq8
  subsumption eq113 eq111


@[equational_result]
theorem Equation28894_implies_Equation2 (G : Type*) [Magma G] (h : Equation28894 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X3 ◇ X3) = ((X0 ◇ (X3 ◇ X3)) ◇ (X4 ◇ X4)) := superpose eq7 eq7
  have eq30 (X0 X1 X4 : G) : (X1 ◇ X1) = (X0 ◇ (X4 ◇ X4)) := superpose eq7 eq10
  have eq55 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq30
  have eq91 (X0 X2 : G) : X0 = X2 := superpose eq55 eq55
  have eq205 (X0 : G) : sK0 ≠ X0 := superpose eq91 eq8
  subsumption eq205 eq91


@[equational_result]
theorem Equation28895_implies_Equation2 (G : Type*) [Magma G] (h : Equation28895 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X4 X5 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X4 ◇ X5)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq11
  have eq41 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq26 eq12
  have eq45 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq26 eq41
  have eq50 (X0 X4 : G) : X0 = X4 := superpose eq45 eq45
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq83 eq50


@[equational_result]
theorem Equation28897_implies_Equation2 (G : Type*) [Magma G] (h : Equation28897 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X0) ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X0) ◇ X1) = (((((X0 ◇ X1) ◇ X2) ◇ (((X1 ◇ X3) ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq11 eq7
  have eq14 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq7
  have eq18 (X0 X1 : G) : ((X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0))) = X0 := superpose eq11 eq10
  have eq21 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq11 eq10
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0)) ◇ X0)) := superpose eq7 eq10
  have eq24 (X0 X1 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq11 eq10
  have eq31 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq11 eq14
  have eq42 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) = X2 := superpose eq14 eq7
  have eq49 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X4) ◇ X0)))) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X4) ◇ X0))))) = X3 := superpose eq10 eq9
  have eq57 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq11 eq9
  have eq75 (X0 : G) : ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose eq11 eq21
  have eq112 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (((((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq11 eq12
  have eq121 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ ((((X2 ◇ X0) ◇ X4) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (X2 ◇ X0))) ◇ X2) = (((((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X5) ◇ (((X2 ◇ X3) ◇ ((((X2 ◇ X0) ◇ X4) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (X2 ◇ X0))) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ ((((X2 ◇ X0) ◇ X4) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0)) ◇ (X2 ◇ X0))) := superpose eq12 eq12
  have eq136 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq31 eq10
  have eq160 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) = X0 := superpose eq21 eq13
  have eq221 (X0 X1 : G) : (((X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq18 eq21
  have eq392 (X0 X1 : G) : ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) ◇ (X0 ◇ X1)) = (((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) ◇ (((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq11 eq22
  have eq1043 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq10 eq221
  have eq1084 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) = (((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2))) ◇ ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) := superpose eq57 eq57
  have eq1614 (X0 X1 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq42 eq49
  have eq1679 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq160 eq1614
  have eq1699 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq1679 eq75
  have eq1700 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq1679 eq136
  have eq1714 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1699 eq1700
  have eq1716 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) = (((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) := superpose eq1714 eq1084
  have eq1744 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq1714 eq24
  have eq1746 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (((((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq1714 eq112
  have eq1750 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq1714 eq392
  have eq1755 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq1714 eq1043
  have eq2098 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) = (((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) := superpose eq1714 eq1716
  have eq2099 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) = (((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) := superpose eq1714 eq2098
  have eq2100 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) = ((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) := superpose eq1714 eq2099
  have eq2143 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq1714 eq1744
  have eq2144 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq1714 eq2143
  have eq2147 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq1714 eq1746
  have eq2152 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq1714 eq1750
  have eq2157 (X0 X1 : G) : (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq2144 eq1755
  have eq2158 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq2157 eq2152
  have eq2160 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq2157 eq2158
  have eq2163 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq2160 eq2144
  have eq2166 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq1714 eq2163
  have eq2167 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq2166 eq2147
  have eq2170 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0)) = ((((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0))) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) := superpose eq2166 eq2100
  have eq2460 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq2166 eq2167
  have eq2461 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq2166 eq2460
  have eq2468 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) = (((((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq2166 eq2170
  have eq2469 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq2461 eq2468
  have eq2470 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq1714 eq2469
  have eq2471 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq2461 eq2470
  have eq2472 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq2471 eq7
  have eq2497 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ ((((X2 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X0))) ◇ X2) = ((((((X0 ◇ X1) ◇ X2) ◇ X5) ◇ (((X2 ◇ X3) ◇ ((((X2 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X0))) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((((X2 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X0))) := superpose eq2471 eq121
  have eq2805 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq2471 eq2472
  have eq2890 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ (((X2 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X2) = ((((((X0 ◇ X1) ◇ X2) ◇ X5) ◇ (((X2 ◇ X3) ◇ (((X2 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2))) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (((X2 ◇ X0) ◇ X4) ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq2471 eq2497
  have eq2891 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ ((X2 ◇ X0) ◇ X4)) ◇ X2) = ((((((X0 ◇ X1) ◇ X2) ◇ X5) ◇ (((X2 ◇ X3) ◇ ((X2 ◇ X0) ◇ X4)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X2 ◇ X0) ◇ X4)) := superpose eq2471 eq2890
  have eq2892 (X0 X1 X2 X3 X5 : G) : (((X2 ◇ X3) ◇ (X2 ◇ X0)) ◇ X2) = ((((((X0 ◇ X1) ◇ X2) ◇ X5) ◇ (((X2 ◇ X3) ◇ (X2 ◇ X0)) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq2471 eq2891
  have eq2893 (X0 X1 X2 X3 X5 : G) : (((X2 ◇ X3) ◇ (X2 ◇ X0)) ◇ X2) = (((((X0 ◇ X1) ◇ X2) ◇ X5) ◇ (((X2 ◇ X3) ◇ (X2 ◇ X0)) ◇ X2)) ◇ (X2 ◇ X0)) := superpose eq2471 eq2892
  have eq2894 (X0 X1 X2 X3 X5 : G) : (((X2 ◇ X3) ◇ (X2 ◇ X0)) ◇ X2) = ((((X0 ◇ X1) ◇ X2) ◇ X5) ◇ (X2 ◇ X0)) := superpose eq2471 eq2893
  have eq2895 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X0)) = (((X2 ◇ X3) ◇ (X2 ◇ X0)) ◇ X2) := superpose eq2471 eq2894
  have eq2896 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X0)) := superpose eq2471 eq2895
  have eq2897 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X0)) := superpose eq2471 eq2896
  have eq2898 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X2 := superpose eq2805 eq2897
  have eq2899 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq2898 eq2166
  have eq2901 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq2899 eq2805
  have eq2913 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq2899 eq2901
  have eq3014 (X0 X1 : G) : X0 = X1 := superpose eq2913 eq2899
  have eq3024 (X0 : G) : sK0 ≠ X0 := superpose eq3014 eq8
  subsumption eq3024 eq3014


@[equational_result]
theorem Equation28899_implies_Equation2 (G : Type*) [Magma G] (h : Equation28899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ ((X0 ◇ X3) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0) := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X0) = X0 := superpose eq11 eq7
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X1) = X0 := superpose eq15 eq13
  have eq48 (X0 X2 X3 X4 : G) : ((X0 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X0 ◇ X4)) = X0 := superpose eq11 eq10
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X0)) = ((X0 ◇ ((X4 ◇ X5) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq10 eq10
  have eq52 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ ((X2 ◇ X3) ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq11 eq10
  have eq58 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ X0)) = X0 := superpose eq48 eq51
  have eq63 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq58 eq52
  have eq64 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq11 eq63
  have eq65 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq64 eq18
  have eq73 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq64 eq65
  have eq76 (X0 X2 : G) : X0 = X2 := superpose eq73 eq73
  have eq84 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq84 eq76


@[equational_result]
theorem Equation28901_implies_Equation2 (G : Type*) [Magma G] (h : Equation28901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq34 eq14


@[equational_result]
theorem Equation28902_implies_Equation2 (G : Type*) [Magma G] (h : Equation28902 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq10 eq10
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq10 eq14
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq32 eq23


@[equational_result]
theorem Equation28903_implies_Equation2 (G : Type*) [Magma G] (h : Equation28903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X3)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ X3) ◇ X4) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) ◇ X0) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq11 eq12
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq50 eq19


@[equational_result]
theorem Equation28906_implies_Equation2 (G : Type*) [Magma G] (h : Equation28906 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq46 eq13


@[equational_result]
theorem Equation28907_implies_Equation2 (G : Type*) [Magma G] (h : Equation28907 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X1 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq66 eq16


@[equational_result]
theorem Equation28909_implies_Equation2 (G : Type*) [Magma G] (h : Equation28909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq43 eq17


@[equational_result]
theorem Equation28910_implies_Equation2 (G : Type*) [Magma G] (h : Equation28910 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X1 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation28911_implies_Equation2 (G : Type*) [Magma G] (h : Equation28911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X1 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq59 eq14


@[equational_result]
theorem Equation28912_implies_Equation2 (G : Type*) [Magma G] (h : Equation28912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X1) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X1 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation28915_implies_Equation2 (G : Type*) [Magma G] (h : Equation28915 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ X0) ◇ X2) = ((((X1 ◇ (X0 ◇ X2)) ◇ (((X3 ◇ X2) ◇ X0) ◇ X2)) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq10
  have eq22 (X0 X1 X2 X3 : G) : (((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq9
  have eq23 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X2) = (((X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X2)) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq9
  have eq34 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq10 eq12
  have eq35 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq37 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq12 eq9
  have eq80 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq35 eq7
  have eq84 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = ((((X2 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) ◇ X0) ◇ X0) := superpose eq35 eq11
  have eq244 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = (((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq37 eq9
  have eq290 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) = ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1)) := superpose eq12 eq22
  have eq390 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq34 eq23
  have eq445 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq10 eq390
  have eq446 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq10 eq445
  have eq447 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq34 eq446
  have eq450 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = ((((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) ◇ X0) := superpose eq447 eq84
  have eq451 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq447 eq80
  have eq474 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X2 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := superpose eq447 eq450
  have eq475 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq447 eq451
  have eq477 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq475 eq474
  have eq480 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq477 eq244
  have eq529 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) = (X1 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X1)) := superpose eq477 eq290
  have eq592 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq477 eq480
  have eq681 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) = X1 := superpose eq592 eq529
  have eq682 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3) = X1 := superpose eq477 eq681
  have eq683 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X1 := superpose eq477 eq682
  have eq684 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq477 eq683
  have eq685 (X0 X1 : G) : X0 = X1 := superpose eq35 eq684
  have eq690 (X0 : G) : sK0 ≠ X0 := superpose eq685 eq8
  subsumption eq690 eq685


@[equational_result]
theorem Equation28916_implies_Equation2 (G : Type*) [Magma G] (h : Equation28916 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ X3) = ((X0 ◇ X2) ◇ ((X0 ◇ X3) ◇ X4)) := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq10 eq10
  have eq43 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ X2) ◇ X3) = ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X5)) := superpose eq10 eq29
  have eq76 (X0 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ X2) ◇ X3) := superpose eq10 eq43
  have eq77 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq76 eq7
  have eq102 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = X0 := superpose eq76 eq77
  have eq103 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq102 eq29
  have eq106 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X3)) = X0 := superpose eq103 eq102
  have eq107 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq103 eq106
  have eq115 (X0 X1 : G) : X0 = X1 := superpose eq107 eq103
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq115 eq8
  subsumption eq125 eq115


@[equational_result]
theorem Equation28919_implies_Equation2 (G : Type*) [Magma G] (h : Equation28919 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ X3) ◇ (X1 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq10 eq11
  have eq31 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq24 eq7
  have eq44 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq24 eq31
  have eq45 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq24 eq44
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq45 eq45
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq50 eq48


@[equational_result]
theorem Equation28920_implies_Equation2 (G : Type*) [Magma G] (h : Equation28920 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ X3) ◇ X4) ◇ X3) ◇ X0) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ X0) = X2 := superpose eq7 eq11
  have eq22 (X0 X2 X4 : G) : (X2 ◇ X0) = X4 := superpose eq17 eq12
  have eq23 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq45 eq23


@[equational_result]
theorem Equation28923_implies_Equation2 (G : Type*) [Magma G] (h : Equation28923 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ (X2 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X2) ◇ (X2 ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : (((X0 ◇ X3) ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) = X3 := superpose eq10 eq9
  have eq13 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq10 eq11
  have eq17 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq7 eq10
  have eq18 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq13 eq10
  have eq31 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq10 eq17
  have eq33 (X2 X3 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X2)) = X3 := superpose eq31 eq12
  have eq35 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq18 eq33
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq50 eq48


@[equational_result]
theorem Equation28924_implies_Equation2 (G : Type*) [Magma G] (h : Equation28924 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X2 ◇ X3) = ((X0 ◇ X2) ◇ (X2 ◇ X4)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq122 eq49


@[equational_result]
theorem Equation28926_implies_Equation2 (G : Type*) [Magma G] (h : Equation28926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X1 ◇ X2))) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq46 eq19


@[equational_result]
theorem Equation28927_implies_Equation2 (G : Type*) [Magma G] (h : Equation28927 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X3 ◇ X2) = ((X0 ◇ X2) ◇ (X4 ◇ X2)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq48 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq121 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq121 eq48


@[equational_result]
theorem Equation28928_implies_Equation2 (G : Type*) [Magma G] (h : Equation28928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X3 ◇ X3)) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq59 eq16


@[equational_result]
theorem Equation28929_implies_Equation2 (G : Type*) [Magma G] (h : Equation28929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X4 ◇ X5)) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq68 eq19


@[equational_result]
theorem Equation28931_implies_Equation2 (G : Type*) [Magma G] (h : Equation28931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X4) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq22 (X0 X1 X2 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X4) ◇ (X1 ◇ X2)) := superpose eq13 eq10
  have eq25 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq13 eq22
  have eq27 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = X0 := superpose eq25 eq7
  have eq30 (X0 X1 X3 : G) : (X3 ◇ X1) = X0 := superpose eq25 eq27
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq30 eq30
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq33 eq31


@[equational_result]
theorem Equation28932_implies_Equation2 (G : Type*) [Magma G] (h : Equation28932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X0 ◇ X2) = ((X0 ◇ X4) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X0) ◇ X3) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq11
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq18 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = X3 := superpose eq11 eq7
  have eq19 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X0) ◇ X3) = X1 := superpose eq14 eq13
  have eq27 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq10 eq10
  have eq30 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq18 eq27
  have eq31 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = X1 := superpose eq30 eq19
  have eq36 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq30 eq31
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq36 eq36
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq42 eq37


@[equational_result]
theorem Equation28933_implies_Equation2 (G : Type*) [Magma G] (h : Equation28933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : (X0 ◇ X3) = ((X0 ◇ X4) ◇ ((X0 ◇ X3) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X3))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ X0) ◇ X5) = ((((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X0) ◇ X5)) ◇ (X0 ◇ X5)) ◇ X0) := superpose eq7 eq7
  have eq34 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X0 ◇ ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X0 ◇ X2))) := superpose eq9 eq10
  have eq40 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq11 eq10
  have eq43 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq10 eq10
  have eq83 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) = ((((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) := superpose eq12 eq12
  have eq95 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) := superpose eq40 eq83
  have eq101 (X0 X1 X2 X3 X6 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X6 ◇ X2)) = X6 := superpose eq12 eq40
  have eq125 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ X3) = (X0 ◇ X0) := superpose eq101 eq34
  have eq128 (X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = (X2 ◇ X2) := superpose eq125 eq95
  have eq134 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := superpose eq10 eq128
  have eq167 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq40 eq134
  have eq168 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq167 eq43
  have eq169 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ X3)) = X0 := superpose eq168 eq7
  have eq220 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq168 eq169
  have eq221 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq168 eq220
  have eq222 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq168 eq221
  have eq233 (X0 X1 : G) : X0 = X1 := superpose eq222 eq168
  have eq235 (X0 : G) : sK0 ≠ X0 := superpose eq233 eq8
  subsumption eq235 eq233


@[equational_result]
theorem Equation28934_implies_Equation2 (G : Type*) [Magma G] (h : Equation28934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ (X3 ◇ X5)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq34 (X0 X5 : G) : X0 = X5 := superpose eq7 eq15
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq90 eq34


@[equational_result]
theorem Equation28936_implies_Equation2 (G : Type*) [Magma G] (h : Equation28936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq51 eq17


@[equational_result]
theorem Equation28937_implies_Equation2 (G : Type*) [Magma G] (h : Equation28937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq10 eq10
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq41 eq18


@[equational_result]
theorem Equation28938_implies_Equation2 (G : Type*) [Magma G] (h : Equation28938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq63 eq18


@[equational_result]
theorem Equation28939_implies_Equation2 (G : Type*) [Magma G] (h : Equation28939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X5)) = X3 := superpose eq7 eq7
  have eq19 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq76 eq19


@[equational_result]
theorem Equation28941_implies_Equation2 (G : Type*) [Magma G] (h : Equation28941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation28942_implies_Equation2 (G : Type*) [Magma G] (h : Equation28942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 : G) : (X0 ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq51 eq13


@[equational_result]
theorem Equation28943_implies_Equation2 (G : Type*) [Magma G] (h : Equation28943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X2 ◇ X3) = ((X0 ◇ X4) ◇ (X3 ◇ X4)) := superpose eq7 eq7
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq33
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq128 eq53


@[equational_result]
theorem Equation28944_implies_Equation2 (G : Type*) [Magma G] (h : Equation28944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ (X0 ◇ X5)) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq61 eq16


@[equational_result]
theorem Equation28946_implies_Equation2 (G : Type*) [Magma G] (h : Equation28946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X1) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation28947_implies_Equation2 (G : Type*) [Magma G] (h : Equation28947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : (X3 ◇ X2) = ((X0 ◇ X4) ◇ (X4 ◇ X3)) := superpose eq7 eq7
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq33
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq128 eq53


@[equational_result]
theorem Equation28948_implies_Equation2 (G : Type*) [Magma G] (h : Equation28948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : (X3 ◇ X3) = ((X0 ◇ X4) ◇ (X4 ◇ X4)) := superpose eq7 eq7
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq7 eq35
  have eq123 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq123 eq57


@[equational_result]
theorem Equation28949_implies_Equation2 (G : Type*) [Magma G] (h : Equation28949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ ((X3 ◇ X4) ◇ X5)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X1 ◇ X2) ◇ X3) ◇ (((X4 ◇ X5) ◇ X0) ◇ X6)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X4 X5 : G) : ((X4 ◇ X5) ◇ X0) = X3 := superpose eq11 eq12
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq48 eq17


@[equational_result]
theorem Equation28951_implies_Equation2 (G : Type*) [Magma G] (h : Equation28951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (X0 ◇ (X5 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq19 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation28952_implies_Equation2 (G : Type*) [Magma G] (h : Equation28952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ (X5 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq61 eq16


@[equational_result]
theorem Equation28953_implies_Equation2 (G : Type*) [Magma G] (h : Equation28953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X0 ◇ (X5 ◇ (X4 ◇ X3))) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq40 eq17


@[equational_result]
theorem Equation28954_implies_Equation2 (G : Type*) [Magma G] (h : Equation28954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ (X5 ◇ X5)) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation28955_implies_Equation2 (G : Type*) [Magma G] (h : Equation28955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X0) ◇ X3) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X3 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation28961_implies_Equation2 (G : Type*) [Magma G] (h : Equation28961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq10 eq10
  have eq13 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq10 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq10 eq12
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq15 eq10
  have eq20 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq15 eq13
  have eq21 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq15 eq20
  have eq23 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = (X0 ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X0))) := superpose eq7 eq17
  have eq29 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) = (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq15 eq23
  have eq30 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq21 eq29
  have eq37 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq30
  have eq69 (X0 X2 : G) : X0 = X2 := superpose eq37 eq37
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq120 eq69


@[equational_result]
theorem Equation28962_implies_Equation2 (G : Type*) [Magma G] (h : Equation28962 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0))) = X0 := superpose eq7 eq9
  have eq19 (X0 X3 : G) : (((X0 ◇ X0) ◇ X3) ◇ X0) = X3 := superpose eq10 eq10
  have eq21 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ (((X3 ◇ X4) ◇ X3) ◇ X2))) ◇ (X2 ◇ (((X3 ◇ X4) ◇ X3) ◇ X2))) = X2 := superpose eq10 eq10
  have eq25 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq7 eq19
  have eq29 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq19 eq7
  have eq33 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X2) ◇ X0) = X2 := superpose eq19 eq7
  have eq37 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X1))) = X1 := superpose eq19 eq11
  have eq56 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq29 eq11
  have eq68 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq25 eq56
  have eq69 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq68 eq7
  have eq76 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (((X3 ◇ X4) ◇ X3) ◇ X2))) ◇ (X2 ◇ (((X3 ◇ X4) ◇ X3) ◇ X2))) = X2 := superpose eq68 eq21
  have eq91 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2))) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2))) = X2 := superpose eq68 eq76
  have eq94 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq19 eq69
  have eq100 (X1 X2 : G) : (X1 ◇ (X1 ◇ (X2 ◇ X1))) = X1 := superpose eq94 eq37
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq94 eq33
  have eq109 (X0 X1 X2 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X4)) ◇ (X2 ◇ X4)) = X2 := superpose eq101 eq91
  have eq119 (X1 X2 X4 : G) : (X1 ◇ (X2 ◇ X4)) = X2 := superpose eq101 eq109
  have eq120 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq119 eq100
  have eq121 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq120 eq101
  have eq130 (X0 X3 : G) : X0 = X3 := superpose eq121 eq121
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq130 eq8
  subsumption eq135 eq130


@[equational_result]
theorem Equation28963_implies_Equation2 (G : Type*) [Magma G] (h : Equation28963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X4) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 X5 : G) : (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4) ◇ (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4) ◇ X5)) = X0 := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq10 eq10
  have eq37 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X3) ◇ (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X3) ◇ X4)) ◇ ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X6)) = X5 := superpose eq10 eq9
  have eq52 (X0 X1 X2 X3 X4 X6 : G) : (((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X1)) ◇ X0) ◇ X4) = (X0 ◇ (X0 ◇ X6)) := superpose eq9 eq10
  have eq57 (X0 X1 X2 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4) = X0 := superpose eq7 eq21
  have eq104 (X0 X5 : G) : (X0 ◇ (X0 ◇ X5)) = X0 := superpose eq57 eq12
  have eq110 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X3) ◇ (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X3) ◇ X4)) ◇ X0) = X5 := superpose eq57 eq37
  have eq121 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X1)) ◇ X0) ◇ X4) = X0 := superpose eq104 eq52
  have eq128 (X0 X3 X5 : G) : (X3 ◇ X0) = X5 := superpose eq121 eq110
  have eq129 (X0 X4 : G) : X0 = X4 := superpose eq7 eq128
  have eq158 (X0 : G) : sK0 ≠ X0 := superpose eq129 eq8
  subsumption eq158 eq129


@[equational_result]
theorem Equation28965_implies_Equation2 (G : Type*) [Magma G] (h : Equation28965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X3) ◇ ((X2 ◇ X1) ◇ (((X1 ◇ X2) ◇ X1) ◇ X0))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ X2) ◇ X0)) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) ◇ X3) ◇ X2) = X3 := superpose eq10 eq11
  have eq22 (X0 X1 X2 X3 : G) : ((((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X2))) ◇ ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X2))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)))) ◇ X3) ◇ X2) = X3 := superpose eq11 eq11
  have eq24 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ ((((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3) ◇ X2) = X3 := superpose eq10 eq11
  have eq27 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)))) = X2 := superpose eq11 eq7
  have eq52 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (((X2 ◇ X3) ◇ (((X3 ◇ X2) ◇ X3) ◇ X4)) ◇ (X2 ◇ X3))) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X2 ◇ X3) ◇ (((X3 ◇ X2) ◇ X3) ◇ X4)) ◇ (X2 ◇ X3))))) = X4 := superpose eq11 eq9
  have eq70 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (((X2 ◇ X1) ◇ X2) ◇ (X1 ◇ X2))))) = X3 := superpose eq9 eq7
  have eq73 (X0 X1 : G) : ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq11
  have eq84 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X3 := superpose eq73 eq70
  have eq105 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq10 eq84
  have eq126 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (X0 ◇ (X1 ◇ X2))) = X3 := superpose eq105 eq84
  have eq142 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X2)))) ◇ X3) ◇ X2) = X3 := superpose eq126 eq22
  have eq144 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X3 := superpose eq27 eq142
  have eq152 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2) ◇ X3) ◇ X2) = X3 := superpose eq144 eq18
  have eq156 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3) ◇ X2) = X3 := superpose eq144 eq24
  have eq167 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (((X3 ◇ X2) ◇ X3) ◇ X4)) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (((X3 ◇ X2) ◇ X3) ◇ X4)))) = X4 := superpose eq144 eq52
  have eq201 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X2) = X3 := superpose eq144 eq156
  have eq210 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X4)) ◇ ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X4)))) = X4 := superpose eq144 eq167
  have eq211 (X0 X1 X2 X4 : G) : ((X1 ◇ (X2 ◇ X4)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X2 ◇ X4)))) = X4 := superpose eq144 eq210
  have eq212 (X0 X1 X2 X4 : G) : ((X1 ◇ (X2 ◇ X4)) ◇ X0) = X4 := superpose eq126 eq211
  have eq213 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq212 eq152
  have eq230 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq213 eq201
  have eq250 (X0 X2 : G) : X0 = X2 := superpose eq230 eq230
  have eq252 (X0 : G) : sK0 ≠ X0 := superpose eq250 eq8
  subsumption eq252 eq250


@[equational_result]
theorem Equation28967_implies_Equation2 (G : Type*) [Magma G] (h : Equation28967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (((X2 ◇ X3) ◇ X2) ◇ X0)) ◇ X1) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq10 eq10
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ (((X3 ◇ X4) ◇ X3) ◇ X5)) ◇ X2) = X5 := superpose eq11 eq11
  have eq56 (X0 X1 X2 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ X4) = X0 := superpose eq7 eq21
  have eq103 (X2 X5 : G) : (X2 ◇ X2) = X5 := superpose eq56 eq47
  have eq231 (X0 X2 : G) : X0 = X2 := superpose eq103 eq103
  have eq236 (X0 : G) : sK0 ≠ X0 := superpose eq231 eq8
  subsumption eq236 eq231


@[equational_result]
theorem Equation28969_implies_Equation2 (G : Type*) [Magma G] (h : Equation28969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ ((X1 ◇ X2) ◇ X1))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq10
  have eq25 (X0 X3 X4 : G) : ((X3 ◇ X4) ◇ X0) = X4 := superpose eq17 eq12
  have eq28 (X0 X1 X3 : G) : (X1 ◇ (X3 ◇ X1)) = X0 := superpose eq25 eq7
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq35 eq33


@[equational_result]
theorem Equation28970_implies_Equation2 (G : Type*) [Magma G] (h : Equation28970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X4) ◇ (X5 ◇ (X3 ◇ X2))) = X4 := superpose eq7 eq7
  have eq10 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ X1) ◇ (X3 ◇ X0)) := superpose eq7 eq7
  have eq13 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq10 eq11
  have eq14 (X0 X2 X3 X4 X5 : G) : (((X0 ◇ X0) ◇ X4) ◇ (X5 ◇ (X3 ◇ X2))) = X4 := superpose eq13 eq9
  have eq17 (X0 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ X4) ◇ (X3 ◇ X2)) = X4 := superpose eq13 eq14
  have eq18 (X0 X2 X4 : G) : (((X0 ◇ X0) ◇ X4) ◇ X2) = X4 := superpose eq13 eq17
  have eq19 (X2 X4 : G) : (X4 ◇ X2) = X4 := superpose eq13 eq18
  have eq21 (X0 X1 : G) : X0 = X1 := superpose eq13 eq19
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq23 eq21


@[equational_result]
theorem Equation28971_implies_Equation2 (G : Type*) [Magma G] (h : Equation28971 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X0 ◇ X1) ◇ (X3 ◇ X3)) := superpose eq7 eq7
  have eq21 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq65 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq146 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq146 eq65


@[equational_result]
theorem Equation28972_implies_Equation2 (G : Type*) [Magma G] (h : Equation28972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X4 ◇ X5)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq21 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq15 eq12
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq10 eq21
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq33 eq24


@[equational_result]
theorem Equation28974_implies_Equation2 (G : Type*) [Magma G] (h : Equation28974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (X3 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X1) = (((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq10
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) = (((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X0) := superpose eq10 eq7
  have eq35 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X0) := superpose eq11 eq11
  have eq40 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X4) ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) ◇ (((((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) ◇ X0)) := superpose eq11 eq10
  have eq44 (X0 X1 X2 X3 X4 : G) : ((((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ X4) ◇ (((X2 ◇ X3) ◇ X2) ◇ X0)) ◇ (((X2 ◇ X3) ◇ X2) ◇ X0)) = (((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq11 eq10
  have eq49 (X1 X2 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X4) ◇ ((X1 ◇ X2) ◇ X1)) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1)) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X1))) := superpose eq17 eq40
  have eq50 (X1 X2 X4 : G) : (X1 ◇ X2) = ((((X1 ◇ X2) ◇ X1) ◇ X4) ◇ ((X1 ◇ X2) ◇ X1)) := superpose eq10 eq49
  have eq78 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X0) = ((((X0 ◇ X2) ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq35 eq7
  have eq172 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq50 eq50
  have eq224 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq7 eq14
  have eq266 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (X0 ◇ X0) := superpose eq7 eq224
  have eq291 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq266 eq7
  have eq292 (X0 X1 X3 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1))) = X3 := superpose eq266 eq9
  have eq304 (X0 X2 X3 X4 : G) : ((((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ X4) ◇ (((X2 ◇ X3) ◇ X2) ◇ X0)) ◇ (((X2 ◇ X3) ◇ X2) ◇ X0)) = (((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq266 eq44
  have eq305 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X0) = ((((X0 ◇ X2) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq266 eq78
  have eq376 (X0 X3 : G) : ((X0 ◇ X3) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq266 eq305
  have eq377 (X0 X3 : G) : ((X0 ◇ X3) ◇ X0) = X0 := superpose eq291 eq376
  have eq378 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq377 eq172
  have eq382 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X0 ◇ X0)) = ((((X2 ◇ X3) ◇ X2) ◇ X0) ◇ (((X2 ◇ X3) ◇ X2) ◇ X0)) := superpose eq377 eq304
  have eq404 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq377 eq378
  have eq414 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = (((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq404 eq382
  have eq415 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq377 eq414
  have eq416 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq377 eq415
  have eq417 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1))) = X3 := superpose eq416 eq292
  have eq420 (X0 X1 X3 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X3) = X3 := superpose eq416 eq417
  have eq421 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq416 eq420
  have eq422 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq421 eq291
  have eq430 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq421 eq422
  have eq432 (X0 X2 : G) : X0 = X2 := superpose eq430 eq430
  have eq434 (X0 : G) : sK0 ≠ X0 := superpose eq432 eq8
  subsumption eq434 eq432


@[equational_result]
theorem Equation28975_implies_Equation2 (G : Type*) [Magma G] (h : Equation28975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (((X1 ◇ X2) ◇ X1) ◇ X1)) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ X3) ◇ X3) = ((((X1 ◇ (X0 ◇ X2)) ◇ X1) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq10 eq10
  have eq15 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := superpose eq10 eq7
  have eq34 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq10 eq11
  have eq36 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (((X2 ◇ X1) ◇ X2) ◇ X2) := superpose eq11 eq11
  have eq37 (X0 X1 X2 X4 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X0) ◇ X1) ◇ (X4 ◇ X2)) = X4 := superpose eq11 eq7
  have eq46 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq10 eq15
  have eq49 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq15 eq15
  have eq99 (X0 X1 : G) : ((((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))))) = X1 := superpose eq9 eq15
  have eq101 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))))) = X1 := superpose eq9 eq99
  have eq139 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = (((X2 ◇ X2) ◇ ((X2 ◇ X2) ◇ X2)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq36 eq10
  have eq169 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X2 ◇ X1) ◇ X2)) ◇ ((X2 ◇ X1) ◇ X2)) = ((X2 ◇ (X2 ◇ X2)) ◇ (X2 ◇ X2)) := superpose eq36 eq34
  have eq175 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq9 eq34
  have eq214 (X0 : G) : (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq7 eq175
  have eq215 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq169 eq214
  have eq216 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq46 eq215
  have eq266 (X0 X1 : G) : (((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq9 eq37
  have eq313 (X0 X1 : G) : ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)) = X1 := superpose eq216 eq266
  have eq314 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq313
  have eq315 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq314 eq14
  have eq327 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq314 eq46
  have eq332 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = ((X2 ◇ X2) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := superpose eq314 eq139
  have eq335 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) := superpose eq314 eq216
  have eq358 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq314 eq315
  have eq412 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (((X2 ◇ X1) ◇ X2) ◇ X2)) := superpose eq7 eq358
  have eq442 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq332 eq412
  have eq443 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq442 eq49
  have eq448 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (X1 ◇ X1) := superpose eq442 eq358
  have eq455 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) = X1 := superpose eq448 eq101
  have eq456 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq448 eq335
  have eq473 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) = X1 := superpose eq34 eq455
  have eq474 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X1 := superpose eq327 eq473
  have eq475 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X1 := superpose eq34 eq474
  have eq476 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq327 eq475
  have eq477 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq476 eq443
  have eq478 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq456 eq477
  have eq481 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq478 eq34
  have eq510 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := superpose eq314 eq481
  have eq511 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = X0 := superpose eq510 eq7
  have eq614 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq511 eq478
  have eq615 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq614 eq442
  have eq628 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq615 eq510
  have eq629 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq628 eq615
  have eq630 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq629 eq511
  have eq643 (X0 X2 : G) : X0 = X2 := superpose eq630 eq630
  have eq645 (X0 : G) : sK0 ≠ X0 := superpose eq643 eq8
  subsumption eq645 eq643


@[equational_result]
theorem Equation28976_implies_Equation2 (G : Type*) [Magma G] (h : Equation28976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ X3) ◇ X3) = ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq42 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X1) = X0 := superpose eq7 eq11
  have eq81 (X0 X3 : G) : X0 = X3 := superpose eq42 eq42
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq81 eq8
  subsumption eq108 eq81


@[equational_result]
theorem Equation28978_implies_Equation2 (G : Type*) [Magma G] (h : Equation28978 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28979_implies_Equation2 (G : Type*) [Magma G] (h : Equation28979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation28980_implies_Equation2 (G : Type*) [Magma G] (h : Equation28980 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28982_implies_Equation2 (G : Type*) [Magma G] (h : Equation28982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28983_implies_Equation2 (G : Type*) [Magma G] (h : Equation28983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28984_implies_Equation2 (G : Type*) [Magma G] (h : Equation28984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28986_implies_Equation2 (G : Type*) [Magma G] (h : Equation28986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28987_implies_Equation2 (G : Type*) [Magma G] (h : Equation28987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28988_implies_Equation2 (G : Type*) [Magma G] (h : Equation28988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28989_implies_Equation2 (G : Type*) [Magma G] (h : Equation28989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X1) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation28991_implies_Equation2 (G : Type*) [Magma G] (h : Equation28991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X3) ◇ X1) ◇ X3) = (((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ ((((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)))) = X2 := superpose eq7 eq10
  have eq20 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq12
  have eq30 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X2) ◇ X3) = ((((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ ((((X4 ◇ X0) ◇ X2) ◇ (X4 ◇ X0)) ◇ X2)) ◇ X4) ◇ (((X4 ◇ X0) ◇ X2) ◇ (X4 ◇ X0))) := superpose eq11 eq11
  have eq31 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X2) = ((((X0 ◇ X4) ◇ X0) ◇ X4) ◇ (((X1 ◇ X3) ◇ X1) ◇ X3)) := superpose eq7 eq11
  have eq34 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X2) ◇ X3) = (((((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X5) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X5) ◇ ((((X2 ◇ X0) ◇ X4) ◇ (X2 ◇ X0)) ◇ X4)) := superpose eq11 eq11
  have eq60 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) ◇ X2) := superpose eq7 eq20
  have eq74 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = (((X1 ◇ X3) ◇ X1) ◇ X3) := superpose eq60 eq11
  have eq77 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X2) ◇ X3) = ((((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X4 ◇ X0)) ◇ X4) ◇ (((X4 ◇ X0) ◇ X2) ◇ (X4 ◇ X0))) := superpose eq60 eq30
  have eq78 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = ((((X0 ◇ X4) ◇ X0) ◇ X4) ◇ (((X1 ◇ X3) ◇ X1) ◇ X3)) := superpose eq60 eq31
  have eq80 (X0 X1 X2 X3 X5 : G) : (((X2 ◇ X3) ◇ X2) ◇ X3) = (((((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X5) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ X5) ◇ (X2 ◇ X0)) := superpose eq60 eq34
  have eq97 (X0 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X2) ◇ X3) = ((X4 ◇ X4) ◇ (((X4 ◇ X0) ◇ X2) ◇ (X4 ◇ X0))) := superpose eq7 eq77
  have eq99 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) = (((X2 ◇ X3) ◇ X2) ◇ X3) := superpose eq60 eq80
  have eq100 (X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X3) = X2 := superpose eq7 eq99
  have eq112 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq100 eq74
  have eq113 (X0 X1 X4 : G) : (X0 ◇ X1) = ((((X0 ◇ X4) ◇ X0) ◇ X4) ◇ X1) := superpose eq100 eq78
  have eq114 (X0 X2 X4 : G) : ((X4 ◇ X4) ◇ (((X4 ◇ X0) ◇ X2) ◇ (X4 ◇ X0))) = X2 := superpose eq100 eq97
  have eq127 (X2 X3 : G) : (X3 ◇ X3) = X2 := superpose eq112 eq100
  have eq139 (X0 X1 X4 : G) : (X0 ◇ X1) = ((X4 ◇ X4) ◇ X1) := superpose eq112 eq113
  have eq140 (X2 X4 : G) : ((X4 ◇ X4) ◇ X2) = X2 := superpose eq112 eq114
  have eq141 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq140 eq139
  have eq148 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq141 eq112
  have eq158 (X0 X1 : G) : X0 = X1 := superpose eq148 eq127
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq158 eq8
  subsumption eq168 eq158


@[equational_result]
theorem Equation28993_implies_Equation2 (G : Type*) [Magma G] (h : Equation28993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X3 ◇ X4) ◇ X3) ◇ X4) = ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq42 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X1) ◇ X2) = X0 := superpose eq7 eq11
  have eq98 (X0 X2 : G) : X0 = X2 := superpose eq10 eq42
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq98 eq8
  subsumption eq134 eq98


@[equational_result]
theorem Equation28995_implies_Equation2 (G : Type*) [Magma G] (h : Equation28995 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation28996_implies_Equation2 (G : Type*) [Magma G] (h : Equation28996 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation28997_implies_Equation2 (G : Type*) [Magma G] (h : Equation28997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation28999_implies_Equation2 (G : Type*) [Magma G] (h : Equation28999 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29000_implies_Equation2 (G : Type*) [Magma G] (h : Equation29000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29001_implies_Equation2 (G : Type*) [Magma G] (h : Equation29001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29003_implies_Equation2 (G : Type*) [Magma G] (h : Equation29003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29004_implies_Equation2 (G : Type*) [Magma G] (h : Equation29004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29005_implies_Equation2 (G : Type*) [Magma G] (h : Equation29005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29006_implies_Equation2 (G : Type*) [Magma G] (h : Equation29006 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29008_implies_Equation2 (G : Type*) [Magma G] (h : Equation29008 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq24 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq13 eq11
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq24
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation29009_implies_Equation2 (G : Type*) [Magma G] (h : Equation29009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq35 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq112 eq35


@[equational_result]
theorem Equation29010_implies_Equation2 (G : Type*) [Magma G] (h : Equation29010 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq28 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq11
  have eq42 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq28 eq11
  have eq48 (X0 X2 : G) : X0 = X2 := superpose eq42 eq42
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq108 eq48


@[equational_result]
theorem Equation29011_implies_Equation2 (G : Type*) [Magma G] (h : Equation29011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq34 (X0 X5 : G) : X0 = X5 := superpose eq7 eq15
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq134 eq34


@[equational_result]
theorem Equation29013_implies_Equation2 (G : Type*) [Magma G] (h : Equation29013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29014_implies_Equation2 (G : Type*) [Magma G] (h : Equation29014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29015_implies_Equation2 (G : Type*) [Magma G] (h : Equation29015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29016_implies_Equation2 (G : Type*) [Magma G] (h : Equation29016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29018_implies_Equation2 (G : Type*) [Magma G] (h : Equation29018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29019_implies_Equation2 (G : Type*) [Magma G] (h : Equation29019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29020_implies_Equation2 (G : Type*) [Magma G] (h : Equation29020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29021_implies_Equation2 (G : Type*) [Magma G] (h : Equation29021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29023_implies_Equation2 (G : Type*) [Magma G] (h : Equation29023 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29024_implies_Equation2 (G : Type*) [Magma G] (h : Equation29024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29025_implies_Equation2 (G : Type*) [Magma G] (h : Equation29025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29026_implies_Equation2 (G : Type*) [Magma G] (h : Equation29026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29028_implies_Equation2 (G : Type*) [Magma G] (h : Equation29028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29029_implies_Equation2 (G : Type*) [Magma G] (h : Equation29029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29030_implies_Equation2 (G : Type*) [Magma G] (h : Equation29030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29031_implies_Equation2 (G : Type*) [Magma G] (h : Equation29031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29032_implies_Equation2 (G : Type*) [Magma G] (h : Equation29032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X1) ◇ X3) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29039_implies_Equation2 (G : Type*) [Magma G] (h : Equation29039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq7 eq10
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ ((X1 ◇ X2) ◇ X2)) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq10 eq7
  have eq24 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ X3)) := superpose eq7 eq11
  have eq25 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X1 ◇ (X2 ◇ X3))) = ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) := superpose eq10 eq11
  have eq26 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) = X2 := superpose eq11 eq11
  have eq30 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq11 eq10
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq24 eq15
  have eq33 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1) = X1 := superpose eq26 eq25
  have eq39 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq30 eq7
  have eq40 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := superpose eq30 eq11
  have eq51 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) := superpose eq39 eq32
  have eq52 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq40 eq33
  have eq53 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := superpose eq52 eq39
  have eq57 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq53 eq12
  have eq62 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq53 eq51
  have eq67 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq57 eq62
  have eq68 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq67 eq30
  have eq88 (X0 X1 : G) : X0 = X1 := superpose eq67 eq68
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq98 eq88


@[equational_result]
theorem Equation29040_implies_Equation2 (G : Type*) [Magma G] (h : Equation29040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ (((X0 ◇ X2) ◇ X2) ◇ X4)) = X3 := superpose eq7 eq7
  have eq47 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq10
  have eq48 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq10 eq10
  have eq82 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq48 eq47
  have eq88 (X0 X3 : G) : X0 = X3 := superpose eq82 eq82
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq122 eq88


@[equational_result]
theorem Equation29043_implies_Equation2 (G : Type*) [Magma G] (h : Equation29043 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq11 eq7
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq7 eq13
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq7 eq10
  have eq24 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq14 eq15
  have eq25 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq14 eq24
  have eq26 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ X1) := superpose eq25 eq14
  have eq27 (X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq26 eq25
  have eq29 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq27 eq10
  have eq40 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq26 eq29
  have eq43 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq29 eq26
  have eq45 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq40 eq27
  have eq48 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq45 eq29
  have eq51 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq45 eq43
  have eq52 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq45 eq51
  have eq54 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq52 eq48
  have eq57 (X0 X1 : G) : X0 = X1 := superpose eq54 eq52
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq59 eq57


@[equational_result]
theorem Equation29044_implies_Equation2 (G : Type*) [Magma G] (h : Equation29044 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ ((X0 ◇ X1) ◇ X4)) = X3 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ X2) := superpose eq11 eq11
  have eq36 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X3) ◇ X0) = X3 := superpose eq7 eq10
  have eq48 (X0 X1 X2 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ X4) = X0 := superpose eq7 eq19
  have eq85 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq48 eq36
  have eq131 (X0 X3 : G) : X0 = X3 := superpose eq10 eq85
  have eq205 (X0 : G) : sK0 ≠ X0 := superpose eq131 eq8
  subsumption eq205 eq131


@[equational_result]
theorem Equation29046_implies_Equation2 (G : Type*) [Magma G] (h : Equation29046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq32 (X0 X4 X5 X6 : G) : ((((X0 ◇ X4) ◇ X4) ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq37 (X0 X4 X5 X6 : G) : (((X0 ◇ X4) ◇ X5) ◇ X6) = X5 := superpose eq12 eq12
  have eq58 (X4 X5 X6 : G) : (X4 ◇ X6) = X5 := superpose eq37 eq32
  have eq65 (X0 X3 : G) : X0 = X3 := superpose eq58 eq58
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq110 eq65


@[equational_result]
theorem Equation29047_implies_Equation2 (G : Type*) [Magma G] (h : Equation29047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X3 X4 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X4 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq35 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq10
  have eq48 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X2)) = X0 := superpose eq35 eq7
  have eq56 (X0 X3 : G) : X0 = X3 := superpose eq48 eq48
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq71 eq56


@[equational_result]
theorem Equation29048_implies_Equation2 (G : Type*) [Magma G] (h : Equation29048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X3)) = (X2 ◇ X2) := superpose eq7 eq7
  have eq16 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq7 eq11
  have eq55 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq124 eq55


@[equational_result]
theorem Equation29049_implies_Equation2 (G : Type*) [Magma G] (h : Equation29049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X0) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 X5 : G) : (X2 ◇ X3) = (X0 ◇ (X4 ◇ X5)) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation29052_implies_Equation2 (G : Type*) [Magma G] (h : Equation29052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (((X2 ◇ X1) ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq11
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq17 (X1 X2 : G) : (((X2 ◇ X1) ◇ X1) ◇ X2) = X1 := superpose eq14 eq13
  have eq42 (X0 X1 : G) : ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X0) = X1 := superpose eq11 eq10
  have eq43 (X0 X1 X2 : G) : (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) = ((X0 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2))) ◇ X0) := superpose eq10 eq10
  have eq49 (X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ (((X1 ◇ X2) ◇ X2) ◇ X2)) := superpose eq42 eq43
  have eq62 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq17 eq11
  have eq66 (X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ ((X1 ◇ X2) ◇ X2)) := superpose eq62 eq49
  have eq71 (X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ (X1 ◇ X2)) := superpose eq62 eq66
  have eq75 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq11 eq71
  have eq83 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq75 eq11
  have eq87 (X0 X2 : G) : X0 = X2 := superpose eq83 eq83
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq89 eq87


@[equational_result]
theorem Equation29053_implies_Equation2 (G : Type*) [Magma G] (h : Equation29053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq64 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq159 eq64


@[equational_result]
theorem Equation29055_implies_Equation2 (G : Type*) [Magma G] (h : Equation29055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29056_implies_Equation2 (G : Type*) [Magma G] (h : Equation29056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29057_implies_Equation2 (G : Type*) [Magma G] (h : Equation29057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29059_implies_Equation2 (G : Type*) [Magma G] (h : Equation29059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29060_implies_Equation2 (G : Type*) [Magma G] (h : Equation29060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29061_implies_Equation2 (G : Type*) [Magma G] (h : Equation29061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29063_implies_Equation2 (G : Type*) [Magma G] (h : Equation29063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29064_implies_Equation2 (G : Type*) [Magma G] (h : Equation29064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29065_implies_Equation2 (G : Type*) [Magma G] (h : Equation29065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29066_implies_Equation2 (G : Type*) [Magma G] (h : Equation29066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X1) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29069_implies_Equation2 (G : Type*) [Magma G] (h : Equation29069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X3 ◇ X2) ◇ X2) ◇ X2) = ((((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1)) ◇ (X2 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1))) = X2 := superpose eq7 eq9
  have eq17 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) = ((((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) := superpose eq9 eq7
  have eq19 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X2 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1))) = X2 := superpose eq7 eq11
  have eq33 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X2 ◇ X3))) = ((((X4 ◇ X0) ◇ X0) ◇ X0) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) := superpose eq9 eq10
  have eq35 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = ((((X4 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X5 ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1)) ◇ (X3 ◇ X1))) := superpose eq10 eq10
  have eq38 (X0 X1 X2 X4 : G) : (((((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ X1) ◇ (X4 ◇ X2)) = X4 := superpose eq10 eq7
  have eq43 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) = (((X2 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ ((((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X1)) := superpose eq10 eq9
  have eq51 (X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) = (((X2 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) := superpose eq17 eq43
  have eq52 (X2 X3 X4 : G) : (X2 ◇ (X2 ◇ X3)) = ((X4 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)) := superpose eq9 eq51
  have eq54 (X0 X2 X3 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq52 eq9
  have eq59 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X2 ◇ X3))) = ((((X4 ◇ X0) ◇ X0) ◇ X0) ◇ (X2 ◇ (X2 ◇ X3))) := superpose eq52 eq33
  have eq67 (X0 X1 X2 X3 X4 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = ((((X4 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq52 eq35
  have eq68 (X1 X2 X4 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ (X4 ◇ X2)) = X4 := superpose eq52 eq38
  have eq77 (X0 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X3))) = ((((X4 ◇ X0) ◇ X0) ◇ X0) ◇ (X2 ◇ (X2 ◇ X3))) := superpose eq52 eq59
  have eq82 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = ((((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq52 eq67
  have eq100 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ (X2 ◇ X1)) = X2 := superpose eq7 eq68
  have eq102 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq54 eq68
  have eq112 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X1)) = X2 := superpose eq7 eq100
  have eq113 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = (((X0 ◇ X1) ◇ X1) ◇ (X3 ◇ (X3 ◇ X1))) := superpose eq112 eq82
  have eq116 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq54 eq102
  have eq118 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq116
  have eq121 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq116 eq116
  have eq134 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X3))) = X2 := superpose eq118 eq77
  have eq140 (X2 X3 : G) : (((X2 ◇ X3) ◇ X3) ◇ X3) = X3 := superpose eq121 eq113
  have eq145 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X2 := superpose eq121 eq19
  have eq148 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq121 eq134
  have eq175 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq140 eq145
  have eq183 (X0 X1 : G) : X0 = X1 := superpose eq148 eq175
  have eq188 (X0 : G) : sK0 ≠ X0 := superpose eq183 eq8
  subsumption eq188 eq183


@[equational_result]
theorem Equation29070_implies_Equation2 (G : Type*) [Magma G] (h : Equation29070 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3)) ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq10 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq63 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq159 eq63


@[equational_result]
theorem Equation29072_implies_Equation2 (G : Type*) [Magma G] (h : Equation29072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29073_implies_Equation2 (G : Type*) [Magma G] (h : Equation29073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation29074_implies_Equation2 (G : Type*) [Magma G] (h : Equation29074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29076_implies_Equation2 (G : Type*) [Magma G] (h : Equation29076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29077_implies_Equation2 (G : Type*) [Magma G] (h : Equation29077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation29078_implies_Equation2 (G : Type*) [Magma G] (h : Equation29078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29080_implies_Equation2 (G : Type*) [Magma G] (h : Equation29080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29081_implies_Equation2 (G : Type*) [Magma G] (h : Equation29081 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29082_implies_Equation2 (G : Type*) [Magma G] (h : Equation29082 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29083_implies_Equation2 (G : Type*) [Magma G] (h : Equation29083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29085_implies_Equation2 (G : Type*) [Magma G] (h : Equation29085 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq23 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq13 eq11
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation29086_implies_Equation2 (G : Type*) [Magma G] (h : Equation29086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ (X4 ◇ (X0 ◇ X2))) = X4 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : ((X0 ◇ X3) ◇ X0) = X4 := superpose eq11 eq10
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq13
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq45 eq28


@[equational_result]
theorem Equation29087_implies_Equation2 (G : Type*) [Magma G] (h : Equation29087 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq10
  have eq21 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq13 eq10
  have eq24 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq35 eq24


@[equational_result]
theorem Equation29088_implies_Equation2 (G : Type*) [Magma G] (h : Equation29088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq31 (X0 X5 : G) : X0 = X5 := superpose eq7 eq15
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq127 eq31


@[equational_result]
theorem Equation29090_implies_Equation2 (G : Type*) [Magma G] (h : Equation29090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29091_implies_Equation2 (G : Type*) [Magma G] (h : Equation29091 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29092_implies_Equation2 (G : Type*) [Magma G] (h : Equation29092 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29093_implies_Equation2 (G : Type*) [Magma G] (h : Equation29093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29095_implies_Equation2 (G : Type*) [Magma G] (h : Equation29095 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29096_implies_Equation2 (G : Type*) [Magma G] (h : Equation29096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29097_implies_Equation2 (G : Type*) [Magma G] (h : Equation29097 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29098_implies_Equation2 (G : Type*) [Magma G] (h : Equation29098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29100_implies_Equation2 (G : Type*) [Magma G] (h : Equation29100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29101_implies_Equation2 (G : Type*) [Magma G] (h : Equation29101 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29102_implies_Equation2 (G : Type*) [Magma G] (h : Equation29102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29103_implies_Equation2 (G : Type*) [Magma G] (h : Equation29103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29105_implies_Equation2 (G : Type*) [Magma G] (h : Equation29105 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29106_implies_Equation2 (G : Type*) [Magma G] (h : Equation29106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29107_implies_Equation2 (G : Type*) [Magma G] (h : Equation29107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29108_implies_Equation2 (G : Type*) [Magma G] (h : Equation29108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29109_implies_Equation2 (G : Type*) [Magma G] (h : Equation29109 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X2) ◇ X3) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29116_implies_Equation2 (G : Type*) [Magma G] (h : Equation29116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (((X1 ◇ X2) ◇ X3) ◇ X0))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq7 eq7
  have eq30 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2)) = X4 := superpose eq10 eq10
  have eq42 (X0 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X0) = X5 := superpose eq30 eq9
  have eq43 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ X3) = X4 := superpose eq30 eq10
  have eq48 (X0 X4 X5 : G) : (X4 ◇ X0) = X5 := superpose eq43 eq42
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq48 eq48
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq61 eq53


@[equational_result]
theorem Equation29117_implies_Equation2 (G : Type*) [Magma G] (h : Equation29117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X3)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq34 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq95 eq34


@[equational_result]
theorem Equation29118_implies_Equation2 (G : Type*) [Magma G] (h : Equation29118 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X3))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : (((((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ X4) ◇ (X1 ◇ X3)) ◇ X5) ◇ X0) = X5 := superpose eq7 eq7
  have eq46 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X1 ◇ X2) ◇ ((((X3 ◇ X0) ◇ X4) ◇ (((X5 ◇ X6) ◇ X7) ◇ (X5 ◇ X7))) ◇ X0)) = X2 := superpose eq10 eq10
  have eq61 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X4 ◇ X0)) = X2 := superpose eq10 eq46
  have eq63 (X0 X4 X5 : G) : ((X4 ◇ X5) ◇ X0) = X5 := superpose eq61 eq12
  have eq78 (X0 X1 X3 : G) : (X3 ◇ (X1 ◇ X3)) = X0 := superpose eq63 eq7
  have eq97 (X0 X3 : G) : X0 = X3 := superpose eq78 eq78
  have eq99 (X0 : G) : sK0 ≠ X0 := superpose eq97 eq8
  subsumption eq99 eq97


@[equational_result]
theorem Equation29119_implies_Equation2 (G : Type*) [Magma G] (h : Equation29119 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (X1 ◇ X4) = (X0 ◇ ((X1 ◇ X2) ◇ X5)) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq61 (X0 X5 : G) : X0 = X5 := superpose eq7 eq22
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq154 eq61


@[equational_result]
theorem Equation29121_implies_Equation2 (G : Type*) [Magma G] (h : Equation29121 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (X0 ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq115 eq45


@[equational_result]
theorem Equation29122_implies_Equation2 (G : Type*) [Magma G] (h : Equation29122 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X5 := superpose eq7 eq7
  have eq10 (X0 X4 : G) : ((X0 ◇ X4) ◇ (X0 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X2 X4 X5 : G) : (((X0 ◇ X4) ◇ X5) ◇ X2) = X5 := superpose eq10 eq9
  have eq13 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X2)) = X0 := superpose eq12 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29123_implies_Equation2 (G : Type*) [Magma G] (h : Equation29123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ (X0 ◇ (X2 ◇ X3))) = X4 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ (X3 ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 : G) : (X4 ◇ ((X2 ◇ X3) ◇ X4)) = X0 := superpose eq7 eq11
  have eq18 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq11 eq11
  have eq41 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq11 eq10
  have eq54 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq41 eq18
  have eq65 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq54 eq13
  have eq87 (X0 X1 : G) : X0 = X1 := superpose eq54 eq65
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq92 eq87


@[equational_result]
theorem Equation29124_implies_Equation2 (G : Type*) [Magma G] (h : Equation29124 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 X4 X5 : G) : (X2 ◇ X4) = (X0 ◇ (X3 ◇ X5)) := superpose eq7 eq7
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq49 (X0 X5 : G) : X0 = X5 := superpose eq7 eq29
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq119 eq49


@[equational_result]
theorem Equation29126_implies_Equation2 (G : Type*) [Magma G] (h : Equation29126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ ((X3 ◇ X1) ◇ ((X1 ◇ X2) ◇ X3))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 X5 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X5 ◇ X3)) = X1 := superpose eq11 eq7
  have eq39 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X6) ◇ X5))) = X4 := superpose eq11 eq10
  have eq62 (X1 X3 X4 : G) : ((X3 ◇ X4) ◇ X1) = X4 := superpose eq27 eq39
  have eq65 (X0 X1 X3 : G) : (X3 ◇ (X3 ◇ X1)) = X0 := superpose eq62 eq7
  have eq92 (X0 X3 : G) : X0 = X3 := superpose eq65 eq65
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq92 eq8
  subsumption eq94 eq92


@[equational_result]
theorem Equation29127_implies_Equation2 (G : Type*) [Magma G] (h : Equation29127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X4) ◇ ((X3 ◇ X2) ◇ X0)) = X4 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X3 ◇ X2) = (X0 ◇ (X0 ◇ X3)) := superpose eq7 eq7
  have eq42 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq11 eq10
  have eq62 (X0 X4 : G) : X0 = X4 := superpose eq10 eq42
  have eq111 (X0 : G) : sK0 ≠ X0 := superpose eq62 eq8
  subsumption eq111 eq62


@[equational_result]
theorem Equation29128_implies_Equation2 (G : Type*) [Magma G] (h : Equation29128 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ X4) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) = X4 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : (X3 ◇ X3) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq73 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq11 eq10
  have eq101 (X0 X2 : G) : X0 = X2 := superpose eq73 eq73
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq101 eq8
  subsumption eq132 eq101


@[equational_result]
theorem Equation29129_implies_Equation2 (G : Type*) [Magma G] (h : Equation29129 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X4 X5 X6 : G) : ((X0 ◇ X5) ◇ ((X3 ◇ X4) ◇ X6)) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X5) ◇ X0)) ◇ X6) ◇ X0) = X6 := superpose eq7 eq7
  have eq13 (X0 X2 X6 : G) : ((X2 ◇ X6) ◇ X0) = X6 := superpose eq10 eq12
  have eq14 (X0 X3 X4 : G) : (X3 ◇ (X3 ◇ X4)) = X0 := superpose eq13 eq7
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq14 eq14
  have eq21 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq21 eq19


@[equational_result]
theorem Equation29131_implies_Equation2 (G : Type*) [Magma G] (h : Equation29131 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X1) = (X0 ◇ (X5 ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq61 (X0 X5 : G) : X0 = X5 := superpose eq7 eq22
  have eq140 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq140 eq61


@[equational_result]
theorem Equation29132_implies_Equation2 (G : Type*) [Magma G] (h : Equation29132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ (X6 ◇ X0)) = X5 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq10
  have eq21 (X0 X2 X3 X4 : G) : (X3 ◇ (X4 ◇ X2)) = X0 := superpose eq15 eq7
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq10 eq21
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq35 eq26


@[equational_result]
theorem Equation29133_implies_Equation2 (G : Type*) [Magma G] (h : Equation29133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 X5 : G) : (X4 ◇ X3) = (X0 ◇ (X5 ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X5 ◇ (X6 ◇ X5)) = X0 := superpose eq7 eq11
  have eq55 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq118 eq55


@[equational_result]
theorem Equation29134_implies_Equation2 (G : Type*) [Magma G] (h : Equation29134 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ (X6 ◇ X6)) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X3 ◇ X4) ◇ X5) ◇ X6) ◇ ((X0 ◇ X1) ◇ X2)) = X6 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq21 (X0 X1 X2 X5 X6 : G) : (X5 ◇ ((X0 ◇ X1) ◇ X2)) = X6 := superpose eq16 eq12
  have eq25 (X1 X5 X6 : G) : (X5 ◇ X1) = X6 := superpose eq16 eq21
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq10 eq25
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq35 eq26


@[equational_result]
theorem Equation29135_implies_Equation2 (G : Type*) [Magma G] (h : Equation29135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X0) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X6 X7 X8 : G) : ((X0 ◇ X6) ◇ (X7 ◇ X8)) = X6 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq21 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq15 eq12
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq10 eq21
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq33 eq24


@[equational_result]
theorem Equation29137_implies_Equation2 (G : Type*) [Magma G] (h : Equation29137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = (X0 ◇ X0) := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 : G) : (((((X0 ◇ (X1 ◇ X1)) ◇ X2) ◇ X3) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = X1 := superpose eq11 eq7
  have eq18 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ X1)) = X3 := superpose eq11 eq7
  have eq22 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq14 eq7
  have eq24 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) = X1 := superpose eq14 eq16
  have eq26 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq18 eq24
  have eq32 (X0 X1 : G) : X0 = X1 := superpose eq22 eq26
  have eq68 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq68 eq32


@[equational_result]
theorem Equation29138_implies_Equation2 (G : Type*) [Magma G] (h : Equation29138 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq60 (X0 X4 : G) : X0 = X4 := superpose eq7 eq17
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq60 eq8
  subsumption eq152 eq60


@[equational_result]
theorem Equation29139_implies_Equation2 (G : Type*) [Magma G] (h : Equation29139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ (((X1 ◇ X2) ◇ X3) ◇ X1)) ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq7
  have eq11 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq11
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq18 (X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X1) ◇ X2) = X1 := superpose eq14 eq13
  have eq20 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ X3) ◇ (X5 ◇ X4)) = X5 := superpose eq18 eq9
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq20 eq14
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq54 eq38


@[equational_result]
theorem Equation29140_implies_Equation2 (G : Type*) [Magma G] (h : Equation29140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X4 : G) : (X0 ◇ (X3 ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq64 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq159 eq64


@[equational_result]
theorem Equation29142_implies_Equation2 (G : Type*) [Magma G] (h : Equation29142 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29143_implies_Equation2 (G : Type*) [Magma G] (h : Equation29143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29144_implies_Equation2 (G : Type*) [Magma G] (h : Equation29144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29145_implies_Equation2 (G : Type*) [Magma G] (h : Equation29145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29147_implies_Equation2 (G : Type*) [Magma G] (h : Equation29147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29148_implies_Equation2 (G : Type*) [Magma G] (h : Equation29148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29149_implies_Equation2 (G : Type*) [Magma G] (h : Equation29149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29150_implies_Equation2 (G : Type*) [Magma G] (h : Equation29150 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29152_implies_Equation2 (G : Type*) [Magma G] (h : Equation29152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29153_implies_Equation2 (G : Type*) [Magma G] (h : Equation29153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29154_implies_Equation2 (G : Type*) [Magma G] (h : Equation29154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29155_implies_Equation2 (G : Type*) [Magma G] (h : Equation29155 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29157_implies_Equation2 (G : Type*) [Magma G] (h : Equation29157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29158_implies_Equation2 (G : Type*) [Magma G] (h : Equation29158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29159_implies_Equation2 (G : Type*) [Magma G] (h : Equation29159 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29160_implies_Equation2 (G : Type*) [Magma G] (h : Equation29160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29161_implies_Equation2 (G : Type*) [Magma G] (h : Equation29161 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X1) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29163_implies_Equation2 (G : Type*) [Magma G] (h : Equation29163 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq23 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq13 eq11
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq37 eq24


@[equational_result]
theorem Equation29164_implies_Equation2 (G : Type*) [Magma G] (h : Equation29164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ (X4 ◇ X2)) = X4 := superpose eq7 eq7
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq11
  have eq36 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq23 eq11
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq10 eq36
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq95 eq40


@[equational_result]
theorem Equation29165_implies_Equation2 (G : Type*) [Magma G] (h : Equation29165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X3 X4 X5 : G) : (((X0 ◇ X4) ◇ (X0 ◇ X3)) ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X2 X3 X4 : G) : ((X0 ◇ X2) ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq7
  have eq28 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X3 := superpose eq10 eq9
  have eq42 (X0 X2 X4 : G) : ((X0 ◇ X2) ◇ X0) = X4 := superpose eq28 eq10
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq42 eq42
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq62 eq51


@[equational_result]
theorem Equation29166_implies_Equation2 (G : Type*) [Magma G] (h : Equation29166 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 X6 X7 : G) : (((X0 ◇ X5) ◇ (X0 ◇ X4)) ◇ (X6 ◇ X7)) = X6 := superpose eq7 eq7
  have eq10 (X0 X2 X5 X6 : G) : ((X0 ◇ X2) ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X6 := superpose eq10 eq9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq31 (X0 X5 : G) : X0 = X5 := superpose eq7 eq15
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq127 eq31


@[equational_result]
theorem Equation29168_implies_Equation2 (G : Type*) [Magma G] (h : Equation29168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29169_implies_Equation2 (G : Type*) [Magma G] (h : Equation29169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29170_implies_Equation2 (G : Type*) [Magma G] (h : Equation29170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29171_implies_Equation2 (G : Type*) [Magma G] (h : Equation29171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29173_implies_Equation2 (G : Type*) [Magma G] (h : Equation29173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29174_implies_Equation2 (G : Type*) [Magma G] (h : Equation29174 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29175_implies_Equation2 (G : Type*) [Magma G] (h : Equation29175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29176_implies_Equation2 (G : Type*) [Magma G] (h : Equation29176 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29178_implies_Equation2 (G : Type*) [Magma G] (h : Equation29178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29179_implies_Equation2 (G : Type*) [Magma G] (h : Equation29179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29180_implies_Equation2 (G : Type*) [Magma G] (h : Equation29180 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29181_implies_Equation2 (G : Type*) [Magma G] (h : Equation29181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29183_implies_Equation2 (G : Type*) [Magma G] (h : Equation29183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29184_implies_Equation2 (G : Type*) [Magma G] (h : Equation29184 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29185_implies_Equation2 (G : Type*) [Magma G] (h : Equation29185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29186_implies_Equation2 (G : Type*) [Magma G] (h : Equation29186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29187_implies_Equation2 (G : Type*) [Magma G] (h : Equation29187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X2) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29189_implies_Equation2 (G : Type*) [Magma G] (h : Equation29189 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq23 (X0 X1 X3 : G) : (X0 ◇ X1) = X3 := superpose eq13 eq11
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq38 eq25


@[equational_result]
theorem Equation29190_implies_Equation2 (G : Type*) [Magma G] (h : Equation29190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq11
  have eq21 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq14 eq11
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq37 eq26


@[equational_result]
theorem Equation29191_implies_Equation2 (G : Type*) [Magma G] (h : Equation29191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (((X0 ◇ X4) ◇ X4) ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq7
  have eq10 (X0 X3 X4 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ X5) ◇ X3) ◇ X3) = ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X0 ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = (((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X2 ◇ X3))) ◇ X0) := superpose eq10 eq9
  have eq97 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X5 ◇ X6) ◇ (X3 ◇ X4)) = ((X3 ◇ (X3 ◇ X4)) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X2)) := superpose eq11 eq10
  have eq110 (X3 X4 X5 X6 : G) : ((X5 ◇ X6) ◇ (X3 ◇ X4)) = ((X3 ◇ (X3 ◇ X4)) ◇ (X3 ◇ (X3 ◇ X4))) := superpose eq29 eq97
  have eq111 (X3 X4 X5 X6 : G) : ((X5 ◇ X6) ◇ (X3 ◇ X4)) = X3 := superpose eq10 eq110
  have eq146 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq111
  have eq170 (X0 X3 X4 : G) : ((X0 ◇ (X0 ◇ X3)) ◇ X0) = X4 := superpose eq146 eq10
  have eq181 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq146 eq170
  have eq220 (X0 X2 : G) : X0 = X2 := superpose eq181 eq181
  have eq222 (X0 : G) : sK0 ≠ X0 := superpose eq220 eq8
  subsumption eq222 eq220


@[equational_result]
theorem Equation29192_implies_Equation2 (G : Type*) [Magma G] (h : Equation29192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq34 (X0 X5 : G) : X0 = X5 := superpose eq7 eq15
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq134 eq34


@[equational_result]
theorem Equation29194_implies_Equation2 (G : Type*) [Magma G] (h : Equation29194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29195_implies_Equation2 (G : Type*) [Magma G] (h : Equation29195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29196_implies_Equation2 (G : Type*) [Magma G] (h : Equation29196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29197_implies_Equation2 (G : Type*) [Magma G] (h : Equation29197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29199_implies_Equation2 (G : Type*) [Magma G] (h : Equation29199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29200_implies_Equation2 (G : Type*) [Magma G] (h : Equation29200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29201_implies_Equation2 (G : Type*) [Magma G] (h : Equation29201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29202_implies_Equation2 (G : Type*) [Magma G] (h : Equation29202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29204_implies_Equation2 (G : Type*) [Magma G] (h : Equation29204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29205_implies_Equation2 (G : Type*) [Magma G] (h : Equation29205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29206_implies_Equation2 (G : Type*) [Magma G] (h : Equation29206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29207_implies_Equation2 (G : Type*) [Magma G] (h : Equation29207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29209_implies_Equation2 (G : Type*) [Magma G] (h : Equation29209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29210_implies_Equation2 (G : Type*) [Magma G] (h : Equation29210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29211_implies_Equation2 (G : Type*) [Magma G] (h : Equation29211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29212_implies_Equation2 (G : Type*) [Magma G] (h : Equation29212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29213_implies_Equation2 (G : Type*) [Magma G] (h : Equation29213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X3) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29215_implies_Equation2 (G : Type*) [Magma G] (h : Equation29215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X0 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X5 : G) : (X0 ◇ (X5 ◇ (X1 ◇ X2))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq23 (X0 X1 X5 : G) : (X0 ◇ X1) = X5 := superpose eq13 eq11
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq37 eq24


@[equational_result]
theorem Equation29216_implies_Equation2 (G : Type*) [Magma G] (h : Equation29216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X0 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ (X5 ◇ X3)) = X5 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq32 (X0 X5 : G) : X0 = X5 := superpose eq7 eq16
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq100 eq32


@[equational_result]
theorem Equation29217_implies_Equation2 (G : Type*) [Magma G] (h : Equation29217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X0 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X3 X5 X6 : G) : ((X0 ◇ X5) ◇ (X6 ◇ (X0 ◇ X3))) = X6 := superpose eq7 eq7
  have eq11 (X0 X4 X5 : G) : (X0 ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X0) = X6 := superpose eq11 eq10
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq11 eq13
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq43 eq26


@[equational_result]
theorem Equation29218_implies_Equation2 (G : Type*) [Magma G] (h : Equation29218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X0 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ (X6 ◇ X5)) = X6 := superpose eq7 eq7
  have eq11 (X0 X4 X5 : G) : (X0 ◇ (X5 ◇ (X0 ◇ X4))) = X5 := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq11 eq11
  have eq36 (X0 X5 : G) : (X0 ◇ X0) = X5 := superpose eq23 eq11
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq10 eq36
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq83 eq40


@[equational_result]
theorem Equation29219_implies_Equation2 (G : Type*) [Magma G] (h : Equation29219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X0 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X6 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq30 (X0 X6 : G) : X0 = X6 := superpose eq7 eq14
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq83 eq30


@[equational_result]
theorem Equation29221_implies_Equation2 (G : Type*) [Magma G] (h : Equation29221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X1 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29222_implies_Equation2 (G : Type*) [Magma G] (h : Equation29222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X1 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation29223_implies_Equation2 (G : Type*) [Magma G] (h : Equation29223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X1 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29224_implies_Equation2 (G : Type*) [Magma G] (h : Equation29224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X1 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29225_implies_Equation2 (G : Type*) [Magma G] (h : Equation29225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X1 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29227_implies_Equation2 (G : Type*) [Magma G] (h : Equation29227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X2 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29228_implies_Equation2 (G : Type*) [Magma G] (h : Equation29228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X2 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29229_implies_Equation2 (G : Type*) [Magma G] (h : Equation29229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X2 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29230_implies_Equation2 (G : Type*) [Magma G] (h : Equation29230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X2 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29231_implies_Equation2 (G : Type*) [Magma G] (h : Equation29231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X2 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29233_implies_Equation2 (G : Type*) [Magma G] (h : Equation29233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X3 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29234_implies_Equation2 (G : Type*) [Magma G] (h : Equation29234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X3 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29235_implies_Equation2 (G : Type*) [Magma G] (h : Equation29235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X3 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation29236_implies_Equation2 (G : Type*) [Magma G] (h : Equation29236 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X3 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29237_implies_Equation2 (G : Type*) [Magma G] (h : Equation29237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X3 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29239_implies_Equation2 (G : Type*) [Magma G] (h : Equation29239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X4 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29240_implies_Equation2 (G : Type*) [Magma G] (h : Equation29240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X4 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29241_implies_Equation2 (G : Type*) [Magma G] (h : Equation29241 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X4 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29242_implies_Equation2 (G : Type*) [Magma G] (h : Equation29242 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X4 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29243_implies_Equation2 (G : Type*) [Magma G] (h : Equation29243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X4 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29245_implies_Equation2 (G : Type*) [Magma G] (h : Equation29245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X5 ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29246_implies_Equation2 (G : Type*) [Magma G] (h : Equation29246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X5 ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29247_implies_Equation2 (G : Type*) [Magma G] (h : Equation29247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X5 ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29248_implies_Equation2 (G : Type*) [Magma G] (h : Equation29248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X5 ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29249_implies_Equation2 (G : Type*) [Magma G] (h : Equation29249 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X5 ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29250_implies_Equation2 (G : Type*) [Magma G] (h : Equation29250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ (X5 ◇ X6)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation29456_implies_Equation2 (G : Type*) [Magma G] (h : Equation29456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq66 eq15


@[equational_result]
theorem Equation29459_implies_Equation2 (G : Type*) [Magma G] (h : Equation29459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation29461_implies_Equation2 (G : Type*) [Magma G] (h : Equation29461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3))))) = X1 := superpose eq7 eq7
  have eq20 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = X0 := superpose eq10 eq10
  have eq21 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X2))) = ((X1 ◇ X0) ◇ X1) := superpose eq10 eq7
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = X2 := superpose eq10 eq7
  have eq48 (X0 X1 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X1 := superpose eq10 eq20
  have eq66 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq10 eq24
  have eq88 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq10 eq48
  have eq123 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0)) = ((X3 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X3) := superpose eq24 eq21
  have eq135 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X1) = X1 := superpose eq21 eq48
  have eq143 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0)) = X1 := superpose eq66 eq123
  have eq152 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq88 eq135
  have eq153 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) = X1 := superpose eq152 eq143
  have eq173 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X0) = X1 := superpose eq152 eq153
  have eq174 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = X1 := superpose eq152 eq173
  have eq175 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq152 eq174
  have eq176 (X0 X3 : G) : X0 = X3 := superpose eq175 eq175
  have eq178 (X0 : G) : sK0 ≠ X0 := superpose eq176 eq8
  subsumption eq178 eq176


@[equational_result]
theorem Equation29462_implies_Equation2 (G : Type*) [Magma G] (h : Equation29462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation29463_implies_Equation2 (G : Type*) [Magma G] (h : Equation29463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation29466_implies_Equation2 (G : Type*) [Magma G] (h : Equation29466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29469_implies_Equation2 (G : Type*) [Magma G] (h : Equation29469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29471_implies_Equation2 (G : Type*) [Magma G] (h : Equation29471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ (X3 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) = ((X1 ◇ (((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2))))) = X1 := superpose eq7 eq9
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq49 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = X2 := superpose eq13 eq7
  have eq60 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X1) = ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq13 eq29
  have eq68 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) := superpose eq29 eq7
  have eq84 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq60 eq29
  have eq103 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq13 eq49
  have eq123 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq103 eq68
  have eq126 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq103 eq84
  have eq143 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) = X1 := superpose eq123 eq13
  have eq180 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) = X1 := superpose eq123 eq143
  have eq207 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq180 eq180
  have eq213 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq126 eq207
  have eq214 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X1 := superpose eq213 eq180
  have eq229 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq213 eq214
  have eq230 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq213 eq229
  have eq231 (X0 X3 : G) : X0 = X3 := superpose eq230 eq230
  have eq233 (X0 : G) : sK0 ≠ X0 := superpose eq231 eq8
  subsumption eq233 eq231


@[equational_result]
theorem Equation29473_implies_Equation2 (G : Type*) [Magma G] (h : Equation29473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ (X3 ◇ X0))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29475_implies_Equation2 (G : Type*) [Magma G] (h : Equation29475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X3 ◇ X0))))) = X1 := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq10 eq9
  have eq31 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq10 eq26
  have eq88 (X0 X3 : G) : X0 = X3 := superpose eq7 eq31
  have eq181 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq181 eq88


@[equational_result]
theorem Equation29476_implies_Equation2 (G : Type*) [Magma G] (h : Equation29476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq48 eq11


@[equational_result]
theorem Equation29477_implies_Equation2 (G : Type*) [Magma G] (h : Equation29477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation29479_implies_Equation2 (G : Type*) [Magma G] (h : Equation29479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1))))) = ((X1 ◇ (((X2 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1))))) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X3)))) = X1 := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq7 eq10
  have eq44 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq14 eq14
  have eq54 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq14 eq9
  have eq57 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) = X0 := superpose eq54 eq26
  have eq70 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq57 eq7
  have eq111 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq70 eq44
  have eq145 (X0 X1 : G) : X0 = X1 := superpose eq111 eq54
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq145 eq8
  subsumption eq168 eq145


@[equational_result]
theorem Equation29481_implies_Equation2 (G : Type*) [Magma G] (h : Equation29481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation29483_implies_Equation2 (G : Type*) [Magma G] (h : Equation29483 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X3 ◇ X3)))) = ((X1 ◇ (((X2 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X3 ◇ X3)))) ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X3 ◇ X3))))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X0 := superpose eq10 eq7
  have eq20 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X0)) ◇ X2) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) := superpose eq7 eq9
  have eq28 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X0 := superpose eq15 eq20
  have eq31 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose eq15 eq15
  have eq33 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ X0) := superpose eq10 eq15
  have eq40 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq33 eq28
  have eq64 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq40 eq15
  have eq65 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq40 eq64
  have eq68 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq65 eq40
  have eq69 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq15 eq68
  have eq72 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq69 eq15
  have eq74 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := superpose eq69 eq31
  have eq75 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := superpose eq69 eq33
  have eq87 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq69 eq74
  have eq88 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq69 eq75
  have eq149 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq87 eq88
  have eq153 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq149 eq72
  have eq159 (X0 X2 : G) : X0 = X2 := superpose eq153 eq153
  have eq164 (X0 : G) : sK0 ≠ X0 := superpose eq159 eq8
  subsumption eq164 eq159


@[equational_result]
theorem Equation29484_implies_Equation2 (G : Type*) [Magma G] (h : Equation29484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation29485_implies_Equation2 (G : Type*) [Magma G] (h : Equation29485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation29487_implies_Equation2 (G : Type*) [Magma G] (h : Equation29487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X0 ◇ (X4 ◇ X5))))) = X1 := superpose eq7 eq7
  have eq38 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq11 eq7
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq11 eq38
  have eq109 (X0 X4 : G) : X0 = X4 := superpose eq7 eq46
  have eq205 (X0 : G) : sK0 ≠ X0 := superpose eq109 eq8
  subsumption eq205 eq109


@[equational_result]
theorem Equation29488_implies_Equation2 (G : Type*) [Magma G] (h : Equation29488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq58 eq12


@[equational_result]
theorem Equation29489_implies_Equation2 (G : Type*) [Magma G] (h : Equation29489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation29490_implies_Equation2 (G : Type*) [Magma G] (h : Equation29490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation29493_implies_Equation2 (G : Type*) [Magma G] (h : Equation29493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq66 eq15


@[equational_result]
theorem Equation29496_implies_Equation2 (G : Type*) [Magma G] (h : Equation29496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X2 ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq10
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq66 eq15


@[equational_result]
theorem Equation29498_implies_Equation2 (G : Type*) [Magma G] (h : Equation29498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) = ((X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ (X1 ◇ X0))) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))))) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2)))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq9
  have eq20 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (((((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X3) ◇ (X1 ◇ (((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X3) ◇ (X1 ◇ X4)))) ◇ X0) ◇ (((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X3) ◇ (X1 ◇ (((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X3) ◇ (X1 ◇ X4))))) := superpose eq7 eq10
  have eq23 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))))) = X1 := superpose eq7 eq10
  have eq38 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq17 eq23
  have eq43 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := superpose eq38 eq38
  have eq46 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3)))) := superpose eq10 eq38
  have eq71 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (((((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) ◇ X0) ◇ (((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))))) := superpose eq46 eq20
  have eq81 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq43 eq71
  have eq82 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := superpose eq43 eq81
  have eq83 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X0 := superpose eq82 eq7
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq38 eq83
  have eq111 (X0 X3 : G) : X0 = X3 := superpose eq83 eq101
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq111 eq8
  subsumption eq145 eq111


@[equational_result]
theorem Equation29499_implies_Equation2 (G : Type*) [Magma G] (h : Equation29499 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) ◇ (X2 ◇ X0)) ◇ X3) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq7 eq10
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq122 eq38


@[equational_result]
theorem Equation29500_implies_Equation2 (G : Type*) [Magma G] (h : Equation29500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ (X3 ◇ X0)) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq70 eq15


@[equational_result]
theorem Equation29503_implies_Equation2 (G : Type*) [Magma G] (h : Equation29503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X0))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29506_implies_Equation2 (G : Type*) [Magma G] (h : Equation29506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X0))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29508_implies_Equation2 (G : Type*) [Magma G] (h : Equation29508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0))) := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0))) := superpose eq10 eq10
  have eq18 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := superpose eq10 eq10
  have eq19 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0))) ◇ (X0 ◇ (X0 ◇ X1))) = X2 := superpose eq10 eq7
  have eq23 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X2 ◇ X0)) := superpose eq7 eq14
  have eq25 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X2 := superpose eq16 eq19
  have eq59 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := superpose eq7 eq25
  have eq83 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) ◇ X1) = ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X3)))) ◇ X0) := superpose eq7 eq23
  have eq162 (X0 X1 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) = X0 := superpose eq59 eq7
  have eq231 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq162 eq18
  have eq245 (X0 X1 X3 : G) : ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X3)))) ◇ X0) = X1 := superpose eq231 eq83
  have eq248 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X0 := superpose eq245 eq23
  have eq316 (X0 X1 : G) : X0 = X1 := superpose eq7 eq248
  have eq334 (X0 : G) : sK0 ≠ X0 := superpose eq316 eq8
  subsumption eq334 eq316


@[equational_result]
theorem Equation29510_implies_Equation2 (G : Type*) [Magma G] (h : Equation29510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X0))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29512_implies_Equation2 (G : Type*) [Magma G] (h : Equation29512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)))) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq9 eq9
  have eq17 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) = X2 := superpose eq13 eq10
  have eq62 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) := superpose eq14 eq14
  have eq65 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X1 := superpose eq14 eq7
  have eq72 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((((X2 ◇ (X1 ◇ ((X0 ◇ X3) ◇ X4))) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ (X1 ◇ ((X0 ◇ X3) ◇ X4))) ◇ X2)) := superpose eq14 eq17
  have eq92 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X1 := superpose eq65 eq65
  have eq116 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X3)) ◇ X1) = X0 := superpose eq92 eq62
  have eq119 (X0 X1 X3 : G) : (X0 ◇ X3) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose eq116 eq72
  have eq121 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ X3) := superpose eq92 eq119
  have eq179 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X1) ◇ X3) = X0 := superpose eq65 eq121
  have eq258 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X2 := superpose eq179 eq17
  have eq285 (X0 X3 : G) : X0 = X3 := superpose eq258 eq258
  have eq332 (X0 : G) : sK0 ≠ X0 := superpose eq285 eq8
  subsumption eq332 eq285


@[equational_result]
theorem Equation29514_implies_Equation2 (G : Type*) [Magma G] (h : Equation29514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X0)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation29516_implies_Equation2 (G : Type*) [Magma G] (h : Equation29516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq27 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) = X1 := superpose eq10 eq7
  have eq29 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose eq10 eq9
  have eq46 (X0 X1 X2 : G) : (((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X2 := superpose eq27 eq27
  have eq48 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq27 eq9
  have eq57 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = (X0 ◇ X1) := superpose eq48 eq29
  have eq64 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X1) ◇ X2) = X0 := superpose eq27 eq57
  have eq105 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X2 := superpose eq64 eq46
  have eq106 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq48 eq105
  have eq107 (X0 X3 : G) : X0 = X3 := superpose eq7 eq106
  have eq207 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq207 eq107


@[equational_result]
theorem Equation29518_implies_Equation2 (G : Type*) [Magma G] (h : Equation29518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X3 ◇ X0)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation29521_implies_Equation2 (G : Type*) [Magma G] (h : Equation29521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))))) ◇ (X3 ◇ X0)) ◇ X2) = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq9
  have eq27 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ X0)) ◇ X2) = X3 := superpose eq17 eq9
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2) = X0 := superpose eq17 eq7
  have eq40 (X0 X1 X2 X3 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) ◇ X2) = X3 := superpose eq17 eq27
  have eq55 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq17 eq40
  have eq62 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq29 eq40
  have eq67 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X2 := superpose eq62 eq55
  have eq69 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq62 eq67
  have eq70 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X2) = X0 := superpose eq69 eq29
  have eq85 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq69 eq70
  have eq86 (X0 X1 : G) : X0 = X1 := superpose eq17 eq85
  have eq91 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq91 eq86


@[equational_result]
theorem Equation29522_implies_Equation2 (G : Type*) [Magma G] (h : Equation29522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ X0)) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation29524_implies_Equation2 (G : Type*) [Magma G] (h : Equation29524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4)))) ◇ (X5 ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ X5)))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4)))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq9
  have eq19 (X0 X1 X5 : G) : ((((X1 ◇ X0) ◇ X1) ◇ (X5 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) = X5 := superpose eq14 eq10
  have eq31 (X0 X1 X2 X3 : G) : (((((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2))) = X3 := superpose eq19 eq7
  have eq74 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ ((((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X4)))) ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) := superpose eq19 eq11
  have eq77 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := superpose eq11 eq7
  have eq78 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X2 ◇ X3))) = X1 := superpose eq11 eq7
  have eq106 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X2) = (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X3 ◇ X4))) := superpose eq19 eq78
  have eq125 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X3 ◇ X2)) ◇ (X0 ◇ X1)) = X3 := superpose eq78 eq19
  have eq126 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := superpose eq78 eq7
  have eq141 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) := superpose eq106 eq74
  have eq149 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ X0) = X3 := superpose eq125 eq141
  have eq150 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X1) ◇ (X0 ◇ X2))) = X3 := superpose eq149 eq31
  have eq155 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = (X0 ◇ X1) := superpose eq126 eq77
  have eq167 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X1) ◇ X4) = X0 := superpose eq78 eq155
  have eq231 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq167 eq150
  have eq236 (X0 X4 : G) : X0 = X4 := superpose eq7 eq231
  have eq359 (X0 : G) : sK0 ≠ X0 := superpose eq236 eq8
  subsumption eq359 eq236


@[equational_result]
theorem Equation29525_implies_Equation2 (G : Type*) [Magma G] (h : Equation29525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X5))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4)))) ◇ (X5 ◇ X0)) ◇ X2) = X5 := superpose eq7 eq7
  have eq23 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0)) ◇ X4) = X3 := superpose eq9 eq7
  have eq32 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X1 ◇ (X0 ◇ (X1 ◇ (((X2 ◇ X3) ◇ X4) ◇ X5)))) ◇ (X6 ◇ X0)) ◇ (X7 ◇ X6)) ◇ X2) = X7 := superpose eq7 eq10
  have eq51 (X2 X6 X7 : G) : (X6 ◇ X2) = X7 := superpose eq23 eq32
  have eq52 (X0 X4 : G) : X0 = X4 := superpose eq7 eq51
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq149 eq52


@[equational_result]
theorem Equation29526_implies_Equation2 (G : Type*) [Magma G] (h : Equation29526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X5) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) ◇ (X5 ◇ X0)) ◇ X4) = X5 := superpose eq7 eq7
  have eq12 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq9 eq10
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation29527_implies_Equation2 (G : Type*) [Magma G] (h : Equation29527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X7 : G) : (((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ (X4 ◇ X0)) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq10
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation29529_implies_Equation2 (G : Type*) [Magma G] (h : Equation29529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0))))) = X1 := superpose eq7 eq7
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq10 eq9
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq7 eq26
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq117 eq32


@[equational_result]
theorem Equation29530_implies_Equation2 (G : Type*) [Magma G] (h : Equation29530 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq50 eq11


@[equational_result]
theorem Equation29531_implies_Equation2 (G : Type*) [Magma G] (h : Equation29531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation29533_implies_Equation2 (G : Type*) [Magma G] (h : Equation29533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = ((X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0))) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq10 eq10
  have eq38 (X0 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X2) ◇ X4)) = X0 := superpose eq10 eq12
  have eq79 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = (X1 ◇ X1) := superpose eq38 eq9
  have eq83 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq79 eq7
  have eq87 (X0 X2 : G) : X0 = X2 := superpose eq10 eq83
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq106 eq87


@[equational_result]
theorem Equation29535_implies_Equation2 (G : Type*) [Magma G] (h : Equation29535 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation29538_implies_Equation2 (G : Type*) [Magma G] (h : Equation29538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq51 eq11


@[equational_result]
theorem Equation29539_implies_Equation2 (G : Type*) [Magma G] (h : Equation29539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation29541_implies_Equation2 (G : Type*) [Magma G] (h : Equation29541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ (X0 ◇ (X4 ◇ (X0 ◇ X5))))) = X1 := superpose eq7 eq7
  have eq36 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq11 eq7
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq36
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq129 eq47


@[equational_result]
theorem Equation29542_implies_Equation2 (G : Type*) [Magma G] (h : Equation29542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq57 eq12


@[equational_result]
theorem Equation29543_implies_Equation2 (G : Type*) [Magma G] (h : Equation29543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation29544_implies_Equation2 (G : Type*) [Magma G] (h : Equation29544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation29546_implies_Equation2 (G : Type*) [Magma G] (h : Equation29546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq10 eq10
  have eq14 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X1 := superpose eq10 eq10
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X1 ◇ X3) ◇ X5)) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq12 eq12
  have eq39 (X0 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X2) ◇ X4)) = X0 := superpose eq10 eq12
  have eq80 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = X1 := superpose eq39 eq37
  have eq86 (X0 X1 X2 X3 X5 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X5))) = X3 := superpose eq12 eq14
  have eq117 (X1 X2 X3 : G) : (X2 ◇ X1) = X3 := superpose eq80 eq86
  have eq118 (X0 X3 : G) : X0 = X3 := superpose eq7 eq117
  have eq258 (X0 : G) : sK0 ≠ X0 := superpose eq118 eq8
  subsumption eq258 eq118


@[equational_result]
theorem Equation29548_implies_Equation2 (G : Type*) [Magma G] (h : Equation29548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) ◇ (X3 ◇ (X4 ◇ X0))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29550_implies_Equation2 (G : Type*) [Magma G] (h : Equation29550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X3 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ X1)))))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq9 eq9
  have eq23 (X0 X1 : G) : (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq10 eq10
  have eq26 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) = X1 := superpose eq10 eq7
  have eq27 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) := superpose eq10 eq7
  have eq31 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq9 eq23
  have eq39 (X0 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X2) ◇ X4)) = X0 := superpose eq9 eq12
  have eq76 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq39 eq31
  have eq77 (X0 X2 : G) : (X2 ◇ (X0 ◇ X0)) = X2 := superpose eq39 eq27
  have eq86 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ X0)) = X1 := superpose eq76 eq26
  have eq89 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq76 eq77
  have eq90 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = X1 := superpose eq89 eq86
  have eq97 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq89 eq90
  have eq98 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq89 eq97
  have eq99 (X0 X1 : G) : X0 = X1 := superpose eq76 eq98
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq99 eq8
  subsumption eq107 eq99


@[equational_result]
theorem Equation29552_implies_Equation2 (G : Type*) [Magma G] (h : Equation29552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ (X3 ◇ (X4 ◇ X0))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29556_implies_Equation2 (G : Type*) [Magma G] (h : Equation29556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ (X4 ◇ X0))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29558_implies_Equation2 (G : Type*) [Magma G] (h : Equation29558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = ((X1 ◇ X0) ◇ X1) := superpose eq10 eq10
  have eq47 (X0 X1 X5 : G) : ((X5 ◇ X1) ◇ X5) = X0 := superpose eq7 eq13
  have eq143 (X0 X4 : G) : X0 = X4 := superpose eq7 eq47
  have eq259 (X0 : G) : sK0 ≠ X0 := superpose eq143 eq8
  subsumption eq259 eq143


@[equational_result]
theorem Equation29559_implies_Equation2 (G : Type*) [Magma G] (h : Equation29559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ (X4 ◇ (X5 ◇ X0))) ◇ X5) = X4 := superpose eq7 eq7
  have eq22 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq156 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq156 eq57


@[equational_result]
theorem Equation29560_implies_Equation2 (G : Type*) [Magma G] (h : Equation29560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ (X4 ◇ (X5 ◇ X0))) ◇ X3) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X5) = X2 := superpose eq7 eq7
  have eq12 (X0 X3 X4 : G) : (X0 ◇ X3) = X4 := superpose eq10 eq9
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation29561_implies_Equation2 (G : Type*) [Magma G] (h : Equation29561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 X7 : G) : (((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ (X4 ◇ (X5 ◇ X0))) ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq9
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29564_implies_Equation2 (G : Type*) [Magma G] (h : Equation29564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq48 eq11


@[equational_result]
theorem Equation29565_implies_Equation2 (G : Type*) [Magma G] (h : Equation29565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation29569_implies_Equation2 (G : Type*) [Magma G] (h : Equation29569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation29571_implies_Equation2 (G : Type*) [Magma G] (h : Equation29571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3)))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3))))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X0) = ((X4 ◇ X1) ◇ X4) := superpose eq9 eq9
  have eq18 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ (X3 ◇ (X3 ◇ X3))) ◇ (X4 ◇ (X4 ◇ X4)))) = (((X0 ◇ X1) ◇ X0) ◇ (X5 ◇ (X5 ◇ X5))) := superpose eq9 eq9
  have eq20 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X2))) ◇ (X3 ◇ (X3 ◇ X3)))) = X0 := superpose eq7 eq9
  have eq28 (X0 X1 X5 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X5 ◇ (X5 ◇ X5))) = X1 := superpose eq20 eq18
  have eq96 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq15 eq28
  have eq134 (X0 X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X3 := superpose eq96 eq28
  have eq141 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X1) := superpose eq96 eq15
  have eq144 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X0)) = X1 := superpose eq96 eq10
  have eq165 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq7 eq144
  have eq166 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X1) = X0 := superpose eq165 eq7
  have eq167 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3)))) := superpose eq165 eq9
  have eq168 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3))))) = X1 := superpose eq165 eq10
  have eq175 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X3)))) = X0 := superpose eq165 eq20
  have eq226 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X1) = X0 := superpose eq165 eq166
  have eq227 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq165 eq167
  have eq228 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X2 ◇ X2) ◇ (X0 ◇ X3)) := superpose eq165 eq227
  have eq229 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq165 eq228
  have eq230 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X3 ◇ X3)))) = X1 := superpose eq165 eq168
  have eq231 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3))) = X1 := superpose eq165 eq230
  have eq232 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X1 := superpose eq165 eq231
  have eq257 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = X0 := superpose eq165 eq175
  have eq258 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X3)) = X0 := superpose eq165 eq257
  have eq259 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq165 eq258
  have eq260 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq165 eq259
  have eq261 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X3)) = X0 := superpose eq165 eq260
  have eq263 (X0 X2 X3 : G) : (((X2 ◇ X3) ◇ X2) ◇ X0) = X3 := superpose eq261 eq134
  have eq264 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = X1 := superpose eq263 eq141
  have eq268 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X3)) = X0 := superpose eq264 eq229
  have eq271 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq268 eq232
  have eq273 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq268 eq226
  have eq295 (X0 X1 : G) : X0 = X1 := superpose eq273 eq271
  have eq300 (X0 : G) : sK0 ≠ X0 := superpose eq295 eq8
  subsumption eq300 eq295


@[equational_result]
theorem Equation29572_implies_Equation2 (G : Type*) [Magma G] (h : Equation29572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq11 (X0 X3 : G) : X0 = X3 := superpose eq7 eq10
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq63 eq11


@[equational_result]
theorem Equation29573_implies_Equation2 (G : Type*) [Magma G] (h : Equation29573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation29575_implies_Equation2 (G : Type*) [Magma G] (h : Equation29575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ (X4 ◇ (X4 ◇ X5)))) ◇ X0))) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X0 ◇ (X4 ◇ (X4 ◇ X5))))) = X1 := superpose eq7 eq7
  have eq140 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X1) = X2 := superpose eq11 eq9
  have eq167 (X0 X4 : G) : X0 = X4 := superpose eq7 eq140
  have eq305 (X0 : G) : sK0 ≠ X0 := superpose eq167 eq8
  subsumption eq305 eq167


@[equational_result]
theorem Equation29576_implies_Equation2 (G : Type*) [Magma G] (h : Equation29576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq72 eq12


@[equational_result]
theorem Equation29577_implies_Equation2 (G : Type*) [Magma G] (h : Equation29577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq56 eq12


@[equational_result]
theorem Equation29578_implies_Equation2 (G : Type*) [Magma G] (h : Equation29578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation29580_implies_Equation2 (G : Type*) [Magma G] (h : Equation29580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X0 ◇ (X4 ◇ (X5 ◇ X0))))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq10 eq10
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((X1 ◇ X3) ◇ X5)) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq13 eq13
  have eq40 (X0 X2 X3 X4 : G) : (X3 ◇ ((X0 ◇ X2) ◇ X4)) = X0 := superpose eq10 eq13
  have eq76 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = X1 := superpose eq40 eq37
  have eq89 (X0 X1 X2 X3 X5 X6 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ (X5 ◇ (X6 ◇ X2))))) = X3 := superpose eq13 eq11
  have eq119 (X1 X2 X3 : G) : (X2 ◇ X1) = X3 := superpose eq76 eq89
  have eq120 (X0 X4 : G) : X0 = X4 := superpose eq7 eq119
  have eq226 (X0 : G) : sK0 ≠ X0 := superpose eq120 eq8
  subsumption eq226 eq120


@[equational_result]
theorem Equation29581_implies_Equation2 (G : Type*) [Magma G] (h : Equation29581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation29582_implies_Equation2 (G : Type*) [Magma G] (h : Equation29582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq40 eq12


@[equational_result]
theorem Equation29583_implies_Equation2 (G : Type*) [Magma G] (h : Equation29583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation29585_implies_Equation2 (G : Type*) [Magma G] (h : Equation29585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq10 eq10
  have eq48 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq7 eq13
  have eq129 (X0 X4 : G) : X0 = X4 := superpose eq7 eq48
  have eq227 (X0 : G) : sK0 ≠ X0 := superpose eq129 eq8
  subsumption eq227 eq129


@[equational_result]
theorem Equation29586_implies_Equation2 (G : Type*) [Magma G] (h : Equation29586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X3) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq46 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq134 eq46


@[equational_result]
theorem Equation29587_implies_Equation2 (G : Type*) [Magma G] (h : Equation29587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X5) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq10
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq15
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq153 eq57


@[equational_result]
theorem Equation29588_implies_Equation2 (G : Type*) [Magma G] (h : Equation29588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation29590_implies_Equation2 (G : Type*) [Magma G] (h : Equation29590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X4 ◇ (X5 ◇ X4)))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq36 (X0 X1 X4 : G) : ((X4 ◇ X1) ◇ X4) = X0 := superpose eq9 eq10
  have eq72 (X0 X4 : G) : X0 = X4 := superpose eq7 eq36
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq162 eq72


@[equational_result]
theorem Equation29591_implies_Equation2 (G : Type*) [Magma G] (h : Equation29591 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq43 eq12


@[equational_result]
theorem Equation29592_implies_Equation2 (G : Type*) [Magma G] (h : Equation29592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq59 eq12


@[equational_result]
theorem Equation29593_implies_Equation2 (G : Type*) [Magma G] (h : Equation29593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation29595_implies_Equation2 (G : Type*) [Magma G] (h : Equation29595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X4 ◇ (X5 ◇ X5)))) = ((X1 ◇ X0) ◇ X1) := superpose eq7 eq7
  have eq35 (X0 X1 X4 : G) : ((X4 ◇ X1) ◇ X4) = X0 := superpose eq9 eq10
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq35
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq154 eq67


@[equational_result]
theorem Equation29596_implies_Equation2 (G : Type*) [Magma G] (h : Equation29596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq12 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq58 eq12


@[equational_result]
theorem Equation29597_implies_Equation2 (G : Type*) [Magma G] (h : Equation29597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation29598_implies_Equation2 (G : Type*) [Magma G] (h : Equation29598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation29600_implies_Equation2 (G : Type*) [Magma G] (h : Equation29600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X3)) := superpose eq10 eq10
  have eq51 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq7 eq14
  have eq181 (X0 X5 : G) : X0 = X5 := superpose eq7 eq51
  have eq331 (X0 : G) : sK0 ≠ X0 := superpose eq181 eq8
  subsumption eq331 eq181


@[equational_result]
theorem Equation29601_implies_Equation2 (G : Type*) [Magma G] (h : Equation29601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq45 eq13


@[equational_result]
theorem Equation29602_implies_Equation2 (G : Type*) [Magma G] (h : Equation29602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq42 eq14


@[equational_result]
theorem Equation29603_implies_Equation2 (G : Type*) [Magma G] (h : Equation29603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X4) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X4 X7 : G) : (X0 ◇ X7) = X4 := superpose eq7 eq7
  have eq13 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation29604_implies_Equation2 (G : Type*) [Magma G] (h : Equation29604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X5 X9 : G) : (X0 ◇ X9) = X5 := superpose eq7 eq7
  have eq13 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation29607_implies_Equation2 (G : Type*) [Magma G] (h : Equation29607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq11
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq71 eq15


@[equational_result]
theorem Equation29610_implies_Equation2 (G : Type*) [Magma G] (h : Equation29610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq11
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq73 eq15


@[equational_result]
theorem Equation29612_implies_Equation2 (G : Type*) [Magma G] (h : Equation29612 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) = ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) ◇ X0))) ◇ X1) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X3)))) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X3))))) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X2 ◇ (X2 ◇ X0)) ◇ X2) := superpose eq7 eq9
  have eq20 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))))) = X0 := superpose eq7 eq10
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X5)))) ◇ X4) ◇ X0))) ◇ (((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X5)))) ◇ X4)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X5)))) ◇ X4) ◇ X0)))) = X1 := superpose eq10 eq10
  have eq45 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)))) = X0 := superpose eq7 eq15
  have eq49 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = X1 := superpose eq15 eq7
  have eq77 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq45 eq20
  have eq82 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq77 eq49
  have eq90 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) ◇ (((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X5)))) ◇ X4)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0))) = X1 := superpose eq82 eq26
  have eq127 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X5)))) ◇ X4)) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X0)) = X1 := superpose eq82 eq90
  have eq128 (X0 X1 X3 X4 X5 : G) : ((X0 ◇ (((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X5)))) ◇ X4)) ◇ X0) = X1 := superpose eq82 eq127
  have eq129 (X0 X1 X3 X4 X5 : G) : ((((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X5)))) ◇ X4) ◇ X0) = X1 := superpose eq82 eq128
  have eq130 (X0 X1 X4 : G) : (X4 ◇ X0) = X1 := superpose eq82 eq129
  have eq131 (X0 X3 : G) : X0 = X3 := superpose eq130 eq130
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq131 eq8
  subsumption eq133 eq131


@[equational_result]
theorem Equation29613_implies_Equation2 (G : Type*) [Magma G] (h : Equation29613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) = ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) ◇ X0))) ◇ X3) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))))) ◇ X0) ◇ X3) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq7 eq10
  have eq26 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X2 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq7 eq9
  have eq37 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := superpose eq17 eq17
  have eq48 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X2)) ◇ X2) = ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))))) ◇ X0) := superpose eq7 eq26
  have eq60 (X0 X1 X2 : G) : (X2 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))) = (((X0 ◇ (X0 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq26 eq26
  have eq64 (X0 X1 X2 X3 : G) : (((X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1))) ◇ X3) ◇ X1) = X1 := superpose eq26 eq10
  have eq91 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X2 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1)))))) := superpose eq17 eq60
  have eq93 (X0 X1 X2 X3 : G) : (((X2 ◇ (X2 ◇ X0)) ◇ X3) ◇ X1) = X1 := superpose eq17 eq64
  have eq95 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X1 := superpose eq93 eq37
  have eq120 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) := superpose eq95 eq91
  have eq124 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0) = ((X3 ◇ (X3 ◇ X2)) ◇ X2) := superpose eq95 eq48
  have eq146 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := superpose eq95 eq120
  have eq147 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq95 eq146
  have eq158 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0) = X2 := superpose eq147 eq124
  have eq159 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) = X2 := superpose eq147 eq158
  have eq160 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq147 eq159
  have eq161 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq147 eq160
  have eq162 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq147 eq161
  have eq173 (X0 X1 : G) : X0 = X1 := superpose eq147 eq162
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq173 eq8
  subsumption eq175 eq173


@[equational_result]
theorem Equation29614_implies_Equation2 (G : Type*) [Magma G] (h : Equation29614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0) ◇ X5) = X3 := superpose eq7 eq7
  have eq14 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq11
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq75 eq15


@[equational_result]
theorem Equation29617_implies_Equation2 (G : Type*) [Magma G] (h : Equation29617 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X2 ◇ X0))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29620_implies_Equation2 (G : Type*) [Magma G] (h : Equation29620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X2) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X2 ◇ X0))) ◇ X3) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq7 eq9
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29622_implies_Equation2 (G : Type*) [Magma G] (h : Equation29622 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ X0))) = ((X1 ◇ (X1 ◇ X3)) ◇ X1) := superpose eq7 eq10
  have eq20 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X2)) = X1 := superpose eq10 eq7
  have eq22 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X3)) ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) = X3 := superpose eq13 eq9
  have eq55 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := superpose eq7 eq20
  have eq58 (X0 X1 X2 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = X2 := superpose eq22 eq20
  have eq64 (X0 X1 : G) : ((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X1 := superpose eq20 eq7
  have eq105 (X0 X1 X2 X5 : G) : (X1 ◇ X0) = (X1 ◇ (((X2 ◇ (X2 ◇ X0)) ◇ X2) ◇ X5)) := superpose eq22 eq55
  have eq190 (X0 X1 X2 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) = X2 := superpose eq105 eq58
  have eq193 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq64 eq190
  have eq312 (X0 X3 : G) : X0 = X3 := superpose eq7 eq193
  have eq551 (X0 : G) : sK0 ≠ X0 := superpose eq312 eq8
  subsumption eq551 eq312


@[equational_result]
theorem Equation29624_implies_Equation2 (G : Type*) [Magma G] (h : Equation29624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ X0))) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq9
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq27 eq14


@[equational_result]
theorem Equation29626_implies_Equation2 (G : Type*) [Magma G] (h : Equation29626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X3 ◇ X0)))) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X3 ◇ X0))))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ X3))) := superpose eq9 eq9
  have eq17 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))))) = X0 := superpose eq7 eq10
  have eq36 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ (X4 ◇ ((X1 ◇ X3) ◇ X5))) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) := superpose eq12 eq12
  have eq37 (X0 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X4))) = X0 := superpose eq7 eq12
  have eq38 (X0 X2 X3 X4 : G) : (X3 ◇ (X3 ◇ ((X0 ◇ X2) ◇ X4))) = X0 := superpose eq9 eq12
  have eq75 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq37 eq17
  have eq77 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) = X1 := superpose eq38 eq36
  have eq89 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq7 eq75
  have eq116 (X0 X1 X2 : G) : (X0 ◇ X2) = X1 := superpose eq89 eq77
  have eq186 (X0 X3 : G) : X0 = X3 := superpose eq116 eq116
  have eq191 (X0 : G) : sK0 ≠ X0 := superpose eq186 eq8
  subsumption eq191 eq186


@[equational_result]
theorem Equation29628_implies_Equation2 (G : Type*) [Magma G] (h : Equation29628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X3) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X0) ◇ X5) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X5 : G) : (X0 ◇ X5) = X3 := superpose eq7 eq11
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq46 eq14


@[equational_result]
theorem Equation29630_implies_Equation2 (G : Type*) [Magma G] (h : Equation29630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ X1) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X1) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X3 ◇ (X2 ◇ X1))))) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) = ((X2 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X4))))) ◇ X2) := superpose eq9 eq10
  have eq29 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X2 ◇ X0)) = X1 := superpose eq10 eq7
  have eq39 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = (((((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) := superpose eq29 eq29
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) = X1 := superpose eq29 eq29
  have eq44 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) = X2 := superpose eq7 eq29
  have eq57 (X0 X1 X2 X3 : G) : (X2 ◇ X1) = ((X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) := superpose eq44 eq39
  have eq59 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq41 eq57
  have eq60 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq59 eq25
  have eq63 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X1 := superpose eq59 eq29
  have eq80 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq59 eq60
  have eq81 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq59 eq80
  have eq86 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq59 eq63
  have eq95 (X0 X1 : G) : X0 = X1 := superpose eq81 eq86
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq95 eq8
  subsumption eq100 eq95


