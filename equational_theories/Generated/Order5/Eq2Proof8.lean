import equational_theories.Equations.All
import equational_theories.MagmaOp
import equational_theories.Superposition
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ByContra
set_option linter.unusedVariables false

@[equational_result]
theorem Equation18195_implies_Equation2 (G : Type*) [Magma G] (h : Equation18195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X2 ◇ ((X3 ◇ X3) ◇ X2)) = (X0 ◇ (X4 ◇ ((X5 ◇ X5) ◇ X4))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq12 eq12
  have eq22 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ X5) ◇ X4))) = (X2 ◇ X3) := superpose eq16 eq9
  have eq27 (X0 X2 X3 X4 X5 : G) : (X2 ◇ X3) = (X0 ◇ (X4 ◇ X5)) := superpose eq16 eq22
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq12 eq27
  have eq43 (X0 X3 : G) : X0 = X3 := superpose eq12 eq34
  have eq76 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq76 eq43


@[equational_result]
theorem Equation18196_implies_Equation2 (G : Type*) [Magma G] (h : Equation18196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation18197_implies_Equation2 (G : Type*) [Magma G] (h : Equation18197 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation18199_implies_Equation2 (G : Type*) [Magma G] (h : Equation18199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq10 eq10
  have eq23 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq18 eq12
  have eq24 (X0 X5 : G) : X0 = X5 := superpose eq7 eq23
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq46 eq24


@[equational_result]
theorem Equation18200_implies_Equation2 (G : Type*) [Magma G] (h : Equation18200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq12
  have eq35 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq74 (X0 X4 : G) : X0 = X4 := superpose eq12 eq35
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq149 eq74


@[equational_result]
theorem Equation18201_implies_Equation2 (G : Type*) [Magma G] (h : Equation18201 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq12 eq16
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq66 eq22


@[equational_result]
theorem Equation18202_implies_Equation2 (G : Type*) [Magma G] (h : Equation18202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq12 eq18
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq47 eq32


@[equational_result]
theorem Equation18203_implies_Equation2 (G : Type*) [Magma G] (h : Equation18203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq12 eq16
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq66 eq22


@[equational_result]
theorem Equation18206_implies_Equation2 (G : Type*) [Magma G] (h : Equation18206 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq11 eq11
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq9 eq20
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq67 eq23


@[equational_result]
theorem Equation18209_implies_Equation2 (G : Type*) [Magma G] (h : Equation18209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2))) = X1 := superpose eq10 eq7
  have eq18 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq10 eq13
  have eq22 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq18 eq16
  have eq73 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq18 eq22
  have eq124 (X0 X1 : G) : X0 = X1 := superpose eq10 eq73
  have eq206 (X0 : G) : sK0 ≠ X0 := superpose eq124 eq8
  subsumption eq206 eq124


@[equational_result]
theorem Equation18211_implies_Equation2 (G : Type*) [Magma G] (h : Equation18211 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq9 eq9
  have eq22 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X1)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1)) := superpose eq7 eq10
  have eq25 (X0 X1 : G) : (X1 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq9 eq10
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq10 eq9
  have eq34 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq15 eq25
  have eq36 (X0 X1 X3 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ X3) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq30 eq12
  have eq37 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ (X2 ◇ X0)) = X2 := superpose eq30 eq10
  have eq72 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq37 eq15
  have eq74 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq15 eq15
  have eq76 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq9 eq15
  have eq94 (X0 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq76 eq74
  have eq96 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X1)) := superpose eq76 eq22
  have eq103 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq94 eq72
  have eq105 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq103 eq30
  have eq106 (X0 X1 X3 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ X3) ◇ (X1 ◇ X1)) := superpose eq105 eq36
  have eq112 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := superpose eq105 eq106
  have eq115 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X2) ◇ X1)) = (X0 ◇ X0) := superpose eq105 eq96
  have eq116 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X0 := superpose eq115 eq7
  have eq118 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq116 eq112
  have eq119 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq118 eq34
  have eq123 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = X0 := superpose eq118 eq94
  have eq131 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq118 eq123
  have eq132 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq131 eq119
  have eq142 (X0 X1 : G) : X0 = X1 := superpose eq132 eq131
  have eq144 (X0 : G) : sK0 ≠ X0 := superpose eq142 eq8
  subsumption eq144 eq142


@[equational_result]
theorem Equation18213_implies_Equation2 (G : Type*) [Magma G] (h : Equation18213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X5))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq10 eq9
  have eq27 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq10 eq12
  have eq36 (X0 X1 : G) : X0 = X1 := superpose eq10 eq27
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq69 eq36


@[equational_result]
theorem Equation18216_implies_Equation2 (G : Type*) [Magma G] (h : Equation18216 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (((X0 ◇ X0) ◇ X1) ◇ X2))) = X1 := superpose eq10 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq10 eq14
  have eq23 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X1 := superpose eq19 eq17
  have eq71 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq19 eq23
  have eq125 (X0 X1 : G) : X0 = X1 := superpose eq10 eq71
  have eq187 (X0 : G) : sK0 ≠ X0 := superpose eq125 eq8
  subsumption eq187 eq125


@[equational_result]
theorem Equation18219_implies_Equation2 (G : Type*) [Magma G] (h : Equation18219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq9 eq9
  have eq17 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose eq11 eq7
  have eq21 (X0 X1 : G) : X0 = X1 := superpose eq9 eq17
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq30 eq21


@[equational_result]
theorem Equation18221_implies_Equation2 (G : Type*) [Magma G] (h : Equation18221 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq21 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq7 eq10
  have eq30 (X0 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq21 eq10
  have eq31 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq21 eq7
  have eq38 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq9 eq21
  have eq42 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq30 eq38
  have eq49 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq21 eq31
  have eq54 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq31 eq49
  have eq57 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = X2 := superpose eq54 eq9
  have eq60 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := superpose eq54 eq42
  have eq66 (X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1))) = X2 := superpose eq60 eq57
  have eq69 (X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X2 := superpose eq60 eq66
  have eq78 (X0 X2 : G) : X0 = X2 := superpose eq69 eq69
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq83 eq78


@[equational_result]
theorem Equation18223_implies_Equation2 (G : Type*) [Magma G] (h : Equation18223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq13 eq7
  have eq28 (X0 X2 : G) : X0 = X2 := superpose eq10 eq20
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation18225_implies_Equation2 (G : Type*) [Magma G] (h : Equation18225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = ((X1 ◇ X1) ◇ ((X0 ◇ ((X2 ◇ X0) ◇ X3)) ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X1) = ((((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq20 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) := superpose eq10 eq7
  have eq35 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq9 eq7
  have eq39 (X0 X1 X3 : G) : ((X3 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X3))) = X0 := superpose eq7 eq20
  have eq84 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)) = X2 := superpose eq10 eq39
  have eq86 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq20 eq39
  have eq90 (X0 X1 X2 : G) : (((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq11 eq39
  have eq112 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) ◇ X0) ◇ ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq86 eq90
  have eq150 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ (X3 ◇ (X1 ◇ X1))) = X3 := superpose eq7 eq84
  have eq187 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq150 eq35
  have eq195 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq187 eq84
  have eq196 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := superpose eq187 eq86
  have eq220 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq187 eq112
  have eq241 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X0 := superpose eq195 eq7
  have eq250 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq220 eq196
  have eq252 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq220 eq241
  have eq256 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq220 eq250
  have eq263 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq256 eq252
  have eq264 (X0 X3 : G) : X0 = X3 := superpose eq263 eq263
  have eq266 (X0 : G) : sK0 ≠ X0 := superpose eq264 eq8
  subsumption eq266 eq264


@[equational_result]
theorem Equation18227_implies_Equation2 (G : Type*) [Magma G] (h : Equation18227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq7
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq10 eq20
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq30 eq26


@[equational_result]
theorem Equation18229_implies_Equation2 (G : Type*) [Magma G] (h : Equation18229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = ((((X0 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X3 ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) := superpose eq10 eq10
  have eq14 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = ((((X2 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq15 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = ((((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq10 eq7
  have eq17 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) ◇ (X3 ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))))) = X3 := superpose eq10 eq7
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) = ((X1 ◇ X1) ◇ (X3 ◇ X1)) := superpose eq7 eq12
  have eq19 (X0 X1 X2 X3 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) ◇ (X3 ◇ X1)) = X3 := superpose eq7 eq17
  have eq22 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X0) ◇ (X3 ◇ ((X2 ◇ X0) ◇ X0)))) ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X3 ◇ ((X2 ◇ X0) ◇ X0))))) ◇ (X4 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X3 ◇ ((X2 ◇ X0) ◇ X0))))))) = X4 := superpose eq10 eq9
  have eq36 (X1 X3 X4 : G) : (((X1 ◇ X3) ◇ (X1 ◇ X3)) ◇ (X4 ◇ (X1 ◇ (X1 ◇ X3)))) = X4 := superpose eq7 eq22
  have eq41 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ (X3 ◇ ((X1 ◇ X1) ◇ X0))) = X3 := superpose eq7 eq36
  have eq49 (X0 X1 : G) : (X1 ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq7 eq36
  have eq55 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq36 eq7
  have eq66 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X3 ◇ (X2 ◇ X2))) = X3 := superpose eq7 eq19
  have eq103 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X1 ◇ X2) ◇ X2) ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq7 eq41
  have eq123 (X0 X1 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq103 eq15
  have eq126 (X0 X1 X2 : G) : (X0 ◇ X0) = ((((X2 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X2 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq123 eq14
  have eq130 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq123 eq49
  have eq138 (X0 X1 : G) : (X0 ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq123 eq126
  have eq139 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq123 eq138
  have eq141 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ ((X2 ◇ X0) ◇ X0)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0))) := superpose eq130 eq18
  have eq146 (X1 X3 : G) : ((X1 ◇ X1) ◇ (X3 ◇ X1)) = X3 := superpose eq141 eq19
  have eq148 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X3 ◇ (X2 ◇ X2))) = X3 := superpose eq141 eq66
  have eq157 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq146 eq139
  have eq160 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq157 eq55
  have eq169 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq157 eq123
  have eq179 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := superpose eq157 eq160
  have eq186 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X3 ◇ X2)) = X3 := superpose eq157 eq148
  have eq187 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ X2)) = X3 := superpose eq157 eq186
  have eq189 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq187 eq179
  have eq199 (X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ X2) := superpose eq187 eq189
  have eq200 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq157 eq199
  have eq202 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq200 eq169
  have eq207 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq200 eq202
  have eq209 (X0 X2 : G) : X0 = X2 := superpose eq207 eq207
  have eq214 (X0 : G) : sK0 ≠ X0 := superpose eq209 eq8
  subsumption eq214 eq209


@[equational_result]
theorem Equation18231_implies_Equation2 (G : Type*) [Magma G] (h : Equation18231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq10 eq10
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X1)) = X0 := superpose eq12 eq7
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq10 eq20
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq38 eq27


@[equational_result]
theorem Equation18233_implies_Equation2 (G : Type*) [Magma G] (h : Equation18233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq7 eq10
  have eq23 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X4 ◇ X1)) = X4 := superpose eq7 eq9
  have eq43 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X3) = (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X4 ◇ X4) ◇ X3)) := superpose eq16 eq16
  have eq51 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) = ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2)))) := superpose eq16 eq16
  have eq54 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq9 eq16
  have eq67 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4)))) ◇ (X5 ◇ X2)) = X5 := superpose eq16 eq9
  have eq93 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ (X3 ◇ (X1 ◇ X1))) = X3 := superpose eq7 eq23
  have eq98 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2))) ◇ (X3 ◇ X2)) = X3 := superpose eq16 eq23
  have eq121 (X1 X3 : G) : (X1 ◇ X1) = ((X3 ◇ X3) ◇ (X1 ◇ X1)) := superpose eq93 eq51
  have eq133 (X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X3 ◇ X2)) = X3 := superpose eq43 eq98
  have eq144 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X1))) = X2 := superpose eq54 eq7
  have eq188 (X0 X2 X5 : G) : (((X0 ◇ X0) ◇ X2) ◇ (X5 ◇ X2)) = X5 := superpose eq144 eq67
  have eq195 (X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X3 ◇ X2)) = X3 := superpose eq188 eq133
  have eq196 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq195 eq121
  have eq205 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1))) = X0 := superpose eq196 eq7
  have eq208 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq196 eq16
  have eq229 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq196 eq205
  have eq233 (X0 X1 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := superpose eq196 eq208
  have eq234 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X2 := superpose eq196 eq233
  have eq237 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq234 eq229
  have eq242 (X0 X2 : G) : X0 = X2 := superpose eq237 eq237
  have eq250 (X0 : G) : sK0 ≠ X0 := superpose eq242 eq8
  subsumption eq250 eq242


@[equational_result]
theorem Equation18234_implies_Equation2 (G : Type*) [Magma G] (h : Equation18234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq11 eq11
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X2)) = X0 := superpose eq15 eq7
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq11 eq24
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq40 eq31


@[equational_result]
theorem Equation18235_implies_Equation2 (G : Type*) [Magma G] (h : Equation18235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq11 eq11
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X2)) = X0 := superpose eq14 eq7
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq11 eq22
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq39 eq30


@[equational_result]
theorem Equation18237_implies_Equation2 (G : Type*) [Magma G] (h : Equation18237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X4) = ((((X2 ◇ X3) ◇ X4) ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq29 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq41 (X0 X2 : G) : X0 = X2 := superpose eq29 eq29
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq107 eq41


@[equational_result]
theorem Equation18238_implies_Equation2 (G : Type*) [Magma G] (h : Equation18238 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq11 eq11
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X3)) = X0 := superpose eq14 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq22 eq22
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq39 eq30


@[equational_result]
theorem Equation18239_implies_Equation2 (G : Type*) [Magma G] (h : Equation18239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq11 eq11
  have eq24 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X3)) = X0 := superpose eq14 eq7
  have eq31 (X0 X4 : G) : X0 = X4 := superpose eq24 eq24
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq40 eq31


@[equational_result]
theorem Equation18240_implies_Equation2 (G : Type*) [Magma G] (h : Equation18240 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq11 eq11
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X3)) = X0 := superpose eq14 eq7
  have eq30 (X0 X4 : G) : X0 = X4 := superpose eq22 eq22
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq39 eq30


@[equational_result]
theorem Equation18243_implies_Equation2 (G : Type*) [Magma G] (h : Equation18243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation18246_implies_Equation2 (G : Type*) [Magma G] (h : Equation18246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq34 eq14


@[equational_result]
theorem Equation18248_implies_Equation2 (G : Type*) [Magma G] (h : Equation18248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq92 eq40


@[equational_result]
theorem Equation18250_implies_Equation2 (G : Type*) [Magma G] (h : Equation18250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq73 eq19


@[equational_result]
theorem Equation18253_implies_Equation2 (G : Type*) [Magma G] (h : Equation18253 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X2)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq10 eq9
  have eq12 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose eq11 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18255_implies_Equation2 (G : Type*) [Magma G] (h : Equation18255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation18256_implies_Equation2 (G : Type*) [Magma G] (h : Equation18256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation18258_implies_Equation2 (G : Type*) [Magma G] (h : Equation18258 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18259_implies_Equation2 (G : Type*) [Magma G] (h : Equation18259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18260_implies_Equation2 (G : Type*) [Magma G] (h : Equation18260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18262_implies_Equation2 (G : Type*) [Magma G] (h : Equation18262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X0) ◇ X2)) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ X1)) = ((X4 ◇ X4) ◇ (X4 ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X4))) := superpose eq7 eq9
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X4) ◇ (X4 ◇ (X3 ◇ X4))) = ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := superpose eq9 eq9
  have eq18 (X0 X2 : G) : ((X2 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq9
  have eq31 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ X3) = ((X2 ◇ X2) ◇ (X2 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2))) := superpose eq9 eq7
  have eq39 (X0 X1 X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq18 eq16
  have eq42 (X0 X2 X3 : G) : (X2 ◇ ((X3 ◇ X0) ◇ X2)) = X0 := superpose eq18 eq9
  have eq45 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq42 eq7
  have eq46 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X1)) = ((X4 ◇ X4) ◇ (X4 ◇ (X0 ◇ X4))) := superpose eq42 eq12
  have eq48 (X2 X3 : G) : ((X3 ◇ (X2 ◇ X3)) ◇ X2) = X3 := superpose eq42 eq39
  have eq53 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq46
  have eq57 (X2 X3 : G) : (X2 ◇ X2) = X3 := superpose eq53 eq48
  have eq64 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ X3) = ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq42 eq31
  have eq65 (X1 X2 X3 X4 : G) : ((X4 ◇ X1) ◇ X3) = ((X2 ◇ X2) ◇ X1) := superpose eq53 eq64
  have eq66 (X1 X3 X4 : G) : ((X4 ◇ X1) ◇ X3) = X1 := superpose eq45 eq65
  have eq67 (X0 X2 : G) : (X2 ◇ X0) = X0 := superpose eq66 eq42
  have eq77 (X0 X1 : G) : X0 = X1 := superpose eq67 eq57
  have eq91 (X0 : G) : sK0 ≠ X0 := superpose eq77 eq8
  subsumption eq91 eq77


@[equational_result]
theorem Equation18264_implies_Equation2 (G : Type*) [Magma G] (h : Equation18264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq83 eq19


@[equational_result]
theorem Equation18266_implies_Equation2 (G : Type*) [Magma G] (h : Equation18266 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18267_implies_Equation2 (G : Type*) [Magma G] (h : Equation18267 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18268_implies_Equation2 (G : Type*) [Magma G] (h : Equation18268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18270_implies_Equation2 (G : Type*) [Magma G] (h : Equation18270 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18271_implies_Equation2 (G : Type*) [Magma G] (h : Equation18271 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18272_implies_Equation2 (G : Type*) [Magma G] (h : Equation18272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18274_implies_Equation2 (G : Type*) [Magma G] (h : Equation18274 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18275_implies_Equation2 (G : Type*) [Magma G] (h : Equation18275 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18276_implies_Equation2 (G : Type*) [Magma G] (h : Equation18276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18277_implies_Equation2 (G : Type*) [Magma G] (h : Equation18277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18279_implies_Equation2 (G : Type*) [Magma G] (h : Equation18279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation18280_implies_Equation2 (G : Type*) [Magma G] (h : Equation18280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X0)) = X3 := superpose eq10 eq9
  have eq13 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = X3 := superpose eq10 eq11
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation18281_implies_Equation2 (G : Type*) [Magma G] (h : Equation18281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation18283_implies_Equation2 (G : Type*) [Magma G] (h : Equation18283 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq45 eq16


@[equational_result]
theorem Equation18285_implies_Equation2 (G : Type*) [Magma G] (h : Equation18285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation18289_implies_Equation2 (G : Type*) [Magma G] (h : Equation18289 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq44 eq14


@[equational_result]
theorem Equation18291_implies_Equation2 (G : Type*) [Magma G] (h : Equation18291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq42 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq59 eq42


@[equational_result]
theorem Equation18292_implies_Equation2 (G : Type*) [Magma G] (h : Equation18292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X2)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ ((X0 ◇ X3) ◇ X2)) = X0 := superpose eq7 eq11
  have eq19 (X0 X1 X4 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X4 := superpose eq13 eq10
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq35 eq28


@[equational_result]
theorem Equation18293_implies_Equation2 (G : Type*) [Magma G] (h : Equation18293 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq50 eq17


@[equational_result]
theorem Equation18294_implies_Equation2 (G : Type*) [Magma G] (h : Equation18294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation18296_implies_Equation2 (G : Type*) [Magma G] (h : Equation18296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq10 eq10
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq61 eq16


@[equational_result]
theorem Equation18298_implies_Equation2 (G : Type*) [Magma G] (h : Equation18298 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation18300_implies_Equation2 (G : Type*) [Magma G] (h : Equation18300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation18301_implies_Equation2 (G : Type*) [Magma G] (h : Equation18301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation18302_implies_Equation2 (G : Type*) [Magma G] (h : Equation18302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18304_implies_Equation2 (G : Type*) [Magma G] (h : Equation18304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18305_implies_Equation2 (G : Type*) [Magma G] (h : Equation18305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18306_implies_Equation2 (G : Type*) [Magma G] (h : Equation18306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18308_implies_Equation2 (G : Type*) [Magma G] (h : Equation18308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18309_implies_Equation2 (G : Type*) [Magma G] (h : Equation18309 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18310_implies_Equation2 (G : Type*) [Magma G] (h : Equation18310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18311_implies_Equation2 (G : Type*) [Magma G] (h : Equation18311 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X1 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18315_implies_Equation2 (G : Type*) [Magma G] (h : Equation18315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq45 eq15


@[equational_result]
theorem Equation18317_implies_Equation2 (G : Type*) [Magma G] (h : Equation18317 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18318_implies_Equation2 (G : Type*) [Magma G] (h : Equation18318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18319_implies_Equation2 (G : Type*) [Magma G] (h : Equation18319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18321_implies_Equation2 (G : Type*) [Magma G] (h : Equation18321 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18322_implies_Equation2 (G : Type*) [Magma G] (h : Equation18322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18323_implies_Equation2 (G : Type*) [Magma G] (h : Equation18323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18325_implies_Equation2 (G : Type*) [Magma G] (h : Equation18325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18326_implies_Equation2 (G : Type*) [Magma G] (h : Equation18326 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18327_implies_Equation2 (G : Type*) [Magma G] (h : Equation18327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18328_implies_Equation2 (G : Type*) [Magma G] (h : Equation18328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18330_implies_Equation2 (G : Type*) [Magma G] (h : Equation18330 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq75 eq19


@[equational_result]
theorem Equation18331_implies_Equation2 (G : Type*) [Magma G] (h : Equation18331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ ((X3 ◇ X0) ◇ X2)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X2 ◇ ((X3 ◇ X0) ◇ X2)) = X0 := superpose eq7 eq11
  have eq19 (X0 X1 X4 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X4 := superpose eq13 eq10
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq36 eq29


@[equational_result]
theorem Equation18332_implies_Equation2 (G : Type*) [Magma G] (h : Equation18332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : ((X1 ◇ X1) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation18333_implies_Equation2 (G : Type*) [Magma G] (h : Equation18333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X4 : G) : ((X1 ◇ X1) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation18335_implies_Equation2 (G : Type*) [Magma G] (h : Equation18335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18336_implies_Equation2 (G : Type*) [Magma G] (h : Equation18336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18337_implies_Equation2 (G : Type*) [Magma G] (h : Equation18337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18338_implies_Equation2 (G : Type*) [Magma G] (h : Equation18338 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18340_implies_Equation2 (G : Type*) [Magma G] (h : Equation18340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18341_implies_Equation2 (G : Type*) [Magma G] (h : Equation18341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18342_implies_Equation2 (G : Type*) [Magma G] (h : Equation18342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18343_implies_Equation2 (G : Type*) [Magma G] (h : Equation18343 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18345_implies_Equation2 (G : Type*) [Magma G] (h : Equation18345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18346_implies_Equation2 (G : Type*) [Magma G] (h : Equation18346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18347_implies_Equation2 (G : Type*) [Magma G] (h : Equation18347 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18348_implies_Equation2 (G : Type*) [Magma G] (h : Equation18348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18350_implies_Equation2 (G : Type*) [Magma G] (h : Equation18350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18351_implies_Equation2 (G : Type*) [Magma G] (h : Equation18351 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18352_implies_Equation2 (G : Type*) [Magma G] (h : Equation18352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18353_implies_Equation2 (G : Type*) [Magma G] (h : Equation18353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18354_implies_Equation2 (G : Type*) [Magma G] (h : Equation18354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18356_implies_Equation2 (G : Type*) [Magma G] (h : Equation18356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X3 ◇ X3) ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X1 ◇ X2) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ (X2 ◇ X3)))) := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq25 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((X1 ◇ X2) ◇ X0) := superpose eq17 eq10
  have eq27 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ X0) := superpose eq17 eq13
  have eq37 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq25 eq17
  have eq47 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq37 eq27
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq47 eq17
  have eq54 (X0 X3 : G) : X0 = X3 := superpose eq49 eq49
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq59 eq54


@[equational_result]
theorem Equation18357_implies_Equation2 (G : Type*) [Magma G] (h : Equation18357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X3 ◇ X3) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq10
  have eq20 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X3 ◇ X3) ◇ (X0 ◇ X2)))) = X3 := superpose eq10 eq7
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2)))) ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq7
  have eq32 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3)))) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3)))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3))))) ◇ X2))) ◇ X0) = X2 := superpose eq9 eq10
  have eq34 (X0 X1 X2 X3 : G) : (X0 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3)))) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3)))) ◇ X2)) := superpose eq9 eq10
  have eq37 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) = ((X0 ◇ X1) ◇ X0) := superpose eq10 eq15
  have eq39 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq15 eq15
  have eq52 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3)))) ◇ ((((X2 ◇ ((X2 ◇ X2) ◇ X3)) ◇ X0) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3))) ◇ X2))) ◇ X0) = X2 := superpose eq37 eq32
  have eq54 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3)))) ◇ (((X3 ◇ X2) ◇ X3) ◇ X2))) ◇ X0) = X2 := superpose eq37 eq52
  have eq56 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3)))) ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq39 eq54
  have eq58 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) = X1 := superpose eq39 eq37
  have eq59 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq58 eq56
  have eq63 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X2)) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2)) := superpose eq58 eq34
  have eq64 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq58 eq30
  have eq68 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq64 eq59
  have eq72 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ X2)) := superpose eq68 eq63
  have eq73 (X0 X3 : G) : (X0 ◇ (X3 ◇ X3)) = X3 := superpose eq68 eq20
  have eq81 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq73 eq72
  have eq87 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq81 eq68
  have eq90 (X0 X3 : G) : X0 = X3 := superpose eq87 eq87
  have eq100 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq100 eq90


@[equational_result]
theorem Equation18358_implies_Equation2 (G : Type*) [Magma G] (h : Equation18358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq11
  have eq46 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq14
  have eq95 (X0 X4 : G) : X0 = X4 := superpose eq11 eq46
  have eq185 (X0 : G) : sK0 ≠ X0 := superpose eq95 eq8
  subsumption eq185 eq95


@[equational_result]
theorem Equation18360_implies_Equation2 (G : Type*) [Magma G] (h : Equation18360 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)))))) = X2 := superpose eq9 eq9
  have eq21 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq13
  have eq27 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq21 eq21
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq21 eq27
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq51 eq28


@[equational_result]
theorem Equation18361_implies_Equation2 (G : Type*) [Magma G] (h : Equation18361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X1))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X2 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq7 eq7
  have eq43 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ X1) ◇ X2)))) ◇ (X3 ◇ X0)) ◇ (X4 ◇ X3)) = X4 := superpose eq9 eq11
  have eq99 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X0 ◇ X1) ◇ X2)) ◇ X0) := superpose eq7 eq10
  have eq100 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) = (((X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1)))) ◇ X2) ◇ X0) := superpose eq11 eq10
  have eq118 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) = (((X0 ◇ X2) ◇ X2) ◇ X0) := superpose eq7 eq100
  have eq132 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ ((X3 ◇ X4) ◇ (((X3 ◇ X4) ◇ X1) ◇ X2)))) ◇ (X3 ◇ X0)) = (((X4 ◇ X3) ◇ X3) ◇ X4) := superpose eq9 eq118
  have eq138 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X2 ◇ X3)) ◇ X1))) = ((X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) ◇ (X2 ◇ X3)) := superpose eq7 eq118
  have eq144 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X2 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3))) = (((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X2) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq118 eq118
  have eq146 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) = ((X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X1 ◇ X1)) := superpose eq118 eq118
  have eq196 (X3 X4 : G) : ((((X4 ◇ X3) ◇ X3) ◇ X4) ◇ (X4 ◇ X3)) = X4 := superpose eq132 eq43
  have eq206 (X1 X2 : G) : (X2 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) = X1 := superpose eq11 eq146
  have eq226 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq12 eq12
  have eq229 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = ((X2 ◇ (((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0))) ◇ (X2 ◇ X1)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq118 eq12
  have eq251 (X0 X1 X2 X3 : G) : (X2 ◇ (((X0 ◇ X1) ◇ X3) ◇ ((((X0 ◇ X1) ◇ X3) ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X3) ◇ X0) ◇ X1))) ◇ X2))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X3) ◇ X0) ◇ X1))) := superpose eq12 eq118
  have eq257 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = ((X2 ◇ (X2 ◇ X1)) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq11 eq229
  have eq266 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq118 eq196
  have eq286 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0)) ◇ X0) := superpose eq196 eq12
  have eq288 (X0 X1 : G) : ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := superpose eq196 eq118
  have eq299 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X2) ◇ (((X0 ◇ X2) ◇ X2) ◇ X0))) := superpose eq196 eq11
  have eq304 (X0 X1 X2 : G) : (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) = ((((X0 ◇ X2) ◇ (((X0 ◇ X2) ◇ X2) ◇ X0)) ◇ (((X0 ◇ X2) ◇ X2) ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq196 eq118
  have eq308 (X1 : G) : (X1 ◇ X1) = (X1 ◇ ((X1 ◇ X1) ◇ X1)) := superpose eq11 eq266
  have eq311 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := superpose eq99 eq288
  have eq316 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) ◇ (X2 ◇ X2)) := superpose eq311 eq299
  have eq319 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ ((((X0 ◇ X2) ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq99 eq304
  have eq320 (X0 X2 : G) : (X0 ◇ X2) = ((X2 ◇ X0) ◇ (X2 ◇ X2)) := superpose eq319 eq316
  have eq341 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq196 eq99
  have eq344 (X0 X1 X2 : G) : (X1 ◇ X2) = ((((X2 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X0)))) ◇ (X2 ◇ X1)) := superpose eq118 eq99
  have eq351 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ ((X3 ◇ (((X2 ◇ X0) ◇ X1) ◇ X2)) ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))))) = X3 := superpose eq99 eq9
  have eq353 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = ((X2 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) ◇ (((X2 ◇ X0) ◇ X1) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1)))) := superpose eq99 eq11
  have eq354 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X2 ◇ X0) ◇ X1)) = ((X2 ◇ (((X0 ◇ X1) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) ◇ ((X2 ◇ X0) ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq99 eq12
  have eq380 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ ((X2 ◇ X0) ◇ X1)) = ((X2 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq7 eq354
  have eq382 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X2 ◇ X3)) ◇ X1))) = ((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq380 eq138
  have eq391 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq308 eq118
  have eq406 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ X1) = (((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq308 eq99
  have eq407 (X0 X1 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq308 eq118
  have eq428 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ X1) := superpose eq99 eq406
  have eq429 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq428 eq391
  have eq435 (X1 X2 : G) : (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X1 := superpose eq429 eq206
  have eq452 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq341 eq407
  have eq453 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq435 eq452
  have eq454 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq453 eq429
  have eq456 (X0 X1 : G) : ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = X1 := superpose eq454 eq311
  have eq460 (X0 X2 : G) : (X0 ◇ X2) = ((X2 ◇ X0) ◇ X2) := superpose eq454 eq320
  have eq474 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ X0) := superpose eq460 eq286
  have eq476 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose eq456 eq474
  have eq477 (X0 X1 X2 : G) : (X2 ◇ X0) = (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) := superpose eq476 eq118
  have eq547 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X3) ◇ X0) ◇ X1))) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X3) ◇ X0) ◇ X1))) := superpose eq477 eq251
  have eq550 (X0 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ (X2 ◇ X3)) = ((X0 ◇ ((X0 ◇ X2) ◇ X3)) ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq477 eq382
  have eq552 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X0)) = X2 := superpose eq477 eq11
  have eq564 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X2 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X3))) = (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq477 eq144
  have eq585 (X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = ((X2 ◇ (X2 ◇ X1)) ◇ (X1 ◇ X2)) := superpose eq477 eq257
  have eq590 (X1 X2 : G) : (X1 ◇ X2) = ((((X2 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)) := superpose eq477 eq344
  have eq600 (X0 X1 X2 : G) : (X1 ◇ X2) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq550 eq99
  have eq615 (X0 X1 X2 : G) : ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) = ((X2 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq550 eq380
  have eq623 (X1 X2 : G) : (X2 ◇ ((X2 ◇ X1) ◇ X1)) = (((X1 ◇ X2) ◇ X2) ◇ ((X2 ◇ X1) ◇ X1)) := superpose eq477 eq564
  have eq637 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)) := superpose eq552 eq590
  have eq638 (X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ X1) ◇ X1) := superpose eq637 eq585
  have eq652 (X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ X1)) := superpose eq638 eq623
  have eq669 (X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = ((X1 ◇ X2) ◇ (X2 ◇ X1)) := superpose eq638 eq652
  have eq670 (X1 X2 : G) : (X2 ◇ (X2 ◇ X1)) = X2 := superpose eq552 eq669
  have eq672 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X3) ◇ X0) ◇ X1))) = ((X0 ◇ X1) ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X3) ◇ X0) ◇ X1))) := superpose eq670 eq547
  have eq675 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) = (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) := superpose eq670 eq226
  have eq676 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq670 eq615
  have eq694 (X0 X1 X2 : G) : (X2 ◇ ((((X0 ◇ X1) ◇ X2) ◇ X0) ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq460 eq675
  have eq707 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ X3) ◇ (X3 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq694 eq672
  have eq711 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq552 eq707
  have eq713 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = ((X2 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1))) ◇ X2) := superpose eq711 eq353
  have eq726 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ ((X3 ◇ (((X2 ◇ X0) ◇ X1) ◇ X2)) ◇ (X2 ◇ (X0 ◇ X1))))) = X3 := superpose eq676 eq351
  have eq728 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq676 eq600
  have eq741 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X2) := superpose eq676 eq713
  have eq747 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = (X2 ◇ (X0 ◇ X1)) := superpose eq728 eq741
  have eq755 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ ((X3 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X0 ◇ X1))))) = X3 := superpose eq747 eq726
  have eq902 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X3 ◇ (X3 ◇ (((X2 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X1)))))) = X3 := superpose eq747 eq755
  have eq903 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X2 ◇ X0) ◇ X1)) ◇ X3) = X3 := superpose eq670 eq902
  have eq904 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3) = X3 := superpose eq747 eq903
  have eq905 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq670 eq904
  have eq907 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq905 eq552
  have eq921 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq905 eq907
  have eq957 (X0 X1 : G) : X0 = X1 := superpose eq921 eq905
  have eq967 (X0 : G) : sK0 ≠ X0 := superpose eq957 eq8
  subsumption eq967 eq957


@[equational_result]
theorem Equation18362_implies_Equation2 (G : Type*) [Magma G] (h : Equation18362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ X4) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) ◇ ((X1 ◇ X4) ◇ (X0 ◇ X5))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X4) = (((X0 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) ◇ X0) := superpose eq11 eq10
  have eq14 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq11
  have eq22 (X0 X1 X3 X4 : G) : (X1 ◇ X4) = (((X0 ◇ X1) ◇ X3) ◇ X0) := superpose eq14 eq13
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq22
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq11 eq34
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq80 eq44


@[equational_result]
theorem Equation18365_implies_Equation2 (G : Type*) [Magma G] (h : Equation18365 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ ((X3 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))) ◇ ((X3 ◇ X2) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X2))))) := superpose eq7 eq9
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))))))) = X1 := superpose eq9 eq9
  have eq104 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq9 eq12
  have eq117 (X0 X1 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X1 := superpose eq104 eq7
  have eq118 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq104 eq7
  have eq129 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq104 eq118
  have eq130 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq129 eq117
  have eq187 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2)))) ◇ X0) = X1 := superpose eq9 eq130
  have eq188 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X1))) = (((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X1)))) ◇ (X0 ◇ X1)) := superpose eq10 eq130
  have eq190 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X1)))) ◇ (X0 ◇ X1)) = X2 := superpose eq11 eq130
  have eq202 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq130 eq9
  have eq223 (X1 X2 X3 : G) : (X3 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X1))) = X2 := superpose eq190 eq188
  have eq247 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq223 eq187
  have eq328 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ X0) := superpose eq223 eq202
  have eq329 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X0 := superpose eq328 eq7
  have eq382 (X0 X1 : G) : X0 = X1 := superpose eq329 eq247
  have eq430 (X0 : G) : sK0 ≠ X0 := superpose eq382 eq8
  subsumption eq430 eq382


@[equational_result]
theorem Equation18366_implies_Equation2 (G : Type*) [Magma G] (h : Equation18366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X2) = ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) ◇ ((X4 ◇ X2) ◇ (X0 ◇ X5))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) ◇ X0) := superpose eq11 eq10
  have eq14 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq11
  have eq22 (X0 X1 X2 X4 : G) : (X4 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq14 eq13
  have eq25 (X0 X2 X4 : G) : (X4 ◇ X2) = (X0 ◇ X0) := superpose eq14 eq22
  have eq26 (X0 X4 : G) : (X4 ◇ X4) = X0 := superpose eq11 eq25
  have eq38 (X0 X2 : G) : X0 = X2 := superpose eq11 eq26
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq72 eq38


@[equational_result]
theorem Equation18368_implies_Equation2 (G : Type*) [Magma G] (h : Equation18368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X4 ◇ X5) ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X6 X7 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X6 ◇ X7)))) = X2 := superpose eq9 eq9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq17 eq14
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq31 eq31
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq64 eq38


@[equational_result]
theorem Equation18369_implies_Equation2 (G : Type*) [Magma G] (h : Equation18369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X0 ◇ X2))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq34 (X0 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq11
  have eq39 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ (X2 ◇ ((X2 ◇ X6) ◇ X7))) = ((X1 ◇ ((X0 ◇ X2) ◇ (((X0 ◇ X2) ◇ X3) ◇ X4))) ◇ X0) := superpose eq11 eq11
  have eq40 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) = ((X5 ◇ X2) ◇ X0) := superpose eq11 eq10
  have eq61 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (((X0 ◇ X2) ◇ X3) ◇ X4))) ◇ X0) = X2 := superpose eq34 eq11
  have eq65 (X2 X5 X6 X7 : G) : (X5 ◇ (X2 ◇ ((X2 ◇ X6) ◇ X7))) = X2 := superpose eq61 eq39
  have eq70 (X0 X2 X5 : G) : ((X5 ◇ X2) ◇ X0) = X2 := superpose eq65 eq40
  have eq96 (X0 X2 : G) : X0 = X2 := superpose eq34 eq70
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq132 eq96


@[equational_result]
theorem Equation18370_implies_Equation2 (G : Type*) [Magma G] (h : Equation18370 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq11
  have eq33 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq13 eq13
  have eq72 (X0 X4 : G) : X0 = X4 := superpose eq11 eq33
  have eq147 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq147 eq72


@[equational_result]
theorem Equation18371_implies_Equation2 (G : Type*) [Magma G] (h : Equation18371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X7 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X0 ◇ X7))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ X0) := superpose eq11 eq10
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq11 eq13
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq11 eq30
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq72 eq39


@[equational_result]
theorem Equation18373_implies_Equation2 (G : Type*) [Magma G] (h : Equation18373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq15
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq15 eq25
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq43 eq26


@[equational_result]
theorem Equation18374_implies_Equation2 (G : Type*) [Magma G] (h : Equation18374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((X1 ◇ X2) ◇ X3) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (((X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) ◇ X3) ◇ (X0 ◇ X2)))) = X3 := superpose eq11 eq7
  have eq47 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq7 eq12
  have eq53 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0) := superpose eq7 eq12
  have eq54 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X2 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X0))) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := superpose eq11 eq12
  have eq126 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1))) := superpose eq47 eq11
  have eq128 (X0 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq47 eq11
  have eq129 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (((X1 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq47 eq12
  have eq159 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2)) ◇ (X3 ◇ ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2)) ◇ X0)))) = X3 := superpose eq9 eq22
  have eq160 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq11 eq22
  have eq197 (X0 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq128 eq7
  have eq230 (X0 X1 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1)) = (((X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ X1))) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq47 eq54
  have eq237 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq10 eq54
  have eq273 (X0 X1 : G) : (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq9 eq160
  have eq286 (X0 : G) : ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X0 := superpose eq160 eq7
  have eq300 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (((X3 ◇ (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X0))) ◇ X2) ◇ (X0 ◇ X1)))) = X2 := superpose eq160 eq22
  have eq315 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq273 eq286
  have eq319 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq315 eq47
  have eq323 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq315 eq129
  have eq335 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := superpose eq315 eq197
  have eq361 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = ((((X1 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq319 eq237
  have eq381 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X1 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq319 eq160
  have eq406 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq381 eq323
  have eq407 (X0 X1 : G) : (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := superpose eq406 eq381
  have eq408 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq319 eq407
  have eq412 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) := superpose eq408 eq126
  have eq414 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) = (((X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq408 eq230
  have eq429 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq408 eq406
  have eq432 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) = (((X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq429 eq414
  have eq433 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq412 eq432
  have eq434 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X1)) := superpose eq429 eq433
  have eq436 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq434 eq412
  have eq483 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))))) := superpose eq315 eq9
  have eq492 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq7 eq483
  have eq493 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq492 eq361
  have eq495 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq335 eq493
  have eq500 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq495 eq436
  have eq501 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq495 eq500
  have eq519 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq501 eq408
  have eq561 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ X0) := superpose eq519 eq53
  have eq629 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ X0) := superpose eq7 eq561
  have eq630 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq519 eq629
  have eq631 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ (((X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X2) ◇ (X0 ◇ X1)))) = X2 := superpose eq630 eq300
  have eq635 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ X0)))) = X3 := superpose eq630 eq159
  have eq767 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq630 eq631
  have eq833 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ ((X1 ◇ X2) ◇ X0))) = X3 := superpose eq767 eq635
  have eq834 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) = X3 := superpose eq767 eq833
  have eq835 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq767 eq834
  have eq836 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq767 eq835
  have eq837 (X0 X3 : G) : X0 = X3 := superpose eq836 eq836
  have eq856 (X0 : G) : sK0 ≠ X0 := superpose eq837 eq8
  subsumption eq856 eq837


@[equational_result]
theorem Equation18375_implies_Equation2 (G : Type*) [Magma G] (h : Equation18375 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq11
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X0 := superpose eq14 eq7
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq11 eq23
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq34 eq30


@[equational_result]
theorem Equation18377_implies_Equation2 (G : Type*) [Magma G] (h : Equation18377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X2) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (((X3 ◇ X4) ◇ (X3 ◇ X4)) ◇ (X3 ◇ X4)))))) = X2 := superpose eq9 eq9
  have eq23 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq13
  have eq25 (X0 X1 X2 : G) : (X0 ◇ X2) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := superpose eq23 eq11
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X1)) = X0 := superpose eq23 eq7
  have eq29 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq23 eq25
  have eq31 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq29 eq26
  have eq32 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq29 eq31
  have eq46 (X0 X2 : G) : X0 = X2 := superpose eq32 eq32
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq48 eq46


@[equational_result]
theorem Equation18379_implies_Equation2 (G : Type*) [Magma G] (h : Equation18379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq11
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X1)) = X0 := superpose eq14 eq7
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq11 eq22
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq40 eq31


@[equational_result]
theorem Equation18381_implies_Equation2 (G : Type*) [Magma G] (h : Equation18381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = X0 := superpose eq14 eq7
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq26 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq26 eq24


@[equational_result]
theorem Equation18382_implies_Equation2 (G : Type*) [Magma G] (h : Equation18382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq9
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X4 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))))))) = X4 := superpose eq9 eq9
  have eq20 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq13
  have eq21 (X0 X1 X4 : G) : (X1 ◇ (X4 ◇ X0)) = X4 := superpose eq9 eq14
  have eq24 (X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ (X1 ◇ X2)) := superpose eq21 eq10
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = X0 := superpose eq21 eq7
  have eq27 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq20 eq24
  have eq32 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq27 eq26
  have eq35 (X0 X2 : G) : X0 = X2 := superpose eq32 eq32
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq37 eq35


@[equational_result]
theorem Equation18383_implies_Equation2 (G : Type*) [Magma G] (h : Equation18383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X0 ◇ X5))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = X0 := superpose eq13 eq7
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq25 eq23


@[equational_result]
theorem Equation18385_implies_Equation2 (G : Type*) [Magma G] (h : Equation18385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ (((X1 ◇ X2) ◇ X5) ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) = X2 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq9 eq9
  have eq26 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq16 eq12
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq70 eq38


@[equational_result]
theorem Equation18386_implies_Equation2 (G : Type*) [Magma G] (h : Equation18386 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (((X1 ◇ X2) ◇ X5) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X2))))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X4 ◇ (X0 ◇ X3))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq34 (X0 X5 : G) : (X0 ◇ (X5 ◇ X0)) = X5 := superpose eq10 eq11
  have eq41 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X6))) = (((X1 ◇ X2) ◇ X3) ◇ X0) := superpose eq11 eq10
  have eq48 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) = ((X0 ◇ X1) ◇ X0) := superpose eq11 eq34
  have eq49 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq34 eq34
  have eq62 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) = X1 := superpose eq49 eq48
  have eq66 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq62 eq41
  have eq70 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq66 eq9
  have eq75 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X3)) = X0 := superpose eq70 eq7
  have eq94 (X0 X2 : G) : X0 = X2 := superpose eq34 eq75
  have eq101 (X0 : G) : sK0 ≠ X0 := superpose eq94 eq8
  subsumption eq101 eq94


@[equational_result]
theorem Equation18387_implies_Equation2 (G : Type*) [Magma G] (h : Equation18387 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X4) = ((X0 ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq11
  have eq21 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X4) = ((X0 ◇ X3) ◇ (X1 ◇ X2)) := superpose eq13 eq12
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X3)) = X0 := superpose eq13 eq7
  have eq25 (X1 X4 : G) : (X1 ◇ X4) = X1 := superpose eq11 eq21
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq25 eq23
  have eq31 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq25 eq30
  have eq34 (X0 X2 : G) : X0 = X2 := superpose eq31 eq31
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq36 eq34


@[equational_result]
theorem Equation18388_implies_Equation2 (G : Type*) [Magma G] (h : Equation18388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X1 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq11
  have eq21 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X3)) = X0 := superpose eq13 eq7
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq11 eq21
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq39 eq30


@[equational_result]
theorem Equation18391_implies_Equation2 (G : Type*) [Magma G] (h : Equation18391 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq37 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq14 eq14
  have eq61 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X0 := superpose eq37 eq7
  have eq88 (X0 X1 : G) : X0 = X1 := superpose eq61 eq37
  have eq110 (X0 : G) : sK0 ≠ X0 := superpose eq88 eq8
  subsumption eq110 eq88


@[equational_result]
theorem Equation18392_implies_Equation2 (G : Type*) [Magma G] (h : Equation18392 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq11
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X0 := superpose eq14 eq7
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq11 eq24
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq35 eq31


@[equational_result]
theorem Equation18396_implies_Equation2 (G : Type*) [Magma G] (h : Equation18396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq11
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X1)) = X0 := superpose eq15 eq7
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq11 eq23
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq40 eq31


@[equational_result]
theorem Equation18399_implies_Equation2 (G : Type*) [Magma G] (h : Equation18399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (((X0 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq10 eq10
  have eq35 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ (((((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2)))) ◇ (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))))) ◇ ((((((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2)))) ◇ (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2)))) ◇ (((((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2)))) ◇ (((X1 ◇ ((X2 ◇ X2) ◇ X2)) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))))))) = X3 := superpose eq10 eq9
  have eq43 (X0 X2 X3 : G) : (X3 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X2))) = X0 := superpose eq7 eq17
  have eq91 (X0 X1 X3 : G) : (X1 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)))) = X3 := superpose eq43 eq35
  have eq93 (X0 X3 : G) : (X0 ◇ (X3 ◇ X0)) = X3 := superpose eq43 eq9
  have eq103 (X1 X3 : G) : (X1 ◇ ((X1 ◇ X1) ◇ X1)) = X3 := superpose eq43 eq91
  have eq152 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq93 eq93
  have eq157 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq152 eq103
  have eq179 (X0 X2 : G) : X0 = X2 := superpose eq157 eq157
  have eq184 (X0 : G) : sK0 ≠ X0 := superpose eq179 eq8
  subsumption eq184 eq179


@[equational_result]
theorem Equation18400_implies_Equation2 (G : Type*) [Magma G] (h : Equation18400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq10
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X2)) = X0 := superpose eq13 eq7
  have eq29 (X0 X2 : G) : X0 = X2 := superpose eq10 eq21
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq40 eq29


@[equational_result]
theorem Equation18402_implies_Equation2 (G : Type*) [Magma G] (h : Equation18402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X0 ◇ X1))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X3) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq10
  have eq34 (X0 X1 X5 : G) : (X0 ◇ (X5 ◇ X1)) = X5 := superpose eq10 eq11
  have eq59 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq34 eq15
  have eq63 (X0 X3 : G) : X0 = X3 := superpose eq59 eq59
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq79 eq63


@[equational_result]
theorem Equation18403_implies_Equation2 (G : Type*) [Magma G] (h : Equation18403 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X0 ◇ (X2 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X2))) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq34 (X0 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq11
  have eq50 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ X0) = (X2 ◇ (X1 ◇ ((X3 ◇ X4) ◇ X3))) := superpose eq11 eq34
  have eq51 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq34 eq34
  have eq76 (X1 X2 X3 X4 : G) : (X2 ◇ (X1 ◇ ((X3 ◇ X4) ◇ X3))) = X1 := superpose eq51 eq50
  have eq77 (X1 X2 X4 : G) : (X2 ◇ (X1 ◇ X4)) = X1 := superpose eq51 eq76
  have eq79 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X4 := superpose eq77 eq10
  have eq86 (X0 X2 X4 : G) : (X2 ◇ X0) = X4 := superpose eq77 eq79
  have eq92 (X0 X2 : G) : X0 = X2 := superpose eq34 eq86
  have eq142 (X0 : G) : sK0 ≠ X0 := superpose eq92 eq8
  subsumption eq142 eq92


@[equational_result]
theorem Equation18404_implies_Equation2 (G : Type*) [Magma G] (h : Equation18404 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X1) = ((X3 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq25 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq7 eq11
  have eq38 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = X0 := superpose eq25 eq7
  have eq55 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X0 := superpose eq25 eq38
  have eq56 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq25 eq55
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq56 eq56
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq59 eq57


@[equational_result]
theorem Equation18405_implies_Equation2 (G : Type*) [Magma G] (h : Equation18405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq11
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X3)) = X0 := superpose eq13 eq7
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq11 eq22
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq41 eq30


@[equational_result]
theorem Equation18407_implies_Equation2 (G : Type*) [Magma G] (h : Equation18407 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ X4) ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0))) = X2 := superpose eq7 eq9
  have eq17 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq28 (X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X2)) = X2 := superpose eq17 eq15
  have eq58 (X0 X2 : G) : X0 = X2 := superpose eq17 eq28
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq67 eq58


@[equational_result]
theorem Equation18408_implies_Equation2 (G : Type*) [Magma G] (h : Equation18408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ X4) ◇ (X0 ◇ ((X3 ◇ X0) ◇ X2))))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X0)))) := superpose eq11 eq11
  have eq18 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq11
  have eq40 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X4 ◇ X1) ◇ X5)))) ◇ (X0 ◇ X1)) = X1 := superpose eq9 eq7
  have eq42 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ ((X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ ((X4 ◇ X3) ◇ X5)))) ◇ ((X6 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ ((X4 ◇ X3) ◇ X5))))) ◇ X3))) ◇ X0) = X3 := superpose eq9 eq11
  have eq49 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ ((X3 ◇ X1) ◇ X0))) = ((X0 ◇ X1) ◇ X0) := superpose eq11 eq18
  have eq55 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X3)) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3)))) := superpose eq18 eq9
  have eq61 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2))) ◇ X0) = X2 := superpose eq18 eq11
  have eq67 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X0)) ◇ ((X0 ◇ X2) ◇ X0)) := superpose eq49 eq16
  have eq68 (X0 X2 X3 X4 X5 : G) : (((X3 ◇ (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ ((X4 ◇ X3) ◇ X5))))) ◇ X3) ◇ X0) = X3 := superpose eq49 eq42
  have eq69 (X0 X3 : G) : ((X0 ◇ X3) ◇ X0) = X3 := superpose eq9 eq68
  have eq70 (X0 X1 X2 X3 : G) : (X0 ◇ X2) = ((X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X0)) ◇ X0)) ◇ X2) := superpose eq69 eq67
  have eq71 (X0 X1 X2 X3 : G) : (X2 ◇ (X1 ◇ ((X3 ◇ X1) ◇ X0))) = X1 := superpose eq69 eq49
  have eq75 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq71 eq40
  have eq86 (X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X1) ◇ X3)) = (X1 ◇ X1) := superpose eq71 eq55
  have eq91 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ X2) := superpose eq86 eq70
  have eq101 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq75 eq61
  have eq102 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X2) ◇ X2) := superpose eq101 eq91
  have eq110 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq101 eq102
  have eq115 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq110 eq18
  have eq141 (X0 X1 : G) : X0 = X1 := superpose eq110 eq115
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq141 eq8
  subsumption eq151 eq141


@[equational_result]
theorem Equation18409_implies_Equation2 (G : Type*) [Magma G] (h : Equation18409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ X4) ◇ X5))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq11
  have eq21 (X0 X4 X5 : G) : (X0 ◇ (X5 ◇ X4)) = X4 := superpose eq13 eq9
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq11 eq21
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq29 eq25


@[equational_result]
theorem Equation18410_implies_Equation2 (G : Type*) [Magma G] (h : Equation18410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : (X0 ◇ (X5 ◇ ((X6 ◇ X5) ◇ X7))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq11
  have eq22 (X0 X5 X6 : G) : (X0 ◇ (X6 ◇ X5)) = X5 := superpose eq14 eq9
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq11 eq22
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq31 eq27


@[equational_result]
theorem Equation18412_implies_Equation2 (G : Type*) [Magma G] (h : Equation18412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X5 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X5 ◇ X3) ◇ X3))))) = X2 := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X0))) = X2 := superpose eq7 eq9
  have eq25 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq15 eq13
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq25 eq25
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq25 eq32
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq56 eq33


@[equational_result]
theorem Equation18413_implies_Equation2 (G : Type*) [Magma G] (h : Equation18413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X3 ◇ X1) ◇ X2))))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1))) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X4 ◇ X0)) ◇ (X5 ◇ X4)) = X5 := superpose eq7 eq11
  have eq25 (X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ (X5 ◇ X4)) = X5 := superpose eq12 eq15
  have eq26 (X0 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X4 := superpose eq25 eq9
  have eq31 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq26 eq26
  have eq64 (X0 X1 : G) : X0 = X1 := superpose eq31 eq25
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq64 eq8
  subsumption eq72 eq64


@[equational_result]
theorem Equation18414_implies_Equation2 (G : Type*) [Magma G] (h : Equation18414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ (X1 ◇ X2)) ◇ X5))) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) = X2 := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X3))) = X2 := superpose eq9 eq9
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq15 eq14
  have eq63 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq134 eq63


@[equational_result]
theorem Equation18415_implies_Equation2 (G : Type*) [Magma G] (h : Equation18415 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq11
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X1)) = X0 := superpose eq13 eq7
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq11 eq22
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq40 eq31


@[equational_result]
theorem Equation18417_implies_Equation2 (G : Type*) [Magma G] (h : Equation18417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ X2) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X3) = ((((X2 ◇ X3) ◇ X4) ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ (X0 ◇ X5)) ◇ (X0 ◇ ((X4 ◇ X3) ◇ X2))) ◇ (X6 ◇ X1)) = X6 := superpose eq7 eq11
  have eq33 (X0 X1 X2 X4 X5 : G) : (X2 ◇ X0) = ((X0 ◇ X1) ◇ (X5 ◇ (X4 ◇ X2))) := superpose eq12 eq12
  have eq48 (X1 X2 X6 : G) : ((X2 ◇ X1) ◇ (X6 ◇ X1)) = X6 := superpose eq33 eq13
  have eq58 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq12 eq48
  have eq118 (X0 X4 : G) : X0 = X4 := superpose eq7 eq58
  have eq252 (X0 : G) : sK0 ≠ X0 := superpose eq118 eq8
  subsumption eq252 eq118


@[equational_result]
theorem Equation18418_implies_Equation2 (G : Type*) [Magma G] (h : Equation18418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ (X0 ◇ ((X3 ◇ X2) ◇ X2))) ◇ (X0 ◇ ((X3 ◇ X2) ◇ X2))))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X3 ◇ ((X1 ◇ X2) ◇ X2)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X2))) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11
  have eq54 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X5))) ◇ (X3 ◇ ((X4 ◇ X5) ◇ X5)))) ◇ ((X2 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X5))) ◇ (X3 ◇ ((X4 ◇ X5) ◇ X5))))) ◇ (X6 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X5))) ◇ (X3 ◇ ((X4 ◇ X5) ◇ X5)))) ◇ ((X2 ◇ (X3 ◇ ((X4 ◇ X5) ◇ X5))) ◇ (X3 ◇ ((X4 ◇ X5) ◇ X5))))))) = X7 := superpose eq11 eq9
  have eq65 (X0 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ ((X3 ◇ X2) ◇ X2))) = X0 := superpose eq7 eq25
  have eq113 (X0 X1 X3 X6 X7 : G) : (X3 ◇ ((X0 ◇ ((X1 ◇ X3) ◇ X3)) ◇ (X6 ◇ ((X1 ◇ X3) ◇ X3)))) = X7 := superpose eq65 eq54
  have eq140 (X3 X6 X7 : G) : (X3 ◇ X6) = X7 := superpose eq65 eq113
  have eq141 (X0 X4 : G) : X0 = X4 := superpose eq7 eq140
  have eq174 (X0 : G) : sK0 ≠ X0 := superpose eq141 eq8
  subsumption eq174 eq141


@[equational_result]
theorem Equation18419_implies_Equation2 (G : Type*) [Magma G] (h : Equation18419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq11
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X2)) = X0 := superpose eq13 eq7
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq11 eq23
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq41 eq30


@[equational_result]
theorem Equation18420_implies_Equation2 (G : Type*) [Magma G] (h : Equation18420 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq11
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X2)) = X0 := superpose eq13 eq7
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq11 eq23
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq41 eq30


@[equational_result]
theorem Equation18422_implies_Equation2 (G : Type*) [Magma G] (h : Equation18422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ X5) ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq10
  have eq29 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq46 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq29 eq13
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq46 eq46
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq77 eq49


@[equational_result]
theorem Equation18423_implies_Equation2 (G : Type*) [Magma G] (h : Equation18423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X3))) ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X3) = ((X1 ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq16 (X0 X4 : G) : (X0 ◇ (X4 ◇ X0)) = X4 := superpose eq7 eq10
  have eq40 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq11 eq11
  have eq73 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X3 ◇ X3))) = X4 := superpose eq11 eq16
  have eq102 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X0 := superpose eq16 eq40
  have eq141 (X2 X3 X4 : G) : (X2 ◇ X3) = X4 := superpose eq102 eq73
  have eq158 (X0 X3 : G) : X0 = X3 := superpose eq141 eq141
  have eq201 (X0 : G) : sK0 ≠ X0 := superpose eq158 eq8
  subsumption eq201 eq158


@[equational_result]
theorem Equation18424_implies_Equation2 (G : Type*) [Magma G] (h : Equation18424 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ X5) ◇ X5))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X0 ◇ ((X4 ◇ X4) ◇ X4))))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq10
  have eq15 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq7 eq13
  have eq23 (X0 X4 X5 : G) : (X0 ◇ (X5 ◇ X5)) = X4 := superpose eq15 eq9
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq13 eq23
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation18425_implies_Equation2 (G : Type*) [Magma G] (h : Equation18425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : (X0 ◇ (X5 ◇ ((X6 ◇ X6) ◇ X7))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq11
  have eq21 (X0 X5 X6 : G) : (X0 ◇ (X6 ◇ X6)) = X5 := superpose eq13 eq9
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq11 eq21
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq36 eq27


@[equational_result]
theorem Equation18427_implies_Equation2 (G : Type*) [Magma G] (h : Equation18427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X5 X6 X7 : G) : (X0 ◇ (X5 ◇ ((X6 ◇ X7) ◇ (X1 ◇ X2)))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X1))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X5 X6 : G) : (X0 ◇ (X5 ◇ (X6 ◇ (X1 ◇ X2)))) = X5 := superpose eq7 eq10
  have eq29 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq7 eq9
  have eq46 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq29 eq13
  have eq49 (X0 X3 : G) : X0 = X3 := superpose eq46 eq46
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq77 eq49


@[equational_result]
theorem Equation18428_implies_Equation2 (G : Type*) [Magma G] (h : Equation18428 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4))) ◇ (X5 ◇ X0)) = X5 := superpose eq7 eq7
  have eq14 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X3 ◇ X2))))) = X4 := superpose eq10 eq10
  have eq32 (X0 X5 : G) : (X0 ◇ (X5 ◇ X0)) = X5 := superpose eq7 eq11
  have eq39 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X4 ◇ (X3 ◇ ((X5 ◇ X6) ◇ X7))) = ((X2 ◇ X3) ◇ (X0 ◇ X1)) := superpose eq11 eq7
  have eq40 (X0 X1 X2 X3 X4 X5 X6 : G) : (X3 ◇ (X2 ◇ ((X4 ◇ X5) ◇ X6))) = ((X1 ◇ X2) ◇ X0) := superpose eq11 eq10
  have eq50 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq32 eq7
  have eq63 (X3 X4 X5 X6 X7 : G) : (X4 ◇ (X3 ◇ ((X5 ◇ X6) ◇ X7))) = X3 := superpose eq50 eq39
  have eq66 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq63 eq40
  have eq72 (X3 X4 X6 : G) : (X4 ◇ (X3 ◇ X6)) = X3 := superpose eq66 eq63
  have eq73 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq72 eq14
  have eq87 (X0 X2 : G) : X0 = X2 := superpose eq32 eq73
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq137 eq87


@[equational_result]
theorem Equation18429_implies_Equation2 (G : Type*) [Magma G] (h : Equation18429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : (X0 ◇ (X5 ◇ ((X6 ◇ X7) ◇ X6))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq11
  have eq21 (X0 X5 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X5 := superpose eq13 eq9
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq11 eq21
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq36 eq27


@[equational_result]
theorem Equation18430_implies_Equation2 (G : Type*) [Magma G] (h : Equation18430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : (X0 ◇ (X5 ◇ ((X6 ◇ X7) ◇ X7))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X6 X7 : G) : ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X0 ◇ ((X6 ◇ X7) ◇ X7))))) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq9 eq10
  have eq14 (X0 X5 X6 : G) : (X0 ◇ (X5 ◇ X6)) = X5 := superpose eq7 eq13
  have eq23 (X0 X5 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X5 := superpose eq14 eq9
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq13 eq23
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation18431_implies_Equation2 (G : Type*) [Magma G] (h : Equation18431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X0 ◇ ((X3 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X6 X7 X8 X9 : G) : (X0 ◇ (X6 ◇ ((X7 ◇ X8) ◇ X9))) = X6 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = X3 := superpose eq7 eq7
  have eq13 (X0 X6 X7 : G) : (X0 ◇ (X6 ◇ X7)) = X6 := superpose eq7 eq11
  have eq21 (X0 X6 X7 X8 : G) : (X0 ◇ (X7 ◇ X8)) = X6 := superpose eq13 eq9
  have eq27 (X0 X4 : G) : X0 = X4 := superpose eq11 eq21
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq36 eq27


@[equational_result]
theorem Equation18433_implies_Equation2 (G : Type*) [Magma G] (h : Equation18433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq12
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq15 eq7
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq15 eq18
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq15 eq25
  have eq27 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq15 eq26
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation18434_implies_Equation2 (G : Type*) [Magma G] (h : Equation18434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2))) ◇ (X1 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq7 eq10
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X0))) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X2)))) = X3 := superpose eq10 eq7
  have eq33 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X2)))) = X3 := superpose eq15 eq21
  have eq34 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq15 eq33
  have eq36 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X1 ◇ (X0 ◇ X2))))) = X3 := superpose eq34 eq9
  have eq49 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ (X1 ◇ (X0 ◇ X2)))) = X3 := superpose eq34 eq36
  have eq50 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X2))) = X3 := superpose eq34 eq49
  have eq51 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = X3 := superpose eq34 eq50
  have eq52 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq34 eq51
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq52 eq52
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq55 eq53


@[equational_result]
theorem Equation18435_implies_Equation2 (G : Type*) [Magma G] (h : Equation18435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation18437_implies_Equation2 (G : Type*) [Magma G] (h : Equation18437 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))))) := superpose eq7 eq9
  have eq13 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) ◇ (X0 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3)))))) = X4 := superpose eq9 eq9
  have eq14 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ ((X4 ◇ X0) ◇ X0))) = X4 := superpose eq7 eq9
  have eq16 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (((X2 ◇ X3) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) ◇ X0)) = X4 := superpose eq9 eq13
  have eq22 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X1 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0)) := superpose eq14 eq12
  have eq24 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq16 eq22
  have eq25 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X4 := superpose eq24 eq21
  have eq31 (X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X3)) = X4 := superpose eq24 eq25
  have eq32 (X1 X2 X4 : G) : (X1 ◇ X2) = X4 := superpose eq24 eq31
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq32 eq32
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq38 eq33


@[equational_result]
theorem Equation18439_implies_Equation2 (G : Type*) [Magma G] (h : Equation18439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation18443_implies_Equation2 (G : Type*) [Magma G] (h : Equation18443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation18445_implies_Equation2 (G : Type*) [Magma G] (h : Equation18445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq56 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq136 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq136 eq56


@[equational_result]
theorem Equation18446_implies_Equation2 (G : Type*) [Magma G] (h : Equation18446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ (X1 ◇ (X0 ◇ X2))) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq155 eq67


@[equational_result]
theorem Equation18447_implies_Equation2 (G : Type*) [Magma G] (h : Equation18447 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation18448_implies_Equation2 (G : Type*) [Magma G] (h : Equation18448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X0 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation18450_implies_Equation2 (G : Type*) [Magma G] (h : Equation18450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ X3) ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ ((X0 ◇ X4) ◇ X0))) = X4 := superpose eq7 eq9
  have eq29 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose eq10 eq10
  have eq30 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1)) = X0 := superpose eq7 eq10
  have eq39 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq13 eq29
  have eq58 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2))) = X3 := superpose eq7 eq30
  have eq84 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq58 eq39
  have eq86 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X1)) = X0 := superpose eq84 eq7
  have eq104 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq84 eq86
  have eq105 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq84 eq104
  have eq106 (X0 X3 : G) : X0 = X3 := superpose eq105 eq105
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq106 eq8
  subsumption eq108 eq106


@[equational_result]
theorem Equation18452_implies_Equation2 (G : Type*) [Magma G] (h : Equation18452 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation18454_implies_Equation2 (G : Type*) [Magma G] (h : Equation18454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18455_implies_Equation2 (G : Type*) [Magma G] (h : Equation18455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18456_implies_Equation2 (G : Type*) [Magma G] (h : Equation18456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18458_implies_Equation2 (G : Type*) [Magma G] (h : Equation18458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation18459_implies_Equation2 (G : Type*) [Magma G] (h : Equation18459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation18460_implies_Equation2 (G : Type*) [Magma G] (h : Equation18460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18462_implies_Equation2 (G : Type*) [Magma G] (h : Equation18462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18463_implies_Equation2 (G : Type*) [Magma G] (h : Equation18463 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18464_implies_Equation2 (G : Type*) [Magma G] (h : Equation18464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18465_implies_Equation2 (G : Type*) [Magma G] (h : Equation18465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18469_implies_Equation2 (G : Type*) [Magma G] (h : Equation18469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation18471_implies_Equation2 (G : Type*) [Magma G] (h : Equation18471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18472_implies_Equation2 (G : Type*) [Magma G] (h : Equation18472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18473_implies_Equation2 (G : Type*) [Magma G] (h : Equation18473 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18475_implies_Equation2 (G : Type*) [Magma G] (h : Equation18475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18476_implies_Equation2 (G : Type*) [Magma G] (h : Equation18476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18477_implies_Equation2 (G : Type*) [Magma G] (h : Equation18477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18479_implies_Equation2 (G : Type*) [Magma G] (h : Equation18479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18480_implies_Equation2 (G : Type*) [Magma G] (h : Equation18480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18481_implies_Equation2 (G : Type*) [Magma G] (h : Equation18481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18482_implies_Equation2 (G : Type*) [Magma G] (h : Equation18482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18484_implies_Equation2 (G : Type*) [Magma G] (h : Equation18484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X1 ◇ X2) ◇ ((X4 ◇ X5) ◇ (X1 ◇ X2)))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq12 eq12
  have eq17 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq7 eq12
  have eq21 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (X1 ◇ X2))) = X5 := superpose eq16 eq9
  have eq31 (X0 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ X2)) = X5 := superpose eq17 eq21
  have eq35 (X0 X2 X5 : G) : (X0 ◇ X2) = X5 := superpose eq17 eq31
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq35 eq35
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq38 eq36


@[equational_result]
theorem Equation18485_implies_Equation2 (G : Type*) [Magma G] (h : Equation18485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4))) ◇ (X1 ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ ((X4 ◇ X0) ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq11 eq12
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq50 eq39


@[equational_result]
theorem Equation18486_implies_Equation2 (G : Type*) [Magma G] (h : Equation18486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X1 ◇ X2) ◇ ((X4 ◇ X5) ◇ X4))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X2 := superpose eq7 eq7
  have eq36 (X0 X5 : G) : X0 = X5 := superpose eq9 eq11
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq44 eq36


@[equational_result]
theorem Equation18487_implies_Equation2 (G : Type*) [Magma G] (h : Equation18487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X0)) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation18489_implies_Equation2 (G : Type*) [Magma G] (h : Equation18489 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18490_implies_Equation2 (G : Type*) [Magma G] (h : Equation18490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18491_implies_Equation2 (G : Type*) [Magma G] (h : Equation18491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18492_implies_Equation2 (G : Type*) [Magma G] (h : Equation18492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18494_implies_Equation2 (G : Type*) [Magma G] (h : Equation18494 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18495_implies_Equation2 (G : Type*) [Magma G] (h : Equation18495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18496_implies_Equation2 (G : Type*) [Magma G] (h : Equation18496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18497_implies_Equation2 (G : Type*) [Magma G] (h : Equation18497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18499_implies_Equation2 (G : Type*) [Magma G] (h : Equation18499 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18500_implies_Equation2 (G : Type*) [Magma G] (h : Equation18500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18501_implies_Equation2 (G : Type*) [Magma G] (h : Equation18501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18502_implies_Equation2 (G : Type*) [Magma G] (h : Equation18502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18504_implies_Equation2 (G : Type*) [Magma G] (h : Equation18504 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18505_implies_Equation2 (G : Type*) [Magma G] (h : Equation18505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18506_implies_Equation2 (G : Type*) [Magma G] (h : Equation18506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18507_implies_Equation2 (G : Type*) [Magma G] (h : Equation18507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18508_implies_Equation2 (G : Type*) [Magma G] (h : Equation18508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X1 ◇ ((X3 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18511_implies_Equation2 (G : Type*) [Magma G] (h : Equation18511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq11 eq11
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq89 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq89 eq25


@[equational_result]
theorem Equation18512_implies_Equation2 (G : Type*) [Magma G] (h : Equation18512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation18516_implies_Equation2 (G : Type*) [Magma G] (h : Equation18516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation18519_implies_Equation2 (G : Type*) [Magma G] (h : Equation18519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ ((X3 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))) ◇ ((X2 ◇ ((X0 ◇ X2) ◇ X2)) ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X2))))) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X2)) ◇ ((X0 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))))) ◇ (((X2 ◇ ((X3 ◇ X2) ◇ X2)) ◇ ((X0 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2)))) ◇ (X0 ◇ ((X2 ◇ ((X3 ◇ X2) ◇ X2)) ◇ ((X0 ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))))))) = X3 := superpose eq9 eq7
  have eq39 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))) ◇ (((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1)))) ◇ (X3 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ ((X3 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))) ◇ (X1 ◇ ((X2 ◇ X1) ◇ X1))))))))) = X4 := superpose eq10 eq9
  have eq45 (X1 X2 X4 : G) : (X2 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X1)) ◇ X2)) = X4 := superpose eq15 eq39
  have eq164 (X0 X3 : G) : X0 = X3 := superpose eq45 eq45
  have eq179 (X0 : G) : sK0 ≠ X0 := superpose eq164 eq8
  subsumption eq179 eq164


@[equational_result]
theorem Equation18520_implies_Equation2 (G : Type*) [Magma G] (h : Equation18520 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq54 eq18


@[equational_result]
theorem Equation18522_implies_Equation2 (G : Type*) [Magma G] (h : Equation18522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq159 eq67


@[equational_result]
theorem Equation18523_implies_Equation2 (G : Type*) [Magma G] (h : Equation18523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq10
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq25
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq163 eq61


@[equational_result]
theorem Equation18524_implies_Equation2 (G : Type*) [Magma G] (h : Equation18524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X3)) ◇ ((X4 ◇ X5) ◇ X5))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X4) ◇ X4)))) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X3 X4 : G) : (X0 ◇ X3) = (X0 ◇ ((X3 ◇ X4) ◇ X4)) := superpose eq7 eq11
  have eq19 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq11 eq11
  have eq23 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X4)) = X4 := superpose eq18 eq9
  have eq31 (X0 X2 X4 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X4)) = X4 := superpose eq18 eq23
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq31 eq19
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq59 eq34


@[equational_result]
theorem Equation18525_implies_Equation2 (G : Type*) [Magma G] (h : Equation18525 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation18529_implies_Equation2 (G : Type*) [Magma G] (h : Equation18529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation18531_implies_Equation2 (G : Type*) [Magma G] (h : Equation18531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18532_implies_Equation2 (G : Type*) [Magma G] (h : Equation18532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18533_implies_Equation2 (G : Type*) [Magma G] (h : Equation18533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18535_implies_Equation2 (G : Type*) [Magma G] (h : Equation18535 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation18536_implies_Equation2 (G : Type*) [Magma G] (h : Equation18536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation18537_implies_Equation2 (G : Type*) [Magma G] (h : Equation18537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18539_implies_Equation2 (G : Type*) [Magma G] (h : Equation18539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X1 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18540_implies_Equation2 (G : Type*) [Magma G] (h : Equation18540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X1 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18541_implies_Equation2 (G : Type*) [Magma G] (h : Equation18541 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X1 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18542_implies_Equation2 (G : Type*) [Magma G] (h : Equation18542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X1 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18545_implies_Equation2 (G : Type*) [Magma G] (h : Equation18545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ ((X3 ◇ X0) ◇ X3)) = ((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X2 ◇ X3)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 : G) : (X0 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0)) = X2 := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X0) ◇ X2)) = ((X1 ◇ ((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0)) ◇ (((X2 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) ◇ X2)) := superpose eq7 eq11
  have eq18 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X3) ◇ X0)) ◇ X3) = ((X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X0)))) ◇ ((X2 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X0))) ◇ (X0 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X0)))))) := superpose eq11 eq7
  have eq28 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X1)) = ((X3 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) ◇ X0)) := superpose eq11 eq10
  have eq32 (X0 X1 X2 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ X1)) = X0 := superpose eq7 eq10
  have eq38 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X0) ◇ (X1 ◇ (X4 ◇ X0))) = ((X2 ◇ (X3 ◇ (X4 ◇ X0))) ◇ ((X3 ◇ (X4 ◇ X0)) ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X3 ◇ (X4 ◇ X0))))) := superpose eq10 eq7
  have eq43 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X1)) := superpose eq15 eq28
  have eq149 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ ((X3 ◇ X2) ◇ X0))) = X2 := superpose eq32 eq11
  have eq162 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X0) = ((X4 ◇ X0) ◇ (X1 ◇ (X4 ◇ X0))) := superpose eq149 eq38
  have eq164 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X3) ◇ X0)) ◇ X3) = ((X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X0)))) ◇ (((X0 ◇ ((X0 ◇ X3) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X3) ◇ X0)))) := superpose eq162 eq18
  have eq207 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X0 ◇ X3) ◇ X0)) ◇ X3) = ((X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X3) ◇ X0)))) ◇ X3) := superpose eq7 eq164
  have eq208 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) := superpose eq207 eq43
  have eq209 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq12 eq208
  have eq211 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq209 eq7
  have eq213 (X0 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X2 := superpose eq209 eq12
  have eq238 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq213 eq162
  have eq244 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq238 eq209
  have eq252 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq244 eq211
  have eq258 (X0 X3 : G) : X0 = X3 := superpose eq252 eq252
  have eq260 (X0 : G) : sK0 ≠ X0 := superpose eq258 eq8
  subsumption eq260 eq258


@[equational_result]
theorem Equation18546_implies_Equation2 (G : Type*) [Magma G] (h : Equation18546 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq79 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq79 eq18


@[equational_result]
theorem Equation18548_implies_Equation2 (G : Type*) [Magma G] (h : Equation18548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18549_implies_Equation2 (G : Type*) [Magma G] (h : Equation18549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18550_implies_Equation2 (G : Type*) [Magma G] (h : Equation18550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18552_implies_Equation2 (G : Type*) [Magma G] (h : Equation18552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18553_implies_Equation2 (G : Type*) [Magma G] (h : Equation18553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18554_implies_Equation2 (G : Type*) [Magma G] (h : Equation18554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18556_implies_Equation2 (G : Type*) [Magma G] (h : Equation18556 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18557_implies_Equation2 (G : Type*) [Magma G] (h : Equation18557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18558_implies_Equation2 (G : Type*) [Magma G] (h : Equation18558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18559_implies_Equation2 (G : Type*) [Magma G] (h : Equation18559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18561_implies_Equation2 (G : Type*) [Magma G] (h : Equation18561 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X4) ◇ (X4 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X3 X5 : G) : (((X1 ◇ X0) ◇ X5) ◇ (X5 ◇ X3)) = X1 := superpose eq7 eq11
  have eq27 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq15 eq12
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq7 eq27
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq54 eq28


@[equational_result]
theorem Equation18562_implies_Equation2 (G : Type*) [Magma G] (h : Equation18562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) ◇ X0) = X4 := superpose eq7 eq7
  have eq20 (X0 X4 X6 : G) : (X0 ◇ X4) = X6 := superpose eq12 eq12
  have eq67 (X0 X4 : G) : X0 = X4 := superpose eq7 eq20
  have eq149 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq149 eq67


@[equational_result]
theorem Equation18563_implies_Equation2 (G : Type*) [Magma G] (h : Equation18563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation18564_implies_Equation2 (G : Type*) [Magma G] (h : Equation18564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq7 eq11
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation18566_implies_Equation2 (G : Type*) [Magma G] (h : Equation18566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18567_implies_Equation2 (G : Type*) [Magma G] (h : Equation18567 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18568_implies_Equation2 (G : Type*) [Magma G] (h : Equation18568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18569_implies_Equation2 (G : Type*) [Magma G] (h : Equation18569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18571_implies_Equation2 (G : Type*) [Magma G] (h : Equation18571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18572_implies_Equation2 (G : Type*) [Magma G] (h : Equation18572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18573_implies_Equation2 (G : Type*) [Magma G] (h : Equation18573 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18574_implies_Equation2 (G : Type*) [Magma G] (h : Equation18574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18576_implies_Equation2 (G : Type*) [Magma G] (h : Equation18576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18577_implies_Equation2 (G : Type*) [Magma G] (h : Equation18577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18578_implies_Equation2 (G : Type*) [Magma G] (h : Equation18578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18579_implies_Equation2 (G : Type*) [Magma G] (h : Equation18579 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18581_implies_Equation2 (G : Type*) [Magma G] (h : Equation18581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18582_implies_Equation2 (G : Type*) [Magma G] (h : Equation18582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18583_implies_Equation2 (G : Type*) [Magma G] (h : Equation18583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18584_implies_Equation2 (G : Type*) [Magma G] (h : Equation18584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18585_implies_Equation2 (G : Type*) [Magma G] (h : Equation18585 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X2 ◇ ((X3 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18587_implies_Equation2 (G : Type*) [Magma G] (h : Equation18587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq56 eq21


@[equational_result]
theorem Equation18588_implies_Equation2 (G : Type*) [Magma G] (h : Equation18588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X0 ◇ X0) ◇ X2)) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq54 eq19


@[equational_result]
theorem Equation18589_implies_Equation2 (G : Type*) [Magma G] (h : Equation18589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation18590_implies_Equation2 (G : Type*) [Magma G] (h : Equation18590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation18592_implies_Equation2 (G : Type*) [Magma G] (h : Equation18592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq59 eq22


@[equational_result]
theorem Equation18593_implies_Equation2 (G : Type*) [Magma G] (h : Equation18593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) = X4 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq60 eq22


@[equational_result]
theorem Equation18594_implies_Equation2 (G : Type*) [Magma G] (h : Equation18594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ (X1 ◇ X2)) ◇ X4))) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq9 eq9
  have eq45 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq161 eq45


@[equational_result]
theorem Equation18595_implies_Equation2 (G : Type*) [Magma G] (h : Equation18595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation18597_implies_Equation2 (G : Type*) [Magma G] (h : Equation18597 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X4 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq62 eq22


@[equational_result]
theorem Equation18598_implies_Equation2 (G : Type*) [Magma G] (h : Equation18598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X2)) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation18599_implies_Equation2 (G : Type*) [Magma G] (h : Equation18599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq69 eq16


@[equational_result]
theorem Equation18600_implies_Equation2 (G : Type*) [Magma G] (h : Equation18600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation18602_implies_Equation2 (G : Type*) [Magma G] (h : Equation18602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X5 ◇ X4) ◇ (X1 ◇ X2)))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X3) ◇ (X4 ◇ X0)) = X2 := superpose eq7 eq7
  have eq40 (X0 X5 : G) : X0 = X5 := superpose eq9 eq11
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq50 eq40


@[equational_result]
theorem Equation18603_implies_Equation2 (G : Type*) [Magma G] (h : Equation18603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))) ◇ (X3 ◇ X0)) = X4 := superpose eq7 eq7
  have eq27 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq62 eq27


@[equational_result]
theorem Equation18604_implies_Equation2 (G : Type*) [Magma G] (h : Equation18604 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ ((X0 ◇ X3) ◇ X3)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq40 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq58 eq40


@[equational_result]
theorem Equation18605_implies_Equation2 (G : Type*) [Magma G] (h : Equation18605 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation18607_implies_Equation2 (G : Type*) [Magma G] (h : Equation18607 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ X0) = X5 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq59 eq22


@[equational_result]
theorem Equation18608_implies_Equation2 (G : Type*) [Magma G] (h : Equation18608 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X3)) ◇ X0) = X5 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq74 eq22


@[equational_result]
theorem Equation18609_implies_Equation2 (G : Type*) [Magma G] (h : Equation18609 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation18610_implies_Equation2 (G : Type*) [Magma G] (h : Equation18610 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq59 eq17


@[equational_result]
theorem Equation18611_implies_Equation2 (G : Type*) [Magma G] (h : Equation18611 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X0 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation18613_implies_Equation2 (G : Type*) [Magma G] (h : Equation18613 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((((X1 ◇ X0) ◇ X1) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq11 eq11
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq53 eq19


@[equational_result]
theorem Equation18614_implies_Equation2 (G : Type*) [Magma G] (h : Equation18614 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) = X4 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq60 eq22


@[equational_result]
theorem Equation18615_implies_Equation2 (G : Type*) [Magma G] (h : Equation18615 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ ((X1 ◇ X0) ◇ X3)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq42 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq42 eq8
  subsumption eq62 eq42


@[equational_result]
theorem Equation18616_implies_Equation2 (G : Type*) [Magma G] (h : Equation18616 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation18618_implies_Equation2 (G : Type*) [Magma G] (h : Equation18618 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18619_implies_Equation2 (G : Type*) [Magma G] (h : Equation18619 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18620_implies_Equation2 (G : Type*) [Magma G] (h : Equation18620 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18621_implies_Equation2 (G : Type*) [Magma G] (h : Equation18621 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18623_implies_Equation2 (G : Type*) [Magma G] (h : Equation18623 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18624_implies_Equation2 (G : Type*) [Magma G] (h : Equation18624 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18625_implies_Equation2 (G : Type*) [Magma G] (h : Equation18625 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation18626_implies_Equation2 (G : Type*) [Magma G] (h : Equation18626 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18628_implies_Equation2 (G : Type*) [Magma G] (h : Equation18628 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18629_implies_Equation2 (G : Type*) [Magma G] (h : Equation18629 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18630_implies_Equation2 (G : Type*) [Magma G] (h : Equation18630 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18631_implies_Equation2 (G : Type*) [Magma G] (h : Equation18631 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18633_implies_Equation2 (G : Type*) [Magma G] (h : Equation18633 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18634_implies_Equation2 (G : Type*) [Magma G] (h : Equation18634 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18635_implies_Equation2 (G : Type*) [Magma G] (h : Equation18635 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18636_implies_Equation2 (G : Type*) [Magma G] (h : Equation18636 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18637_implies_Equation2 (G : Type*) [Magma G] (h : Equation18637 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18639_implies_Equation2 (G : Type*) [Magma G] (h : Equation18639 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X0) = X4 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq62 eq22


@[equational_result]
theorem Equation18640_implies_Equation2 (G : Type*) [Magma G] (h : Equation18640 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X2)) ◇ X0) = X4 := superpose eq7 eq7
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq63 eq22


@[equational_result]
theorem Equation18641_implies_Equation2 (G : Type*) [Magma G] (h : Equation18641 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq56 eq16


@[equational_result]
theorem Equation18642_implies_Equation2 (G : Type*) [Magma G] (h : Equation18642 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation18644_implies_Equation2 (G : Type*) [Magma G] (h : Equation18644 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18645_implies_Equation2 (G : Type*) [Magma G] (h : Equation18645 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18646_implies_Equation2 (G : Type*) [Magma G] (h : Equation18646 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18647_implies_Equation2 (G : Type*) [Magma G] (h : Equation18647 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18649_implies_Equation2 (G : Type*) [Magma G] (h : Equation18649 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18650_implies_Equation2 (G : Type*) [Magma G] (h : Equation18650 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18651_implies_Equation2 (G : Type*) [Magma G] (h : Equation18651 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18652_implies_Equation2 (G : Type*) [Magma G] (h : Equation18652 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18654_implies_Equation2 (G : Type*) [Magma G] (h : Equation18654 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18655_implies_Equation2 (G : Type*) [Magma G] (h : Equation18655 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18656_implies_Equation2 (G : Type*) [Magma G] (h : Equation18656 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18657_implies_Equation2 (G : Type*) [Magma G] (h : Equation18657 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18659_implies_Equation2 (G : Type*) [Magma G] (h : Equation18659 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18660_implies_Equation2 (G : Type*) [Magma G] (h : Equation18660 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18661_implies_Equation2 (G : Type*) [Magma G] (h : Equation18661 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18662_implies_Equation2 (G : Type*) [Magma G] (h : Equation18662 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18663_implies_Equation2 (G : Type*) [Magma G] (h : Equation18663 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X2 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18665_implies_Equation2 (G : Type*) [Magma G] (h : Equation18665 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (X4 ◇ ((X4 ◇ X5) ◇ (X1 ◇ X2)))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X3) ◇ (X2 ◇ X0)) = X4 := superpose eq7 eq7
  have eq44 (X0 X6 : G) : X0 = X6 := superpose eq9 eq11
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq64 eq44


@[equational_result]
theorem Equation18666_implies_Equation2 (G : Type*) [Magma G] (h : Equation18666 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3))) ◇ (X4 ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((((X2 ◇ X3) ◇ X4) ◇ X0) ◇ X3)) ◇ X0) = X4 := superpose eq7 eq7
  have eq39 (X0 X5 X6 : G) : (X0 ◇ X6) = X5 := superpose eq11 eq12
  have eq48 (X0 X4 : G) : X0 = X4 := superpose eq7 eq39
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq48 eq8
  subsumption eq135 eq48


@[equational_result]
theorem Equation18667_implies_Equation2 (G : Type*) [Magma G] (h : Equation18667 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ ((X3 ◇ X0) ◇ X3)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq37 (X0 X5 : G) : X0 = X5 := superpose eq11 eq11
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq56 eq37


@[equational_result]
theorem Equation18668_implies_Equation2 (G : Type*) [Magma G] (h : Equation18668 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation18670_implies_Equation2 (G : Type*) [Magma G] (h : Equation18670 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18671_implies_Equation2 (G : Type*) [Magma G] (h : Equation18671 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18672_implies_Equation2 (G : Type*) [Magma G] (h : Equation18672 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18673_implies_Equation2 (G : Type*) [Magma G] (h : Equation18673 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18675_implies_Equation2 (G : Type*) [Magma G] (h : Equation18675 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18676_implies_Equation2 (G : Type*) [Magma G] (h : Equation18676 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation18677_implies_Equation2 (G : Type*) [Magma G] (h : Equation18677 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18678_implies_Equation2 (G : Type*) [Magma G] (h : Equation18678 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18680_implies_Equation2 (G : Type*) [Magma G] (h : Equation18680 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18681_implies_Equation2 (G : Type*) [Magma G] (h : Equation18681 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18682_implies_Equation2 (G : Type*) [Magma G] (h : Equation18682 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18683_implies_Equation2 (G : Type*) [Magma G] (h : Equation18683 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18685_implies_Equation2 (G : Type*) [Magma G] (h : Equation18685 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18686_implies_Equation2 (G : Type*) [Magma G] (h : Equation18686 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18687_implies_Equation2 (G : Type*) [Magma G] (h : Equation18687 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18688_implies_Equation2 (G : Type*) [Magma G] (h : Equation18688 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18689_implies_Equation2 (G : Type*) [Magma G] (h : Equation18689 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X3 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18691_implies_Equation2 (G : Type*) [Magma G] (h : Equation18691 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X0) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X6 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ X0) = X6 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq59 eq22


@[equational_result]
theorem Equation18692_implies_Equation2 (G : Type*) [Magma G] (h : Equation18692 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X0) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X6 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ X0) = X6 := superpose eq7 eq7
  have eq22 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq63 eq22


@[equational_result]
theorem Equation18693_implies_Equation2 (G : Type*) [Magma G] (h : Equation18693 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X0) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation18694_implies_Equation2 (G : Type*) [Magma G] (h : Equation18694 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X0) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X6 : G) : ((X1 ◇ X2) ◇ X0) = X6 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation18695_implies_Equation2 (G : Type*) [Magma G] (h : Equation18695 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X0) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X6 : G) : ((X1 ◇ X2) ◇ X0) = X6 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq58 eq16


@[equational_result]
theorem Equation18697_implies_Equation2 (G : Type*) [Magma G] (h : Equation18697 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X1) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18698_implies_Equation2 (G : Type*) [Magma G] (h : Equation18698 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X1) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18699_implies_Equation2 (G : Type*) [Magma G] (h : Equation18699 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X1) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18700_implies_Equation2 (G : Type*) [Magma G] (h : Equation18700 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X1) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18701_implies_Equation2 (G : Type*) [Magma G] (h : Equation18701 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X1) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18703_implies_Equation2 (G : Type*) [Magma G] (h : Equation18703 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X2) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18704_implies_Equation2 (G : Type*) [Magma G] (h : Equation18704 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X2) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18705_implies_Equation2 (G : Type*) [Magma G] (h : Equation18705 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X2) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18706_implies_Equation2 (G : Type*) [Magma G] (h : Equation18706 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X2) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18707_implies_Equation2 (G : Type*) [Magma G] (h : Equation18707 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X2) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18709_implies_Equation2 (G : Type*) [Magma G] (h : Equation18709 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X3) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18710_implies_Equation2 (G : Type*) [Magma G] (h : Equation18710 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X3) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18711_implies_Equation2 (G : Type*) [Magma G] (h : Equation18711 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X3) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18712_implies_Equation2 (G : Type*) [Magma G] (h : Equation18712 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X3) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18713_implies_Equation2 (G : Type*) [Magma G] (h : Equation18713 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X3) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18715_implies_Equation2 (G : Type*) [Magma G] (h : Equation18715 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X4) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18716_implies_Equation2 (G : Type*) [Magma G] (h : Equation18716 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X4) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation18717_implies_Equation2 (G : Type*) [Magma G] (h : Equation18717 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X4) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18718_implies_Equation2 (G : Type*) [Magma G] (h : Equation18718 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X4) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18719_implies_Equation2 (G : Type*) [Magma G] (h : Equation18719 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X4) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18721_implies_Equation2 (G : Type*) [Magma G] (h : Equation18721 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X5) ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18722_implies_Equation2 (G : Type*) [Magma G] (h : Equation18722 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X5) ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18723_implies_Equation2 (G : Type*) [Magma G] (h : Equation18723 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X5) ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18724_implies_Equation2 (G : Type*) [Magma G] (h : Equation18724 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X5) ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18725_implies_Equation2 (G : Type*) [Magma G] (h : Equation18725 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X5) ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18726_implies_Equation2 (G : Type*) [Magma G] (h : Equation18726 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X3 ◇ ((X4 ◇ X5) ◇ X6))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation18932_implies_Equation2 (G : Type*) [Magma G] (h : Equation18932 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X2)) = (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2)))) = X0 := superpose eq7 eq10
  have eq17 (X0 X3 : G) : ((X3 ◇ X0) ◇ X0) = X0 := superpose eq7 eq13
  have eq21 (X0 X1 X3 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = (X0 ◇ ((((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1)))) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ X3))) := superpose eq9 eq9
  have eq24 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X2)))) := superpose eq9 eq9
  have eq29 (X0 X3 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X3))) = X0 := superpose eq7 eq21
  have eq30 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq7 eq24
  have eq31 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq29 eq30
  have eq32 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq31 eq29
  have eq38 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq32 eq10
  have eq39 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq32 eq31
  have eq41 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq17 eq38
  have eq61 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq32 eq41
  have eq63 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq17 eq61
  have eq66 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq63 eq39
  have eq68 (X0 X1 : G) : X0 = X1 := superpose eq66 eq63
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq70 eq68


@[equational_result]
theorem Equation18935_implies_Equation2 (G : Type*) [Magma G] (h : Equation18935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) = X0 := superpose eq11 eq7
  have eq15 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq11 eq10
  have eq18 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq11 eq10
  have eq26 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq10 eq11
  have eq28 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq18 eq26
  have eq29 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq18 eq28
  have eq31 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq29 eq18
  have eq32 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X0 := superpose eq29 eq13
  have eq39 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq31 eq7
  have eq42 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := superpose eq31 eq15
  have eq52 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq31 eq32
  have eq59 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq31 eq39
  have eq60 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq39 eq39
  have eq90 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X0 := superpose eq52 eq42
  have eq289 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) = ((X0 ◇ (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq90 eq39
  have eq454 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq52 eq59
  have eq497 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq52 eq454
  have eq500 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq497 eq289
  have eq523 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq31 eq500
  have eq524 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq497 eq523
  have eq525 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq497 eq524
  have eq579 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq525 eq60
  have eq606 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq525 eq579
  have eq610 (X0 X2 : G) : X0 = X2 := superpose eq606 eq606
  have eq615 (X0 : G) : sK0 ≠ X0 := superpose eq610 eq8
  subsumption eq615 eq610


@[equational_result]
theorem Equation18937_implies_Equation2 (G : Type*) [Magma G] (h : Equation18937 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X1)) = (X0 ◇ ((((X0 ◇ X0) ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X1))) ◇ (X3 ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ ((X3 ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq17 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X1)) = (X0 ◇ (((X0 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X0)))) := superpose eq14 eq9
  have eq20 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ ((X3 ◇ X3) ◇ X0)) = X3 := superpose eq14 eq10
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X1))) = X0 := superpose eq14 eq7
  have eq22 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ X1)) = (X0 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X0)))) := superpose eq14 eq17
  have eq23 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X3 ◇ X0)) = X3 := superpose eq14 eq20
  have eq34 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq14 eq21
  have eq36 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq14 eq21
  have eq57 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq23 eq11
  have eq170 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X5 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X5 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) ◇ X0)) := superpose eq22 eq23
  have eq304 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq34 eq57
  have eq343 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq34 eq304
  have eq350 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq343 eq36
  have eq384 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq343 eq350
  have eq407 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X5 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) = (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ X0) := superpose eq384 eq170
  have eq466 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X5 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) = X0 := superpose eq384 eq407
  have eq467 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := superpose eq384 eq466
  have eq468 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X4)) ◇ (X0 ◇ (X1 ◇ X2))) = X0 := superpose eq384 eq467
  have eq469 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X4)) ◇ (X1 ◇ X2)) = X0 := superpose eq384 eq468
  have eq470 (X0 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ X2) = X0 := superpose eq384 eq469
  have eq471 (X0 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ X2) = X0 := superpose eq384 eq470
  have eq472 (X0 X2 X4 : G) : (X4 ◇ X2) = X0 := superpose eq384 eq471
  have eq473 (X0 X1 : G) : X0 = X1 := superpose eq14 eq472
  have eq478 (X0 : G) : sK0 ≠ X0 := superpose eq473 eq8
  subsumption eq478 eq473


@[equational_result]
theorem Equation18938_implies_Equation2 (G : Type*) [Magma G] (h : Equation18938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq7 eq12
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq17 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) = X0 := superpose eq12 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq15 eq7
  have eq21 (X0 X2 : G) : (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq15 eq14
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq15 eq19
  have eq26 (X0 X2 : G) : (X0 ◇ X2) = (X0 ◇ (X0 ◇ X2)) := superpose eq15 eq21
  have eq27 (X0 X2 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X2)) = X0 := superpose eq15 eq17
  have eq28 (X0 X2 : G) : (X0 ◇ (X0 ◇ X2)) = X0 := superpose eq15 eq27
  have eq29 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq28 eq26
  have eq32 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq29 eq25
  have eq35 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq29 eq32
  have eq36 (X0 X1 : G) : X0 = X1 := superpose eq35 eq29
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq38 eq36


@[equational_result]
theorem Equation18939_implies_Equation2 (G : Type*) [Magma G] (h : Equation18939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X3)) = (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq7 eq12
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq18 (X0 X2 X3 : G) : (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) = X0 := superpose eq12 eq7
  have eq20 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ (X2 ◇ X3))) := superpose eq15 eq14
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X2 := superpose eq15 eq11
  have eq25 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X3))) = X0 := superpose eq15 eq18
  have eq26 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X0 := superpose eq25 eq20
  have eq32 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq21 eq21
  have eq36 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq26 eq32
  have eq37 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq36 eq12
  have eq43 (X0 X1 : G) : X0 = X1 := superpose eq37 eq36
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq45 eq43


@[equational_result]
theorem Equation18942_implies_Equation2 (G : Type*) [Magma G] (h : Equation18942 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = (X0 ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (((X2 ◇ X0) ◇ X1) ◇ X0)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2)))) = X0 := superpose eq7 eq11
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq11
  have eq27 (X0 X1 X2 X3 X4 : G) : ((((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X4))) = X0 := superpose eq7 eq10
  have eq33 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (X0 ◇ X1)) := superpose eq10 eq11
  have eq40 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X1 ◇ (X0 ◇ X1)) := superpose eq7 eq33
  have eq57 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq14
  have eq102 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq57 eq11
  have eq103 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq57 eq9
  have eq104 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq57 eq10
  have eq112 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq57 eq10
  have eq127 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq57 eq40
  have eq135 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq7 eq40
  have eq145 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq40 eq7
  have eq150 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq40 eq11
  have eq165 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := superpose eq135 eq103
  have eq166 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq165 eq127
  have eq167 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq145 eq166
  have eq169 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq167 eq102
  have eq174 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq167 eq112
  have eq180 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq167 eq169
  have eq181 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq180 eq16
  have eq184 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq180 eq104
  have eq185 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := superpose eq180 eq135
  have eq196 (X0 X1 X2 : G) : ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq185 eq174
  have eq197 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq185 eq196
  have eq226 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq180 eq40
  have eq230 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = (X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0))) := superpose eq180 eq9
  have eq254 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) = ((((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq40 eq181
  have eq283 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3)) = ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3)) ◇ (X1 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)))) ◇ (((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3)) ◇ X4))) := superpose eq181 eq9
  have eq309 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3)) = ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X3)) ◇ X4))) := superpose eq230 eq283
  have eq323 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq40 eq184
  have eq338 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq184 eq9
  have eq348 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2))) := superpose eq184 eq40
  have eq358 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq226 eq323
  have eq359 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq358 eq226
  have eq367 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq359 eq40
  have eq376 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ X1) ◇ (((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq359 eq150
  have eq391 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq359 eq185
  have eq393 (X0 X1 X2 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq359 eq197
  have eq395 (X0 X1 X2 X3 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq359 eq254
  have eq429 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (((X0 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq391 eq338
  have eq430 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq393 eq429
  have eq441 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := superpose eq391 eq348
  have eq442 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq430 eq441
  have eq443 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq184 eq442
  have eq444 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq443 eq395
  have eq458 (X0 X1 X2 : G) : ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) ◇ (X0 ◇ X1)) := superpose eq359 eq444
  have eq459 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq391 eq458
  have eq460 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq367 eq459
  have eq463 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X2))) := superpose eq460 eq376
  have eq471 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := superpose eq443 eq463
  have eq481 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ X4))) := superpose eq471 eq309
  have eq524 (X0 X1 X2 X4 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X4))) = X1 := superpose eq7 eq481
  have eq644 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := superpose eq9 eq443
  have eq680 (X0 X1 X2 X4 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X4))) = X1 := superpose eq644 eq524
  have eq683 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1)) ◇ X1) = X1 := superpose eq443 eq680
  have eq684 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq683 eq181
  have eq685 (X0 X1 X2 X4 : G) : (X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X4))) = X0 := superpose eq684 eq27
  have eq801 (X0 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X0 := superpose eq684 eq685
  have eq802 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq684 eq801
  have eq819 (X0 X1 : G) : X0 = X1 := superpose eq684 eq802
  have eq832 (X0 : G) : sK0 ≠ X0 := superpose eq819 eq8
  subsumption eq832 eq819


@[equational_result]
theorem Equation18945_implies_Equation2 (G : Type*) [Magma G] (h : Equation18945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = (X0 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = (X0 ◇ ((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq7 eq11
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X3 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq11
  have eq26 (X0 X1 X2 X3 X5 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = (X3 ◇ ((((X3 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X3) ◇ X5))) := superpose eq9 eq9
  have eq55 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq14
  have eq62 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X4)) = (((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ ((((((X0 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X4)) ◇ X0) ◇ (X0 ◇ X5))) := superpose eq14 eq9
  have eq101 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq11 eq55
  have eq104 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq55 eq55
  have eq145 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ X2) := superpose eq104 eq101
  have eq164 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X0)) := superpose eq145 eq12
  have eq179 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = X1 := superpose eq104 eq164
  have eq183 (X0 X1 X3 X5 : G) : ((X3 ◇ X0) ◇ X1) = (X3 ◇ ((((X3 ◇ X0) ◇ X1) ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X3) ◇ X5))) := superpose eq179 eq26
  have eq192 (X0 X1 X2 X4 X5 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X4)) = (((X0 ◇ X1) ◇ X2) ◇ ((((((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X4)) ◇ X0) ◇ (X0 ◇ X5))) := superpose eq179 eq62
  have eq216 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X1) = (X3 ◇ (X0 ◇ X3)) := superpose eq179 eq183
  have eq217 (X0 X1 X3 : G) : ((X3 ◇ X0) ◇ X1) = X0 := superpose eq104 eq216
  have eq222 (X0 X1 X2 X4 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X4)) = X2 := superpose eq217 eq192
  have eq223 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) ◇ X0) = X2 := superpose eq217 eq222
  have eq224 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq217 eq223
  have eq225 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq224 eq55
  have eq232 (X0 X1 : G) : X0 = X1 := superpose eq224 eq225
  have eq237 (X0 : G) : sK0 ≠ X0 := superpose eq232 eq8
  subsumption eq237 eq232


@[equational_result]
theorem Equation18947_implies_Equation2 (G : Type*) [Magma G] (h : Equation18947 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = (X0 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ X3) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq12 eq12
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)) = X2 := superpose eq12 eq7
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq11
  have eq41 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq14
  have eq69 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = (X0 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq12 eq9
  have eq83 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq41 eq41
  have eq86 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq41 eq7
  have eq90 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq41 eq7
  have eq100 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq86 eq83
  have eq150 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)) := superpose eq86 eq9
  have eq162 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq86 eq12
  have eq192 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) = (((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq14 eq16
  have eq231 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq100 eq16
  have eq253 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq231 eq162
  have eq254 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq14 eq253
  have eq257 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq254 eq41
  have eq259 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq254 eq86
  have eq260 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := superpose eq254 eq90
  have eq265 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (((((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq254 eq150
  have eq282 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq259 eq257
  have eq283 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq282 eq30
  have eq292 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq283 eq69
  have eq315 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq282 eq260
  have eq316 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) := superpose eq315 eq192
  have eq323 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) := superpose eq292 eq316
  have eq393 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq292 eq265
  have eq394 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq282 eq393
  have eq395 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq282 eq394
  have eq396 (X1 X2 : G) : (X1 ◇ X2) = (X1 ◇ (X2 ◇ X1)) := superpose eq395 eq323
  have eq447 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq395 eq396
  have eq459 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X0 := superpose eq447 eq7
  have eq462 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq447 eq12
  have eq530 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X0 := superpose eq447 eq459
  have eq531 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq447 eq530
  have eq537 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq447 eq462
  have eq596 (X0 X1 : G) : X0 = X1 := superpose eq531 eq537
  have eq601 (X0 : G) : sK0 ≠ X0 := superpose eq596 eq8
  subsumption eq601 eq596


@[equational_result]
theorem Equation18948_implies_Equation2 (G : Type*) [Magma G] (h : Equation18948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq11 eq10
  have eq24 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) := superpose eq10 eq10
  have eq29 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) = (((X0 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq10 eq7
  have eq33 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq24
  have eq34 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq33
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq34 eq7
  have eq37 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq34 eq10
  have eq42 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq34 eq16
  have eq49 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X3)) := superpose eq34 eq37
  have eq56 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq34 eq42
  have eq57 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq34 eq56
  have eq58 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq34 eq57
  have eq80 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) ◇ (X0 ◇ X1)) := superpose eq34 eq29
  have eq81 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ X1)) := superpose eq35 eq80
  have eq82 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = (X1 ◇ (X0 ◇ X1)) := superpose eq34 eq81
  have eq83 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) = X0 := superpose eq82 eq58
  have eq88 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X3)) := superpose eq82 eq49
  have eq95 (X0 X1 X3 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X3)) := superpose eq82 eq88
  have eq96 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq83 eq95
  have eq97 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq96 eq35
  have eq106 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq96 eq97
  have eq122 (X0 X1 : G) : X0 = X1 := superpose eq106 eq96
  have eq124 (X0 : G) : sK0 ≠ X0 := superpose eq122 eq8
  subsumption eq124 eq122


@[equational_result]
theorem Equation18949_implies_Equation2 (G : Type*) [Magma G] (h : Equation18949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = (X0 ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X0)) ◇ (X4 ◇ X5))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq12
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq12 eq12
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ X0) = (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq13 eq10
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = (X0 ◇ (((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) ◇ (X4 ◇ X5))) := superpose eq13 eq9
  have eq21 (X0 X1 X4 X5 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq13 eq19
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X4 ◇ X5))) := superpose eq13 eq20
  have eq23 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = (X0 ◇ (X1 ◇ (X4 ◇ X5))) := superpose eq14 eq22
  have eq24 (X0 X1 X4 X5 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq14 eq21
  have eq25 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = X1 := superpose eq14 eq13
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ X3)) := superpose eq24 eq23
  have eq28 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq25 eq26
  have eq29 (X0 X1 X2 : G) : (X2 ◇ ((X2 ◇ X1) ◇ X0)) = X2 := superpose eq28 eq11
  have eq35 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq28 eq29
  have eq38 (X0 X1 : G) : X0 = X1 := superpose eq28 eq35
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq48 eq38


@[equational_result]
theorem Equation18951_implies_Equation2 (G : Type*) [Magma G] (h : Equation18951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) ◇ (((X2 ◇ X0) ◇ X3) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq7 eq12
  have eq36 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq14
  have eq40 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X0 := superpose eq14 eq10
  have eq86 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)))) := superpose eq36 eq10
  have eq89 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ X0)) := superpose eq36 eq7
  have eq91 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = (((((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) ◇ ((((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) ◇ X3) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := superpose eq36 eq11
  have eq164 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq36 eq40
  have eq188 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq164 eq86
  have eq190 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = X0 := superpose eq164 eq89
  have eq191 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ X0)) := superpose eq164 eq91
  have eq198 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq164 eq14
  have eq224 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X3) ◇ X0)) := superpose eq190 eq191
  have eq236 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq198 eq224
  have eq240 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq236 eq188
  have eq247 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq198 eq240
  have eq263 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X1))) = X2 := superpose eq247 eq10
  have eq376 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq247 eq263
  have eq377 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq247 eq376
  have eq378 (X0 X3 : G) : X0 = X3 := superpose eq377 eq377
  have eq380 (X0 : G) : sK0 ≠ X0 := superpose eq378 eq8
  subsumption eq380 eq378


@[equational_result]
theorem Equation18952_implies_Equation2 (G : Type*) [Magma G] (h : Equation18952 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X2)) = (X0 ◇ ((((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq7 eq10
  have eq14 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq10 eq10
  have eq38 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq14 eq9
  have eq39 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq14 eq7
  have eq52 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq39 eq14
  have eq54 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq52 eq38
  have eq57 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq52 eq10
  have eq58 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq52 eq13
  have eq61 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq52 eq54
  have eq63 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq61 eq58
  have eq64 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq63 eq57
  have eq68 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq63 eq64
  have eq69 (X0 X3 : G) : X0 = X3 := superpose eq68 eq68
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq71 eq69


@[equational_result]
theorem Equation18953_implies_Equation2 (G : Type*) [Magma G] (h : Equation18953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X5))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : ((X4 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq7 eq12
  have eq15 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ X1)) := superpose eq7 eq12
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X2))) = X0 := superpose eq15 eq7
  have eq29 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq22 eq12
  have eq37 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq12 eq13
  have eq49 (X0 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X4))) = X0 := superpose eq13 eq10
  have eq58 (X0 X3 : G) : ((X3 ◇ X0) ◇ X0) = X0 := superpose eq37 eq49
  have eq93 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X0) := superpose eq29 eq12
  have eq100 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq58 eq93
  have eq108 (X0 X1 X4 : G) : ((X4 ◇ X0) ◇ X1) = X0 := superpose eq100 eq13
  have eq125 (X0 X1 X4 : G) : (X4 ◇ X1) = X0 := superpose eq100 eq108
  have eq126 (X0 X3 : G) : X0 = X3 := superpose eq125 eq125
  have eq128 (X0 : G) : sK0 ≠ X0 := superpose eq126 eq8
  subsumption eq128 eq126


@[equational_result]
theorem Equation18955_implies_Equation2 (G : Type*) [Magma G] (h : Equation18955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq11 eq10
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ ((X2 ◇ X2) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0)))) := superpose eq7 eq10
  have eq25 (X0 X1 : G) : (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq10 eq7
  have eq34 (X0 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) = X0 := superpose eq11 eq17
  have eq41 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq17 eq10
  have eq46 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X2 ◇ X2)) := superpose eq41 eq18
  have eq80 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq25 eq10
  have eq95 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq46 eq80
  have eq96 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X0 := superpose eq34 eq95
  have eq99 (X0 : G) : (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq96 eq34
  have eq105 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq96 eq17
  have eq119 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq105 eq99
  have eq122 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq119 eq96
  have eq123 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq122 eq105
  have eq138 (X0 X1 : G) : X0 = X1 := superpose eq123 eq122
  have eq151 (X0 : G) : sK0 ≠ X0 := superpose eq138 eq8
  subsumption eq151 eq138


@[equational_result]
theorem Equation18956_implies_Equation2 (G : Type*) [Magma G] (h : Equation18956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X3) ◇ (X2 ◇ X3))))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X3))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq7 eq7
  have eq13 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq12 eq12
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X0 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq7 eq12
  have eq35 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq11
  have eq43 (X0 X1 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq13 eq7
  have eq45 (X0 X1 : G) : ((X0 ◇ X1) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) = X1 := superpose eq13 eq7
  have eq226 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2))) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq14 eq11
  have eq256 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq13 eq45
  have eq292 (X0 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq35 eq256
  have eq483 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := superpose eq292 eq7
  have eq504 (X0 : G) : (X0 ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq292 eq12
  have eq525 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq35 eq504
  have eq526 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq483 eq525
  have eq528 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq526 eq35
  have eq529 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq526 eq43
  have eq706 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq526 eq528
  have eq731 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2))) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq706 eq226
  have eq800 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2))) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)))) ◇ (X0 ◇ X1)) := superpose eq526 eq731
  have eq801 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ X1)) := superpose eq526 eq800
  have eq809 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq526 eq529
  have eq810 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq526 eq809
  have eq812 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq810 eq801
  have eq823 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq706 eq812
  have eq824 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := superpose eq810 eq823
  have eq825 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq810 eq824
  have eq902 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X3) ◇ (X2 ◇ X3))))) = X2 := superpose eq825 eq10
  have eq1151 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq825 eq902
  have eq1152 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq825 eq1151
  have eq1153 (X0 X3 : G) : X0 = X3 := superpose eq1152 eq1152
  have eq1155 (X0 : G) : sK0 ≠ X0 := superpose eq1153 eq8
  subsumption eq1155 eq1153


@[equational_result]
theorem Equation18957_implies_Equation2 (G : Type*) [Magma G] (h : Equation18957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X1 ◇ X3)) = (X0 ◇ X1) := superpose eq7 eq12
  have eq16 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq12 eq12
  have eq24 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq16 eq15
  have eq26 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq24 eq11
  have eq30 (X0 X2 : G) : ((X0 ◇ X2) ◇ X0) = X2 := superpose eq24 eq26
  have eq31 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq24 eq30
  have eq34 (X0 X1 : G) : X0 = X1 := superpose eq31 eq24
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq44 eq34


@[equational_result]
theorem Equation18960_implies_Equation2 (G : Type*) [Magma G] (h : Equation18960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X2)) = (X0 ◇ ((((X0 ◇ X2) ◇ (X2 ◇ X2)) ◇ X3) ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq11
  have eq37 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq7 eq14
  have eq39 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq14 eq14
  have eq43 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X2 := superpose eq14 eq11
  have eq69 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (((X2 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X2 := superpose eq37 eq43
  have eq70 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X2 := superpose eq39 eq69
  have eq71 (X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq70 eq39
  have eq72 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq71 eq70
  have eq77 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq72 eq7
  have eq78 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X3))) = X2 := superpose eq72 eq9
  have eq87 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq72 eq78
  have eq89 (X0 X3 : G) : X0 = X3 := superpose eq77 eq87
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq8
  subsumption eq96 eq89


@[equational_result]
theorem Equation18961_implies_Equation2 (G : Type*) [Magma G] (h : Equation18961 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ ((X0 ◇ X4) ◇ (X4 ◇ X5)))) = X2 := superpose eq7 eq11
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq14
  have eq29 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq21 eq21
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq21 eq29
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq58 eq30


@[equational_result]
theorem Equation18963_implies_Equation2 (G : Type*) [Magma G] (h : Equation18963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X5 ◇ X1))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq12
  have eq20 (X0 X2 : G) : (X2 ◇ X0) = X2 := superpose eq14 eq12
  have eq25 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X5 ◇ X1))) = X2 := superpose eq20 eq10
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq20 eq25
  have eq28 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq20 eq27
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq28 eq28
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq34 eq29


@[equational_result]
theorem Equation18964_implies_Equation2 (G : Type*) [Magma G] (h : Equation18964 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X2)) = (X0 ◇ ((((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X4) ◇ (X5 ◇ X4))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X2 X4 X5 : G) : (X0 ◇ ((X2 ◇ X4) ◇ (X5 ◇ X4))) = X2 := superpose eq12 eq9
  have eq17 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq12 eq15
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq17 eq17
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq29 eq18


@[equational_result]
theorem Equation18965_implies_Equation2 (G : Type*) [Magma G] (h : Equation18965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq12 eq16
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq66 eq24


@[equational_result]
theorem Equation18966_implies_Equation2 (G : Type*) [Magma G] (h : Equation18966 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq67 eq25


@[equational_result]
theorem Equation18969_implies_Equation2 (G : Type*) [Magma G] (h : Equation18969 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X3 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2)))) = X0 := superpose eq7 eq10
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq7 eq10
  have eq16 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (((X2 ◇ (X0 ◇ X1)) ◇ X1) ◇ X3))) := superpose eq10 eq7
  have eq26 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3)) = (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3))) := superpose eq9 eq10
  have eq27 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = ((X4 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ ((X4 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3)))) := superpose eq9 eq10
  have eq33 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X3 ◇ X0) ◇ ((X3 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq13 eq13
  have eq37 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq10 eq13
  have eq38 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = ((X3 ◇ X1) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X4))) := superpose eq9 eq13
  have eq39 (X0 X1 X2 X3 : G) : (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = ((X3 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) := superpose eq13 eq13
  have eq46 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ (X3 ◇ X0)) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := superpose eq13 eq7
  have eq57 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := superpose eq7 eq33
  have eq58 (X0 X2 X3 : G) : (X3 ◇ X0) = ((X2 ◇ (X3 ◇ X0)) ◇ X0) := superpose eq57 eq46
  have eq59 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq58 eq37
  have eq61 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3))) := superpose eq58 eq16
  have eq65 (X0 X1 X3 : G) : (X3 ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq58 eq59
  have eq68 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X3)) := superpose eq61 eq26
  have eq70 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) := superpose eq68 eq38
  have eq71 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = ((X4 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ ((X4 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) := superpose eq68 eq27
  have eq74 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) := superpose eq68 eq9
  have eq77 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2)))) = X0 := superpose eq70 eq11
  have eq78 (X0 X1 X2 X4 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = ((X4 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ (X4 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) := superpose eq65 eq71
  have eq79 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X0 := superpose eq74 eq77
  have eq82 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = ((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) := superpose eq74 eq70
  have eq84 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X2)) = X1 := superpose eq79 eq82
  have eq89 (X1 X2 X3 : G) : ((X3 ◇ X1) ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ X1) := superpose eq84 eq39
  have eq93 (X1 X4 : G) : ((X4 ◇ X1) ◇ (X4 ◇ X1)) = X1 := superpose eq84 eq78
  have eq116 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq84 eq89
  have eq143 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq93 eq93
  have eq150 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq116 eq143
  have eq151 (X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X1 := superpose eq150 eq84
  have eq157 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq150 eq151
  have eq159 (X0 X1 : G) : X0 = X1 := superpose eq150 eq157
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq159 eq8
  subsumption eq161 eq159


@[equational_result]
theorem Equation18972_implies_Equation2 (G : Type*) [Magma G] (h : Equation18972 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq22 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X3)) = (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ (X0 ◇ X4))) := superpose eq7 eq9
  have eq31 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) = X0 := superpose eq9 eq7
  have eq41 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ ((((X1 ◇ X2) ◇ X0) ◇ X2) ◇ (((X1 ◇ X2) ◇ X0) ◇ X2))) := superpose eq10 eq13
  have eq44 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X4)) = ((X1 ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3)))) := superpose eq9 eq13
  have eq45 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3)) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq13 eq13
  have eq52 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) = (X0 ◇ (X0 ◇ X0)) := superpose eq9 eq13
  have eq53 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3)) = ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq13 eq13
  have eq66 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3))) := superpose eq13 eq7
  have eq74 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ X3)) = X2 := superpose eq7 eq41
  have eq82 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X3)) = X1 := superpose eq7 eq45
  have eq83 (X0 X1 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X3)) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3)))) = X1 := superpose eq82 eq44
  have eq85 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X3)) = (((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X0) := superpose eq82 eq22
  have eq89 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq52 eq31
  have eq96 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3)) = X0 := superpose eq89 eq53
  have eq99 (X0 X1 X3 : G) : ((X1 ◇ ((X0 ◇ X1) ◇ X3)) ◇ X3) = X1 := superpose eq96 eq83
  have eq105 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X1) := superpose eq82 eq66
  have eq106 (X0 X1 X3 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X3)) = (X0 ◇ X0) := superpose eq105 eq85
  have eq111 (X1 X3 : G) : ((X1 ◇ X1) ◇ X3) = X1 := superpose eq106 eq99
  have eq136 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := superpose eq13 eq111
  have eq137 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq111 eq111
  have eq166 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ X2) := superpose eq137 eq136
  have eq174 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq111 eq166
  have eq198 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X2 := superpose eq174 eq74
  have eq238 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq174 eq198
  have eq239 (X0 X3 : G) : X0 = X3 := superpose eq238 eq238
  have eq258 (X0 : G) : sK0 ≠ X0 := superpose eq239 eq8
  subsumption eq258 eq239


@[equational_result]
theorem Equation18974_implies_Equation2 (G : Type*) [Magma G] (h : Equation18974 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = (X0 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) ◇ ((((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 : G) : (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = (X0 ◇ (X0 ◇ (X4 ◇ (X2 ◇ X0)))) := superpose eq9 eq9
  have eq16 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X4 ◇ (X2 ◇ X0))) = ((X3 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X5 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))))) := superpose eq9 eq9
  have eq18 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X0))) = ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq7 eq9
  have eq20 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X4 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) := superpose eq9 eq9
  have eq21 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = ((X0 ◇ X1) ◇ (X3 ◇ X0)) := superpose eq9 eq9
  have eq22 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) = X0 := superpose eq9 eq7
  have eq98 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X0))) := superpose eq7 eq22
  have eq99 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))))) = X0 := superpose eq21 eq22
  have eq107 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X0)) := superpose eq22 eq9
  have eq187 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X1)))))) := superpose eq9 eq14
  have eq224 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = ((X0 ◇ (X3 ◇ (X2 ◇ X0))) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))))) := superpose eq14 eq22
  have eq225 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X3 ◇ (X2 ◇ X0))) ◇ (X4 ◇ X0)) = ((X3 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))) := superpose eq14 eq9
  have eq230 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X4 ◇ X0)) = ((X0 ◇ (X3 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X3 ◇ (X2 ◇ X0))) ◇ (X5 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))))) := superpose eq14 eq9
  have eq286 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X2) = ((X3 ◇ (X4 ◇ X2)) ◇ ((X4 ◇ X2) ◇ ((X4 ◇ X2) ◇ (((X4 ◇ X2) ◇ X5) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))))) := superpose eq9 eq99
  have eq290 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X2 ◇ X0))) = ((X3 ◇ (X0 ◇ (X4 ◇ (X2 ◇ X0)))) ◇ ((X0 ◇ (X4 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X4 ◇ (X2 ◇ X0))) ◇ (((X0 ◇ (X4 ◇ (X2 ◇ X0))) ◇ X5) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))))) := superpose eq14 eq99
  have eq309 (X0 X3 : G) : ((X0 ◇ X3) ◇ ((X0 ◇ X3) ◇ X0)) = X3 := superpose eq99 eq10
  have eq338 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) ◇ (X3 ◇ X0)) := superpose eq309 eq107
  have eq342 (X0 X1 X2 X3 X5 : G) : (X1 ◇ (X2 ◇ X0)) = ((X0 ◇ (X3 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X3 ◇ (X2 ◇ X0))) ◇ (X5 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))))) := superpose eq338 eq230
  have eq346 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (X4 ◇ (X2 ◇ X0))) = ((X3 ◇ (X0 ◇ (X4 ◇ (X2 ◇ X0)))) ◇ (X1 ◇ (X2 ◇ X0))) := superpose eq342 eq290
  have eq351 (X0 X1 X2 X3 X5 : G) : (X0 ◇ (X1 ◇ (X2 ◇ X0))) = ((X3 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X5 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))))) := superpose eq346 eq16
  have eq354 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X2) = ((X3 ◇ (X4 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := superpose eq351 eq286
  have eq355 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) := superpose eq354 eq187
  have eq358 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = ((X1 ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X4 ◇ X1)) := superpose eq355 eq20
  have eq359 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X3 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))) := superpose eq358 eq225
  have eq364 (X0 X2 X3 : G) : (X3 ◇ (X2 ◇ X0)) = ((X0 ◇ (X3 ◇ (X2 ◇ X0))) ◇ (X2 ◇ X0)) := superpose eq359 eq224
  have eq365 (X0 X2 X3 : G) : (X2 ◇ X0) = (X3 ◇ (X2 ◇ X0)) := superpose eq358 eq364
  have eq372 (X0 X1 X2 : G) : (X2 ◇ X1) = (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq365 eq98
  have eq373 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X0))) = ((X2 ◇ X1) ◇ X0) := superpose eq365 eq18
  have eq374 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = X0 := superpose eq365 eq7
  have eq375 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X3) ◇ (((X2 ◇ X1) ◇ X3) ◇ X0)) = X3 := superpose eq365 eq10
  have eq498 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X0)) := superpose eq365 eq372
  have eq499 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = (((X1 ◇ X0) ◇ (X2 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq365 eq373
  have eq500 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ X1) ◇ X0) := superpose eq365 eq499
  have eq503 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X2 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq500 eq498
  have eq506 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X3) ◇ (X3 ◇ X0)) = X3 := superpose eq500 eq375
  have eq507 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ (X3 ◇ X0)) = X3 := superpose eq500 eq506
  have eq508 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq507 eq503
  have eq510 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X0 := superpose eq508 eq374
  have eq516 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq508 eq510
  have eq836 (X0 X1 : G) : X0 = X1 := superpose eq516 eq508
  have eq850 (X0 : G) : sK0 ≠ X0 := superpose eq836 eq8
  subsumption eq850 eq836


@[equational_result]
theorem Equation18975_implies_Equation2 (G : Type*) [Magma G] (h : Equation18975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = (X0 ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq10 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = X0 := superpose eq12 eq9
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq13 eq7
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq14
  have eq17 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq15 eq13
  have eq21 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq14 eq17
  have eq28 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq21 eq17
  have eq30 (X0 X1 : G) : X0 = X1 := superpose eq15 eq28
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq38 eq30


@[equational_result]
theorem Equation18976_implies_Equation2 (G : Type*) [Magma G] (h : Equation18976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ (X4 ◇ X5))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq11
  have eq16 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X2 ◇ X3))) = X0 := superpose eq11 eq7
  have eq17 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X3)) = X0 := superpose eq16 eq9
  have eq27 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq17 eq13
  have eq33 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X0 := superpose eq27 eq17
  have eq37 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq27 eq33
  have eq39 (X0 X1 : G) : X0 = X1 := superpose eq37 eq27
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq57 eq39


@[equational_result]
theorem Equation18979_implies_Equation2 (G : Type*) [Magma G] (h : Equation18979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X2)) = (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq11
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq7
  have eq26 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq12
  have eq27 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq12 eq7
  have eq32 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq12 eq7
  have eq36 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1))) = X0 := superpose eq26 eq14
  have eq38 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq27 eq36
  have eq86 (X0 X2 : G) : (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) = X0 := superpose eq38 eq9
  have eq90 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq38 eq10
  have eq98 (X0 X2 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X2))) = X0 := superpose eq12 eq86
  have eq99 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq12 eq90
  have eq100 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq98 eq99
  have eq105 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq100 eq32
  have eq118 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq100 eq105
  have eq134 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X2))) = X0 := superpose eq118 eq7
  have eq215 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := superpose eq100 eq134
  have eq219 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq100 eq215
  have eq221 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ (X0 ◇ X2))) = X0 := superpose eq219 eq134
  have eq246 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq219 eq221
  have eq260 (X0 X2 : G) : X0 = X2 := superpose eq246 eq246
  have eq265 (X0 : G) : sK0 ≠ X0 := superpose eq260 eq8
  subsumption eq265 eq260


@[equational_result]
theorem Equation18982_implies_Equation2 (G : Type*) [Magma G] (h : Equation18982 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X2)) = (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq10
  have eq24 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X2)) = (((X1 ◇ X1) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X4))) := superpose eq7 eq9
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X3)) = ((((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X4)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X5))) := superpose eq9 eq9
  have eq33 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X2)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq9 eq9
  have eq35 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X3) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X2))) ◇ X1)) = X3 := superpose eq9 eq10
  have eq52 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X3)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq7 eq33
  have eq57 (X0 X1 X2 X4 : G) : ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = ((X2 ◇ X2) ◇ (X2 ◇ X4)) := superpose eq9 eq33
  have eq104 (X0 X1 X3 X4 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = (((X1 ◇ X1) ◇ (X1 ◇ X3)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X4))) := superpose eq52 eq24
  have eq106 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X3)) = ((((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X5))) := superpose eq52 eq27
  have eq108 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ X3) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0)) ◇ X1)) = X3 := superpose eq52 eq35
  have eq119 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X3)) = ((((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) := superpose eq52 eq106
  have eq120 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X3)) = ((((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1))) := superpose eq104 eq119
  have eq163 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq13
  have eq180 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq10 eq163
  have eq183 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq163 eq163
  have eq194 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ X3) ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1)) = X3 := superpose eq183 eq108
  have eq201 (X1 X2 : G) : (X1 ◇ X2) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X2) := superpose eq183 eq180
  have eq208 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X3)) = ((((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq201 eq120
  have eq230 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X3)) = ((X0 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := superpose eq201 eq208
  have eq231 (X2 X3 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X3)) = X2 := superpose eq7 eq230
  have eq236 (X0 X2 X4 : G) : ((X2 ◇ X2) ◇ (X2 ◇ X4)) = ((X2 ◇ X2) ◇ X0) := superpose eq231 eq57
  have eq246 (X0 X2 : G) : ((X2 ◇ X2) ◇ X0) = X2 := superpose eq231 eq236
  have eq247 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ X3) ◇ (X1 ◇ X0)) = X3 := superpose eq246 eq194
  have eq251 (X0 X1 X3 : G) : (X1 ◇ (X1 ◇ X0)) = X3 := superpose eq246 eq247
  have eq292 (X0 X3 : G) : X0 = X3 := superpose eq251 eq251
  have eq297 (X0 : G) : sK0 ≠ X0 := superpose eq292 eq8
  subsumption eq297 eq292


@[equational_result]
theorem Equation18984_implies_Equation2 (G : Type*) [Magma G] (h : Equation18984 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ X3) ◇ ((((X1 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0)) = X3 := superpose eq7 eq7
  have eq25 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X0))))) = X3 := superpose eq9 eq7
  have eq46 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ X2) ◇ (X3 ◇ X2)) ◇ X4) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X4 := superpose eq9 eq10
  have eq249 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X1) ◇ X3) ◇ ((X4 ◇ X1) ◇ (((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X0))))) ◇ (X5 ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X0)))))))) = X3 := superpose eq9 eq25
  have eq265 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq46 eq25
  have eq303 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X4 ◇ X1) ◇ (((X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X0))))) ◇ (X5 ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X1 ◇ X0)))))))) = X3 := superpose eq265 eq249
  have eq399 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq265 eq303
  have eq406 (X0 X2 : G) : X0 = X2 := superpose eq399 eq399
  have eq416 (X0 : G) : sK0 ≠ X0 := superpose eq406 eq8
  subsumption eq416 eq406


@[equational_result]
theorem Equation18985_implies_Equation2 (G : Type*) [Magma G] (h : Equation18985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq10
  have eq12 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq10 eq10
  have eq15 (X1 X2 : G) : ((X1 ◇ X1) ◇ (X2 ◇ X2)) = X1 := superpose eq12 eq11
  have eq22 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq15 eq15
  have eq23 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq15
  have eq27 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq23 eq22
  have eq31 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq27 eq10
  have eq32 (X0 X2 : G) : X0 = X2 := superpose eq31 eq31
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation18986_implies_Equation2 (G : Type*) [Magma G] (h : Equation18986 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq11
  have eq22 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X2)) = X1 := superpose eq11 eq10
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ X2) = (X0 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X3)) := superpose eq10 eq10
  have eq27 (X1 X2 : G) : ((X1 ◇ X1) ◇ X2) = X1 := superpose eq22 eq23
  have eq33 (X0 X1 : G) : X0 = X1 := superpose eq13 eq27
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq37 eq33


@[equational_result]
theorem Equation18988_implies_Equation2 (G : Type*) [Magma G] (h : Equation18988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ X3) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X3) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)))) := superpose eq7 eq10
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0))) = X3 := superpose eq7 eq10
  have eq15 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0))) = X3 := superpose eq10 eq10
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq7 eq10
  have eq46 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X2)) ◇ (X4 ◇ X3))) = X4 := superpose eq9 eq14
  have eq349 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2) = ((X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2)) ◇ (X0 ◇ X0)) := superpose eq11 eq46
  have eq350 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq16 eq46
  have eq453 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq7 eq350
  have eq454 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq350 eq7
  have eq455 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq350 eq9
  have eq467 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := superpose eq350 eq15
  have eq479 (X0 X1 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ X0)))) := superpose eq350 eq12
  have eq485 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq350 eq14
  have eq500 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq454 eq453
  have eq503 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = ((X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) ◇ X0) := superpose eq500 eq349
  have eq505 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) := superpose eq500 eq455
  have eq506 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := superpose eq500 eq505
  have eq534 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := superpose eq500 eq467
  have eq535 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq500 eq534
  have eq557 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) := superpose eq500 eq479
  have eq558 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq500 eq557
  have eq559 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0))) := superpose eq500 eq558
  have eq566 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ X0)) := superpose eq535 eq485
  have eq567 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0)) = X0 := superpose eq500 eq566
  have eq568 (X0 X1 X2 : G) : (X0 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq500 eq567
  have eq1034 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2))) = (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X2 ◇ ((X2 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2))) ◇ X2))) := superpose eq12 eq535
  have eq1108 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ X2) = (X2 ◇ (((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X2))) := superpose eq506 eq1034
  have eq1114 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = (X0 ◇ (((X1 ◇ X2) ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq1108 eq12
  have eq1142 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X0 := superpose eq568 eq1114
  have eq1143 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq1142 eq7
  have eq1436 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq1143 eq559
  have eq1448 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ X0) := superpose eq500 eq1436
  have eq1449 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq500 eq1448
  have eq1469 (X0 X2 : G) : (X0 ◇ X2) = ((X0 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq1449 eq503
  have eq1543 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq1449 eq1469
  have eq1544 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X1))) = X2 := superpose eq1543 eq10
  have eq1604 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq1543 eq1544
  have eq1605 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq1543 eq1604
  have eq1606 (X0 X1 : G) : X0 = X1 := superpose eq500 eq1605
  have eq1611 (X0 : G) : sK0 ≠ X0 := superpose eq1606 eq8
  subsumption eq1611 eq1606


@[equational_result]
theorem Equation18989_implies_Equation2 (G : Type*) [Magma G] (h : Equation18989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = (X0 ◇ (((X1 ◇ X0) ◇ X3) ◇ (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X3) ◇ (X0 ◇ X3))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) ◇ X0)) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X3) ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X4) ◇ (X0 ◇ X4))))))) = X3 := superpose eq7 eq10
  have eq20 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq46 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ ((X2 ◇ (X0 ◇ ((X1 ◇ X3) ◇ (X2 ◇ X3)))) ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X3) ◇ (X2 ◇ X3)))))) = X0 := superpose eq10 eq20
  have eq48 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq20 eq20
  have eq65 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ X3) ◇ (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3))) := superpose eq20 eq9
  have eq112 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X1))) := superpose eq48 eq9
  have eq117 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq48 eq20
  have eq120 (X0 X1 : G) : (X1 ◇ X1) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq48 eq11
  have eq139 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq117
  have eq140 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1))) := superpose eq139 eq112
  have eq148 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq20 eq120
  have eq222 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := superpose eq139 eq16
  have eq223 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq139 eq9
  have eq254 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq223 eq140
  have eq267 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) = ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ X3) ◇ (((X0 ◇ X2) ◇ ((X1 ◇ X1) ◇ X2)) ◇ X3))) := superpose eq254 eq65
  have eq289 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq254 eq46
  have eq317 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := superpose eq289 eq222
  have eq321 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X1) = ((X1 ◇ X1) ◇ (((X0 ◇ X1) ◇ X3) ◇ (((X0 ◇ X2) ◇ X1) ◇ X3))) := superpose eq289 eq267
  have eq328 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X1 := superpose eq289 eq321
  have eq329 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq328 eq148
  have eq429 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq328 eq329
  have eq431 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq429 eq289
  have eq433 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := superpose eq431 eq317
  have eq436 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X1) = X2 := superpose eq431 eq433
  have eq437 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq431 eq436
  have eq438 (X0 X3 : G) : X0 = X3 := superpose eq437 eq437
  have eq446 (X0 : G) : sK0 ≠ X0 := superpose eq438 eq8
  subsumption eq446 eq438


@[equational_result]
theorem Equation18990_implies_Equation2 (G : Type*) [Magma G] (h : Equation18990 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X2 ◇ X5))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X4 : G) : (((X1 ◇ X0) ◇ X0) ◇ X4) = X0 := superpose eq7 eq12
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X2) = ((X0 ◇ X1) ◇ X3) := superpose eq12 eq12
  have eq21 (X0 X1 X3 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := superpose eq12 eq16
  have eq22 (X0 X1 X4 : G) : ((X1 ◇ X0) ◇ X4) = X0 := superpose eq21 eq13
  have eq24 (X0 X1 X2 X5 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X5))) = X2 := superpose eq21 eq10
  have eq27 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq22 eq21
  have eq34 (X0 X1 X2 X5 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X5)) = X2 := superpose eq27 eq24
  have eq35 (X0 X1 X2 X5 : G) : ((X1 ◇ X0) ◇ X5) = X2 := superpose eq27 eq34
  have eq36 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq27 eq35
  have eq37 (X0 X3 : G) : X0 = X3 := superpose eq36 eq36
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq42 eq37


@[equational_result]
theorem Equation18992_implies_Equation2 (G : Type*) [Magma G] (h : Equation18992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ X3) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq10 eq10
  have eq13 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0))) = X3 := superpose eq7 eq10
  have eq19 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ ((((X1 ◇ X3) ◇ X4) ◇ X5) ◇ (((X1 ◇ X3) ◇ X4) ◇ ((X1 ◇ X3) ◇ X4)))) = ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) := superpose eq9 eq9
  have eq27 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (((X1 ◇ X3) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X4) ◇ (X0 ◇ X0))) := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X3) ◇ X4) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) = ((X1 ◇ X1) ◇ (((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) ◇ X5) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))))) := superpose eq9 eq9
  have eq33 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq9 eq9
  have eq49 (X0 X1 X3 : G) : (((X1 ◇ X0) ◇ X3) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq33
  have eq53 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) = (((X1 ◇ X3) ◇ X4) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) := superpose eq9 eq33
  have eq72 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ X3) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) := superpose eq33 eq9
  have eq75 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2)))) := superpose eq33 eq10
  have eq99 (X0 X1 X3 X4 X5 : G) : (X4 ◇ ((((X1 ◇ X3) ◇ X4) ◇ X5) ◇ (((X1 ◇ X3) ◇ X4) ◇ ((X1 ◇ X3) ◇ X4)))) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) := superpose eq49 eq19
  have eq103 (X0 X1 X3 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (((X1 ◇ X3) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X4) ◇ (X0 ◇ X0))) := superpose eq49 eq27
  have eq104 (X0 X1 X3 X4 X5 : G) : (((X1 ◇ X3) ◇ X4) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) = ((X1 ◇ X1) ◇ (((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) ◇ X5) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))))) := superpose eq49 eq29
  have eq115 (X0 X1 X3 X4 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) = (X4 ◇ (X4 ◇ (((X1 ◇ X3) ◇ X4) ◇ ((X1 ◇ X3) ◇ X4)))) := superpose eq49 eq99
  have eq117 (X0 X1 X3 X4 : G) : (((X1 ◇ X3) ◇ X4) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) = ((X1 ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))))) := superpose eq49 eq104
  have eq121 (X0 X1 X3 X4 : G) : (((X1 ◇ X3) ◇ X4) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) = ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) := superpose eq49 eq53
  have eq148 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X4) ◇ (X0 ◇ X4))) ◇ (X2 ◇ X2))) = X3 := superpose eq33 eq13
  have eq150 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ ((((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) ◇ X4) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X2))) = X3 := superpose eq13 eq13
  have eq170 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) ◇ X2) ◇ (((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) ◇ X3) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))))) = X2 := superpose eq13 eq7
  have eq171 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ ((((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X4) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X2))) = X3 := superpose eq103 eq150
  have eq172 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ ((((X0 ◇ X0) ◇ X4) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (X2 ◇ X2))) = X3 := superpose eq75 eq171
  have eq173 (X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (X4 ◇ (X2 ◇ X2))) = X3 := superpose eq10 eq172
  have eq184 (X0 X1 X2 X3 : G) : (((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X2) ◇ (((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X2 := superpose eq103 eq170
  have eq185 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ (((X0 ◇ X0) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X2 := superpose eq75 eq184
  have eq186 (X0 X2 X3 : G) : (((X0 ◇ X0) ◇ X2) ◇ X3) = X2 := superpose eq173 eq185
  have eq189 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X0)) = (X0 ◇ X3) := superpose eq186 eq72
  have eq192 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X2) ◇ X3) = X2 := superpose eq33 eq186
  have eq222 (X0 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X4) ◇ (X0 ◇ X4))) = X3 := superpose eq192 eq148
  have eq223 (X0 X1 X3 X4 : G) : (((X1 ◇ X3) ◇ X4) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) = ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq222 eq117
  have eq232 (X1 X3 X4 : G) : (((X1 ◇ X3) ◇ X4) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) = X1 := superpose eq222 eq223
  have eq234 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) = X1 := superpose eq232 eq121
  have eq237 (X1 X3 X4 : G) : (X4 ◇ (X4 ◇ (((X1 ◇ X3) ◇ X4) ◇ ((X1 ◇ X3) ◇ X4)))) = X1 := superpose eq234 eq115
  have eq238 (X1 X2 : G) : (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = X1 := superpose eq237 eq12
  have eq239 (X1 X3 X4 : G) : (X4 ◇ (X1 ◇ X3)) = X1 := superpose eq238 eq237
  have eq266 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq239 eq189
  have eq276 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq266 eq186
  have eq281 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq266 eq276
  have eq282 (X0 X3 : G) : X0 = X3 := superpose eq281 eq281
  have eq287 (X0 : G) : sK0 ≠ X0 := superpose eq282 eq8
  subsumption eq287 eq282


@[equational_result]
theorem Equation18993_implies_Equation2 (G : Type*) [Magma G] (h : Equation18993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X3 := superpose eq10 eq10
  have eq14 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) = X2 := superpose eq14 eq7
  have eq56 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) = X2 := superpose eq14 eq7
  have eq68 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq56 eq52
  have eq70 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq68 eq12
  have eq76 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = X2 := superpose eq70 eq10
  have eq99 (X0 X2 : G) : X0 = X2 := superpose eq76 eq76
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq99 eq8
  subsumption eq106 eq99


@[equational_result]
theorem Equation18994_implies_Equation2 (G : Type*) [Magma G] (h : Equation18994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X5))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq10
  have eq45 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ (X0 ◇ X0)) := superpose eq16 eq16
  have eq125 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X0 ◇ (X0 ◇ X0)))) = X2 := superpose eq45 eq7
  have eq132 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) = X2 := superpose eq45 eq7
  have eq148 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X2 := superpose eq132 eq125
  have eq152 (X0 X2 : G) : (X0 ◇ (X0 ◇ X0)) = X2 := superpose eq148 eq16
  have eq220 (X0 X2 : G) : X0 = X2 := superpose eq152 eq152
  have eq227 (X0 : G) : sK0 ≠ X0 := superpose eq220 eq8
  subsumption eq227 eq220


@[equational_result]
theorem Equation18998_implies_Equation2 (G : Type*) [Magma G] (h : Equation18998 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq17 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq12 eq7
  have eq41 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X1 ◇ X0)) := superpose eq12 eq17
  have eq42 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq17 eq17
  have eq53 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq42 eq41
  have eq56 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) = X0 := superpose eq53 eq7
  have eq81 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X2)) = X0 := superpose eq53 eq56
  have eq82 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq53 eq81
  have eq90 (X0 X2 : G) : X0 = X2 := superpose eq82 eq82
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq90 eq8
  subsumption eq92 eq90


@[equational_result]
theorem Equation19000_implies_Equation2 (G : Type*) [Magma G] (h : Equation19000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X1)) = (X0 ◇ (((X1 ◇ X0) ◇ X4) ◇ (X5 ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X5 ◇ (X1 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X4) ◇ ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X5) ◇ X0)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq10 eq10
  have eq36 (X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G) : (((X1 ◇ X4) ◇ X5) ◇ (X6 ◇ (X1 ◇ X4))) = ((X7 ◇ X1) ◇ (((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X1 ◇ X0)))) ◇ X8) ◇ (X9 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))))) := superpose eq9 eq9
  have eq43 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X0)) = ((X0 ◇ X3) ◇ (X4 ◇ X0)) := superpose eq9 eq9
  have eq57 (X0 X1 X4 X5 X6 : G) : (X0 ◇ (X4 ◇ (X1 ◇ X0))) = (((X1 ◇ X0) ◇ X5) ◇ (X6 ◇ (X1 ◇ X0))) := superpose eq7 eq43
  have eq128 (X0 X1 X2 X3 X6 X7 X8 X9 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X6 ◇ X3)) ◇ X7) ◇ (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X6 ◇ X3)) ◇ X8) ◇ X9)) = X7 := superpose eq9 eq11
  have eq147 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X4) ◇ X0) = X4 := superpose eq10 eq11
  have eq165 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X4) ◇ X5) ◇ X6) ◇ (X5 ◇ X0)) = X6 := superpose eq11 eq10
  have eq189 (X0 X1 X2 X3 X6 X7 X8 X9 : G) : ((X6 ◇ X3) ◇ (((((X0 ◇ X1) ◇ (X2 ◇ X0)) ◇ (X6 ◇ X3)) ◇ X8) ◇ X9)) = X7 := superpose eq147 eq128
  have eq196 (X3 X6 X7 X9 : G) : ((X6 ◇ X3) ◇ ((X6 ◇ X3) ◇ X9)) = X7 := superpose eq147 eq189
  have eq201 (X0 X4 X5 X6 : G) : ((X4 ◇ X6) ◇ (X5 ◇ X0)) = X6 := superpose eq147 eq165
  have eq202 (X1 X4 X5 X6 : G) : (((X1 ◇ X4) ◇ X5) ◇ (X6 ◇ (X1 ◇ X4))) = X1 := superpose eq201 eq36
  have eq257 (X0 X1 X4 : G) : (X0 ◇ (X4 ◇ (X1 ◇ X0))) = X1 := superpose eq202 eq57
  have eq262 (X0 X1 X2 X4 : G) : (X0 ◇ (X0 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X0)))) = X1 := superpose eq257 eq13
  have eq268 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq257 eq262
  have eq271 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq268 eq257
  have eq274 (X3 X7 X9 : G) : (X3 ◇ (X3 ◇ X9)) = X7 := superpose eq271 eq196
  have eq286 (X3 X7 X9 : G) : (X3 ◇ X9) = X7 := superpose eq271 eq274
  have eq287 (X0 X3 : G) : X0 = X3 := superpose eq286 eq286
  have eq292 (X0 : G) : sK0 ≠ X0 := superpose eq287 eq8
  subsumption eq292 eq287


@[equational_result]
theorem Equation19001_implies_Equation2 (G : Type*) [Magma G] (h : Equation19001 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq12 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq15 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation19002_implies_Equation2 (G : Type*) [Magma G] (h : Equation19002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X5 ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq12 (X0 X2 X5 : G) : (X0 ◇ (X0 ◇ (X5 ◇ X5))) = X2 := superpose eq11 eq10
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq11 eq12
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq28 eq21


@[equational_result]
theorem Equation19003_implies_Equation2 (G : Type*) [Magma G] (h : Equation19003 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X6 X7 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X6 ◇ X7))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X6 X7 : G) : (X0 ◇ (X0 ◇ (X6 ◇ X7))) = X2 := superpose eq12 eq10
  have eq24 (X0 X4 : G) : X0 = X4 := superpose eq12 eq16
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq31 eq24


@[equational_result]
theorem Equation19005_implies_Equation2 (G : Type*) [Magma G] (h : Equation19005 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X3)) = ((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ (X0 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) = (((X0 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X1)) ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3)))) ◇ ((X4 ◇ (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3)))) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3)))) := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) ◇ X0) ◇ ((X4 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1)))) = X0 := superpose eq7 eq11
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = ((((X3 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X2))) := superpose eq7 eq11
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ ((X4 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X3 ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X2 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))))) := superpose eq11 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)))) := superpose eq7 eq10
  have eq24 (X0 X1 X2 X3 X4 : G) : (X0 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3)) = ((X4 ◇ (X0 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3))) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X1)) ◇ X3)) ◇ X4))) := superpose eq7 eq10
  have eq46 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) ◇ X1)))) := superpose eq23 eq23
  have eq50 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) ◇ X1)) = ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) ◇ (((X3 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))))) := superpose eq23 eq23
  have eq52 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) ◇ X1))) := superpose eq23 eq7
  have eq54 (X0 X1 X2 X3 : G) : (((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) ◇ X1) ◇ ((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) = X1 := superpose eq23 eq7
  have eq116 (X0 X1 X2 : G) : (((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0))) ◇ X0) ◇ X0) = X0 := superpose eq7 eq54
  have eq200 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq116 eq7
  have eq294 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0))) ◇ X0) = ((X0 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0))) ◇ X0)) ◇ (((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0))) ◇ X0) ◇ X0)) := superpose eq116 eq200
  have eq300 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq200 eq7
  have eq304 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) = X0 := superpose eq200 eq23
  have eq337 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0))) ◇ X0) = ((X0 ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0))) ◇ X0)) ◇ X0) := superpose eq116 eq294
  have eq343 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X1) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X4))) = (((((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X4)) ◇ (X3 ◇ X1))) ◇ ((X3 ◇ X1) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X4)))) ◇ (X1 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X4)))) := superpose eq10 eq18
  have eq425 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq300 eq11
  have eq478 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) = ((((X3 ◇ ((X4 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) ◇ X1))) ◇ (((X4 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ ((X5 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ ((X4 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) ◇ X1)))) := superpose eq23 eq16
  have eq659 (X0 X1 X4 X5 : G) : ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ ((X4 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (((X5 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))))) := superpose eq116 eq22
  have eq770 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq7 eq304
  have eq815 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq304 eq300
  have eq819 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq815 eq770
  have eq821 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq815 eq819
  have eq823 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq821 eq425
  have eq969 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0))) := superpose eq821 eq23
  have eq1017 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ X0) := superpose eq823 eq969
  have eq1018 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq821 eq1017
  have eq1067 (X0 X1 X4 X5 : G) : ((X0 ◇ X1) ◇ ((X4 ◇ X1) ◇ (X1 ◇ (((X5 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))))) = X1 := superpose eq1018 eq659
  have eq1269 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq200 eq1018
  have eq1316 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ X0))) := superpose eq1018 eq23
  have eq1317 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))))) := superpose eq1018 eq23
  have eq1327 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := superpose eq1018 eq200
  have eq1530 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0))) := superpose eq7 eq1327
  have eq1601 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ X4))) = ((((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ (((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ X4)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2)))) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ X4)))) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ X4)))) := superpose eq24 eq12
  have eq2295 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq1327 eq1269
  have eq2338 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := superpose eq2295 eq1316
  have eq2360 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X0)) := superpose eq2338 eq1317
  have eq2367 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = ((X2 ◇ X0) ◇ X0) := superpose eq1018 eq2360
  have eq2368 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X0 := superpose eq1018 eq2367
  have eq2372 (X0 X1 X2 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0))) ◇ X0) = X0 := superpose eq2368 eq337
  have eq2717 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X1))) := superpose eq2372 eq46
  have eq2718 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ X1) = ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) ◇ (((X3 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))))) := superpose eq2372 eq50
  have eq2719 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ ((X3 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ X1)) := superpose eq2372 eq52
  have eq2726 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) = ((((X3 ◇ ((X4 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ X1)) ◇ (((X4 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ ((X5 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ ((X4 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ X1))) := superpose eq2372 eq478
  have eq2732 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X1 := superpose eq2295 eq2717
  have eq2748 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ X4))) = ((((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ (((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ X4)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2)))) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3)) ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ X4)))) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3)) := superpose eq2732 eq1601
  have eq2776 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) ◇ X1)) = ((X3 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ X1) := superpose eq2732 eq2718
  have eq2777 (X0 X1 X2 X3 : G) : ((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) ◇ X1) = ((X3 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ X1) := superpose eq2372 eq2776
  have eq2778 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)))) ◇ X1) = X1 := superpose eq2372 eq2777
  have eq2779 (X0 X1 X2 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1))) = (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) := superpose eq2778 eq2719
  have eq2783 (X0 X1 X4 X5 : G) : ((X0 ◇ X1) ◇ ((X4 ◇ X1) ◇ (((X5 ◇ X1) ◇ (X1 ◇ X0)) ◇ X1))) = X1 := superpose eq2779 eq1067
  have eq2795 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = ((((X3 ◇ ((X4 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1)) ◇ X1)) ◇ (((X4 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1)) ◇ ((X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1)) ◇ ((X4 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1)) ◇ X1))) := superpose eq2779 eq2726
  have eq2796 (X0 X1 X2 X3 X5 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = ((((X3 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1)) ◇ ((X5 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1)) ◇ X1)) := superpose eq2368 eq2795
  have eq2797 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = ((((X3 ◇ X1) ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1)) ◇ X1) := superpose eq2368 eq2796
  have eq2798 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X2)) ◇ X1) = X1 := superpose eq2368 eq2797
  have eq2800 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0)) := superpose eq2798 eq1530
  have eq2805 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ ((X4 ◇ X1) ◇ X1)) = X1 := superpose eq2798 eq2783
  have eq2806 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X0) := superpose eq2798 eq2800
  have eq2807 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq2798 eq2806
  have eq2832 (X1 X3 X4 : G) : ((X3 ◇ X1) ◇ (X1 ◇ (X1 ◇ X4))) = (((X1 ◇ ((X1 ◇ (X1 ◇ X4)) ◇ (X3 ◇ X1))) ◇ ((X3 ◇ X1) ◇ (X1 ◇ (X1 ◇ X4)))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X4)))) := superpose eq2807 eq343
  have eq2889 (X0 X3 X4 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X3) ◇ X4))) = ((((X0 ◇ X3) ◇ (((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X3) ◇ X4)) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X3)) ◇ ((X0 ◇ X3) ◇ X4)))) ◇ (X0 ◇ X3)) := superpose eq2807 eq2748
  have eq2921 (X1 X3 X4 : G) : ((X3 ◇ X1) ◇ (X1 ◇ (X1 ◇ X4))) = (((X1 ◇ ((X1 ◇ (X1 ◇ X4)) ◇ (X3 ◇ X1))) ◇ ((X3 ◇ X1) ◇ (X1 ◇ (X1 ◇ X4)))) ◇ (X1 ◇ (X1 ◇ X4))) := superpose eq1269 eq2832
  have eq2922 (X1 X3 X4 : G) : (X1 ◇ (X1 ◇ X4)) = ((X3 ◇ X1) ◇ (X1 ◇ (X1 ◇ X4))) := superpose eq2368 eq2921
  have eq2923 (X1 X4 : G) : (X1 ◇ (X1 ◇ X4)) = X1 := superpose eq2807 eq2922
  have eq3050 (X0 X3 : G) : (X0 ◇ (X0 ◇ X3)) = ((((X0 ◇ X3) ◇ ((X0 ◇ X3) ◇ X0)) ◇ (X0 ◇ (X0 ◇ X3))) ◇ (X0 ◇ X3)) := superpose eq2807 eq2889
  have eq3051 (X0 X3 : G) : (X0 ◇ X3) = (X0 ◇ (X0 ◇ X3)) := superpose eq2368 eq3050
  have eq3052 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq2923 eq3051
  have eq3090 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ (X4 ◇ X1)) = X1 := superpose eq3052 eq2805
  have eq3091 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X4) = X1 := superpose eq3052 eq3090
  have eq3092 (X0 X1 X4 : G) : (X0 ◇ X4) = X1 := superpose eq3052 eq3091
  have eq3093 (X0 X1 : G) : X0 = X1 := superpose eq821 eq3092
  have eq3119 (X0 : G) : sK0 ≠ X0 := superpose eq3093 eq8
  subsumption eq3119 eq3093


@[equational_result]
theorem Equation19006_implies_Equation2 (G : Type*) [Magma G] (h : Equation19006 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X2)) = (X0 ◇ ((X3 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((((X3 ◇ X0) ◇ (X0 ◇ X3)) ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ ((((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X3)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1))) := superpose eq7 eq11
  have eq18 (X0 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ ((((X4 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X4)) ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2)))) = X0 := superpose eq7 eq11
  have eq23 (X0 X1 X3 X4 : G) : ((((X3 ◇ X1) ◇ (X1 ◇ X3)) ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ ((X4 ◇ ((((X3 ◇ X1) ◇ (X1 ◇ X3)) ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((((X3 ◇ X1) ◇ (X1 ◇ X3)) ◇ (X0 ◇ X1)) ◇ X1) ◇ X4))) := superpose eq11 eq7
  have eq24 (X0 X3 : G) : ((X3 ◇ X0) ◇ X0) = X0 := superpose eq7 eq18
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X0)))) := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0))) = (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X3 ◇ (X0 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ (X1 ◇ X0))) ◇ X3))) := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 : G) : ((((X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2)) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = (X1 ◇ ((X3 ◇ ((((X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2)) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) ◇ (((((X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ X2)) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X3))) := superpose eq9 eq9
  have eq37 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X1)) = (X2 ◇ ((((X3 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1))) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0))) ◇ (((X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1))) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0)) ◇ X3)) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1))) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ X0)))) := superpose eq9 eq9
  have eq45 (X1 X3 : G) : (X1 ◇ ((X3 ◇ X1) ◇ (X1 ◇ X3))) = X1 := superpose eq7 eq34
  have eq46 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X1)) = (X2 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1))) := superpose eq7 eq37
  have eq47 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X1)) = X2 := superpose eq45 eq46
  have eq49 (X0 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X3))) = X0 := superpose eq47 eq9
  have eq51 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq47 eq11
  have eq52 (X0 X1 X3 : G) : (X0 ◇ ((((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X3)) ◇ X0) ◇ (X0 ◇ X1))) = X0 := superpose eq47 eq12
  have eq59 (X0 X1 X4 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ ((X4 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ X1) ◇ X4))) := superpose eq47 eq23
  have eq61 (X0 X2 : G) : (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := superpose eq47 eq27
  have eq63 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ ((X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3))) := superpose eq47 eq29
  have eq69 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq47 eq49
  have eq70 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) = X0 := superpose eq47 eq52
  have eq72 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq47 eq59
  have eq78 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq47 eq63
  have eq79 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := superpose eq61 eq78
  have eq109 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq69 eq51
  have eq113 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq109 eq72
  have eq150 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := superpose eq79 eq79
  have eq157 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq113 eq150
  have eq158 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := superpose eq24 eq157
  have eq159 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq158 eq79
  have eq161 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq159 eq158
  have eq162 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq161 eq70
  have eq167 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq161 eq162
  have eq168 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq161 eq167
  have eq171 (X0 X1 : G) : X0 = X1 := superpose eq168 eq161
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq171 eq8
  subsumption eq173 eq171


@[equational_result]
theorem Equation19007_implies_Equation2 (G : Type*) [Magma G] (h : Equation19007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X2 ◇ X0) ◇ (X0 ◇ X3)) = (X0 ◇ ((X4 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X5))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq7 eq7
  have eq14 (X0 X2 X3 X4 X5 : G) : ((X4 ◇ X0) ◇ ((X5 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3)))) = X0 := superpose eq7 eq11
  have eq21 (X0 X4 : G) : ((X4 ◇ X0) ◇ X0) = X0 := superpose eq7 eq14
  have eq25 (X0 X1 X2 X4 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ X4))) := superpose eq7 eq9
  have eq27 (X0 X2 X3 X4 X5 X6 : G) : (X0 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X4)) = (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ ((X5 ◇ (X0 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X4))) ◇ ((X0 ◇ (((X2 ◇ X0) ◇ (X0 ◇ X3)) ◇ X4)) ◇ X6))) := superpose eq7 eq9
  have eq32 (X0 X1 X2 X3 X6 X7 : G) : ((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = (X1 ◇ ((X6 ◇ ((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2)))) ◇ (((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) ◇ X7))) := superpose eq9 eq9
  have eq35 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X3)) = (X2 ◇ ((X5 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X4)))) := superpose eq9 eq9
  have eq42 (X1 X6 X7 : G) : (X1 ◇ ((X6 ◇ X1) ◇ (X1 ◇ X7))) = X1 := superpose eq7 eq32
  have eq43 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X3)) = (X2 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) := superpose eq7 eq35
  have eq44 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X3)) = X2 := superpose eq42 eq43
  have eq50 (X0 X4 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X4))) = X0 := superpose eq44 eq25
  have eq51 (X0 X4 X5 X6 : G) : (X0 ◇ (X0 ◇ X4)) = (X0 ◇ ((X5 ◇ (X0 ◇ (X0 ◇ X4))) ◇ ((X0 ◇ (X0 ◇ X4)) ◇ X6))) := superpose eq44 eq27
  have eq57 (X0 X4 : G) : (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X0 ◇ (X0 ◇ X4))) := superpose eq44 eq51
  have eq58 (X0 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X0 := superpose eq50 eq57
  have eq88 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq21 eq58
  have eq90 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq21 eq88
  have eq92 (X2 X3 : G) : (X2 ◇ (X2 ◇ X3)) = X2 := superpose eq90 eq44
  have eq95 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq90 eq92
  have eq96 (X0 X1 : G) : X0 = X1 := superpose eq95 eq90
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq98 eq96


@[equational_result]
theorem Equation19009_implies_Equation2 (G : Type*) [Magma G] (h : Equation19009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ ((X3 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1))) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ X3)) = ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq11 eq7
  have eq22 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X4 ◇ X4)) = (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) ◇ (X2 ◇ ((X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3))) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)))))) := superpose eq10 eq10
  have eq34 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq13
  have eq39 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq13 eq7
  have eq55 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := superpose eq11 eq9
  have eq66 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq9
  have eq67 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1))) := superpose eq9 eq10
  have eq96 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq66 eq13
  have eq102 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X1 := superpose eq66 eq7
  have eq104 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq39 eq96
  have eq105 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq39 eq104
  have eq106 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq105 eq34
  have eq120 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq106 eq11
  have eq125 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq120 eq106
  have eq126 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ ((X3 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X0))) := superpose eq125 eq9
  have eq136 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ (X1 ◇ X1))) = ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) ◇ (X2 ◇ X1)) := superpose eq125 eq67
  have eq139 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := superpose eq125 eq55
  have eq144 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X4 ◇ X4)) = (((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3)) ◇ (X2 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X3))))) := superpose eq125 eq22
  have eq149 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ X1)) = X0 := superpose eq125 eq7
  have eq152 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq125 eq13
  have eq169 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ X1) = (X0 ◇ ((X3 ◇ ((X2 ◇ X0) ◇ X1)) ◇ (X1 ◇ X0))) := superpose eq125 eq126
  have eq184 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X1 ◇ X1))) = ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X1)) := superpose eq125 eq136
  have eq185 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X1)) = (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ X1)) := superpose eq125 eq184
  have eq191 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq125 eq139
  have eq192 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq125 eq191
  have eq201 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X4 ◇ X4)) = (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)))) := superpose eq125 eq144
  have eq202 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X4) = (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)))) := superpose eq125 eq201
  have eq248 (X0 X1 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := superpose eq125 eq102
  have eq249 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq125 eq248
  have eq254 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq149 eq149
  have eq263 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq152 eq149
  have eq277 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = ((X0 ◇ (((X1 ◇ X0) ◇ X2) ◇ X0)) ◇ X0) := superpose eq254 eq152
  have eq293 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := superpose eq192 eq152
  have eq300 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq192 eq293
  have eq302 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq300 eq249
  have eq306 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X1 ◇ X0) ◇ X2) ◇ X0) := superpose eq302 eq277
  have eq308 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X0 := superpose eq125 eq306
  have eq311 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X1)) = (((X0 ◇ X1) ◇ X2) ◇ X1) := superpose eq308 eq185
  have eq312 (X0 X1 X2 X3 : G) : ((X3 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X2 ◇ X1)) = X1 := superpose eq308 eq311
  have eq316 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ X0) ◇ X1) := superpose eq312 eq169
  have eq320 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X1) = X0 := superpose eq125 eq316
  have eq321 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq320 eq263
  have eq330 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X2 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)))) = X2 := superpose eq320 eq202
  have eq367 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) = X2 := superpose eq321 eq330
  have eq368 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X2 := superpose eq321 eq367
  have eq369 (X2 X3 : G) : (X3 ◇ X3) = X2 := superpose eq321 eq368
  have eq388 (X0 X2 : G) : X0 = X2 := superpose eq369 eq369
  have eq396 (X0 : G) : sK0 ≠ X0 := superpose eq388 eq8
  subsumption eq396 eq388


@[equational_result]
theorem Equation19011_implies_Equation2 (G : Type*) [Magma G] (h : Equation19011 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X0) ◇ (X3 ◇ X4)) = ((X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) ◇ (X0 ◇ (X1 ◇ X5))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq18 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X3))) = X0 := superpose eq12 eq7
  have eq38 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq11 eq15
  have eq45 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq15 eq7
  have eq86 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = (X0 ◇ ((X3 ◇ X0) ◇ X2)) := superpose eq11 eq38
  have eq101 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X1) ◇ (X2 ◇ X3)) = (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X1 ◇ ((X4 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) ◇ X5))) := superpose eq38 eq10
  have eq164 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X1 ◇ X3)) = (X0 ◇ X0) := superpose eq7 eq45
  have eq195 (X0 X1 X2 X3 : G) : ((X2 ◇ X0) ◇ (X1 ◇ X3)) = X0 := superpose eq15 eq164
  have eq217 (X1 X4 X5 : G) : (X1 ◇ (X1 ◇ ((X4 ◇ X1) ◇ X5))) = X1 := superpose eq195 eq101
  have eq258 (X1 X4 X5 : G) : (X1 ◇ ((X4 ◇ X1) ◇ X5)) = X1 := superpose eq86 eq217
  have eq259 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X0 := superpose eq258 eq86
  have eq261 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ X2) ◇ X0)) = X2 := superpose eq259 eq11
  have eq269 (X0 X2 : G) : (X0 ◇ X2) = X2 := superpose eq259 eq261
  have eq272 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X3))) = X0 := superpose eq269 eq18
  have eq281 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X3)) = X0 := superpose eq269 eq272
  have eq282 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq269 eq281
  have eq309 (X0 X1 : G) : X0 = X1 := superpose eq269 eq282
  have eq322 (X0 : G) : sK0 ≠ X0 := superpose eq309 eq8
  subsumption eq322 eq309


@[equational_result]
theorem Equation19013_implies_Equation2 (G : Type*) [Magma G] (h : Equation19013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ (((X2 ◇ X0) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (((((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq12 eq12
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq7 eq12
  have eq19 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq12 eq14
  have eq32 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0))) ◇ X3) ◇ ((X0 ◇ X3) ◇ X0)) = X3 := superpose eq12 eq11
  have eq43 (X0 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq11 eq19
  have eq45 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq19 eq11
  have eq46 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := superpose eq19 eq7
  have eq53 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq15 eq43
  have eq97 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq53 eq7
  have eq113 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq97 eq53
  have eq114 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq113 eq15
  have eq122 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := superpose eq113 eq45
  have eq123 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := superpose eq113 eq46
  have eq143 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq113 eq123
  have eq144 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq143 eq122
  have eq145 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq113 eq144
  have eq146 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq114 eq145
  have eq147 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X0))) ◇ X3) ◇ X0) = X3 := superpose eq146 eq32
  have eq196 (X0 X3 : G) : (X3 ◇ X0) = X3 := superpose eq146 eq147
  have eq374 (X0 X1 : G) : X0 = X1 := superpose eq196 eq146
  have eq396 (X0 : G) : sK0 ≠ X0 := superpose eq374 eq8
  subsumption eq396 eq374


@[equational_result]
theorem Equation19014_implies_Equation2 (G : Type*) [Magma G] (h : Equation19014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X2)) = (X0 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq7 eq12
  have eq15 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq18 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) = X0 := superpose eq12 eq7
  have eq20 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = (X0 ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq15 eq14
  have eq27 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X2)) = X0 := superpose eq15 eq18
  have eq28 (X0 X2 : G) : ((X2 ◇ X0) ◇ X2) = X0 := superpose eq27 eq20
  have eq38 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq28 eq12
  have eq41 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq38 eq28
  have eq44 (X0 X1 : G) : X0 = X1 := superpose eq41 eq38
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq57 eq44


@[equational_result]
theorem Equation19015_implies_Equation2 (G : Type*) [Magma G] (h : Equation19015 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X3)) = (X0 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3))) := superpose eq7 eq12
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq18 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3))) = X0 := superpose eq12 eq7
  have eq19 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ (X2 ◇ X3)) = X0 := superpose eq18 eq13
  have eq50 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq14 eq19
  have eq56 (X0 X2 X3 : G) : (X0 ◇ (X2 ◇ X3)) = X0 := superpose eq50 eq19
  have eq62 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq50 eq56
  have eq65 (X0 X1 : G) : X0 = X1 := superpose eq62 eq50
  have eq67 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq67 eq65


@[equational_result]
theorem Equation19017_implies_Equation2 (G : Type*) [Magma G] (h : Equation19017 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X4 : G) : ((X0 ◇ X4) ◇ X4) = X4 := superpose eq7 eq12
  have eq16 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq54 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq16 eq7
  have eq59 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq16 eq54
  have eq202 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq59 eq59
  have eq232 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq13 eq202
  have eq233 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1))) = X0 := superpose eq232 eq7
  have eq309 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X0 := superpose eq232 eq233
  have eq310 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq232 eq309
  have eq514 (X0 X1 : G) : X0 = X1 := superpose eq310 eq232
  have eq532 (X0 : G) : sK0 ≠ X0 := superpose eq514 eq8
  subsumption eq532 eq514


@[equational_result]
theorem Equation19018_implies_Equation2 (G : Type*) [Magma G] (h : Equation19018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ X2)) = (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2))) := superpose eq7 eq12
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq18 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2))) = X0 := superpose eq12 eq7
  have eq19 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ X2)) = X0 := superpose eq18 eq13
  have eq28 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq14 eq19
  have eq32 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq19 eq19
  have eq42 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq19 eq28
  have eq45 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ (X2 ◇ X0)) := superpose eq28 eq19
  have eq47 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq42 eq32
  have eq48 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq28 eq45
  have eq56 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq48 eq47
  have eq58 (X0 X1 : G) : X0 = X1 := superpose eq14 eq56
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq66 eq58


@[equational_result]
theorem Equation19019_implies_Equation2 (G : Type*) [Magma G] (h : Equation19019 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ (X3 ◇ X3)) = (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) := superpose eq7 eq12
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq17 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) = X0 := superpose eq12 eq7
  have eq18 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq14 eq13
  have eq25 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X0 := superpose eq14 eq17
  have eq26 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X0 := superpose eq25 eq18
  have eq33 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq12 eq26
  have eq41 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq33 eq26
  have eq43 (X0 X1 : G) : X0 = X1 := superpose eq14 eq41
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq43 eq8
  subsumption eq51 eq43


@[equational_result]
theorem Equation19020_implies_Equation2 (G : Type*) [Magma G] (h : Equation19020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ (X3 ◇ X4)) = (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) := superpose eq7 eq12
  have eq14 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq12
  have eq18 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) = X0 := superpose eq12 eq7
  have eq19 (X0 X2 X3 X4 : G) : ((X2 ◇ X0) ◇ (X3 ◇ X4)) = X0 := superpose eq18 eq13
  have eq25 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X3)) = X0 := superpose eq12 eq11
  have eq31 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq11 eq12
  have eq32 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X0 := superpose eq25 eq31
  have eq38 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq12 eq32
  have eq46 (X0 X2 X3 X4 : G) : (X2 ◇ (X3 ◇ X4)) = X0 := superpose eq38 eq19
  have eq49 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq38 eq46
  have eq50 (X0 X1 : G) : X0 = X1 := superpose eq14 eq49
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq58 eq50


@[equational_result]
theorem Equation19022_implies_Equation2 (G : Type*) [Magma G] (h : Equation19022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ (((X2 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3) ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X3 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1)))) ◇ X4) ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X3 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))))))) = X4 := superpose eq7 eq10
  have eq16 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) ◇ X0) ◇ X4) ◇ ((X3 ◇ X0) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) ◇ X0)))) = X4 := superpose eq7 eq10
  have eq18 (X0 X1 X2 : G) : (X2 ◇ X0) = ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq54 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X1 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)))) := superpose eq18 eq9
  have eq56 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1)))) = X2 := superpose eq18 eq7
  have eq80 (X0 X1 X2 : G) : (X2 ◇ X1) = ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X2 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) := superpose eq18 eq11
  have eq106 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq7 eq56
  have eq108 (X0 X1 : G) : (X1 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq56 eq56
  have eq175 (X0 X1 : G) : ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X0 := superpose eq106 eq56
  have eq176 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))))) = X1 := superpose eq106 eq10
  have eq235 (X0 X1 X2 X4 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ X4) ◇ ((X2 ◇ X1) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)))) = X4 := superpose eq18 eq16
  have eq276 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq176 eq14
  have eq493 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) := superpose eq7 eq175
  have eq824 (X0 X1 : G) : (X1 ◇ X1) = ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq18 eq80
  have eq1055 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0))))) := superpose eq824 eq176
  have eq1399 (X0 X1 : G) : (X0 ◇ X1) = (((((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X1)) := superpose eq106 eq276
  have eq1818 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0)))) = X1 := superpose eq108 eq235
  have eq1946 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) := superpose eq108 eq1818
  have eq1962 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq56 eq1946
  have eq1963 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq1962
  have eq1971 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (((X2 ◇ X1) ◇ X1) ◇ X1))) := superpose eq1963 eq54
  have eq1997 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := superpose eq1963 eq175
  have eq2067 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0)))) := superpose eq1963 eq1055
  have eq2086 (X0 X1 : G) : (X0 ◇ X1) = ((((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq1963 eq1399
  have eq2113 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := superpose eq1963 eq493
  have eq2288 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq1963 eq1997
  have eq2289 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := superpose eq1963 eq2288
  have eq2349 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)))) := superpose eq1963 eq2067
  have eq2350 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)))) := superpose eq1963 eq2349
  have eq2351 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)))) := superpose eq1963 eq2350
  have eq2352 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq1971 eq2351
  have eq2353 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq2289 eq2352
  have eq2421 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq1963 eq2113
  have eq2422 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq1963 eq2421
  have eq2423 (X0 X1 : G) : (X0 ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq2422 eq2086
  have eq2425 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := superpose eq2353 eq2423
  have eq2426 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq2353 eq2425
  have eq2428 (X0 X1 X2 : G) : (X0 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq2426 eq7
  have eq2429 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ ((X3 ◇ X0) ◇ (((X2 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0))) := superpose eq2426 eq9
  have eq3114 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq2426 eq2428
  have eq3115 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq2426 eq3114
  have eq3116 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq3115 eq2429
  have eq3117 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X1) = X0 := superpose eq2426 eq3116
  have eq3118 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq2426 eq3117
  have eq3162 (X0 X1 : G) : X0 = X1 := superpose eq3115 eq3118
  have eq3167 (X0 : G) : sK0 ≠ X0 := superpose eq3162 eq8
  subsumption eq3167 eq3162


@[equational_result]
theorem Equation19024_implies_Equation2 (G : Type*) [Magma G] (h : Equation19024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X4) ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X1) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X4 : G) : ((X4 ◇ X0) ◇ X4) = X0 := superpose eq7 eq12
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) := superpose eq12 eq12
  have eq34 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq11 eq12
  have eq40 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq13 eq13
  have eq42 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq11 eq13
  have eq53 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = X3 := superpose eq40 eq34
  have eq61 (X0 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq53 eq10
  have eq65 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X0 ◇ X1) ◇ X3) := superpose eq53 eq16
  have eq75 (X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X1) = X1 := superpose eq53 eq42
  have eq76 (X2 X3 : G) : (X2 ◇ X3) = X3 := superpose eq75 eq65
  have eq81 (X0 X3 X4 X5 : G) : (X3 ◇ (X0 ◇ (X4 ◇ X5))) = X4 := superpose eq76 eq61
  have eq84 (X3 X4 X5 : G) : (X3 ◇ (X4 ◇ X5)) = X4 := superpose eq76 eq81
  have eq85 (X3 X4 X5 : G) : (X3 ◇ X5) = X4 := superpose eq76 eq84
  have eq86 (X0 X3 : G) : X0 = X3 := superpose eq85 eq85
  have eq91 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq91 eq86


@[equational_result]
theorem Equation19026_implies_Equation2 (G : Type*) [Magma G] (h : Equation19026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X1 ◇ X1)) = (X0 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq11
  have eq13 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq11 eq11
  have eq18 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ (X1 ◇ X1)) := superpose eq12 eq9
  have eq19 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = X0 := superpose eq12 eq7
  have eq20 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq12 eq18
  have eq22 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq12 eq13
  have eq23 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq19 eq22
  have eq26 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq23 eq20
  have eq27 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq23 eq12
  have eq28 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq23 eq11
  have eq30 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq23 eq26
  have eq31 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := superpose eq23 eq30
  have eq32 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq23 eq31
  have eq33 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq23 eq27
  have eq41 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq28 eq33
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq41 eq32
  have eq51 (X0 X2 : G) : X0 = X2 := superpose eq49 eq49
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq59 eq51


@[equational_result]
theorem Equation19028_implies_Equation2 (G : Type*) [Magma G] (h : Equation19028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq12
  have eq15 (X0 X4 : G) : ((X0 ◇ X4) ◇ X0) = X4 := superpose eq7 eq12
  have eq25 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ ((X4 ◇ X0) ◇ (X1 ◇ X2))) = X3 := superpose eq12 eq11
  have eq47 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq15 eq15
  have eq54 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X1 ◇ X3)) = X1 := superpose eq47 eq13
  have eq65 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = X1 := superpose eq15 eq54
  have eq73 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X1) = X3 := superpose eq65 eq25
  have eq75 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq73 eq12
  have eq84 (X0 X2 : G) : X0 = X2 := superpose eq54 eq75
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq84 eq8
  subsumption eq108 eq84


@[equational_result]
theorem Equation19030_implies_Equation2 (G : Type*) [Magma G] (h : Equation19030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X2 ◇ X1)) = (X0 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X3) ◇ (X0 ◇ X0)) = X3 := superpose eq7 eq7
  have eq36 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = X0 := superpose eq10 eq9
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq36 eq36
  have eq125 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq125 eq57


@[equational_result]
theorem Equation19032_implies_Equation2 (G : Type*) [Magma G] (h : Equation19032 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ (X2 ◇ X3)) = (X0 ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X4 ◇ X5))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ (X2 ◇ X3)) = (X0 ◇ (((X4 ◇ X5) ◇ (X1 ◇ X0)) ◇ X5)) := superpose eq7 eq11
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (((X4 ◇ X5) ◇ (X1 ◇ X0)) ◇ X5)) = (((X2 ◇ X3) ◇ X1) ◇ X3) := superpose eq11 eq11
  have eq16 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ (X1 ◇ X3)) ◇ X4) ◇ (X0 ◇ X0)) = X4 := superpose eq7 eq11
  have eq75 (X0 X1 X2 X3 X4 X5 X6 : G) : ((((X3 ◇ X4) ◇ (X3 ◇ X5)) ◇ X6) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X6 := superpose eq16 eq16
  have eq76 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X3))) = X2 := superpose eq9 eq16
  have eq94 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X2 ◇ X3)) = X1 := superpose eq76 eq9
  have eq118 (X0 X1 X4 X5 : G) : (X0 ◇ (((X4 ◇ X5) ◇ (X1 ◇ X0)) ◇ X5)) = X1 := superpose eq94 eq12
  have eq135 (X1 X3 X4 X5 X6 : G) : ((((X3 ◇ X4) ◇ (X3 ◇ X5)) ◇ X6) ◇ X1) = X6 := superpose eq94 eq75
  have eq139 (X1 X2 X3 : G) : (((X2 ◇ X3) ◇ X1) ◇ X3) = X1 := superpose eq118 eq13
  have eq163 (X1 X4 X6 : G) : ((X4 ◇ X6) ◇ X1) = X6 := superpose eq94 eq135
  have eq165 (X1 X3 : G) : (X3 ◇ X3) = X1 := superpose eq163 eq139
  have eq170 (X0 X2 : G) : X0 = X2 := superpose eq165 eq165
  have eq187 (X0 : G) : sK0 ≠ X0 := superpose eq170 eq8
  subsumption eq187 eq170


@[equational_result]
theorem Equation19034_implies_Equation2 (G : Type*) [Magma G] (h : Equation19034 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ (X3 ◇ X1)) = (X0 ◇ ((X4 ◇ (X1 ◇ X0)) ◇ (X5 ◇ (X1 ◇ X0)))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X3 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq12
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X2) ◇ X0)) := superpose eq12 eq12
  have eq15 (X0 X4 : G) : ((X0 ◇ X4) ◇ X0) = X4 := superpose eq7 eq12
  have eq20 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = (X0 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X4 ◇ ((X1 ◇ X2) ◇ X0)))) := superpose eq12 eq7
  have eq21 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ ((X6 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X1)) ◇ X5)) ◇ (X7 ◇ (((X2 ◇ X1) ◇ (X3 ◇ X1)) ◇ X5)))) = (X0 ◇ (X4 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1)))) := superpose eq7 eq9
  have eq23 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X5 ◇ ((X1 ◇ X2) ◇ X4)) ◇ (X6 ◇ ((X1 ◇ X2) ◇ X4)))) = (X0 ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq12 eq9
  have eq25 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ ((X6 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X3)) ◇ X5)) ◇ (X7 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X3)) ◇ X5)))) = ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) ◇ X0) := superpose eq7 eq9
  have eq27 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ ((X5 ◇ ((X2 ◇ X3) ◇ X4)) ◇ (X6 ◇ ((X2 ◇ X3) ◇ X4)))) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := superpose eq12 eq9
  have eq31 (X0 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ (X4 ◇ (X0 ◇ X2)))) = X0 := superpose eq12 eq9
  have eq35 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : ((X3 ◇ (X4 ◇ (X1 ◇ X5))) ◇ (X6 ◇ (X4 ◇ (X1 ◇ X5)))) = ((X7 ◇ (X1 ◇ X5)) ◇ (((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X8 ◇ ((X4 ◇ (X1 ◇ X5)) ◇ (X7 ◇ (X1 ◇ X5)))))) := superpose eq9 eq9
  have eq61 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X1) ◇ (X3 ◇ X1)) = (X0 ◇ (X4 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1)))) := superpose eq20 eq21
  have eq64 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ (X3 ◇ (X1 ◇ X2))) := superpose eq20 eq23
  have eq68 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X3 ◇ X1)) = (X0 ◇ (X3 ◇ X1)) := superpose eq64 eq61
  have eq73 (X0 X2 X3 X4 X5 X6 X7 : G) : (X5 ◇ ((X6 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X3)) ◇ X5)) ◇ (X7 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X3)) ◇ X5)))) = ((X4 ◇ X3) ◇ X0) := superpose eq64 eq25
  have eq74 (X0 X2 X3 X4 X5 : G) : ((X4 ◇ X3) ◇ X0) = (X5 ◇ (((X2 ◇ X3) ◇ (X4 ◇ X3)) ◇ X5)) := superpose eq64 eq73
  have eq78 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = (X4 ◇ ((X2 ◇ X3) ◇ X4)) := superpose eq64 eq27
  have eq79 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := superpose eq14 eq78
  have eq81 (X0 X3 X4 X5 : G) : ((X4 ◇ X3) ◇ X0) = (X5 ◇ (X4 ◇ X3)) := superpose eq79 eq74
  have eq88 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = X0 := superpose eq79 eq31
  have eq90 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X3 ◇ X1)) = X1 := superpose eq88 eq13
  have eq91 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X1 := superpose eq90 eq68
  have eq96 (X0 X3 X4 : G) : ((X4 ◇ X3) ◇ X0) = X3 := superpose eq91 eq81
  have eq107 (X1 X3 X4 X5 X6 : G) : (X1 ◇ X5) = ((X3 ◇ (X4 ◇ (X1 ◇ X5))) ◇ (X6 ◇ (X4 ◇ (X1 ◇ X5)))) := superpose eq96 eq35
  have eq108 (X1 X3 X4 X5 : G) : (X1 ◇ X5) = ((X3 ◇ (X4 ◇ (X1 ◇ X5))) ◇ (X1 ◇ X5)) := superpose eq91 eq107
  have eq109 (X1 X5 : G) : (X1 ◇ X5) = X5 := superpose eq91 eq108
  have eq110 (X0 X4 : G) : (X4 ◇ X0) = X4 := superpose eq109 eq15
  have eq237 (X0 X1 : G) : X0 = X1 := superpose eq109 eq110
  have eq250 (X0 : G) : sK0 ≠ X0 := superpose eq237 eq8
  subsumption eq250 eq237


@[equational_result]
theorem Equation19035_implies_Equation2 (G : Type*) [Magma G] (h : Equation19035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X1)) ◇ X4) ◇ (X0 ◇ (X5 ◇ (X2 ◇ X0)))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X3 ◇ X2)) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq12
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq12 eq12
  have eq18 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X3 ◇ X2)) = X1 := superpose eq14 eq13
  have eq20 (X0 X2 X4 X5 : G) : ((X2 ◇ X4) ◇ (X0 ◇ (X5 ◇ (X2 ◇ X0)))) = X4 := superpose eq18 eq10
  have eq47 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq14 eq20
  have eq52 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq47 eq12
  have eq53 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq47 eq14
  have eq65 (X0 X1 : G) : X0 = X1 := superpose eq52 eq53
  have eq70 (X0 : G) : sK0 ≠ X0 := superpose eq65 eq8
  subsumption eq70 eq65


@[equational_result]
theorem Equation19036_implies_Equation2 (G : Type*) [Magma G] (h : Equation19036 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X2) ◇ (X3 ◇ X3)) ◇ X4) ◇ (X0 ◇ (X5 ◇ X5))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X3 ◇ X3)) = (X0 ◇ (X1 ◇ X0)) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq11 eq11
  have eq17 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X3 ◇ X3)) = X1 := superpose eq13 eq12
  have eq18 (X0 X2 X4 X5 : G) : ((X2 ◇ X4) ◇ (X0 ◇ (X5 ◇ X5))) = X4 := superpose eq17 eq10
  have eq31 (X0 X1 : G) : X0 = X1 := superpose eq18 eq13
  have eq46 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq46 eq31


@[equational_result]
theorem Equation19037_implies_Equation2 (G : Type*) [Magma G] (h : Equation19037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X1) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq12 eq12
  have eq25 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = X1 := superpose eq12 eq11
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ X3) = (X0 ◇ ((X4 ◇ (X1 ◇ X0)) ◇ X5)) := superpose eq11 eq11
  have eq32 (X1 X2 X3 : G) : ((X2 ◇ X1) ◇ X3) = X1 := superpose eq25 eq26
  have eq40 (X0 X2 : G) : X0 = X2 := superpose eq14 eq32
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq44 eq40


@[equational_result]
theorem Equation19039_implies_Equation2 (G : Type*) [Magma G] (h : Equation19039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) ◇ ((X3 ◇ X3) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq11
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := superpose eq11 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) := superpose eq11 eq7
  have eq16 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))))) = X1 := superpose eq11 eq7
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : (((X2 ◇ X2) ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = ((((X4 ◇ X4) ◇ (X0 ◇ X1)) ◇ (((X2 ◇ X2) ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) ◇ ((X5 ◇ X5) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) := superpose eq10 eq10
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X0) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq11 eq10
  have eq23 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ X3) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) ◇ X0) ◇ ((X4 ◇ X4) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1)))) = X0 := superpose eq7 eq10
  have eq26 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq10 eq10
  have eq32 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq12 eq26
  have eq33 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq32
  have eq34 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X2) ◇ X0)) := superpose eq33 eq22
  have eq35 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq33 eq14
  have eq38 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) ◇ (X3 ◇ X0)) := superpose eq33 eq10
  have eq41 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq33 eq15
  have eq42 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))))) = X1 := superpose eq33 eq16
  have eq45 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = ((((X4 ◇ X4) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) ◇ ((X5 ◇ X5) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) := superpose eq33 eq20
  have eq46 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ X3) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) ◇ X0) ◇ ((X4 ◇ X4) ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := superpose eq33 eq23
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq33 eq34
  have eq50 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X2 ◇ X0)) := superpose eq35 eq49
  have eq55 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((((X1 ◇ X1) ◇ (X0 ◇ X2)) ◇ X0) ◇ (X3 ◇ X0)) := superpose eq50 eq38
  have eq56 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((((X1 ◇ X1) ◇ X2) ◇ X0) ◇ (X3 ◇ X0)) := superpose eq50 eq55
  have eq57 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X0)) := superpose eq33 eq56
  have eq60 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) ◇ (X2 ◇ X0)) := superpose eq50 eq41
  have eq61 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq50 eq60
  have eq62 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq50 eq61
  have eq63 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := superpose eq50 eq62
  have eq64 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq33 eq63
  have eq65 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq33 eq64
  have eq66 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) = X1 := superpose eq50 eq42
  have eq67 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) = X1 := superpose eq50 eq66
  have eq68 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X0)) = X1 := superpose eq50 eq67
  have eq69 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = X1 := superpose eq33 eq68
  have eq89 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = ((((X4 ◇ X4) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) ◇ ((X5 ◇ X5) ◇ (X0 ◇ X1))) := superpose eq50 eq45
  have eq90 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = ((((X4 ◇ X4) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) ◇ ((X5 ◇ X5) ◇ X1)) := superpose eq50 eq89
  have eq91 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = ((((X4 ◇ X4) ◇ (X0 ◇ X1)) ◇ ((X2 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)))) ◇ (X5 ◇ X1)) := superpose eq33 eq90
  have eq92 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = ((((X4 ◇ X4) ◇ (X0 ◇ X1)) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) ◇ (X5 ◇ X1)) := superpose eq50 eq91
  have eq93 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = ((((X4 ◇ X4) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X5 ◇ X1)) := superpose eq50 eq92
  have eq94 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = ((((X4 ◇ X4) ◇ (X0 ◇ X1)) ◇ X1) ◇ (X5 ◇ X1)) := superpose eq50 eq93
  have eq95 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ X1) := superpose eq57 eq94
  have eq96 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := superpose eq65 eq95
  have eq97 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq50 eq96
  have eq98 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ X1) ◇ (((X3 ◇ X3) ◇ X0) ◇ X1)) := superpose eq50 eq97
  have eq99 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = ((X2 ◇ X1) ◇ ((X3 ◇ X0) ◇ X1)) := superpose eq33 eq98
  have eq100 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ X3) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) ◇ X0) ◇ ((X4 ◇ X4) ◇ (X0 ◇ X1))) = X0 := superpose eq50 eq46
  have eq101 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ X3) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) ◇ X0) ◇ ((X4 ◇ X4) ◇ X1)) = X0 := superpose eq50 eq100
  have eq102 (X0 X1 X2 X3 X4 : G) : ((((X3 ◇ X3) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) ◇ X0) ◇ (X4 ◇ X1)) = X0 := superpose eq33 eq101
  have eq103 (X0 X1 X3 X4 : G) : ((((X3 ◇ X3) ◇ (X1 ◇ X0)) ◇ X0) ◇ (X4 ◇ X1)) = X0 := superpose eq50 eq102
  have eq104 (X0 X1 X3 X4 : G) : ((((X3 ◇ X3) ◇ X0) ◇ X0) ◇ (X4 ◇ X1)) = X0 := superpose eq50 eq103
  have eq105 (X0 X1 X3 X4 : G) : (((X3 ◇ X3) ◇ X0) ◇ (X4 ◇ X1)) = X0 := superpose eq65 eq104
  have eq106 (X0 X1 X3 X4 : G) : ((X3 ◇ X0) ◇ (X4 ◇ X1)) = X0 := superpose eq33 eq105
  have eq107 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq106 eq99
  have eq115 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq107 eq69
  have eq148 (X0 X2 : G) : X0 = X2 := superpose eq115 eq115
  have eq162 (X0 : G) : sK0 ≠ X0 := superpose eq148 eq8
  subsumption eq162 eq148


@[equational_result]
theorem Equation19040_implies_Equation2 (G : Type*) [Magma G] (h : Equation19040 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X2)) = (X0 ◇ ((X3 ◇ X3) ◇ (((X2 ◇ X2) ◇ (X0 ◇ X2)) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((((X3 ◇ X3) ◇ (X0 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X3))) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ ((((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2))) ◇ (X0 ◇ X1))) := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ ((((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X3)) ◇ ((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X3))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X1 := superpose eq9 eq7
  have eq22 (X0 X1 X2 X4 : G) : ((((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2))) ◇ X1) = ((X0 ◇ X1) ◇ ((((X4 ◇ X4) ◇ (X1 ◇ X4)) ◇ ((X4 ◇ X4) ◇ (X1 ◇ X4))) ◇ X1)) := superpose eq10 eq10
  have eq37 (X0 X1 X2 X3 X4 : G) : ((((((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2))) ◇ X1) ◇ ((((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2))) ◇ X1)) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((((X4 ◇ X4) ◇ ((X0 ◇ X1) ◇ X4)) ◇ ((X4 ◇ X4) ◇ ((X0 ◇ X1) ◇ X4))) ◇ (X0 ◇ X1))) := superpose eq10 eq13
  have eq51 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3)))) ◇ ((((X5 ◇ X5) ◇ ((((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3))) ◇ X5)) ◇ ((X5 ◇ X5) ◇ ((((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3))) ◇ X5))) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3))))) = ((((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2))) ◇ X1))) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2))) ◇ X1)))) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3)))) := superpose eq22 eq22
  have eq73 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X1) = ((X4 ◇ (X3 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((((X2 ◇ X2) ◇ (X1 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2))) ◇ X1))) := superpose eq22 eq10
  have eq81 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ X1)) := superpose eq22 eq9
  have eq151 (X0 X1 X2 X3 : G) : (((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = ((X2 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) ◇ ((((X3 ◇ X3) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ X3)) ◇ ((X3 ◇ X3) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ X3))) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))))) := superpose eq73 eq22
  have eq207 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq73 eq15
  have eq221 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := superpose eq13 eq15
  have eq243 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq221 eq207
  have eq246 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ X1)) = X1 := superpose eq221 eq81
  have eq259 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X2 ◇ X0) ◇ ((((X3 ◇ X3) ◇ (X0 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X3))) ◇ X0))) := superpose eq243 eq73
  have eq260 (X0 X2 : G) : ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((((X2 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) := superpose eq243 eq10
  have eq269 (X0 X1 X3 : G) : ((((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ X0) ◇ X3)) ◇ ((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ X0) ◇ X3))) ◇ ((X0 ◇ X0) ◇ X0))) := superpose eq243 eq22
  have eq276 (X1 X3 X4 X5 : G) : ((X4 ◇ (((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3)))) ◇ ((((X5 ◇ X5) ◇ ((((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3))) ◇ X5)) ◇ ((X5 ◇ X5) ◇ ((((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3))) ◇ X5))) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3))))) = ((((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3)))) := superpose eq259 eq51
  have eq292 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq246 eq260
  have eq299 (X1 X3 X4 X5 : G) : ((X4 ◇ (((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3)))) ◇ ((((X5 ◇ X5) ◇ ((((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3))) ◇ X5)) ◇ ((X5 ◇ X5) ◇ ((((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3))) ◇ X5))) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3))))) = ((X1 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3)))) := superpose eq292 eq276
  have eq314 (X0 X1 : G) : (((((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) ◇ X1) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq299 eq151
  have eq339 (X0 X1 : G) : ((((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ X0) ◇ X1))) ◇ ((X0 ◇ X0) ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq13 eq269
  have eq340 (X0 X1 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq292 eq339
  have eq341 (X0 X1 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) ◇ X0) = X0 := superpose eq292 eq340
  have eq342 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X0) := superpose eq341 eq10
  have eq345 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ ((((X4 ◇ X4) ◇ (X1 ◇ X4)) ◇ ((X4 ◇ X4) ◇ (X1 ◇ X4))) ◇ X1)) = X1 := superpose eq341 eq22
  have eq351 (X0 X1 X3 X4 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((((X4 ◇ X4) ◇ ((X0 ◇ X1) ◇ X4)) ◇ ((X4 ◇ X4) ◇ ((X0 ◇ X1) ◇ X4))) ◇ (X0 ◇ X1))) := superpose eq341 eq37
  have eq424 (X0 X1 : G) : ((X1 ◇ X1) ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = (X1 ◇ (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) := superpose eq341 eq314
  have eq465 (X1 X3 X4 : G) : ((X1 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3)))) = ((X4 ◇ (((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3)))) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3)))) := superpose eq341 eq299
  have eq467 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = X1 := superpose eq341 eq345
  have eq468 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := superpose eq341 eq351
  have eq469 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq467 eq468
  have eq470 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X2)) = X0 := superpose eq469 eq7
  have eq471 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X2) ◇ X3))) := superpose eq469 eq9
  have eq485 (X0 X2 X3 : G) : (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X2) ◇ X3)) := superpose eq469 eq471
  have eq717 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq469 eq424
  have eq718 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq485 eq717
  have eq844 (X1 X3 : G) : (((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3))) = ((X1 ◇ X1) ◇ (((X3 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3)))) := superpose eq467 eq465
  have eq845 (X1 X3 : G) : ((X1 ◇ X3) ◇ (X1 ◇ X3)) = ((X1 ◇ X1) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) := superpose eq469 eq844
  have eq846 (X1 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X3) ◇ (X1 ◇ X3)) := superpose eq718 eq845
  have eq848 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X0)) := superpose eq846 eq718
  have eq852 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq470 eq848
  have eq854 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq852 eq342
  have eq866 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq852 eq854
  have eq867 (X0 X3 : G) : X0 = X3 := superpose eq866 eq866
  have eq869 (X0 : G) : sK0 ≠ X0 := superpose eq867 eq8
  subsumption eq869 eq867


@[equational_result]
theorem Equation19041_implies_Equation2 (G : Type*) [Magma G] (h : Equation19041 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ (X2 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ X2) := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq11 eq7
  have eq19 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq15 eq13
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = X0 := superpose eq19 eq7
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq19 eq22
  have eq29 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq19 eq28
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq29 eq29
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq32 eq30


@[equational_result]
theorem Equation19043_implies_Equation2 (G : Type*) [Magma G] (h : Equation19043 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq7 eq12
  have eq21 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq15 eq7
  have eq34 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq21 eq15
  have eq45 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq34 eq12
  have eq48 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq45 eq21
  have eq54 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq45 eq48
  have eq59 (X0 X2 : G) : X0 = X2 := superpose eq54 eq54
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq61 eq59


@[equational_result]
theorem Equation19045_implies_Equation2 (G : Type*) [Magma G] (h : Equation19045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (((X0 ◇ X0) ◇ X1) ◇ (X2 ◇ X4))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X3) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq13 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = X3 := superpose eq12 eq10
  have eq16 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ X0)) = X2 := superpose eq13 eq11
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq16
  have eq19 (X0 X3 : G) : X0 = X3 := superpose eq18 eq18
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq27 eq19


@[equational_result]
theorem Equation19048_implies_Equation2 (G : Type*) [Magma G] (h : Equation19048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X0 := superpose eq11 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq13
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation19049_implies_Equation2 (G : Type*) [Magma G] (h : Equation19049 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X4))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq12
  have eq21 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = X3 := superpose eq15 eq10
  have eq27 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq21 eq21
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq12 eq27
  have eq80 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq80 eq30


@[equational_result]
theorem Equation19051_implies_Equation2 (G : Type*) [Magma G] (h : Equation19051 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq12 eq12
  have eq21 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq14 eq12
  have eq27 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation19052_implies_Equation2 (G : Type*) [Magma G] (h : Equation19052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ (X4 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq14 (X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X1) = X3 := superpose eq12 eq10
  have eq18 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq14 eq14
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq14 eq18
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq74 eq24


@[equational_result]
theorem Equation19053_implies_Equation2 (G : Type*) [Magma G] (h : Equation19053 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq49 eq32


@[equational_result]
theorem Equation19054_implies_Equation2 (G : Type*) [Magma G] (h : Equation19054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq51 eq34


@[equational_result]
theorem Equation19056_implies_Equation2 (G : Type*) [Magma G] (h : Equation19056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = ((((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X3 ◇ X0)) ◇ (X4 ◇ X0)) := superpose eq7 eq10
  have eq18 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq29 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X1 ◇ X2) ◇ (X0 ◇ X3)) := superpose eq7 eq12
  have eq32 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq12 eq7
  have eq40 (X0 X3 X4 : G) : (X3 ◇ X0) = (((X0 ◇ X3) ◇ (X3 ◇ X0)) ◇ (X4 ◇ X0)) := superpose eq29 eq15
  have eq42 (X0 X2 X3 : G) : (X2 ◇ X3) = ((X2 ◇ X3) ◇ X0) := superpose eq29 eq12
  have eq49 (X0 X3 X4 : G) : (X3 ◇ X0) = ((X3 ◇ X0) ◇ (X4 ◇ X0)) := superpose eq29 eq40
  have eq51 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq42 eq18
  have eq59 (X0 X3 : G) : (X3 ◇ X0) = X0 := superpose eq32 eq49
  have eq65 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq59 eq51
  have eq69 (X0 X3 : G) : X0 = X3 := superpose eq65 eq65
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq74 eq69


@[equational_result]
theorem Equation19057_implies_Equation2 (G : Type*) [Magma G] (h : Equation19057 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X4 X5 : G) : ((X4 ◇ X0) ◇ X5) = X0 := superpose eq7 eq12
  have eq46 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq86 (X0 X4 : G) : X0 = X4 := superpose eq10 eq46
  have eq167 (X0 : G) : sK0 ≠ X0 := superpose eq86 eq8
  subsumption eq167 eq86


@[equational_result]
theorem Equation19058_implies_Equation2 (G : Type*) [Magma G] (h : Equation19058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X3)) = (X0 ◇ ((X4 ◇ X5) ◇ (((X2 ◇ X3) ◇ (X0 ◇ X3)) ◇ X5))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ ((X4 ◇ X5) ◇ (X0 ◇ X5))))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ ((X3 ◇ ((X4 ◇ X5) ◇ (X0 ◇ X5))) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X2 X3 X4 X5 X6 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X3)) = (X0 ◇ (X4 ◇ (((X2 ◇ X3) ◇ (X0 ◇ X3)) ◇ ((X5 ◇ X6) ◇ (X4 ◇ X6))))) := superpose eq7 eq10
  have eq18 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq22 (X0 X2 X3 X4 X5 X6 : G) : (X2 ◇ (X0 ◇ ((X3 ◇ X4) ◇ (X2 ◇ X4)))) = (X0 ◇ ((X5 ◇ X6) ◇ ((X2 ◇ (X0 ◇ ((X3 ◇ X4) ◇ (X2 ◇ X4)))) ◇ X6))) := superpose eq10 eq7
  have eq33 (X0 X1 X2 X3 X4 X5 X6 X7 X8 : G) : (X1 ◇ (X2 ◇ X0)) = ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X4 ◇ ((X5 ◇ (X6 ◇ (X0 ◇ ((X7 ◇ X8) ◇ (X6 ◇ X8))))) ◇ X0)) ◇ (X2 ◇ X0))) := superpose eq10 eq11
  have eq49 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq18 eq18
  have eq96 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X4) ◇ (X2 ◇ X4))))) ◇ X0) = ((X5 ◇ X0) ◇ ((X6 ◇ X7) ◇ (((X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X4) ◇ (X2 ◇ X4))))) ◇ X0) ◇ X7))) := superpose eq10 eq9
  have eq101 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1))) := superpose eq18 eq9
  have eq125 (X0 X2 X3 : G) : (X0 ◇ X0) = (X0 ◇ ((X2 ◇ X3) ◇ ((X0 ◇ X0) ◇ X3))) := superpose eq49 eq9
  have eq127 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq49 eq7
  have eq145 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq127 eq49
  have eq159 (X0 X1 X2 X3 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ ((X3 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq145 eq101
  have eq160 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) = X0 := superpose eq145 eq125
  have eq175 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq160 eq159
  have eq176 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq175 eq7
  have eq179 (X0 X4 X5 X6 : G) : (X0 ◇ (X4 ◇ (X0 ◇ ((X5 ◇ X6) ◇ (X4 ◇ X6))))) = X0 := superpose eq175 eq12
  have eq185 (X0 X2 X5 X6 : G) : (X2 ◇ (X0 ◇ X2)) = (X0 ◇ ((X5 ◇ X6) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X6))) := superpose eq175 eq22
  have eq187 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ (X2 ◇ X0)) = ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X4 ◇ ((X5 ◇ (X6 ◇ (X0 ◇ X6))) ◇ X0)) ◇ (X2 ◇ X0))) := superpose eq175 eq33
  have eq190 (X0 X1 X2 X5 X6 X7 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0) = ((X5 ◇ X0) ◇ ((X6 ◇ X7) ◇ (((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0) ◇ X7))) := superpose eq175 eq96
  have eq200 (X0 X4 : G) : (X0 ◇ (X4 ◇ (X0 ◇ X4))) = X0 := superpose eq175 eq179
  have eq202 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq175 eq185
  have eq203 (X0 X2 : G) : (X2 ◇ (X0 ◇ X2)) = X0 := superpose eq200 eq202
  have eq221 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ (X2 ◇ X0)) = ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X4 ◇ ((X5 ◇ X0) ◇ X0)) ◇ (X2 ◇ X0))) := superpose eq203 eq187
  have eq222 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X2 ◇ X0)) = ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X4 ◇ X0) ◇ (X2 ◇ X0))) := superpose eq176 eq221
  have eq223 (X0 X1 X2 X3 : G) : (X1 ◇ (X2 ◇ X0)) = ((X3 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X2) := superpose eq175 eq222
  have eq230 (X0 X1 X2 X5 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0) = ((X5 ◇ X0) ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0)) := superpose eq175 eq190
  have eq231 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0) := superpose eq175 eq230
  have eq232 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := superpose eq223 eq231
  have eq233 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq203 eq232
  have eq240 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((X3 ◇ (X1 ◇ X0)) ◇ X2) := superpose eq233 eq223
  have eq246 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X2) := superpose eq233 eq240
  have eq247 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq233 eq246
  have eq254 (X0 X1 : G) : X0 = X1 := superpose eq233 eq247
  have eq264 (X0 : G) : sK0 ≠ X0 := superpose eq254 eq8
  subsumption eq264 eq254


@[equational_result]
theorem Equation19059_implies_Equation2 (G : Type*) [Magma G] (h : Equation19059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X7))) = X2 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq39 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq19 eq19
  have eq83 (X0 X4 : G) : X0 = X4 := superpose eq10 eq39
  have eq171 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq171 eq83


@[equational_result]
theorem Equation19061_implies_Equation2 (G : Type*) [Magma G] (h : Equation19061 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq12 eq12
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq14 eq12
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation19062_implies_Equation2 (G : Type*) [Magma G] (h : Equation19062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ (X1 ◇ X2)) = (X0 ◇ ((X4 ◇ X5) ◇ ((X1 ◇ X0) ◇ X4))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X3 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((((X3 ◇ X4) ◇ (X1 ◇ X3)) ◇ X5) ◇ X0)) = X2 := superpose eq7 eq7
  have eq53 (X0 X1 X2 X3 X4 X5 : G) : (((X3 ◇ X4) ◇ X5) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) = X5 := superpose eq9 eq10
  have eq54 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ (((X2 ◇ X3) ◇ X5) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0)))) = X4 := superpose eq9 eq10
  have eq61 (X3 X4 X5 : G) : ((X3 ◇ X4) ◇ X5) = X4 := superpose eq53 eq54
  have eq63 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X3 ◇ X4) ◇ (X1 ◇ X3)) ◇ X5) ◇ X0)) = X2 := superpose eq61 eq11
  have eq98 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq61 eq63
  have eq99 (X0 X4 : G) : X0 = X4 := superpose eq10 eq98
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq99 eq8
  subsumption eq112 eq99


@[equational_result]
theorem Equation19063_implies_Equation2 (G : Type*) [Magma G] (h : Equation19063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X2 ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq12 eq7
  have eq23 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq19 eq12
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq36 eq34


@[equational_result]
theorem Equation19064_implies_Equation2 (G : Type*) [Magma G] (h : Equation19064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq21 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq13 eq12
  have eq25 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq27 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq27 eq25


@[equational_result]
theorem Equation19066_implies_Equation2 (G : Type*) [Magma G] (h : Equation19066 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : ((X0 ◇ X2) ◇ X3) = X2 := superpose eq7 eq12
  have eq26 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq15 eq12
  have eq32 (X0 X4 : G) : X0 = X4 := superpose eq26 eq26
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq34 eq32


@[equational_result]
theorem Equation19067_implies_Equation2 (G : Type*) [Magma G] (h : Equation19067 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq51 eq34


@[equational_result]
theorem Equation19068_implies_Equation2 (G : Type*) [Magma G] (h : Equation19068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq13 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq11 eq7
  have eq14 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq13
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq13 eq14
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq22 eq15


@[equational_result]
theorem Equation19069_implies_Equation2 (G : Type*) [Magma G] (h : Equation19069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq34 (X0 X3 : G) : X0 = X3 := superpose eq12 eq17
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq51 eq34


@[equational_result]
theorem Equation19071_implies_Equation2 (G : Type*) [Magma G] (h : Equation19071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq17 (X0 X1 X2 X3 X4 X5 : G) : (((((X1 ◇ X2) ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) ◇ X0) = X5 := superpose eq7 eq12
  have eq18 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X2) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq12 eq12
  have eq23 (X0 X4 X5 : G) : (X4 ◇ X0) = X5 := superpose eq18 eq17
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq23
  have eq170 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq170 eq49


@[equational_result]
theorem Equation19072_implies_Equation2 (G : Type*) [Magma G] (h : Equation19072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq12 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq16 eq16
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq16 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation19073_implies_Equation2 (G : Type*) [Magma G] (h : Equation19073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq12 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq15 eq16
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq24 eq17


@[equational_result]
theorem Equation19074_implies_Equation2 (G : Type*) [Magma G] (h : Equation19074 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq12 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq15 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation19076_implies_Equation2 (G : Type*) [Magma G] (h : Equation19076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq7
  have eq14 (X0 X5 X6 : G) : ((X0 ◇ X5) ◇ X6) = X5 := superpose eq7 eq12
  have eq23 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq14 eq12
  have eq26 (X0 X3 : G) : X0 = X3 := superpose eq23 eq23
  have eq28 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq28 eq26


@[equational_result]
theorem Equation19077_implies_Equation2 (G : Type*) [Magma G] (h : Equation19077 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq12 eq16
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq83 eq33


@[equational_result]
theorem Equation19078_implies_Equation2 (G : Type*) [Magma G] (h : Equation19078 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X3) = X0 := superpose eq12 eq7
  have eq17 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq16 eq16
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq16 eq17
  have eq25 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq25 eq18


@[equational_result]
theorem Equation19079_implies_Equation2 (G : Type*) [Magma G] (h : Equation19079 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq23 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq23 eq8
  subsumption eq77 eq23


@[equational_result]
theorem Equation19080_implies_Equation2 (G : Type*) [Magma G] (h : Equation19080 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq24 (X0 X3 : G) : X0 = X3 := superpose eq12 eq16
  have eq78 (X0 : G) : sK0 ≠ X0 := superpose eq24 eq8
  subsumption eq78 eq24


@[equational_result]
theorem Equation19083_implies_Equation2 (G : Type*) [Magma G] (h : Equation19083 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose eq12 eq9
  have eq32 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq9 eq9
  have eq48 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq32 eq31
  have eq50 (X0 X3 : G) : X0 = X3 := superpose eq7 eq48
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq50 eq8
  subsumption eq120 eq50


@[equational_result]
theorem Equation19086_implies_Equation2 (G : Type*) [Magma G] (h : Equation19086 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X2 : G) : X0 = X2 := superpose eq10 eq10
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq41 eq13


@[equational_result]
theorem Equation19088_implies_Equation2 (G : Type*) [Magma G] (h : Equation19088 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 : G) : X0 = X2 := superpose eq7 eq10
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq37 eq14


@[equational_result]
theorem Equation19089_implies_Equation2 (G : Type*) [Magma G] (h : Equation19089 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19090_implies_Equation2 (G : Type*) [Magma G] (h : Equation19090 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19093_implies_Equation2 (G : Type*) [Magma G] (h : Equation19093 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X1) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq13
  have eq94 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq94 eq8
  subsumption eq133 eq94


@[equational_result]
theorem Equation19096_implies_Equation2 (G : Type*) [Magma G] (h : Equation19096 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X0)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X1)) := superpose eq7 eq10
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq13 eq11
  have eq18 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq17 eq13
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq18
  have eq71 (X0 X2 : G) : X0 = X2 := superpose eq35 eq35
  have eq132 (X0 : G) : sK0 ≠ X0 := superpose eq71 eq8
  subsumption eq132 eq71


@[equational_result]
theorem Equation19098_implies_Equation2 (G : Type*) [Magma G] (h : Equation19098 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ ((X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X1))) ◇ X0)) = X3 := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X1) = ((((((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) ◇ (X2 ◇ X1)) ◇ ((((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ X1) ◇ (X2 ◇ X1))) ◇ X0) := superpose eq7 eq9
  have eq55 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq10 eq25
  have eq106 (X0 X2 : G) : X0 = X2 := superpose eq55 eq55
  have eq189 (X0 : G) : sK0 ≠ X0 := superpose eq106 eq8
  subsumption eq189 eq106


@[equational_result]
theorem Equation19099_implies_Equation2 (G : Type*) [Magma G] (h : Equation19099 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq10 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = (((X0 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X3 ◇ X3))) ◇ ((X1 ◇ X1) ◇ (X4 ◇ X4))) := superpose eq7 eq9
  have eq14 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq10 eq9
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) = ((((X0 ◇ X0) ◇ (X4 ◇ X4)) ◇ ((X0 ◇ X0) ◇ (X4 ◇ X4))) ◇ ((((X1 ◇ X0) ◇ (X3 ◇ X3)) ◇ ((X1 ◇ X0) ◇ (X3 ◇ X3))) ◇ (X5 ◇ X5))) := superpose eq9 eq9
  have eq18 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) := superpose eq9 eq9
  have eq24 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1))) := superpose eq12 eq12
  have eq26 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq7 eq12
  have eq41 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq24
  have eq42 (X0 X1 X2 X3 : G) : ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) ◇ (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2))) = ((X0 ◇ X0) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) := superpose eq41 eq18
  have eq43 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq41 eq26
  have eq44 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq10 eq43
  have eq45 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) := superpose eq44 eq14
  have eq46 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = ((X0 ◇ (X3 ◇ X3)) ◇ ((X1 ◇ X1) ◇ (X4 ◇ X4))) := superpose eq44 eq13
  have eq47 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) = ((((X0 ◇ X0) ◇ (X4 ◇ X4)) ◇ ((X0 ◇ X0) ◇ (X4 ◇ X4))) ◇ (((X1 ◇ X0) ◇ (X3 ◇ X3)) ◇ (X5 ◇ X5))) := superpose eq44 eq15
  have eq49 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) = ((X0 ◇ X0) ◇ ((((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) := superpose eq44 eq42
  have eq57 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq44 eq45
  have eq58 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) = X0 := superpose eq44 eq57
  have eq59 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X2)) = X0 := superpose eq44 eq58
  have eq60 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = ((X0 ◇ (X3 ◇ X3)) ◇ ((X1 ◇ X1) ◇ X4)) := superpose eq44 eq46
  have eq61 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = ((X0 ◇ (X3 ◇ X3)) ◇ (X1 ◇ X4)) := superpose eq44 eq60
  have eq62 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = ((X0 ◇ X3) ◇ (X1 ◇ X4)) := superpose eq44 eq61
  have eq63 (X0 X1 X3 X4 : G) : (X0 ◇ X1) = ((X0 ◇ X3) ◇ (X1 ◇ X4)) := superpose eq59 eq62
  have eq64 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) = ((((X0 ◇ X0) ◇ (X4 ◇ X4)) ◇ ((X0 ◇ X0) ◇ (X4 ◇ X4))) ◇ ((X1 ◇ X0) ◇ X5)) := superpose eq63 eq47
  have eq65 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) = (((X0 ◇ X0) ◇ (X4 ◇ X4)) ◇ ((X1 ◇ X0) ◇ X5)) := superpose eq44 eq64
  have eq66 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X2 ◇ X2))) = ((X0 ◇ X4) ◇ ((X1 ◇ X0) ◇ X5)) := superpose eq63 eq65
  have eq67 (X0 X1 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X1 ◇ X0) ◇ X5)) = X1 := superpose eq59 eq66
  have eq70 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) = ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X3)) := superpose eq63 eq49
  have eq71 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ X0) ◇ (X2 ◇ X2)) := superpose eq67 eq70
  have eq72 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ X0) ◇ X2) := superpose eq44 eq71
  have eq73 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X1 := superpose eq44 eq72
  have eq74 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq73 eq63
  have eq75 (X0 X1 X4 : G) : ((X0 ◇ X4) ◇ X1) = X1 := superpose eq73 eq67
  have eq80 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq74 eq75
  have eq104 (X0 X1 : G) : X0 = X1 := superpose eq74 eq80
  have eq108 (X0 : G) : sK0 ≠ X0 := superpose eq104 eq8
  subsumption eq108 eq104


@[equational_result]
theorem Equation19100_implies_Equation2 (G : Type*) [Magma G] (h : Equation19100 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq31 eq13


@[equational_result]
theorem Equation19102_implies_Equation2 (G : Type*) [Magma G] (h : Equation19102 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq9
  have eq31 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq11 eq14
  have eq39 (X0 X1 : G) : (X0 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := superpose eq31 eq11
  have eq40 (X0 X1 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ (X1 ◇ X1)) = X0 := superpose eq7 eq39
  have eq45 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0))) = X0 := superpose eq39 eq7
  have eq59 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X0))) = X0 := superpose eq14 eq45
  have eq60 (X0 X1 : G) : (X1 ◇ (X1 ◇ X1)) = X0 := superpose eq59 eq40
  have eq172 (X0 X1 : G) : X0 = X1 := superpose eq7 eq60
  have eq298 (X0 : G) : sK0 ≠ X0 := superpose eq172 eq8
  subsumption eq298 eq172


@[equational_result]
theorem Equation19103_implies_Equation2 (G : Type*) [Magma G] (h : Equation19103 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq31 (X0 X1 X2 : G) : (X2 ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose eq11 eq9
  have eq34 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq11 eq9
  have eq45 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq34 eq31
  have eq46 (X0 X3 : G) : X0 = X3 := superpose eq7 eq45
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq126 eq46


@[equational_result]
theorem Equation19104_implies_Equation2 (G : Type*) [Magma G] (h : Equation19104 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X4))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq38 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ X3) ◇ ((X0 ◇ X0) ◇ X1))) = X1 := superpose eq12 eq9
  have eq39 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq9 eq9
  have eq53 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq39 eq38
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq53
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq130 eq57


@[equational_result]
theorem Equation19106_implies_Equation2 (G : Type*) [Magma G] (h : Equation19106 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq18 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq18 eq18
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq85 eq30


@[equational_result]
theorem Equation19107_implies_Equation2 (G : Type*) [Magma G] (h : Equation19107 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X3) ◇ (X2 ◇ X3))))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X3))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 X5 X6 : G) : (X4 ◇ X4) = (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))))) ◇ (X5 ◇ (X3 ◇ ((X5 ◇ X6) ◇ (X4 ◇ X6))))) := superpose eq9 eq9
  have eq20 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))))) ◇ ((X4 ◇ X5) ◇ (X3 ◇ X5))) = X4 := superpose eq9 eq7
  have eq25 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ X2)))))) = X3 := superpose eq9 eq7
  have eq34 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X2 ◇ ((X3 ◇ ((X0 ◇ X4) ◇ (X1 ◇ X4))) ◇ X0)) ◇ X3)) = X2 := superpose eq7 eq10
  have eq35 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) ◇ ((X2 ◇ ((X3 ◇ (X4 ◇ (X1 ◇ ((X4 ◇ X5) ◇ (X0 ◇ X5))))) ◇ (X0 ◇ X0))) ◇ X3)) = X2 := superpose eq9 eq10
  have eq45 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ ((X3 ◇ ((X0 ◇ ((X4 ◇ X5) ◇ (X1 ◇ X5))) ◇ X4)) ◇ X0)))) := superpose eq10 eq9
  have eq49 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ ((X3 ◇ ((X0 ◇ X4) ◇ (X1 ◇ X4))) ◇ X0)) ◇ X3)) = X2 := superpose eq20 eq34
  have eq50 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ ((X3 ◇ (X4 ◇ (X1 ◇ ((X4 ◇ X5) ◇ (X0 ◇ X5))))) ◇ (X0 ◇ X0))) ◇ X3)) = X2 := superpose eq20 eq35
  have eq54 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))))) = ((((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2)))))) ◇ (X4 ◇ X4)) := superpose eq9 eq20
  have eq64 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) := superpose eq20 eq10
  have eq78 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := superpose eq20 eq64
  have eq79 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))))) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X4 ◇ X4)) := superpose eq78 eq54
  have eq82 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))))) := superpose eq20 eq79
  have eq83 (X0 X3 X4 X5 X6 : G) : (X4 ◇ X4) = ((X0 ◇ X0) ◇ (X5 ◇ (X3 ◇ ((X5 ◇ X6) ◇ (X4 ◇ X6))))) := superpose eq82 eq12
  have eq86 (X0 X3 X4 X5 : G) : ((X0 ◇ X0) ◇ ((X4 ◇ X5) ◇ (X3 ◇ X5))) = X4 := superpose eq82 eq22
  have eq92 (X0 X3 : G) : ((X3 ◇ X3) ◇ (X0 ◇ X0)) = X3 := superpose eq82 eq25
  have eq98 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ ((X3 ◇ ((X0 ◇ ((X4 ◇ X5) ◇ (X1 ◇ X5))) ◇ X4)) ◇ X0)))) = X1 := superpose eq86 eq45
  have eq103 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ ((X0 ◇ X3) ◇ (X1 ◇ X3))) ◇ X0)) = X2 := superpose eq92 eq10
  have eq145 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ ((X3 ◇ ((X0 ◇ ((X4 ◇ X5) ◇ (X1 ◇ X5))) ◇ X4)) ◇ X0)))) := superpose eq103 eq9
  have eq155 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq98 eq145
  have eq162 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ ((X0 ◇ X4) ◇ (X1 ◇ X4))) ◇ X0)) ◇ X3)) = X2 := superpose eq155 eq49
  have eq163 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X4 ◇ (X1 ◇ ((X4 ◇ X5) ◇ (X0 ◇ X5))))) ◇ (X0 ◇ X0))) ◇ X3)) = X2 := superpose eq155 eq50
  have eq167 (X0 X3 X4 X5 X6 : G) : (X4 ◇ X4) = (X0 ◇ (X5 ◇ (X3 ◇ ((X5 ◇ X6) ◇ (X4 ◇ X6))))) := superpose eq155 eq83
  have eq208 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ ((X3 ◇ (X4 ◇ (X1 ◇ ((X4 ◇ X5) ◇ (X0 ◇ X5))))) ◇ X0)) ◇ X3)) = X2 := superpose eq155 eq163
  have eq209 (X0 X3 X4 X5 X6 : G) : (X0 ◇ (X5 ◇ (X3 ◇ ((X5 ◇ X6) ◇ (X4 ◇ X6))))) = X4 := superpose eq155 eq167
  have eq210 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = X2 := superpose eq209 eq208
  have eq213 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = X2 := superpose eq155 eq210
  have eq215 (X1 X2 X3 : G) : (X1 ◇ (X3 ◇ X3)) = X2 := superpose eq213 eq162
  have eq223 (X1 X2 X3 : G) : (X1 ◇ X3) = X2 := superpose eq155 eq215
  have eq229 (X0 X1 : G) : X0 = X1 := superpose eq155 eq223
  have eq263 (X0 : G) : sK0 ≠ X0 := superpose eq229 eq8
  subsumption eq263 eq229


@[equational_result]
theorem Equation19108_implies_Equation2 (G : Type*) [Magma G] (h : Equation19108 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq54 eq16


@[equational_result]
theorem Equation19111_implies_Equation2 (G : Type*) [Magma G] (h : Equation19111 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq11
  have eq35 (X0 X2 : G) : X0 = X2 := superpose eq7 eq14
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq56 eq35


@[equational_result]
theorem Equation19112_implies_Equation2 (G : Type*) [Magma G] (h : Equation19112 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq39 (X0 X1 X2 X3 : G) : (X2 ◇ ((X3 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1))) = X3 := superpose eq12 eq9
  have eq40 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq9 eq9
  have eq56 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq40 eq39
  have eq58 (X0 X4 : G) : X0 = X4 := superpose eq7 eq56
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq58 eq8
  subsumption eq131 eq58


@[equational_result]
theorem Equation19114_implies_Equation2 (G : Type*) [Magma G] (h : Equation19114 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq49 eq15


@[equational_result]
theorem Equation19115_implies_Equation2 (G : Type*) [Magma G] (h : Equation19115 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ ((X0 ◇ X3) ◇ (X4 ◇ X3))) ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq11
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq65 eq44


@[equational_result]
theorem Equation19116_implies_Equation2 (G : Type*) [Magma G] (h : Equation19116 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19117_implies_Equation2 (G : Type*) [Magma G] (h : Equation19117 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19120_implies_Equation2 (G : Type*) [Magma G] (h : Equation19120 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq7 eq10
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq17 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq13 eq11
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq17 eq13
  have eq61 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq19
  have eq111 (X0 X2 : G) : X0 = X2 := superpose eq61 eq61
  have eq180 (X0 : G) : sK0 ≠ X0 := superpose eq111 eq8
  subsumption eq180 eq111


@[equational_result]
theorem Equation19123_implies_Equation2 (G : Type*) [Magma G] (h : Equation19123 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq10 eq10
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq13 eq9
  have eq20 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq17 eq13
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (((X1 ◇ X1) ◇ X2) ◇ X0)) = X2 := superpose eq17 eq10
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) = X2 := superpose eq20 eq21
  have eq24 (X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X2 := superpose eq20 eq23
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq24 eq24
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq41 eq39


@[equational_result]
theorem Equation19125_implies_Equation2 (G : Type*) [Magma G] (h : Equation19125 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1)))) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X2 ◇ X1)) = X0 := superpose eq7 eq9
  have eq25 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ (X4 ◇ (X0 ◇ X1)))) := superpose eq9 eq7
  have eq51 (X0 X1 X2 X3 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ (X0 ◇ X1))) = X0 := superpose eq9 eq22
  have eq77 (X0 X1 X3 : G) : (X3 ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq51 eq25
  have eq93 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ X1) := superpose eq77 eq77
  have eq133 (X0 X1 X2 X3 : G) : (X3 ◇ (X2 ◇ X1)) = X0 := superpose eq22 eq93
  have eq284 (X0 X3 : G) : X0 = X3 := superpose eq7 eq133
  have eq407 (X0 : G) : sK0 ≠ X0 := superpose eq284 eq8
  subsumption eq407 eq284


@[equational_result]
theorem Equation19126_implies_Equation2 (G : Type*) [Magma G] (h : Equation19126 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq10 eq7
  have eq14 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq10 eq9
  have eq24 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq7 eq9
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X2 ◇ X2)) = X0 := superpose eq7 eq9
  have eq30 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq10 eq9
  have eq44 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq30 eq14
  have eq47 (X0 X1 : G) : (X0 ◇ (X1 ◇ X1)) = X0 := superpose eq12 eq44
  have eq48 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = ((X1 ◇ X1) ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq47 eq9
  have eq55 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := superpose eq47 eq24
  have eq64 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X2)) = ((X1 ◇ X1) ◇ X0) := superpose eq47 eq48
  have eq65 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq47 eq64
  have eq66 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X2)) = X0 := superpose eq65 eq29
  have eq84 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq65 eq55
  have eq85 (X0 X1 X2 : G) : (X1 ◇ X0) = (X1 ◇ (X2 ◇ X2)) := superpose eq47 eq84
  have eq86 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq47 eq85
  have eq89 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = X0 := superpose eq86 eq66
  have eq92 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq86 eq89
  have eq93 (X0 X3 : G) : X0 = X3 := superpose eq92 eq92
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq93 eq8
  subsumption eq98 eq93


@[equational_result]
theorem Equation19127_implies_Equation2 (G : Type*) [Magma G] (h : Equation19127 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : X0 = X1 := superpose eq7 eq11
  have eq32 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq32 eq14


@[equational_result]
theorem Equation19130_implies_Equation2 (G : Type*) [Magma G] (h : Equation19130 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose eq10 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq11 eq11
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19132_implies_Equation2 (G : Type*) [Magma G] (h : Equation19132 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq13 (X0 : G) : sK0 ≠ X0 := superpose eq11 eq8
  subsumption eq13 eq11


@[equational_result]
theorem Equation19133_implies_Equation2 (G : Type*) [Magma G] (h : Equation19133 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation19135_implies_Equation2 (G : Type*) [Magma G] (h : Equation19135 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation19136_implies_Equation2 (G : Type*) [Magma G] (h : Equation19136 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation19137_implies_Equation2 (G : Type*) [Magma G] (h : Equation19137 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19139_implies_Equation2 (G : Type*) [Magma G] (h : Equation19139 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X3 ◇ (X1 ◇ X1)))) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq9
  have eq55 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq90 eq55


@[equational_result]
theorem Equation19140_implies_Equation2 (G : Type*) [Magma G] (h : Equation19140 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X0))) = X2 := superpose eq11 eq7
  have eq29 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq45 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X3)) = ((((X0 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X3)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X3))) ◇ (X4 ◇ X4)) := superpose eq10 eq29
  have eq50 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq11 eq29
  have eq66 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq29 eq50
  have eq68 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := superpose eq66 eq29
  have eq73 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X0))) = X2 := superpose eq66 eq15
  have eq132 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq68
  have eq160 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ (X2 ◇ X0))) = X2 := superpose eq132 eq73
  have eq166 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X3)) = (((X0 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X3)) ◇ (X4 ◇ X4)) := superpose eq132 eq45
  have eq169 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) ◇ X0)) := superpose eq132 eq10
  have eq227 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X3)) = (((X0 ◇ X0) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X3)) ◇ X4) := superpose eq132 eq166
  have eq228 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X3)) = ((X0 ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) ◇ X3)) ◇ X4) := superpose eq132 eq227
  have eq231 (X0 X1 X2 X3 : G) : (X1 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) ◇ X0)) = X2 := superpose eq132 eq169
  have eq232 (X1 X4 : G) : (X1 ◇ X4) = X1 := superpose eq231 eq228
  have eq235 (X0 X1 X2 : G) : (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) = X2 := superpose eq232 eq160
  have eq247 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X1)) = X2 := superpose eq232 eq235
  have eq248 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq232 eq247
  have eq250 (X0 X2 : G) : X0 = X2 := superpose eq248 eq248
  have eq252 (X0 : G) : sK0 ≠ X0 := superpose eq250 eq8
  subsumption eq252 eq250


@[equational_result]
theorem Equation19141_implies_Equation2 (G : Type*) [Magma G] (h : Equation19141 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq137 eq59


@[equational_result]
theorem Equation19143_implies_Equation2 (G : Type*) [Magma G] (h : Equation19143 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation19144_implies_Equation2 (G : Type*) [Magma G] (h : Equation19144 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation19145_implies_Equation2 (G : Type*) [Magma G] (h : Equation19145 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19147_implies_Equation2 (G : Type*) [Magma G] (h : Equation19147 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19148_implies_Equation2 (G : Type*) [Magma G] (h : Equation19148 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19149_implies_Equation2 (G : Type*) [Magma G] (h : Equation19149 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19151_implies_Equation2 (G : Type*) [Magma G] (h : Equation19151 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19152_implies_Equation2 (G : Type*) [Magma G] (h : Equation19152 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19153_implies_Equation2 (G : Type*) [Magma G] (h : Equation19153 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19154_implies_Equation2 (G : Type*) [Magma G] (h : Equation19154 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19156_implies_Equation2 (G : Type*) [Magma G] (h : Equation19156 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ X2)) = ((X1 ◇ X1) ◇ (X0 ◇ (((X3 ◇ X0) ◇ (X0 ◇ X2)) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ ((X3 ◇ (X2 ◇ X2)) ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq7 eq11
  have eq20 (X0 X1 X2 X4 : G) : ((X1 ◇ (X2 ◇ X2)) ◇ X0) = ((X4 ◇ X4) ◇ ((X2 ◇ X2) ◇ (((X1 ◇ (X2 ◇ X2)) ◇ X0) ◇ X4))) := superpose eq7 eq9
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))) ◇ (X1 ◇ X0)) := superpose eq7 eq9
  have eq37 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) = ((X2 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq14 eq14
  have eq73 (X0 X1 X2 : G) : (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq10 eq10
  have eq75 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = ((((X2 ◇ X3) ◇ (X3 ◇ (X1 ◇ X1))) ◇ ((X2 ◇ X3) ◇ (X3 ◇ (X1 ◇ X1)))) ◇ ((X4 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) ◇ X3)) := superpose eq14 eq10
  have eq178 (X0 X1 X3 : G) : ((X3 ◇ X3) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X3))) = X0 := superpose eq7 eq20
  have eq186 (X0 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq11 eq20
  have eq216 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := superpose eq7 eq186
  have eq233 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) := superpose eq11 eq178
  have eq243 (X0 X1 X2 : G) : ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq11 eq178
  have eq266 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := superpose eq178 eq233
  have eq280 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = (((((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2)))) ◇ ((X3 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2)))) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2)))))) := superpose eq7 eq73
  have eq302 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq178 eq73
  have eq308 (X0 X1 X2 X3 : G) : (X0 ◇ X0) = ((((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (((X2 ◇ (X0 ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0)) ◇ ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0)))) ◇ (((X2 ◇ (X0 ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq73 eq10
  have eq322 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X2))) = X0 := superpose eq243 eq280
  have eq332 (X0 X1 X3 X4 : G) : ((X0 ◇ X1) ◇ (X1 ◇ X1)) = (X3 ◇ ((X4 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) ◇ X3)) := superpose eq322 eq75
  have eq333 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := superpose eq322 eq25
  have eq336 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) = X1 := superpose eq322 eq37
  have eq399 (X0 X2 X3 : G) : (X0 ◇ X0) = (((X2 ◇ (X0 ◇ X0)) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq322 eq308
  have eq400 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq336 eq399
  have eq401 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq400 eq216
  have eq402 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq401 eq14
  have eq411 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq401 eq333
  have eq430 (X1 X3 X4 : G) : (X3 ◇ ((X4 ◇ X1) ◇ X3)) = X1 := superpose eq402 eq332
  have eq454 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq411 eq266
  have eq467 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq454 eq302
  have eq490 (X1 X3 : G) : (X3 ◇ X3) = X1 := superpose eq467 eq430
  have eq509 (X0 X2 : G) : X0 = X2 := superpose eq490 eq490
  have eq511 (X0 : G) : sK0 ≠ X0 := superpose eq509 eq8
  subsumption eq511 eq509


@[equational_result]
theorem Equation19157_implies_Equation2 (G : Type*) [Magma G] (h : Equation19157 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq7 eq12
  have eq28 (X0 X1 X2 : G) : (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := superpose eq12 eq9
  have eq64 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq15 eq9
  have eq75 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq64 eq28
  have eq131 (X0 X3 : G) : X0 = X3 := superpose eq7 eq75
  have eq239 (X0 : G) : sK0 ≠ X0 := superpose eq131 eq8
  subsumption eq239 eq131


@[equational_result]
theorem Equation19158_implies_Equation2 (G : Type*) [Magma G] (h : Equation19158 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq38 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X3 ◇ X4) ◇ ((X0 ◇ X0) ◇ X1))) = X4 := superpose eq12 eq9
  have eq39 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9
  have eq53 (X0 X2 X4 : G) : (X2 ◇ X0) = X4 := superpose eq39 eq38
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq53
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq130 eq57


@[equational_result]
theorem Equation19160_implies_Equation2 (G : Type*) [Magma G] (h : Equation19160 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X2 ◇ X2)) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq10 eq7
  have eq12 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X2 ◇ X2)) = X0 := superpose eq11 eq9
  have eq13 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq12 eq10
  have eq14 (X0 X1 : G) : ((X1 ◇ X1) ◇ X0) = X0 := superpose eq12 eq7
  have eq15 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X0 := superpose eq13 eq12
  have eq17 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq13 eq14
  have eq19 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq17 eq15
  have eq20 (X0 X1 : G) : X0 = X1 := superpose eq17 eq19
  have eq22 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq22 eq20


@[equational_result]
theorem Equation19162_implies_Equation2 (G : Type*) [Magma G] (h : Equation19162 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq47 eq16


@[equational_result]
theorem Equation19164_implies_Equation2 (G : Type*) [Magma G] (h : Equation19164 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ X2)) = ((X1 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X2) ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ X0) ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) ◇ (((X2 ◇ X2) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X4) ◇ (((X2 ◇ X0) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X3) ◇ X4))) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := superpose eq7 eq9
  have eq29 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X3)) = ((((X4 ◇ X0) ◇ (X4 ◇ X3)) ◇ ((X4 ◇ X0) ◇ (X4 ◇ X3))) ◇ (X2 ◇ X0)) := superpose eq7 eq9
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X2) ◇ X0)) ◇ (X1 ◇ X2)) = X0 := superpose eq7 eq9
  have eq60 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := superpose eq7 eq37
  have eq61 (X0 X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) ◇ ((X3 ◇ X3) ◇ X1)) := superpose eq9 eq37
  have eq102 (X0 X1 X2 X3 : G) : ((((X2 ◇ X3) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X2 ◇ X3) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ ((X0 ◇ X1) ◇ X3)) = X1 := superpose eq11 eq10
  have eq131 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) = (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X1) := superpose eq9 eq60
  have eq133 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq60 eq37
  have eq153 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq133 eq131
  have eq200 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X3)) = ((X4 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq133 eq29
  have eq209 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X3)) = X1 := superpose eq133 eq102
  have eq217 (X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = ((X2 ◇ X1) ◇ ((X3 ◇ X3) ◇ X1)) := superpose eq153 eq61
  have eq240 (X2 X3 : G) : ((X2 ◇ X2) ◇ X3) = X3 := superpose eq209 eq217
  have eq242 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X4) ◇ (((X2 ◇ X0) ◇ (X2 ◇ X1)) ◇ ((X3 ◇ X3) ◇ X4))) = (X0 ◇ X3) := superpose eq240 eq16
  have eq248 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = X0 := superpose eq240 eq37
  have eq292 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X3) = ((X4 ◇ X4) ◇ (((X2 ◇ X0) ◇ (X2 ◇ X1)) ◇ X4)) := superpose eq240 eq242
  have eq305 (X0 X2 X4 : G) : ((X4 ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose eq248 eq200
  have eq306 (X0 X3 X4 : G) : (X0 ◇ X3) = ((X4 ◇ X4) ◇ (X0 ◇ X4)) := superpose eq248 eq292
  have eq313 (X0 X3 : G) : (X0 ◇ X3) = X0 := superpose eq305 eq306
  have eq314 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X1 := superpose eq313 eq209
  have eq331 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X0) = X1 := superpose eq313 eq314
  have eq332 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq313 eq331
  have eq333 (X0 X3 : G) : X0 = X3 := superpose eq332 eq332
  have eq338 (X0 : G) : sK0 ≠ X0 := superpose eq333 eq8
  subsumption eq338 eq333


@[equational_result]
theorem Equation19165_implies_Equation2 (G : Type*) [Magma G] (h : Equation19165 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X2) ◇ X0)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X1) := superpose eq7 eq12
  have eq26 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X2 := superpose eq16 eq11
  have eq36 (X0 X2 : G) : X0 = X2 := superpose eq7 eq26
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq57 eq36


@[equational_result]
theorem Equation19166_implies_Equation2 (G : Type*) [Magma G] (h : Equation19166 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X4))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq33 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ X1) ◇ ((X3 ◇ X3) ◇ X4))) = X1 := superpose eq12 eq9
  have eq39 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9
  have eq53 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq39 eq33
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq53
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq130 eq57


@[equational_result]
theorem Equation19168_implies_Equation2 (G : Type*) [Magma G] (h : Equation19168 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq61 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq61 eq15


@[equational_result]
theorem Equation19169_implies_Equation2 (G : Type*) [Magma G] (h : Equation19169 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq137 eq53


@[equational_result]
theorem Equation19170_implies_Equation2 (G : Type*) [Magma G] (h : Equation19170 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19171_implies_Equation2 (G : Type*) [Magma G] (h : Equation19171 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19173_implies_Equation2 (G : Type*) [Magma G] (h : Equation19173 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X2 ◇ X2) = ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) ◇ X0) ◇ ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) ◇ X0)) ◇ ((X3 ◇ X3) ◇ (X4 ◇ ((X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) ◇ X0)))) = X4 := superpose eq7 eq9
  have eq15 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X0 ◇ X0)) := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = ((((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0) ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) ◇ ((X4 ◇ ((X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) ◇ (X2 ◇ X2))) := superpose eq7 eq10
  have eq39 (X0 X1 X3 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X3 ◇ (X1 ◇ X1)))) = X3 := superpose eq15 eq7
  have eq72 (X0 X1 : G) : (X1 ◇ X1) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) := superpose eq39 eq39
  have eq74 (X0 X1 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq15 eq39
  have eq90 (X0 X1 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq74 eq72
  have eq144 (X0 X1 X2 X3 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1))) = X3 := superpose eq90 eq7
  have eq150 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := superpose eq90 eq7
  have eq167 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) ◇ X4) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq90 eq13
  have eq186 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq90 eq7
  have eq214 (X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) ◇ X4) = X3 := superpose eq150 eq167
  have eq219 (X0 X1 X2 X4 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = ((X2 ◇ X2) ◇ ((X4 ◇ X2) ◇ (X2 ◇ X2))) := superpose eq214 eq21
  have eq244 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X2 := superpose eq7 eq219
  have eq245 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq244 eq9
  have eq330 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1))) = X3 := superpose eq186 eq144
  have eq362 (X0 X2 X3 : G) : (X2 ◇ (X0 ◇ X0)) = X3 := superpose eq330 eq245
  have eq376 (X0 X2 : G) : X0 = X2 := superpose eq7 eq362
  have eq397 (X0 : G) : sK0 ≠ X0 := superpose eq376 eq8
  subsumption eq397 eq376


@[equational_result]
theorem Equation19175_implies_Equation2 (G : Type*) [Magma G] (h : Equation19175 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq148 eq59


@[equational_result]
theorem Equation19177_implies_Equation2 (G : Type*) [Magma G] (h : Equation19177 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation19178_implies_Equation2 (G : Type*) [Magma G] (h : Equation19178 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19179_implies_Equation2 (G : Type*) [Magma G] (h : Equation19179 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19181_implies_Equation2 (G : Type*) [Magma G] (h : Equation19181 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation19182_implies_Equation2 (G : Type*) [Magma G] (h : Equation19182 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19183_implies_Equation2 (G : Type*) [Magma G] (h : Equation19183 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19185_implies_Equation2 (G : Type*) [Magma G] (h : Equation19185 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19186_implies_Equation2 (G : Type*) [Magma G] (h : Equation19186 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19187_implies_Equation2 (G : Type*) [Magma G] (h : Equation19187 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19188_implies_Equation2 (G : Type*) [Magma G] (h : Equation19188 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19190_implies_Equation2 (G : Type*) [Magma G] (h : Equation19190 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X2 := superpose eq10 eq7
  have eq154 (X0 X1 : G) : X0 = X1 := superpose eq7 eq21
  have eq199 (X0 : G) : sK0 ≠ X0 := superpose eq154 eq8
  subsumption eq199 eq154


@[equational_result]
theorem Equation19191_implies_Equation2 (G : Type*) [Magma G] (h : Equation19191 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X2 := superpose eq9 eq10
  have eq44 (X0 X2 : G) : X0 = X2 := superpose eq7 eq13
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq65 eq44


@[equational_result]
theorem Equation19192_implies_Equation2 (G : Type*) [Magma G] (h : Equation19192 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq12
  have eq53 (X0 X1 : G) : X0 = X1 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation19194_implies_Equation2 (G : Type*) [Magma G] (h : Equation19194 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation19195_implies_Equation2 (G : Type*) [Magma G] (h : Equation19195 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19196_implies_Equation2 (G : Type*) [Magma G] (h : Equation19196 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19198_implies_Equation2 (G : Type*) [Magma G] (h : Equation19198 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19199_implies_Equation2 (G : Type*) [Magma G] (h : Equation19199 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19200_implies_Equation2 (G : Type*) [Magma G] (h : Equation19200 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19202_implies_Equation2 (G : Type*) [Magma G] (h : Equation19202 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19203_implies_Equation2 (G : Type*) [Magma G] (h : Equation19203 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19204_implies_Equation2 (G : Type*) [Magma G] (h : Equation19204 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19205_implies_Equation2 (G : Type*) [Magma G] (h : Equation19205 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19207_implies_Equation2 (G : Type*) [Magma G] (h : Equation19207 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq29 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ X1) := superpose eq11 eq11
  have eq44 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq29
  have eq134 (X0 X4 : G) : X0 = X4 := superpose eq7 eq44
  have eq262 (X0 : G) : sK0 ≠ X0 := superpose eq134 eq8
  subsumption eq262 eq134


@[equational_result]
theorem Equation19208_implies_Equation2 (G : Type*) [Magma G] (h : Equation19208 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq53 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq126 eq53


@[equational_result]
theorem Equation19209_implies_Equation2 (G : Type*) [Magma G] (h : Equation19209 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ (X0 ◇ (X5 ◇ ((X3 ◇ X4) ◇ (X0 ◇ X4))))) = X5 := superpose eq7 eq7
  have eq13 (X0 X1 X5 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X0)) = X5 := superpose eq9 eq10
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq65 eq44


@[equational_result]
theorem Equation19210_implies_Equation2 (G : Type*) [Magma G] (h : Equation19210 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation19212_implies_Equation2 (G : Type*) [Magma G] (h : Equation19212 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19213_implies_Equation2 (G : Type*) [Magma G] (h : Equation19213 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19214_implies_Equation2 (G : Type*) [Magma G] (h : Equation19214 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19215_implies_Equation2 (G : Type*) [Magma G] (h : Equation19215 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19217_implies_Equation2 (G : Type*) [Magma G] (h : Equation19217 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19218_implies_Equation2 (G : Type*) [Magma G] (h : Equation19218 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19219_implies_Equation2 (G : Type*) [Magma G] (h : Equation19219 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19220_implies_Equation2 (G : Type*) [Magma G] (h : Equation19220 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19222_implies_Equation2 (G : Type*) [Magma G] (h : Equation19222 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19223_implies_Equation2 (G : Type*) [Magma G] (h : Equation19223 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19224_implies_Equation2 (G : Type*) [Magma G] (h : Equation19224 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19225_implies_Equation2 (G : Type*) [Magma G] (h : Equation19225 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19227_implies_Equation2 (G : Type*) [Magma G] (h : Equation19227 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19228_implies_Equation2 (G : Type*) [Magma G] (h : Equation19228 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19229_implies_Equation2 (G : Type*) [Magma G] (h : Equation19229 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19230_implies_Equation2 (G : Type*) [Magma G] (h : Equation19230 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19231_implies_Equation2 (G : Type*) [Magma G] (h : Equation19231 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19233_implies_Equation2 (G : Type*) [Magma G] (h : Equation19233 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ (X3 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ X2) ◇ (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1))) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq9 eq9
  have eq19 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq7 eq9
  have eq51 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq19 eq7
  have eq65 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq51 eq10
  have eq83 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq65 eq9
  have eq98 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq83 eq18
  have eq125 (X0 X3 : G) : X0 = X3 := superpose eq98 eq98
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq125 eq8
  subsumption eq130 eq125


@[equational_result]
theorem Equation19234_implies_Equation2 (G : Type*) [Magma G] (h : Equation19234 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ (X3 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := superpose eq7 eq7
  have eq23 (X0 X1 : G) : (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X1 := superpose eq9 eq9
  have eq27 (X0 X1 : G) : (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq23
  have eq84 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2)))) = (((X1 ◇ X1) ◇ X0) ◇ X1) := superpose eq9 eq27
  have eq97 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq27 eq11
  have eq102 (X0 X3 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X3) ◇ X0)) = X3 := superpose eq84 eq9
  have eq129 (X0 X3 : G) : (X0 ◇ (X0 ◇ X0)) = X3 := superpose eq97 eq102
  have eq147 (X0 X1 : G) : X0 = X1 := superpose eq7 eq129
  have eq169 (X0 : G) : sK0 ≠ X0 := superpose eq147 eq8
  subsumption eq169 eq147


@[equational_result]
theorem Equation19235_implies_Equation2 (G : Type*) [Magma G] (h : Equation19235 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (X0 ◇ ((X4 ◇ X4) ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ X1) := superpose eq7 eq12
  have eq33 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq12 eq9
  have eq34 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := superpose eq9 eq9
  have eq254 (X0 X1 X2 X3 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X3)) = X1 := superpose eq15 eq34
  have eq304 (X1 X2 X3 : G) : (X3 ◇ X1) = X2 := superpose eq254 eq33
  have eq311 (X0 X4 : G) : X0 = X4 := superpose eq7 eq304
  have eq360 (X0 : G) : sK0 ≠ X0 := superpose eq311 eq8
  subsumption eq360 eq311


@[equational_result]
theorem Equation19237_implies_Equation2 (G : Type*) [Magma G] (h : Equation19237 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X0 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq12
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ (X1 ◇ X2))) = X3 := superpose eq16 eq9
  have eq26 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X2)) = X3 := superpose eq16 eq21
  have eq27 (X0 X2 X3 : G) : (X0 ◇ X2) = X3 := superpose eq16 eq26
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq30 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq30 eq28


@[equational_result]
theorem Equation19239_implies_Equation2 (G : Type*) [Magma G] (h : Equation19239 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq52 eq18


@[equational_result]
theorem Equation19242_implies_Equation2 (G : Type*) [Magma G] (h : Equation19242 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ (((X0 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq7
  have eq11 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq12 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq10 eq10
  have eq14 (X0 X2 : G) : (X0 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))) = X2 := superpose eq10 eq7
  have eq25 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq7
  have eq37 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq11 eq9
  have eq41 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq25 eq37
  have eq42 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq14 eq41
  have eq45 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X2)))) = X3 := superpose eq42 eq9
  have eq46 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq42 eq7
  have eq57 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ ((X0 ◇ X0) ◇ X2))) = X3 := superpose eq42 eq45
  have eq58 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ X3) ◇ (X0 ◇ X2))) = X3 := superpose eq42 eq57
  have eq59 (X0 X2 X3 : G) : (X0 ◇ (X3 ◇ (X0 ◇ X2))) = X3 := superpose eq42 eq58
  have eq60 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X2)) = X0 := superpose eq42 eq46
  have eq71 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq42 eq60
  have eq75 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq71 eq59
  have eq96 (X0 X1 : G) : X0 = X1 := superpose eq75 eq71
  have eq117 (X0 : G) : sK0 ≠ X0 := superpose eq96 eq8
  subsumption eq117 eq96


@[equational_result]
theorem Equation19243_implies_Equation2 (G : Type*) [Magma G] (h : Equation19243 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19245_implies_Equation2 (G : Type*) [Magma G] (h : Equation19245 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq36 eq18


@[equational_result]
theorem Equation19246_implies_Equation2 (G : Type*) [Magma G] (h : Equation19246 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq7 eq11
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq43 eq16


@[equational_result]
theorem Equation19247_implies_Equation2 (G : Type*) [Magma G] (h : Equation19247 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19248_implies_Equation2 (G : Type*) [Magma G] (h : Equation19248 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19250_implies_Equation2 (G : Type*) [Magma G] (h : Equation19250 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X2) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq32 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq10
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq7 eq32
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq122 eq45


@[equational_result]
theorem Equation19252_implies_Equation2 (G : Type*) [Magma G] (h : Equation19252 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X6 : G) : (X1 ◇ (X0 ◇ (X2 ◇ X6))) = X2 := superpose eq9 eq9
  have eq48 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq15 eq15
  have eq107 (X0 X4 : G) : X0 = X4 := superpose eq7 eq48
  have eq247 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq247 eq107


@[equational_result]
theorem Equation19254_implies_Equation2 (G : Type*) [Magma G] (h : Equation19254 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq11
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := superpose eq12 eq7
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq12 eq19
  have eq26 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq12 eq25
  have eq27 (X0 X3 : G) : X0 = X3 := superpose eq26 eq26
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq27 eq8
  subsumption eq29 eq27


@[equational_result]
theorem Equation19255_implies_Equation2 (G : Type*) [Magma G] (h : Equation19255 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq10 eq10
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq7 eq15
  have eq104 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq104 eq36


@[equational_result]
theorem Equation19256_implies_Equation2 (G : Type*) [Magma G] (h : Equation19256 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ ((X1 ◇ X2) ◇ X5))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X1 := superpose eq7 eq7
  have eq33 (X0 X1 : G) : X0 = X1 := superpose eq12 eq9
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq41 eq33


@[equational_result]
theorem Equation19259_implies_Equation2 (G : Type*) [Magma G] (h : Equation19259 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((((X0 ◇ X1) ◇ (X2 ◇ X2)) ◇ X3) ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq7 eq7
  have eq11 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq11
  have eq13 (X0 : G) : (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq11 eq7
  have eq17 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq12 eq14
  have eq23 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq12
  have eq28 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq23 eq13
  have eq29 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq23 eq28
  have eq30 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq29 eq7
  have eq32 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ (X3 ◇ X3))) := superpose eq29 eq10
  have eq35 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq29 eq17
  have eq39 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((((X0 ◇ X1) ◇ X2) ◇ X3) ◇ (X0 ◇ X3)) := superpose eq29 eq32
  have eq40 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := superpose eq29 eq35
  have eq47 (X0 X1 X2 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ X1)) ◇ X0) = X2 := superpose eq30 eq30
  have eq55 (X0 X1 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X1 := superpose eq29 eq47
  have eq59 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq29 eq55
  have eq60 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X1) ◇ X2) := superpose eq30 eq59
  have eq74 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ (X0 ◇ X3)) := superpose eq60 eq39
  have eq86 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X0 ◇ ((X1 ◇ X2) ◇ X3)) ◇ (X0 ◇ X3)) := superpose eq60 eq74
  have eq87 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X3)) := superpose eq60 eq86
  have eq103 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X2 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0)) := superpose eq29 eq87
  have eq106 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) := superpose eq29 eq87
  have eq117 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := superpose eq103 eq106
  have eq118 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq59 eq117
  have eq119 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq118 eq40
  have eq154 (X0 X2 : G) : X0 = X2 := superpose eq119 eq119
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq154 eq8
  subsumption eq173 eq154


@[equational_result]
theorem Equation19260_implies_Equation2 (G : Type*) [Magma G] (h : Equation19260 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ X1) ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq33 (X0 X2 : G) : X0 = X2 := superpose eq12 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq41 eq33


@[equational_result]
theorem Equation19262_implies_Equation2 (G : Type*) [Magma G] (h : Equation19262 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq45 eq19


@[equational_result]
theorem Equation19263_implies_Equation2 (G : Type*) [Magma G] (h : Equation19263 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq64 eq19


@[equational_result]
theorem Equation19264_implies_Equation2 (G : Type*) [Magma G] (h : Equation19264 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X3)) = X0 := superpose eq11 eq7
  have eq15 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq11 eq11
  have eq16 (X0 X2 X3 : G) : (X2 ◇ (X3 ◇ X3)) = X0 := superpose eq15 eq13
  have eq20 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq15 eq16
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq20 eq20
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq23 eq21


@[equational_result]
theorem Equation19265_implies_Equation2 (G : Type*) [Magma G] (h : Equation19265 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X1) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19268_implies_Equation2 (G : Type*) [Magma G] (h : Equation19268 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X3 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X0 ◇ X0)) := superpose eq7 eq7
  have eq11 (X0 X2 X3 X4 : G) : ((X3 ◇ ((X4 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X4 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X2))))) ◇ (X4 ◇ X4)) = X0 := superpose eq7 eq10
  have eq30 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) = X2 := superpose eq9 eq9
  have eq39 (X0 X4 : G) : (X4 ◇ (X4 ◇ X4)) = X0 := superpose eq30 eq11
  have eq102 (X0 X2 : G) : X0 = X2 := superpose eq7 eq39
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq102 eq8
  subsumption eq118 eq102


@[equational_result]
theorem Equation19269_implies_Equation2 (G : Type*) [Magma G] (h : Equation19269 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3))) ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ ((X0 ◇ X3) ◇ X2)) ◇ (X4 ◇ X5))) = X4 := superpose eq12 eq9
  have eq20 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ ((X0 ◇ X3) ◇ X2))) = X4 := superpose eq12 eq15
  have eq21 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (((X0 ◇ X3) ◇ X2) ◇ X5)) = X4 := superpose eq12 eq20
  have eq22 (X0 X2 X4 X5 : G) : (X0 ◇ (X5 ◇ X2)) = X4 := superpose eq12 eq21
  have eq25 (X0 X4 : G) : X0 = X4 := superpose eq22 eq22
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq25 eq8
  subsumption eq34 eq25


@[equational_result]
theorem Equation19272_implies_Equation2 (G : Type*) [Magma G] (h : Equation19272 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X2))) ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq10
  have eq35 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq15
  have eq91 (X0 X3 : G) : X0 = X3 := superpose eq7 eq35
  have eq202 (X0 : G) : sK0 ≠ X0 := superpose eq91 eq8
  subsumption eq202 eq91


@[equational_result]
theorem Equation19273_implies_Equation2 (G : Type*) [Magma G] (h : Equation19273 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq53 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq53 eq18


@[equational_result]
theorem Equation19276_implies_Equation2 (G : Type*) [Magma G] (h : Equation19276 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))) ◇ (((X0 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))) ◇ (X0 ◇ (((X0 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2)))) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))) ◇ (((X1 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))))))) = X1 := superpose eq9 eq9
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq10 eq10
  have eq43 (X0 X2 X3 : G) : (X3 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))) = X0 := superpose eq7 eq28
  have eq102 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ (((X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))) ◇ X1)))) = X1 := superpose eq43 eq12
  have eq121 (X0 X1 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) = X1 := superpose eq43 eq102
  have eq122 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq43 eq121
  have eq123 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X2)) = X0 := superpose eq122 eq7
  have eq130 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq122 eq123
  have eq131 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq122 eq130
  have eq133 (X0 X2 : G) : X0 = X2 := superpose eq131 eq131
  have eq135 (X0 : G) : sK0 ≠ X0 := superpose eq133 eq8
  subsumption eq135 eq133


@[equational_result]
theorem Equation19277_implies_Equation2 (G : Type*) [Magma G] (h : Equation19277 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ ((X4 ◇ (X2 ◇ X3)) ◇ X0)) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X4 := superpose eq11 eq11
  have eq52 (X0 X5 : G) : X0 = X5 := superpose eq11 eq18
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq168 eq52


@[equational_result]
theorem Equation19279_implies_Equation2 (G : Type*) [Magma G] (h : Equation19279 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq20 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq20 eq8
  subsumption eq40 eq20


@[equational_result]
theorem Equation19280_implies_Equation2 (G : Type*) [Magma G] (h : Equation19280 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2))) ◇ (X5 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2))))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2))) ◇ ((X4 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2))) ◇ X0)) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X2))) ◇ X0)) = X1 := superpose eq7 eq9
  have eq34 (X0 X1 X2 X3 X4 X5 X6 : G) : (X5 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) = ((X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) ◇ X2)) ◇ (X0 ◇ (X6 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) ◇ X2)))) := superpose eq11 eq7
  have eq49 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) ◇ X2)) ◇ (X0 ◇ (X5 ◇ ((X0 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) ◇ X2)))) = X2 := superpose eq18 eq7
  have eq55 (X2 X3 X4 X5 : G) : (X5 ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) = X2 := superpose eq49 eq34
  have eq99 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq55 eq55
  have eq108 (X0 X4 : G) : X0 = X4 := superpose eq7 eq99
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq108 eq8
  subsumption eq157 eq108


@[equational_result]
theorem Equation19281_implies_Equation2 (G : Type*) [Magma G] (h : Equation19281 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq44 eq16


@[equational_result]
theorem Equation19282_implies_Equation2 (G : Type*) [Magma G] (h : Equation19282 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19284_implies_Equation2 (G : Type*) [Magma G] (h : Equation19284 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (X4 ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X5 X6 : G) : (X2 ◇ X3) = (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X5 ◇ X6)))) := superpose eq7 eq9
  have eq18 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq9 eq9
  have eq25 (X1 X2 X3 : G) : (X1 ◇ X2) = (X2 ◇ X3) := superpose eq18 eq13
  have eq49 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq9 eq25
  have eq111 (X0 X4 : G) : X0 = X4 := superpose eq7 eq49
  have eq196 (X0 : G) : sK0 ≠ X0 := superpose eq111 eq8
  subsumption eq196 eq111


@[equational_result]
theorem Equation19285_implies_Equation2 (G : Type*) [Magma G] (h : Equation19285 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (X4 ◇ ((X0 ◇ X3) ◇ (X0 ◇ X2))))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X3) = ((X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X3))) ◇ (((X4 ◇ X3) ◇ X5) ◇ X0)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ X3) = ((X4 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq7 eq12
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X0 ◇ X1)) := superpose eq7 eq12
  have eq31 (X0 X1 X2 X3 X4 X5 : G) : (X4 ◇ X3) = ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ (((X4 ◇ X3) ◇ X5) ◇ X0)) := superpose eq18 eq11
  have eq32 (X0 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (X4 ◇ (X0 ◇ (X0 ◇ X3))))) = X4 := superpose eq18 eq9
  have eq34 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X4 ◇ X5))) = X4 := superpose eq18 eq32
  have eq35 (X0 X3 X4 X5 : G) : (X4 ◇ X3) = (X0 ◇ (((X4 ◇ X3) ◇ X5) ◇ X0)) := superpose eq34 eq31
  have eq41 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X2 := superpose eq34 eq34
  have eq50 (X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X1 := superpose eq41 eq15
  have eq66 (X0 X3 X4 : G) : (X4 ◇ X3) = (X0 ◇ (X4 ◇ X0)) := superpose eq50 eq35
  have eq67 (X3 X4 : G) : (X4 ◇ X3) = X4 := superpose eq41 eq66
  have eq69 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq67 eq41
  have eq79 (X0 X1 : G) : X0 = X1 := superpose eq67 eq69
  have eq81 (X0 : G) : sK0 ≠ X0 := superpose eq79 eq8
  subsumption eq81 eq79


@[equational_result]
theorem Equation19286_implies_Equation2 (G : Type*) [Magma G] (h : Equation19286 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq31 (X0 X1 X2 X3 : G) : (X3 ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq11 eq9
  have eq34 (X0 X1 X2 X3 : G) : (X3 ◇ ((X0 ◇ X1) ◇ X2)) = X0 := superpose eq11 eq9
  have eq45 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq34 eq31
  have eq46 (X0 X4 : G) : X0 = X4 := superpose eq7 eq45
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq126 eq46


@[equational_result]
theorem Equation19287_implies_Equation2 (G : Type*) [Magma G] (h : Equation19287 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : (X0 ◇ ((X5 ◇ X6) ◇ (X5 ◇ X7))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X0 ◇ X3) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq38 (X0 X1 X2 X3 X4 : G) : (X3 ◇ ((X2 ◇ X4) ◇ ((X0 ◇ X1) ◇ X2))) = X2 := superpose eq12 eq9
  have eq39 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X2 := superpose eq9 eq9
  have eq53 (X0 X2 X3 : G) : (X3 ◇ X0) = X2 := superpose eq39 eq38
  have eq56 (X0 X5 : G) : X0 = X5 := superpose eq7 eq53
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq56 eq8
  subsumption eq129 eq56


@[equational_result]
theorem Equation19289_implies_Equation2 (G : Type*) [Magma G] (h : Equation19289 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq7 eq12
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ X1)) = X0 := superpose eq14 eq7
  have eq29 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq14 eq23
  have eq30 (X0 X1 X2 : G) : (X2 ◇ X1) = X0 := superpose eq14 eq29
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq30 eq30
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq33 eq31


@[equational_result]
theorem Equation19290_implies_Equation2 (G : Type*) [Magma G] (h : Equation19290 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ X0)) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = X2 := superpose eq10 eq10
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq115 eq38


@[equational_result]
theorem Equation19291_implies_Equation2 (G : Type*) [Magma G] (h : Equation19291 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation19292_implies_Equation2 (G : Type*) [Magma G] (h : Equation19292 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation19294_implies_Equation2 (G : Type*) [Magma G] (h : Equation19294 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X3 ◇ X2)) ◇ ((X4 ◇ X5) ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X0 ◇ X3)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X0) ◇ (X3 ◇ X4)) = X2 := superpose eq7 eq12
  have eq23 (X0 X1 X4 X5 : G) : (X1 ◇ ((X4 ◇ X5) ◇ X0)) = X4 := superpose eq15 eq11
  have eq31 (X0 X2 : G) : X0 = X2 := superpose eq12 eq23
  have eq40 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq40 eq31


@[equational_result]
theorem Equation19295_implies_Equation2 (G : Type*) [Magma G] (h : Equation19295 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq60 eq16


@[equational_result]
theorem Equation19296_implies_Equation2 (G : Type*) [Magma G] (h : Equation19296 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (((X0 ◇ X3) ◇ (X2 ◇ X3)) ◇ X5))) = X4 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ ((X0 ◇ X5) ◇ (X4 ◇ X5))))) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X1 ◇ (X0 ◇ (((X1 ◇ X6) ◇ (X7 ◇ X6)) ◇ ((X0 ◇ X3) ◇ (((X2 ◇ X4) ◇ (X5 ◇ X4)) ◇ X3))))) = X2 := superpose eq9 eq9
  have eq44 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq10 eq10
  have eq68 (X0 X2 X3 X4 : G) : (X4 ◇ ((X0 ◇ X3) ◇ (X2 ◇ X3))) = X0 := superpose eq7 eq44
  have eq123 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = X2 := superpose eq68 eq13
  have eq167 (X0 X3 : G) : X0 = X3 := superpose eq7 eq123
  have eq201 (X0 : G) : sK0 ≠ X0 := superpose eq167 eq8
  subsumption eq201 eq167


@[equational_result]
theorem Equation19297_implies_Equation2 (G : Type*) [Magma G] (h : Equation19297 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq69 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq69 eq19


@[equational_result]
theorem Equation19299_implies_Equation2 (G : Type*) [Magma G] (h : Equation19299 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq19 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq42 eq19


@[equational_result]
theorem Equation19300_implies_Equation2 (G : Type*) [Magma G] (h : Equation19300 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0) = X3 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq59 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq59 eq21


@[equational_result]
theorem Equation19301_implies_Equation2 (G : Type*) [Magma G] (h : Equation19301 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq60 eq18


@[equational_result]
theorem Equation19302_implies_Equation2 (G : Type*) [Magma G] (h : Equation19302 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19304_implies_Equation2 (G : Type*) [Magma G] (h : Equation19304 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X2 : G) : X0 = X2 := superpose eq7 eq12
  have eq38 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq38 eq18


@[equational_result]
theorem Equation19305_implies_Equation2 (G : Type*) [Magma G] (h : Equation19305 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq73 eq19


@[equational_result]
theorem Equation19306_implies_Equation2 (G : Type*) [Magma G] (h : Equation19306 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq60 eq18


@[equational_result]
theorem Equation19307_implies_Equation2 (G : Type*) [Magma G] (h : Equation19307 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19308_implies_Equation2 (G : Type*) [Magma G] (h : Equation19308 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X0 ◇ X3) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19310_implies_Equation2 (G : Type*) [Magma G] (h : Equation19310 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ (X3 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X2)))) := superpose eq7 eq7
  have eq14 (X0 X1 X4 : G) : (X1 ◇ ((X0 ◇ X4) ◇ (X4 ◇ X0))) = X4 := superpose eq7 eq9
  have eq39 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ X3) ◇ X4) = (X2 ◇ (((X1 ◇ (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X3))) ◇ ((X0 ◇ X3) ◇ X4)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))) := superpose eq10 eq9
  have eq46 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X1) = ((X0 ◇ X3) ◇ X4) := superpose eq14 eq39
  have eq241 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq46
  have eq313 (X0 X3 : G) : X0 = X3 := superpose eq7 eq241
  have eq467 (X0 : G) : sK0 ≠ X0 := superpose eq313 eq8
  subsumption eq467 eq313


@[equational_result]
theorem Equation19312_implies_Equation2 (G : Type*) [Magma G] (h : Equation19312 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X4) ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X4 X5 : G) : (X0 ◇ ((X1 ◇ X4) ◇ (X4 ◇ X5))) = X4 := superpose eq12 eq9
  have eq19 (X0 X1 X4 X5 : G) : (X0 ◇ (X1 ◇ (X4 ◇ X5))) = X4 := superpose eq12 eq14
  have eq23 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X4) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := superpose eq12 eq19
  have eq30 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq19 eq23
  have eq32 (X0 X1 X4 : G) : (X0 ◇ (X1 ◇ X4)) = X4 := superpose eq30 eq19
  have eq35 (X0 X1 X4 : G) : (X0 ◇ X1) = X4 := superpose eq30 eq32
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq35 eq35
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq48 eq36


@[equational_result]
theorem Equation19314_implies_Equation2 (G : Type*) [Magma G] (h : Equation19314 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : (X2 ◇ (X0 ◇ X1)) = X3 := superpose eq9 eq9
  have eq47 (X0 X3 : G) : X0 = X3 := superpose eq7 eq16
  have eq115 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq115 eq47


@[equational_result]
theorem Equation19315_implies_Equation2 (G : Type*) [Magma G] (h : Equation19315 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X2)) = (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : ((((X1 ◇ X2) ◇ X0) ◇ ((X1 ◇ X2) ◇ X3)) ◇ X0) = X3 := superpose eq7 eq10
  have eq34 (X0 X1 X2 X3 X4 : G) : (X1 ◇ ((X0 ◇ X2) ◇ X4)) = (X3 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X2)) ◇ X3)) := superpose eq9 eq10
  have eq40 (X0 X1 X2 X4 : G) : (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X2) ◇ X4)) := superpose eq10 eq34
  have eq43 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq40 eq15
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq7 eq43
  have eq93 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq93 eq53


@[equational_result]
theorem Equation19316_implies_Equation2 (G : Type*) [Magma G] (h : Equation19316 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X4) ◇ ((X1 ◇ X2) ◇ X5))) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X4 : G) : (X1 ◇ X0) = X4 := superpose eq9 eq9
  have eq41 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq160 eq41


@[equational_result]
theorem Equation19318_implies_Equation2 (G : Type*) [Magma G] (h : Equation19318 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X1)) = (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X3 ◇ (X1 ◇ X2)))) := superpose eq7 eq7
  have eq32 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)) = (((X1 ◇ X2) ◇ (X2 ◇ X0)) ◇ X0) := superpose eq7 eq10
  have eq35 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X2) ◇ X0)) ◇ (X2 ◇ X1)) = X0 := superpose eq7 eq10
  have eq51 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X0) ◇ (((X1 ◇ X2) ◇ X0) ◇ X1)) := superpose eq35 eq35
  have eq59 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X1 ◇ X3) ◇ X0) ◇ X1)) = (X0 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X3) ◇ X0))))) := superpose eq35 eq10
  have eq133 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq51 eq35
  have eq281 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq133 eq133
  have eq284 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) := superpose eq133 eq51
  have eq292 (X0 X1 : G) : ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq133 eq32
  have eq395 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq281 eq51
  have eq425 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) := superpose eq395 eq292
  have eq426 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq395 eq281
  have eq427 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq426 eq395
  have eq429 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq427 eq425
  have eq434 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := superpose eq427 eq429
  have eq435 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := superpose eq427 eq434
  have eq436 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq435 eq284
  have eq438 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X3) ◇ X0))))) = ((X1 ◇ X2) ◇ X1) := superpose eq436 eq59
  have eq726 (X0 X1 X2 X3 : G) : (X0 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X3) ◇ X0))))) = X1 := superpose eq436 eq438
  have eq727 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ X1) ◇ (X1 ◇ ((X1 ◇ X3) ◇ X0)))) = X1 := superpose eq436 eq726
  have eq728 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ ((X1 ◇ X3) ◇ X0))) = X1 := superpose eq436 eq727
  have eq729 (X0 X1 X3 : G) : (X0 ◇ ((X1 ◇ X3) ◇ X0)) = X1 := superpose eq436 eq728
  have eq730 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq436 eq729
  have eq739 (X0 X2 : G) : X0 = X2 := superpose eq730 eq730
  have eq741 (X0 : G) : sK0 ≠ X0 := superpose eq739 eq8
  subsumption eq741 eq739


@[equational_result]
theorem Equation19319_implies_Equation2 (G : Type*) [Magma G] (h : Equation19319 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq11
  have eq13 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose eq11 eq7
  have eq16 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq12 eq11
  have eq17 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq16 eq13
  have eq18 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq12 eq17
  have eq20 (X0 X1 : G) : (X0 ◇ (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0))) = X1 := superpose eq12 eq15
  have eq25 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq12
  have eq30 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq25 eq18
  have eq31 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq30 eq7
  have eq37 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := superpose eq30 eq20
  have eq48 (X0 X1 X2 : G) : ((X1 ◇ ((X1 ◇ X0) ◇ X2)) ◇ X0) = X2 := superpose eq31 eq31
  have eq64 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq37 eq48
  have eq121 (X0 X2 : G) : X0 = X2 := superpose eq64 eq64
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq121 eq8
  subsumption eq163 eq121


@[equational_result]
theorem Equation19320_implies_Equation2 (G : Type*) [Magma G] (h : Equation19320 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq54 eq18


@[equational_result]
theorem Equation19322_implies_Equation2 (G : Type*) [Magma G] (h : Equation19322 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X4) ◇ (X5 ◇ (X1 ◇ X2)))) = X4 := superpose eq7 eq7
  have eq18 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq9 eq9
  have eq69 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq161 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq161 eq69


@[equational_result]
theorem Equation19323_implies_Equation2 (G : Type*) [Magma G] (h : Equation19323 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq49 eq17


@[equational_result]
theorem Equation19324_implies_Equation2 (G : Type*) [Magma G] (h : Equation19324 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq11 eq11
  have eq47 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq47 eq15


@[equational_result]
theorem Equation19325_implies_Equation2 (G : Type*) [Magma G] (h : Equation19325 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19327_implies_Equation2 (G : Type*) [Magma G] (h : Equation19327 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (X1 ◇ (X0 ◇ (X4 ◇ (((X2 ◇ X3) ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X2 ◇ X3)))))) = X4 := superpose eq9 eq9
  have eq21 (X0 X1 X4 : G) : (X1 ◇ (X0 ◇ X0)) = X4 := superpose eq9 eq11
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq7 eq21
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq54 eq30


@[equational_result]
theorem Equation19328_implies_Equation2 (G : Type*) [Magma G] (h : Equation19328 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X3 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq11
  have eq15 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq11 eq7
  have eq39 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq14 eq14
  have eq40 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq14 eq14
  have eq41 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq7 eq14
  have eq59 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0)))) = X2 := superpose eq14 eq7
  have eq86 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0))))) = X3 := superpose eq11 eq9
  have eq91 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := superpose eq14 eq9
  have eq96 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = (X1 ◇ (((X0 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := superpose eq14 eq9
  have eq121 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X0)) := superpose eq59 eq96
  have eq123 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (((X2 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X2))))) = X3 := superpose eq121 eq86
  have eq125 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq121 eq15
  have eq156 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1)))) = X3 := superpose eq121 eq123
  have eq158 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq125 eq40
  have eq159 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := superpose eq158 eq39
  have eq164 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X3 ◇ (X2 ◇ (X1 ◇ X2)))) = X3 := superpose eq159 eq156
  have eq165 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq164 eq91
  have eq167 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq165 eq41
  have eq215 (X0 X1 : G) : X0 = X1 := superpose eq165 eq167
  have eq233 (X0 : G) : sK0 ≠ X0 := superpose eq215 eq8
  subsumption eq233 eq215


@[equational_result]
theorem Equation19329_implies_Equation2 (G : Type*) [Magma G] (h : Equation19329 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X4 X5 : G) : (X0 ◇ ((X1 ◇ X1) ◇ (X4 ◇ X5))) = X4 := superpose eq11 eq9
  have eq15 (X0 X1 X4 : G) : (X0 ◇ (X1 ◇ X1)) = X4 := superpose eq11 eq12
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq15 eq15
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq35 eq18


@[equational_result]
theorem Equation19331_implies_Equation2 (G : Type*) [Magma G] (h : Equation19331 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation19332_implies_Equation2 (G : Type*) [Magma G] (h : Equation19332 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation19333_implies_Equation2 (G : Type*) [Magma G] (h : Equation19333 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19335_implies_Equation2 (G : Type*) [Magma G] (h : Equation19335 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19336_implies_Equation2 (G : Type*) [Magma G] (h : Equation19336 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19337_implies_Equation2 (G : Type*) [Magma G] (h : Equation19337 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19339_implies_Equation2 (G : Type*) [Magma G] (h : Equation19339 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19340_implies_Equation2 (G : Type*) [Magma G] (h : Equation19340 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19341_implies_Equation2 (G : Type*) [Magma G] (h : Equation19341 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19342_implies_Equation2 (G : Type*) [Magma G] (h : Equation19342 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X1) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19344_implies_Equation2 (G : Type*) [Magma G] (h : Equation19344 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X2)))) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq9 eq9
  have eq24 (X0 X1 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ X1))) = X3 := superpose eq16 eq9
  have eq30 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq16 eq24
  have eq34 (X0 X2 : G) : X0 = X2 := superpose eq30 eq30
  have eq36 (X0 : G) : sK0 ≠ X0 := superpose eq34 eq8
  subsumption eq36 eq34


@[equational_result]
theorem Equation19345_implies_Equation2 (G : Type*) [Magma G] (h : Equation19345 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq9
  have eq36 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq15
  have eq83 (X0 X3 : G) : X0 = X3 := superpose eq7 eq36
  have eq190 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq190 eq83


@[equational_result]
theorem Equation19346_implies_Equation2 (G : Type*) [Magma G] (h : Equation19346 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X1 ◇ X2)) = X0 := superpose eq11 eq7
  have eq16 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19348_implies_Equation2 (G : Type*) [Magma G] (h : Equation19348 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation19349_implies_Equation2 (G : Type*) [Magma G] (h : Equation19349 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation19350_implies_Equation2 (G : Type*) [Magma G] (h : Equation19350 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19352_implies_Equation2 (G : Type*) [Magma G] (h : Equation19352 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19353_implies_Equation2 (G : Type*) [Magma G] (h : Equation19353 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation19354_implies_Equation2 (G : Type*) [Magma G] (h : Equation19354 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19356_implies_Equation2 (G : Type*) [Magma G] (h : Equation19356 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19357_implies_Equation2 (G : Type*) [Magma G] (h : Equation19357 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19358_implies_Equation2 (G : Type*) [Magma G] (h : Equation19358 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19359_implies_Equation2 (G : Type*) [Magma G] (h : Equation19359 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19361_implies_Equation2 (G : Type*) [Magma G] (h : Equation19361 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (((X1 ◇ X2) ◇ X4) ◇ (X5 ◇ (X1 ◇ X2)))) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ X3) ◇ X5) = (X1 ◇ X0) := superpose eq9 eq9
  have eq46 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq18
  have eq163 (X0 X4 : G) : X0 = X4 := superpose eq7 eq46
  have eq284 (X0 : G) : sK0 ≠ X0 := superpose eq163 eq8
  subsumption eq284 eq163


@[equational_result]
theorem Equation19362_implies_Equation2 (G : Type*) [Magma G] (h : Equation19362 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 : G) : (((X1 ◇ X2) ◇ X3) ◇ (X0 ◇ (X5 ◇ X3))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq30 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X3 ◇ X5)) = ((X2 ◇ X3) ◇ ((X2 ◇ X4) ◇ (X0 ◇ X1))) := superpose eq12 eq7
  have eq37 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ ((X1 ◇ X3) ◇ (X0 ◇ X2))))) = X5 := superpose eq7 eq10
  have eq38 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X1) ◇ (X4 ◇ (X5 ◇ X2))) = X5 := superpose eq12 eq10
  have eq57 (X0 X3 X5 : G) : (X0 ◇ (X3 ◇ X5)) = X0 := superpose eq38 eq30
  have eq65 (X0 X1 X3 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ (X1 ◇ X3)))) = X5 := superpose eq57 eq37
  have eq77 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq57 eq65
  have eq78 (X0 X3 : G) : X0 = X3 := superpose eq77 eq77
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq98 eq78


@[equational_result]
theorem Equation19363_implies_Equation2 (G : Type*) [Magma G] (h : Equation19363 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq57 (X0 X4 : G) : X0 = X4 := superpose eq7 eq19
  have eq152 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq152 eq57


@[equational_result]
theorem Equation19364_implies_Equation2 (G : Type*) [Magma G] (h : Equation19364 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X1 ◇ X4) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq133 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq133 eq57


@[equational_result]
theorem Equation19366_implies_Equation2 (G : Type*) [Magma G] (h : Equation19366 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19367_implies_Equation2 (G : Type*) [Magma G] (h : Equation19367 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19368_implies_Equation2 (G : Type*) [Magma G] (h : Equation19368 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19369_implies_Equation2 (G : Type*) [Magma G] (h : Equation19369 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19371_implies_Equation2 (G : Type*) [Magma G] (h : Equation19371 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19372_implies_Equation2 (G : Type*) [Magma G] (h : Equation19372 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19373_implies_Equation2 (G : Type*) [Magma G] (h : Equation19373 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19374_implies_Equation2 (G : Type*) [Magma G] (h : Equation19374 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19376_implies_Equation2 (G : Type*) [Magma G] (h : Equation19376 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19377_implies_Equation2 (G : Type*) [Magma G] (h : Equation19377 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19378_implies_Equation2 (G : Type*) [Magma G] (h : Equation19378 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19379_implies_Equation2 (G : Type*) [Magma G] (h : Equation19379 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19381_implies_Equation2 (G : Type*) [Magma G] (h : Equation19381 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19382_implies_Equation2 (G : Type*) [Magma G] (h : Equation19382 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19383_implies_Equation2 (G : Type*) [Magma G] (h : Equation19383 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19384_implies_Equation2 (G : Type*) [Magma G] (h : Equation19384 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19385_implies_Equation2 (G : Type*) [Magma G] (h : Equation19385 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X3) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19388_implies_Equation2 (G : Type*) [Magma G] (h : Equation19388 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((((X2 ◇ X0) ◇ (X0 ◇ X2)) ◇ X3) ◇ (X3 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X0 ◇ X3)) = ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (((X3 ◇ X0) ◇ (X0 ◇ X3)) ◇ (X2 ◇ X3)))) := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (X2 ◇ X1) = (X0 ◇ ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X1)) ◇ X0)) := superpose eq7 eq9
  have eq52 (X0 X1 X2 X3 : G) : (X2 ◇ ((((X1 ◇ X3) ◇ (X3 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3)) = (X3 ◇ ((((((((X1 ◇ X3) ◇ (X3 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3) ◇ X3) ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((((X1 ◇ X3) ◇ (X3 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3))) ◇ X3)) := superpose eq18 eq18
  have eq58 (X0 X1 X2 : G) : (X1 ◇ X2) = ((((X1 ◇ X2) ◇ X0) ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0) := superpose eq7 eq18
  have eq60 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X3 ◇ X2)) = ((X0 ◇ X1) ◇ (X3 ◇ (((X2 ◇ X3) ◇ (X3 ◇ X2)) ◇ ((((X1 ◇ X2) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X2)))) := superpose eq18 eq10
  have eq69 (X0 X1 X2 X3 : G) : ((((X1 ◇ ((X3 ◇ X2) ◇ (X2 ◇ X3))) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X3)) ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X3 ◇ X2) ◇ (X2 ◇ X3))) = (X2 ◇ ((X0 ◇ X1) ◇ (((((X1 ◇ ((X3 ◇ X2) ◇ (X2 ◇ X3))) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X3)) ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X3 ◇ X2) ◇ (X2 ◇ X3))) ◇ ((X3 ◇ X2) ◇ (X2 ◇ X3))))) := superpose eq18 eq9
  have eq108 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X0 ◇ X1) ◇ (((((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) ◇ ((((X1 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ X3) ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X2 ◇ X3))) := superpose eq18 eq58
  have eq127 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X2))) = X3 := superpose eq58 eq7
  have eq154 (X0 X1 X2 X3 : G) : ((((X1 ◇ ((X3 ◇ X2) ◇ (X2 ◇ X3))) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X3)) ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X3 ◇ X2) ◇ (X2 ◇ X3))) = (X2 ◇ ((X0 ◇ X1) ◇ X2)) := superpose eq127 eq69
  have eq200 (X0 X1 X2 : G) : (X2 ◇ ((X0 ◇ X1) ◇ X2)) = X2 := superpose eq127 eq154
  have eq201 (X0 X1 X2 X3 : G) : (X2 ◇ ((((X1 ◇ X3) ◇ (X3 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X3)) = X3 := superpose eq200 eq52
  have eq212 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X3 ◇ X2)) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := superpose eq201 eq60
  have eq234 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X0 ◇ X1) ◇ (((X3 ◇ X2) ◇ (X2 ◇ X3)) ◇ (X2 ◇ X3))) ◇ ((X3 ◇ X2) ◇ (X2 ◇ X3))) := superpose eq212 eq108
  have eq244 (X2 X3 : G) : (X2 ◇ X3) = X2 := superpose eq127 eq234
  have eq245 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X2))) = X0 := superpose eq244 eq7
  have eq282 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq244 eq245
  have eq283 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq244 eq282
  have eq284 (X0 X3 : G) : X0 = X3 := superpose eq283 eq283
  have eq286 (X0 : G) : sK0 ≠ X0 := superpose eq284 eq8
  subsumption eq286 eq284


@[equational_result]
theorem Equation19389_implies_Equation2 (G : Type*) [Magma G] (h : Equation19389 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X0)) := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : (X1 ◇ X2) = ((X3 ◇ X4) ◇ X0) := superpose eq7 eq11
  have eq52 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq18
  have eq148 (X0 X4 : G) : X0 = X4 := superpose eq7 eq52
  have eq265 (X0 : G) : sK0 ≠ X0 := superpose eq148 eq8
  subsumption eq265 eq148


@[equational_result]
theorem Equation19392_implies_Equation2 (G : Type*) [Magma G] (h : Equation19392 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X2 ◇ X3)) = ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X0 ◇ ((((X2 ◇ X0) ◇ (X1 ◇ X2)) ◇ X3) ◇ X0)) = X3 := superpose eq7 eq7
  have eq28 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X1) ◇ X0)) ◇ (X2 ◇ X1)) = X0 := superpose eq7 eq9
  have eq53 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ X1)) := superpose eq28 eq10
  have eq62 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ (X1 ◇ X2))) = X0 := superpose eq53 eq7
  have eq120 (X0 X3 : G) : X0 = X3 := superpose eq62 eq62
  have eq129 (X0 : G) : sK0 ≠ X0 := superpose eq120 eq8
  subsumption eq129 eq120


@[equational_result]
theorem Equation19393_implies_Equation2 (G : Type*) [Magma G] (h : Equation19393 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ ((X3 ◇ X4) ◇ X0)) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X1 := superpose eq7 eq7
  have eq33 (X0 X2 : G) : X0 = X2 := superpose eq12 eq11
  have eq41 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq41 eq33


@[equational_result]
theorem Equation19396_implies_Equation2 (G : Type*) [Magma G] (h : Equation19396 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ (X3 ◇ X3)) = ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3)))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq7
  have eq12 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq7 eq11
  have eq14 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq11 eq7
  have eq21 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X2 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq11 eq10
  have eq25 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) ◇ (X1 ◇ X1)) = ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq11 eq10
  have eq48 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq12
  have eq54 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq12 eq7
  have eq60 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq48 eq14
  have eq62 (X0 X1 X2 X3 : G) : ((X3 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X1)) := superpose eq48 eq25
  have eq65 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X1)) := superpose eq60 eq62
  have eq68 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq7 eq54
  have eq69 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X2)) = X0 := superpose eq68 eq7
  have eq77 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq68 eq21
  have eq87 (X0 X1 X2 : G) : (X0 ◇ X1) = ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) := superpose eq68 eq65
  have eq111 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq68 eq69
  have eq115 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq111 eq69
  have eq117 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X1 ◇ X0)) = X1 := superpose eq111 eq77
  have eq127 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq115 eq87
  have eq135 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ X0) = X1 := superpose eq127 eq117
  have eq136 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq127 eq135
  have eq151 (X0 X2 : G) : X0 = X2 := superpose eq136 eq136
  have eq159 (X0 : G) : sK0 ≠ X0 := superpose eq151 eq8
  subsumption eq159 eq151


@[equational_result]
theorem Equation19397_implies_Equation2 (G : Type*) [Magma G] (h : Equation19397 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 X3 : G) : (X2 ◇ X0) = (X0 ◇ (X2 ◇ X3)) := superpose eq7 eq12
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq25 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ X0) = X2 := superpose eq15 eq12
  have eq39 (X0 X3 : G) : X0 = X3 := superpose eq25 eq16
  have eq62 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq62 eq39


@[equational_result]
theorem Equation19399_implies_Equation2 (G : Type*) [Magma G] (h : Equation19399 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq18 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq63 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq63 eq18


@[equational_result]
theorem Equation19400_implies_Equation2 (G : Type*) [Magma G] (h : Equation19400 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X0) ◇ (X4 ◇ X3)) = ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X5 ◇ (X2 ◇ X3)))) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq13 (X0 X3 X4 : G) : ((X3 ◇ X0) ◇ (X4 ◇ X3)) = X3 := superpose eq12 eq10
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X0 := superpose eq13 eq7
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq16 eq16
  have eq23 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq23 eq21


@[equational_result]
theorem Equation19401_implies_Equation2 (G : Type*) [Magma G] (h : Equation19401 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((((X2 ◇ X0) ◇ (X3 ◇ X3)) ◇ X4) ◇ (X5 ◇ X5))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X0 := superpose eq7 eq7
  have eq14 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ (X5 ◇ X5))) = X4 := superpose eq12 eq9
  have eq17 (X0 X3 : G) : (X0 ◇ X3) = X3 := superpose eq12 eq12
  have eq18 (X0 X4 X5 : G) : (X0 ◇ (X4 ◇ X5)) = X4 := superpose eq17 eq14
  have eq21 (X0 X4 X5 : G) : (X0 ◇ X5) = X4 := superpose eq17 eq18
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq21 eq21
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq24 eq22


@[equational_result]
theorem Equation19402_implies_Equation2 (G : Type*) [Magma G] (h : Equation19402 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19405_implies_Equation2 (G : Type*) [Magma G] (h : Equation19405 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq7 eq12
  have eq21 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq15 eq12
  have eq22 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ X1) ◇ (X0 ◇ X2))) = X0 := superpose eq21 eq7
  have eq29 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq21 eq22
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq21 eq29
  have eq31 (X0 X3 : G) : X0 = X3 := superpose eq30 eq30
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq33 eq31


@[equational_result]
theorem Equation19406_implies_Equation2 (G : Type*) [Magma G] (h : Equation19406 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ ((((X2 ◇ X1) ◇ (X0 ◇ X3)) ◇ (X1 ◇ X2)) ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X1 X2 X4 X5 : G) : (X0 ◇ (((X2 ◇ X1) ◇ (X1 ◇ X2)) ◇ (X4 ◇ X5))) = X4 := superpose eq12 eq9
  have eq18 (X0 X1 X2 X4 : G) : (X0 ◇ ((X2 ◇ X1) ◇ (X1 ◇ X2))) = X4 := superpose eq12 eq14
  have eq19 (X0 X1 X2 X4 : G) : (X0 ◇ (X2 ◇ X1)) = X4 := superpose eq12 eq18
  have eq22 (X0 X4 : G) : X0 = X4 := superpose eq19 eq19
  have eq31 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq31 eq22


@[equational_result]
theorem Equation19408_implies_Equation2 (G : Type*) [Magma G] (h : Equation19408 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19409_implies_Equation2 (G : Type*) [Magma G] (h : Equation19409 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19410_implies_Equation2 (G : Type*) [Magma G] (h : Equation19410 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19412_implies_Equation2 (G : Type*) [Magma G] (h : Equation19412 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19413_implies_Equation2 (G : Type*) [Magma G] (h : Equation19413 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19414_implies_Equation2 (G : Type*) [Magma G] (h : Equation19414 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19416_implies_Equation2 (G : Type*) [Magma G] (h : Equation19416 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19417_implies_Equation2 (G : Type*) [Magma G] (h : Equation19417 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19418_implies_Equation2 (G : Type*) [Magma G] (h : Equation19418 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19419_implies_Equation2 (G : Type*) [Magma G] (h : Equation19419 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X1) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19422_implies_Equation2 (G : Type*) [Magma G] (h : Equation19422 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : (X0 ◇ ((((X2 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X3 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))) ◇ ((((X2 ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))) ◇ X0)) := superpose eq7 eq7
  have eq28 (X0 X1 X2 : G) : (X0 ◇ X1) = (X2 ◇ X1) := superpose eq10 eq10
  have eq40 (X0 X2 X3 : G) : (X3 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))) = X0 := superpose eq7 eq28
  have eq92 (X0 X2 X3 : G) : (X0 ◇ (X0 ◇ (X3 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X2))))) = X3 := superpose eq40 eq9
  have eq111 (X0 X3 : G) : (X0 ◇ (X0 ◇ X0)) = X3 := superpose eq40 eq92
  have eq151 (X0 X1 : G) : X0 = X1 := superpose eq7 eq111
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq151 eq8
  subsumption eq168 eq151


@[equational_result]
theorem Equation19423_implies_Equation2 (G : Type*) [Magma G] (h : Equation19423 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((((X2 ◇ X2) ◇ (X0 ◇ X3)) ◇ ((X2 ◇ X2) ◇ (X0 ◇ X3))) ◇ (X4 ◇ X5))) = X4 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq14 (X0 X2 X4 X5 : G) : (X0 ◇ (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X4 ◇ X5))) = X4 := superpose eq12 eq9
  have eq18 (X0 X2 X4 : G) : (X0 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X4 := superpose eq12 eq14
  have eq19 (X0 X2 X4 : G) : (X0 ◇ (X2 ◇ X2)) = X4 := superpose eq12 eq18
  have eq22 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq39 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq39 eq22


@[equational_result]
theorem Equation19425_implies_Equation2 (G : Type*) [Magma G] (h : Equation19425 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19426_implies_Equation2 (G : Type*) [Magma G] (h : Equation19426 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation19427_implies_Equation2 (G : Type*) [Magma G] (h : Equation19427 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19429_implies_Equation2 (G : Type*) [Magma G] (h : Equation19429 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19430_implies_Equation2 (G : Type*) [Magma G] (h : Equation19430 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation19431_implies_Equation2 (G : Type*) [Magma G] (h : Equation19431 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19433_implies_Equation2 (G : Type*) [Magma G] (h : Equation19433 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19434_implies_Equation2 (G : Type*) [Magma G] (h : Equation19434 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19435_implies_Equation2 (G : Type*) [Magma G] (h : Equation19435 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19436_implies_Equation2 (G : Type*) [Magma G] (h : Equation19436 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19438_implies_Equation2 (G : Type*) [Magma G] (h : Equation19438 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (((X0 ◇ X1) ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ X1) := superpose eq12 eq12
  have eq56 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq21
  have eq158 (X0 X4 : G) : X0 = X4 := superpose eq7 eq56
  have eq302 (X0 : G) : sK0 ≠ X0 := superpose eq158 eq8
  subsumption eq302 eq158


@[equational_result]
theorem Equation19439_implies_Equation2 (G : Type*) [Magma G] (h : Equation19439 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((((X2 ◇ X3) ◇ (X0 ◇ X2)) ◇ X4) ◇ (X5 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X2))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq22 (X0 X1 X2 : G) : (X0 ◇ X2) = (X0 ◇ X1) := superpose eq12 eq12
  have eq137 (X0 X1 X5 : G) : (X0 ◇ X1) = X5 := superpose eq22 eq9
  have eq157 (X0 X4 : G) : X0 = X4 := superpose eq7 eq137
  have eq251 (X0 : G) : sK0 ≠ X0 := superpose eq157 eq8
  subsumption eq251 eq157


@[equational_result]
theorem Equation19440_implies_Equation2 (G : Type*) [Magma G] (h : Equation19440 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((((X2 ◇ X3) ◇ (X0 ◇ X3)) ◇ X4) ◇ (X5 ◇ X4))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ X3) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq26 (X0 X1 X2 X3 X4 X5 : G) : (((X0 ◇ X1) ◇ X2) ◇ ((X3 ◇ X4) ◇ (X5 ◇ X4))) = X5 := superpose eq12 eq7
  have eq50 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X1 ◇ ((((X2 ◇ X3) ◇ (X1 ◇ X3)) ◇ ((((X4 ◇ X5) ◇ (X6 ◇ X5)) ◇ X7) ◇ (X0 ◇ X7))) ◇ X0)) = X6 := superpose eq9 eq9
  have eq63 (X0 X1 X6 : G) : (X1 ◇ (X0 ◇ X0)) = X6 := superpose eq26 eq50
  have eq68 (X0 X3 : G) : X0 = X3 := superpose eq7 eq63
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq163 eq68


@[equational_result]
theorem Equation19441_implies_Equation2 (G : Type*) [Magma G] (h : Equation19441 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X3 ◇ X4) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq157 eq57


@[equational_result]
theorem Equation19443_implies_Equation2 (G : Type*) [Magma G] (h : Equation19443 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19444_implies_Equation2 (G : Type*) [Magma G] (h : Equation19444 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19445_implies_Equation2 (G : Type*) [Magma G] (h : Equation19445 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19446_implies_Equation2 (G : Type*) [Magma G] (h : Equation19446 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19448_implies_Equation2 (G : Type*) [Magma G] (h : Equation19448 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19449_implies_Equation2 (G : Type*) [Magma G] (h : Equation19449 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19450_implies_Equation2 (G : Type*) [Magma G] (h : Equation19450 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19451_implies_Equation2 (G : Type*) [Magma G] (h : Equation19451 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19453_implies_Equation2 (G : Type*) [Magma G] (h : Equation19453 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19454_implies_Equation2 (G : Type*) [Magma G] (h : Equation19454 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19455_implies_Equation2 (G : Type*) [Magma G] (h : Equation19455 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19456_implies_Equation2 (G : Type*) [Magma G] (h : Equation19456 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19458_implies_Equation2 (G : Type*) [Magma G] (h : Equation19458 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19459_implies_Equation2 (G : Type*) [Magma G] (h : Equation19459 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19460_implies_Equation2 (G : Type*) [Magma G] (h : Equation19460 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19461_implies_Equation2 (G : Type*) [Magma G] (h : Equation19461 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19462_implies_Equation2 (G : Type*) [Magma G] (h : Equation19462 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X3) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19464_implies_Equation2 (G : Type*) [Magma G] (h : Equation19464 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (X5 ◇ (X1 ◇ X2)))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq24 (X0 X1 X2 X3 X4 X5 : G) : ((X0 ◇ X3) ◇ ((X4 ◇ X5) ◇ (((X0 ◇ X1) ◇ X2) ◇ X0))) = X5 := superpose eq12 eq7
  have eq43 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9
  have eq61 (X0 X2 X3 X5 : G) : ((X0 ◇ X3) ◇ X2) = X5 := superpose eq43 eq24
  have eq179 (X0 X4 : G) : X0 = X4 := superpose eq7 eq61
  have eq285 (X0 : G) : sK0 ≠ X0 := superpose eq179 eq8
  subsumption eq285 eq179


@[equational_result]
theorem Equation19465_implies_Equation2 (G : Type*) [Magma G] (h : Equation19465 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (X5 ◇ ((X3 ◇ X0) ◇ (X0 ◇ X2))))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : (X5 ◇ X3) = ((X1 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X3))) ◇ ((X4 ◇ (X5 ◇ X3)) ◇ X0)) := superpose eq7 eq7
  have eq31 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) := superpose eq7 eq9
  have eq33 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := superpose eq9 eq9
  have eq51 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ X3)) ◇ ((X4 ◇ X3) ◇ X0)) = X3 := superpose eq33 eq7
  have eq57 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X0) := superpose eq33 eq7
  have eq70 (X0 X1 X2 X3 X4 X5 X6 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = ((X4 ◇ ((X5 ◇ X3) ◇ X0)) ◇ ((X6 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) ◇ X3)) := superpose eq33 eq11
  have eq86 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = ((X4 ◇ ((X5 ◇ X6) ◇ (X6 ◇ X3))) ◇ ((X0 ◇ X1) ◇ X6)) := superpose eq11 eq11
  have eq112 (X0 X1 X2 X3 X4 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = ((X4 ◇ ((X5 ◇ X3) ◇ X0)) ◇ ((X2 ◇ X0) ◇ X3)) := superpose eq57 eq70
  have eq113 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X0) ◇ X3)) = X0 := superpose eq51 eq112
  have eq137 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X1)) ◇ X3) = X1 := superpose eq113 eq86
  have eq138 (X0 X2 X3 : G) : (X2 ◇ X3) = (X0 ◇ X3) := superpose eq137 eq31
  have eq169 (X0 X1 X3 : G) : (X1 ◇ (X0 ◇ X1)) = X3 := superpose eq138 eq33
  have eq243 (X0 X3 : G) : X0 = X3 := superpose eq7 eq169
  have eq324 (X0 : G) : sK0 ≠ X0 := superpose eq243 eq8
  subsumption eq324 eq243


@[equational_result]
theorem Equation19466_implies_Equation2 (G : Type*) [Magma G] (h : Equation19466 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (X5 ◇ X4))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (X0 ◇ (X1 ◇ X2))) = X1 := superpose eq12 eq7
  have eq33 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X3 ◇ X4)))) = X1 := superpose eq12 eq9
  have eq53 (X1 X2 X3 : G) : (X2 ◇ X3) = X1 := superpose eq27 eq33
  have eq54 (X0 X4 : G) : X0 = X4 := superpose eq7 eq53
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq148 eq54


@[equational_result]
theorem Equation19467_implies_Equation2 (G : Type*) [Magma G] (h : Equation19467 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : (X0 ◇ ((X5 ◇ X6) ◇ (X6 ◇ X7))) = X6 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 : G) : (X4 ◇ X0) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq38 (X0 X1 X2 X3 X4 X5 : G) : (X3 ◇ ((X4 ◇ X5) ◇ ((X0 ◇ X1) ◇ X2))) = X5 := superpose eq12 eq9
  have eq39 (X0 X1 X2 X3 : G) : (X1 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := superpose eq9 eq9
  have eq55 (X1 X3 X5 : G) : (X3 ◇ X1) = X5 := superpose eq39 eq38
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq55
  have eq130 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq130 eq57


@[equational_result]
theorem Equation19469_implies_Equation2 (G : Type*) [Magma G] (h : Equation19469 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq18 (X0 X3 : G) : X0 = X3 := superpose eq12 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq18 eq8
  subsumption eq52 eq18


@[equational_result]
theorem Equation19470_implies_Equation2 (G : Type*) [Magma G] (h : Equation19470 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ X2) = (X0 ◇ X2) := superpose eq7 eq11
  have eq35 (X0 X2 X4 : G) : (X4 ◇ X2) = X0 := superpose eq11 eq25
  have eq131 (X0 X4 : G) : X0 = X4 := superpose eq7 eq35
  have eq238 (X0 : G) : sK0 ≠ X0 := superpose eq131 eq8
  subsumption eq238 eq131


@[equational_result]
theorem Equation19471_implies_Equation2 (G : Type*) [Magma G] (h : Equation19471 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ ((X1 ◇ X2) ◇ X4))) = X5 := superpose eq7 eq7
  have eq18 (X0 X1 X5 : G) : (X1 ◇ X0) = X5 := superpose eq9 eq9
  have eq69 (X0 X4 : G) : X0 = X4 := superpose eq7 eq18
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq69 eq8
  subsumption eq175 eq69


@[equational_result]
theorem Equation19472_implies_Equation2 (G : Type*) [Magma G] (h : Equation19472 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation19474_implies_Equation2 (G : Type*) [Magma G] (h : Equation19474 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X0) = X1 := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X0 ◇ (X2 ◇ X1)) = X1 := superpose eq7 eq12
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = X0 := superpose eq17 eq7
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq27 eq27
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq37 eq35


@[equational_result]
theorem Equation19475_implies_Equation2 (G : Type*) [Magma G] (h : Equation19475 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X5) ◇ (((X3 ◇ X0) ◇ (X2 ◇ X2)) ◇ ((X3 ◇ X0) ◇ (X2 ◇ X2))))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X4 X5 : G) : ((X5 ◇ X0) ◇ (X4 ◇ X4)) = ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X0)) ◇ X0) = X0 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X2 ◇ X2))) = X0 := superpose eq11 eq7
  have eq17 (X0 X4 X5 : G) : ((X5 ◇ X0) ◇ (X4 ◇ X4)) = X0 := superpose eq15 eq10
  have eq18 (X0 X5 : G) : (X0 ◇ X5) = X5 := superpose eq17 eq9
  have eq25 (X0 X4 X5 : G) : ((X5 ◇ X0) ◇ X4) = X0 := superpose eq18 eq17
  have eq28 (X0 X4 : G) : (X0 ◇ X4) = X0 := superpose eq18 eq25
  have eq31 (X0 X1 : G) : X0 = X1 := superpose eq18 eq28
  have eq33 (X0 : G) : sK0 ≠ X0 := superpose eq31 eq8
  subsumption eq33 eq31


@[equational_result]
theorem Equation19476_implies_Equation2 (G : Type*) [Magma G] (h : Equation19476 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X3 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq58 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq58 eq19


@[equational_result]
theorem Equation19477_implies_Equation2 (G : Type*) [Magma G] (h : Equation19477 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq55 eq19


@[equational_result]
theorem Equation19479_implies_Equation2 (G : Type*) [Magma G] (h : Equation19479 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq21 (X0 X4 : G) : X0 = X4 := superpose eq12 eq12
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq56 eq21


@[equational_result]
theorem Equation19480_implies_Equation2 (G : Type*) [Magma G] (h : Equation19480 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq48 eq17


@[equational_result]
theorem Equation19481_implies_Equation2 (G : Type*) [Magma G] (h : Equation19481 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X0) = X3 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19482_implies_Equation2 (G : Type*) [Magma G] (h : Equation19482 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19484_implies_Equation2 (G : Type*) [Magma G] (h : Equation19484 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X4 := superpose eq7 eq7
  have eq19 (X0 X5 : G) : X0 = X5 := superpose eq12 eq12
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq19 eq8
  subsumption eq57 eq19


@[equational_result]
theorem Equation19485_implies_Equation2 (G : Type*) [Magma G] (h : Equation19485 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X0) = X3 := superpose eq7 eq7
  have eq17 (X0 X3 : G) : X0 = X3 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq49 eq17


@[equational_result]
theorem Equation19486_implies_Equation2 (G : Type*) [Magma G] (h : Equation19486 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 : G) : ((X1 ◇ X2) ◇ X0) = X5 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19487_implies_Equation2 (G : Type*) [Magma G] (h : Equation19487 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19488_implies_Equation2 (G : Type*) [Magma G] (h : Equation19488 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ X0) = X4 := superpose eq7 eq7
  have eq16 (X0 X6 : G) : X0 = X6 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation19490_implies_Equation2 (G : Type*) [Magma G] (h : Equation19490 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X4 X5 : G) : (X0 ◇ ((X4 ◇ (X1 ◇ X2)) ◇ (X5 ◇ (X1 ◇ X2)))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X1) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X3 X4 X5 : G) : (((X4 ◇ ((X3 ◇ X1) ◇ (X0 ◇ X1))) ◇ X5) ◇ X4) = X0 := superpose eq7 eq12
  have eq37 (X0 X1 X2 X6 : G) : (X1 ◇ ((X2 ◇ X0) ◇ (X6 ◇ X0))) = X6 := superpose eq7 eq9
  have eq61 (X0 X4 X5 : G) : ((X0 ◇ X5) ◇ X4) = X0 := superpose eq37 eq13
  have eq73 (X1 X2 X6 : G) : (X1 ◇ X2) = X6 := superpose eq61 eq37
  have eq76 (X0 X3 : G) : X0 = X3 := superpose eq73 eq73
  have eq88 (X0 : G) : sK0 ≠ X0 := superpose eq76 eq8
  subsumption eq88 eq76


@[equational_result]
theorem Equation19491_implies_Equation2 (G : Type*) [Magma G] (h : Equation19491 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (X2 ◇ X3) := superpose eq12 eq12
  have eq64 (X0 X4 X5 : G) : (X4 ◇ X5) = X0 := superpose eq7 eq21
  have eq172 (X0 X4 : G) : X0 = X4 := superpose eq7 eq64
  have eq321 (X0 : G) : sK0 ≠ X0 := superpose eq172 eq8
  subsumption eq321 eq172


@[equational_result]
theorem Equation19492_implies_Equation2 (G : Type*) [Magma G] (h : Equation19492 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ (X0 ◇ X3)) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X1 ◇ X0)) = X0 := superpose eq7 eq12
  have eq37 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X0 := superpose eq16 eq7
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq37 eq37
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq55 eq44


@[equational_result]
theorem Equation19493_implies_Equation2 (G : Type*) [Magma G] (h : Equation19493 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : (X4 ◇ X3) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq57 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq157 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq157 eq57


@[equational_result]
theorem Equation19495_implies_Equation2 (G : Type*) [Magma G] (h : Equation19495 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19496_implies_Equation2 (G : Type*) [Magma G] (h : Equation19496 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19497_implies_Equation2 (G : Type*) [Magma G] (h : Equation19497 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19498_implies_Equation2 (G : Type*) [Magma G] (h : Equation19498 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19500_implies_Equation2 (G : Type*) [Magma G] (h : Equation19500 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19501_implies_Equation2 (G : Type*) [Magma G] (h : Equation19501 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19502_implies_Equation2 (G : Type*) [Magma G] (h : Equation19502 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19503_implies_Equation2 (G : Type*) [Magma G] (h : Equation19503 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19505_implies_Equation2 (G : Type*) [Magma G] (h : Equation19505 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19506_implies_Equation2 (G : Type*) [Magma G] (h : Equation19506 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19507_implies_Equation2 (G : Type*) [Magma G] (h : Equation19507 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19508_implies_Equation2 (G : Type*) [Magma G] (h : Equation19508 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19510_implies_Equation2 (G : Type*) [Magma G] (h : Equation19510 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19511_implies_Equation2 (G : Type*) [Magma G] (h : Equation19511 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19512_implies_Equation2 (G : Type*) [Magma G] (h : Equation19512 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19513_implies_Equation2 (G : Type*) [Magma G] (h : Equation19513 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19514_implies_Equation2 (G : Type*) [Magma G] (h : Equation19514 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X1) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19516_implies_Equation2 (G : Type*) [Magma G] (h : Equation19516 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 X5 : G) : (((X4 ◇ X5) ◇ ((X3 ◇ X2) ◇ (X0 ◇ X1))) ◇ X4) = X0 := superpose eq7 eq12
  have eq19 (X0 X1 X2 X3 X4 : G) : (X0 ◇ X4) = (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X4))) := superpose eq7 eq12
  have eq33 (X0 X1 X4 : G) : ((X0 ◇ X1) ◇ X4) = X0 := superpose eq19 eq13
  have eq41 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ X3) = X0 := superpose eq33 eq7
  have eq46 (X0 X4 : G) : X0 = X4 := superpose eq41 eq41
  have eq48 (X0 : G) : sK0 ≠ X0 := superpose eq46 eq8
  subsumption eq48 eq46


@[equational_result]
theorem Equation19517_implies_Equation2 (G : Type*) [Magma G] (h : Equation19517 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X2))) ◇ (X5 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X2))))) = X5 := superpose eq7 eq7
  have eq12 (X0 X2 X3 X4 : G) : (X0 ◇ (X0 ◇ (X4 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X2))))) = X4 := superpose eq7 eq9
  have eq48 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = X1 := superpose eq9 eq12
  have eq119 (X0 X2 : G) : X0 = X2 := superpose eq7 eq48
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq119 eq8
  subsumption eq163 eq119


@[equational_result]
theorem Equation19518_implies_Equation2 (G : Type*) [Magma G] (h : Equation19518 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X3))) ◇ (X5 ◇ X4))) = X5 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 X5 : G) : ((X4 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X3))) ◇ X5) = X0 := superpose eq7 eq12
  have eq32 (X0 X5 : G) : (X0 ◇ X0) = X5 := superpose eq13 eq9
  have eq33 (X0 X2 : G) : X0 = X2 := superpose eq7 eq32
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq54 eq33


@[equational_result]
theorem Equation19519_implies_Equation2 (G : Type*) [Magma G] (h : Equation19519 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 X6 X7 : G) : (X0 ◇ ((X5 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X4))) ◇ (X6 ◇ X7))) = X6 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 : G) : (X4 ◇ X2) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 X5 X6 : G) : ((X5 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X4))) ◇ X6) = X0 := superpose eq7 eq12
  have eq32 (X0 X6 : G) : (X0 ◇ X0) = X6 := superpose eq13 eq9
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq7 eq32
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq54 eq33


@[equational_result]
theorem Equation19521_implies_Equation2 (G : Type*) [Magma G] (h : Equation19521 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19522_implies_Equation2 (G : Type*) [Magma G] (h : Equation19522 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19523_implies_Equation2 (G : Type*) [Magma G] (h : Equation19523 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19524_implies_Equation2 (G : Type*) [Magma G] (h : Equation19524 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19526_implies_Equation2 (G : Type*) [Magma G] (h : Equation19526 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19527_implies_Equation2 (G : Type*) [Magma G] (h : Equation19527 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19528_implies_Equation2 (G : Type*) [Magma G] (h : Equation19528 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19529_implies_Equation2 (G : Type*) [Magma G] (h : Equation19529 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19531_implies_Equation2 (G : Type*) [Magma G] (h : Equation19531 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19532_implies_Equation2 (G : Type*) [Magma G] (h : Equation19532 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19533_implies_Equation2 (G : Type*) [Magma G] (h : Equation19533 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19534_implies_Equation2 (G : Type*) [Magma G] (h : Equation19534 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19536_implies_Equation2 (G : Type*) [Magma G] (h : Equation19536 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19537_implies_Equation2 (G : Type*) [Magma G] (h : Equation19537 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19538_implies_Equation2 (G : Type*) [Magma G] (h : Equation19538 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19539_implies_Equation2 (G : Type*) [Magma G] (h : Equation19539 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19540_implies_Equation2 (G : Type*) [Magma G] (h : Equation19540 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X2) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19542_implies_Equation2 (G : Type*) [Magma G] (h : Equation19542 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq30 (X0 X1 X2 : G) : (X1 ◇ X1) = (X0 ◇ X2) := superpose eq7 eq12
  have eq50 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq7 eq30
  have eq130 (X0 X4 : G) : X0 = X4 := superpose eq7 eq50
  have eq303 (X0 : G) : sK0 ≠ X0 := superpose eq130 eq8
  subsumption eq303 eq130


@[equational_result]
theorem Equation19543_implies_Equation2 (G : Type*) [Magma G] (h : Equation19543 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X4) ◇ (X5 ◇ ((X3 ◇ X3) ◇ (X0 ◇ X2))))) = X5 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq20 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X4) ◇ ((X5 ◇ X5) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) = X4 := superpose eq11 eq7
  have eq23 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X4 := superpose eq11 eq7
  have eq27 (X3 X4 X5 : G) : ((X3 ◇ X4) ◇ X5) = X4 := superpose eq23 eq20
  have eq30 (X0 X3 X4 X5 : G) : (X0 ◇ ((X4 ◇ X4) ◇ (X5 ◇ X3))) = X5 := superpose eq27 eq9
  have eq37 (X0 X4 X5 : G) : (X0 ◇ X4) = X5 := superpose eq27 eq30
  have eq40 (X0 X3 : G) : X0 = X3 := superpose eq37 eq37
  have eq50 (X0 : G) : sK0 ≠ X0 := superpose eq40 eq8
  subsumption eq50 eq40


@[equational_result]
theorem Equation19544_implies_Equation2 (G : Type*) [Magma G] (h : Equation19544 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X4 X5 : G) : (X0 ◇ ((X4 ◇ X4) ◇ (X5 ◇ X4))) = X5 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X4 ◇ ((X3 ◇ X3) ◇ (X0 ◇ X3))))) = X4 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X4 := superpose eq9 eq10
  have eq44 (X0 X3 : G) : X0 = X3 := superpose eq7 eq13
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq65 eq44


@[equational_result]
theorem Equation19545_implies_Equation2 (G : Type*) [Magma G] (h : Equation19545 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 : G) : (X4 ◇ X4) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq12
  have eq53 (X0 X3 : G) : X0 = X3 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation19547_implies_Equation2 (G : Type*) [Magma G] (h : Equation19547 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19548_implies_Equation2 (G : Type*) [Magma G] (h : Equation19548 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation19549_implies_Equation2 (G : Type*) [Magma G] (h : Equation19549 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19550_implies_Equation2 (G : Type*) [Magma G] (h : Equation19550 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19552_implies_Equation2 (G : Type*) [Magma G] (h : Equation19552 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19553_implies_Equation2 (G : Type*) [Magma G] (h : Equation19553 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19554_implies_Equation2 (G : Type*) [Magma G] (h : Equation19554 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19555_implies_Equation2 (G : Type*) [Magma G] (h : Equation19555 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19557_implies_Equation2 (G : Type*) [Magma G] (h : Equation19557 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19558_implies_Equation2 (G : Type*) [Magma G] (h : Equation19558 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19559_implies_Equation2 (G : Type*) [Magma G] (h : Equation19559 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19560_implies_Equation2 (G : Type*) [Magma G] (h : Equation19560 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19562_implies_Equation2 (G : Type*) [Magma G] (h : Equation19562 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19563_implies_Equation2 (G : Type*) [Magma G] (h : Equation19563 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19564_implies_Equation2 (G : Type*) [Magma G] (h : Equation19564 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19565_implies_Equation2 (G : Type*) [Magma G] (h : Equation19565 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19566_implies_Equation2 (G : Type*) [Magma G] (h : Equation19566 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X3) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19568_implies_Equation2 (G : Type*) [Magma G] (h : Equation19568 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X0 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X5) = (((X0 ◇ X1) ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq31 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ X3) := superpose eq7 eq12
  have eq53 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq31
  have eq136 (X0 X5 : G) : X0 = X5 := superpose eq7 eq53
  have eq311 (X0 : G) : sK0 ≠ X0 := superpose eq136 eq8
  subsumption eq311 eq136


@[equational_result]
theorem Equation19569_implies_Equation2 (G : Type*) [Magma G] (h : Equation19569 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X0 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X7 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X7 ◇ X2))) = X7 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X4 X5 : G) : (X4 ◇ X5) = ((X1 ◇ (X0 ◇ X2)) ◇ X0) := superpose eq7 eq7
  have eq32 (X0 X1 X2 X5 : G) : (X1 ◇ X2) = (X0 ◇ X5) := superpose eq10 eq12
  have eq53 (X0 X5 X6 : G) : (X5 ◇ X6) = X0 := superpose eq7 eq32
  have eq148 (X0 X5 : G) : X0 = X5 := superpose eq7 eq53
  have eq329 (X0 : G) : sK0 ≠ X0 := superpose eq148 eq8
  subsumption eq329 eq148


@[equational_result]
theorem Equation19570_implies_Equation2 (G : Type*) [Magma G] (h : Equation19570 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X0 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X5 : G) : (X3 ◇ X5) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq126 eq53


@[equational_result]
theorem Equation19571_implies_Equation2 (G : Type*) [Magma G] (h : Equation19571 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X0 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X5 X6 X7 : G) : (X0 ◇ ((X5 ◇ X6) ◇ (X7 ◇ X6))) = X7 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X5 X6 X7 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X7 ◇ ((X5 ◇ X6) ◇ (X0 ◇ X6))))) = X7 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X7 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X7 := superpose eq9 eq10
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq13
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq65 eq44


@[equational_result]
theorem Equation19572_implies_Equation2 (G : Type*) [Magma G] (h : Equation19572 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X0 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X5 X6 : G) : (X5 ◇ X6) = ((X1 ◇ X2) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq53 (X0 X6 : G) : X0 = X6 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation19574_implies_Equation2 (G : Type*) [Magma G] (h : Equation19574 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19575_implies_Equation2 (G : Type*) [Magma G] (h : Equation19575 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19576_implies_Equation2 (G : Type*) [Magma G] (h : Equation19576 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19577_implies_Equation2 (G : Type*) [Magma G] (h : Equation19577 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19578_implies_Equation2 (G : Type*) [Magma G] (h : Equation19578 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X1 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19580_implies_Equation2 (G : Type*) [Magma G] (h : Equation19580 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X2 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19581_implies_Equation2 (G : Type*) [Magma G] (h : Equation19581 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X2 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19582_implies_Equation2 (G : Type*) [Magma G] (h : Equation19582 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X2 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19583_implies_Equation2 (G : Type*) [Magma G] (h : Equation19583 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X2 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation19584_implies_Equation2 (G : Type*) [Magma G] (h : Equation19584 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X2 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19586_implies_Equation2 (G : Type*) [Magma G] (h : Equation19586 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X3 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19587_implies_Equation2 (G : Type*) [Magma G] (h : Equation19587 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X3 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19588_implies_Equation2 (G : Type*) [Magma G] (h : Equation19588 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X3 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19589_implies_Equation2 (G : Type*) [Magma G] (h : Equation19589 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X3 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation19590_implies_Equation2 (G : Type*) [Magma G] (h : Equation19590 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X3 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19592_implies_Equation2 (G : Type*) [Magma G] (h : Equation19592 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X4 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19593_implies_Equation2 (G : Type*) [Magma G] (h : Equation19593 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X4 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19594_implies_Equation2 (G : Type*) [Magma G] (h : Equation19594 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X4 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19595_implies_Equation2 (G : Type*) [Magma G] (h : Equation19595 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X4 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19596_implies_Equation2 (G : Type*) [Magma G] (h : Equation19596 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X4 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19598_implies_Equation2 (G : Type*) [Magma G] (h : Equation19598 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X5 ◇ X1))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19599_implies_Equation2 (G : Type*) [Magma G] (h : Equation19599 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X5 ◇ X2))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19600_implies_Equation2 (G : Type*) [Magma G] (h : Equation19600 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X5 ◇ X3))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19601_implies_Equation2 (G : Type*) [Magma G] (h : Equation19601 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X5 ◇ X4))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19602_implies_Equation2 (G : Type*) [Magma G] (h : Equation19602 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X5 ◇ X5))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X6 : G) : X0 = X6 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19603_implies_Equation2 (G : Type*) [Magma G] (h : Equation19603 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X4) ◇ (X5 ◇ X6))) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq17 (X0 X7 : G) : X0 = X7 := superpose eq7 eq7
  have eq19 (X0 : G) : sK0 ≠ X0 := superpose eq17 eq8
  subsumption eq19 eq17


@[equational_result]
theorem Equation19819_implies_Equation2 (G : Type*) [Magma G] (h : Equation19819 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ X0) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq11 eq11
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X2)) := superpose eq11 eq7
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X2)) := superpose eq12 eq10
  have eq20 (X0 X1 X2 : G) : (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq13 eq15
  have eq39 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X2)) = X0 := superpose eq11 eq18
  have eq70 (X0 X1 : G) : (X1 ◇ X0) = X0 := superpose eq39 eq20
  have eq72 (X0 X2 : G) : (X0 ◇ X2) = X0 := superpose eq70 eq39
  have eq125 (X0 X1 : G) : X0 = X1 := superpose eq70 eq72
  have eq127 (X0 : G) : sK0 ≠ X0 := superpose eq125 eq8
  subsumption eq127 eq125


@[equational_result]
theorem Equation19822_implies_Equation2 (G : Type*) [Magma G] (h : Equation19822 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq11 eq11
  have eq14 (X0 X1 : G) : (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := superpose eq11 eq11
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq13 eq12
  have eq22 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X2)) := superpose eq19 eq10
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq11 eq22
  have eq26 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X2)) := superpose eq22 eq22
  have eq29 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq22
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := superpose eq22 eq11
  have eq33 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := superpose eq22 eq26
  have eq34 (X0 X1 X2 : G) : (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := superpose eq33 eq25
  have eq36 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X1 := superpose eq33 eq14
  have eq38 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X1) ◇ X2) := superpose eq34 eq19
  have eq45 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = X1 := superpose eq29 eq38
  have eq47 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq45 eq31
  have eq49 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq47 eq36
  have eq52 (X0 X2 : G) : X0 = X2 := superpose eq49 eq49
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq52 eq8
  subsumption eq72 eq52


@[equational_result]
theorem Equation19824_implies_Equation2 (G : Type*) [Magma G] (h : Equation19824 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X0) = (((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X0)) = X3 := superpose eq7 eq10
  have eq18 (X0 X1 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq10
  have eq26 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)))) := superpose eq11 eq11
  have eq46 (X0 X2 : G) : ((X0 ◇ X2) ◇ ((X2 ◇ X0) ◇ X0)) = X2 := superpose eq18 eq10
  have eq51 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = ((X0 ◇ ((((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq18 eq7
  have eq96 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) := superpose eq18 eq46
  have eq97 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq46 eq10
  have eq104 (X0 : G) : (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq46 eq18
  have eq135 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := superpose eq7 eq16
  have eq155 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := superpose eq135 eq104
  have eq159 (X0 X1 : G) : (X0 ◇ ((X0 ◇ ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1)) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0))) = X0 := superpose eq97 eq7
  have eq236 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq155 eq10
  have eq238 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0))) := superpose eq155 eq10
  have eq261 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := superpose eq236 eq238
  have eq262 (X0 : G) : (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq261 eq97
  have eq265 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0))) = X0 := superpose eq261 eq159
  have eq281 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq261 eq262
  have eq282 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq281 eq261
  have eq285 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose eq282 eq26
  have eq292 (X0 X1 : G) : (X0 ◇ ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) = X0 := superpose eq282 eq265
  have eq293 (X0 X1 : G) : (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := superpose eq282 eq292
  have eq294 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ X0) := superpose eq293 eq96
  have eq295 (X0 X1 : G) : ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := superpose eq282 eq294
  have eq305 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq295 eq285
  have eq313 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq295 eq51
  have eq330 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq295 eq305
  have eq331 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := superpose eq282 eq330
  have eq337 (X0 X1 : G) : (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq282 eq313
  have eq419 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0)) := superpose eq331 eq46
  have eq432 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X0)) := superpose eq295 eq419
  have eq433 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := superpose eq282 eq432
  have eq434 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq282 eq433
  have eq472 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq434 eq337
  have eq584 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := superpose eq7 eq434
  have eq622 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ X0)) = X2 := superpose eq584 eq46
  have eq767 (X0 X1 : G) : (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := superpose eq434 eq622
  have eq1067 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = X0 := superpose eq584 eq767
  have eq1109 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ X0) := superpose eq1067 eq472
  have eq1119 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq282 eq1109
  have eq1121 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq1119 eq10
  have eq1334 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = X2 := superpose eq1119 eq1121
  have eq1335 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ X2) = X2 := superpose eq1119 eq1334
  have eq1336 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq1119 eq1335
  have eq1475 (X0 X1 : G) : X0 = X1 := superpose eq1336 eq1119
  have eq1493 (X0 : G) : sK0 ≠ X0 := superpose eq1475 eq8
  subsumption eq1493 eq1475


@[equational_result]
theorem Equation19826_implies_Equation2 (G : Type*) [Magma G] (h : Equation19826 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X2 ◇ X0) ◇ X5)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq12
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq15 eq15
  have eq65 (X0 X2 X5 : G) : (X0 ◇ ((X2 ◇ X0) ◇ X5)) = X2 := superpose eq42 eq10
  have eq77 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq42 eq65
  have eq85 (X0 X2 : G) : X0 = X2 := superpose eq12 eq77
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq85 eq8
  subsumption eq94 eq85


@[equational_result]
theorem Equation19828_implies_Equation2 (G : Type*) [Magma G] (h : Equation19828 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X1) = (X0 ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X3 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X1))) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X3) = ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : (((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq11 eq11
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X1) = ((((X0 ◇ (X3 ◇ X0)) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X1)) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X0) := superpose eq7 eq11
  have eq15 (X0 X1 X3 : G) : (X1 ◇ X0) = ((((X0 ◇ (X3 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X0) := superpose eq11 eq11
  have eq16 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (((X2 ◇ X0) ◇ X0) ◇ X1)) := superpose eq11 eq7
  have eq18 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) ◇ (X2 ◇ X0))) := superpose eq7 eq10
  have eq21 (X0 X1 X3 X4 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = ((X4 ◇ (((X1 ◇ X0) ◇ X0) ◇ X3)) ◇ (((((X1 ◇ X0) ◇ X0) ◇ X3) ◇ (X1 ◇ X0)) ◇ X4)) := superpose eq11 eq10
  have eq43 (X0 X1 X3 X4 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = ((X1 ◇ X0) ◇ (((((X1 ◇ X0) ◇ X0) ◇ X3) ◇ (X4 ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) ◇ (X3 ◇ (X1 ◇ X0)))) := superpose eq11 eq9
  have eq71 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0))) := superpose eq13 eq16
  have eq73 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ X2) = ((X0 ◇ X1) ◇ (((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq16 eq16
  have eq75 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X1)) ◇ X3)) = X0 := superpose eq7 eq16
  have eq855 (X0 X1 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0)) := superpose eq18 eq21
  have eq1111 (X0 X1 X2 X3 : G) : (X0 ◇ X1) = (((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq15 eq43
  have eq1165 (X0 X1 X2 X3 : G) : ((X3 ◇ X0) ◇ ((X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ X2)) ◇ X3)) = X0 := superpose eq43 eq75
  have eq1227 (X0 X1 X2 X3 : G) : ((X3 ◇ X1) ◇ ((X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ X1)))) ◇ X3)) = X1 := superpose eq71 eq1165
  have eq1323 (X0 X1 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := superpose eq7 eq1227
  have eq1446 (X0 X1 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq7 eq1323
  have eq1455 (X0 : G) : ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X0 := superpose eq1323 eq1323
  have eq1468 (X0 X1 X2 : G) : ((((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := superpose eq1323 eq75
  have eq1598 (X0 : G) : (X0 ◇ (X0 ◇ X0)) = X0 := superpose eq1455 eq13
  have eq1764 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X1)) = X0 := superpose eq1598 eq7
  have eq1821 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq1598 eq1323
  have eq1825 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X0) := superpose eq1598 eq14
  have eq1842 (X0 : G) : (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := superpose eq1764 eq1821
  have eq1843 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq1598 eq1842
  have eq1852 (X0 X1 X2 : G) : (((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := superpose eq1843 eq1468
  have eq1854 (X0 X1 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) ◇ X0)) := superpose eq1843 eq855
  have eq1905 (X0 X1 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := superpose eq1852 eq1854
  have eq1906 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) ◇ X0) := superpose eq1843 eq1905
  have eq1907 (X0 X1 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := superpose eq1446 eq1906
  have eq1955 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) := superpose eq1843 eq1825
  have eq1956 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq1843 eq1955
  have eq1960 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := superpose eq1956 eq1907
  have eq1964 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X0 := superpose eq1960 eq1956
  have eq1988 (X0 X1 X2 : G) : (X0 ◇ X1) = (((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1))))) := superpose eq1964 eq1111
  have eq2383 (X0 X1 : G) : (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := superpose eq1964 eq1988
  have eq2384 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq1964 eq2383
  have eq2385 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := superpose eq1843 eq2384
  have eq2386 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq1964 eq2385
  have eq2395 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ (((X1 ◇ X2) ◇ X2) ◇ (X2 ◇ (X0 ◇ X1)))) := superpose eq2386 eq73
  have eq2470 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ X2) := superpose eq2386 eq2395
  have eq2471 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = X2 := superpose eq2386 eq2470
  have eq2472 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq2386 eq2471
  have eq2473 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq2386 eq2472
  have eq3088 (X0 X1 : G) : X0 = X1 := superpose eq2386 eq2473
  have eq3107 (X0 : G) : sK0 ≠ X0 := superpose eq3088 eq8
  subsumption eq3107 eq3088


@[equational_result]
theorem Equation19829_implies_Equation2 (G : Type*) [Magma G] (h : Equation19829 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X2) = (X0 ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X2))) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X2) = ((X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X2)) ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X2) ◇ X0) ◇ (X3 ◇ X0))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X0)))) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1)))) := superpose eq7 eq11
  have eq24 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X2) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0)) := superpose eq9 eq9
  have eq46 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) = ((X3 ◇ (((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (((((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) ◇ (X4 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))))) := superpose eq11 eq10
  have eq52 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X0) = ((X2 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X0)) ◇ (X0 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)))) := superpose eq7 eq10
  have eq60 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = ((X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq72 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X2) = (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) := superpose eq60 eq24
  have eq78 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = ((X2 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) ◇ (X0 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)))) := superpose eq72 eq52
  have eq91 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = ((X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) ◇ (X1 ◇ X0)) := superpose eq7 eq60
  have eq92 (X0 X1 : G) : ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ X0) := superpose eq7 eq60
  have eq106 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq92 eq7
  have eq107 (X0 X1 X3 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X3 ◇ X0))) := superpose eq92 eq10
  have eq108 (X0 X1 : G) : (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1)))) := superpose eq92 eq12
  have eq128 (X0 X2 X3 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))) := superpose eq92 eq78
  have eq146 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))) = X0 := superpose eq106 eq128
  have eq197 (X0 X1 X2 : G) : (((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) = ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) := superpose eq11 eq92
  have eq199 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := superpose eq106 eq92
  have eq201 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq92 eq92
  have eq203 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X1)) = X1 := superpose eq92 eq106
  have eq204 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X0))) := superpose eq92 eq107
  have eq206 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) := superpose eq92 eq107
  have eq208 (X0 X1 : G) : (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq106 eq199
  have eq229 (X0 X1 : G) : ((X0 ◇ X0) ◇ X1) = (X1 ◇ X1) := superpose eq208 eq206
  have eq231 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := superpose eq229 eq204
  have eq232 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq229 eq208
  have eq235 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ (X1 ◇ X1)) ◇ X0) := superpose eq203 eq231
  have eq248 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X0 ◇ X0)))))) := superpose eq146 eq11
  have eq250 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X0) ◇ (X2 ◇ X0)) := superpose eq146 eq92
  have eq261 (X0 X1 : G) : (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := superpose eq235 eq248
  have eq270 (X0 X2 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X2 ◇ X0)) := superpose eq261 eq250
  have eq271 (X0 X2 : G) : ((X0 ◇ X0) ◇ (X2 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := superpose eq92 eq270
  have eq272 (X0 X2 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X2 ◇ X0)) := superpose eq201 eq271
  have eq273 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq232 eq272
  have eq275 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = (((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq273 eq197
  have eq280 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = X0 := superpose eq273 eq106
  have eq281 (X0 X1 : G) : (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := superpose eq273 eq108
  have eq304 (X0 X1 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = ((X3 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) ◇ (((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) ◇ (X4 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))))) := superpose eq275 eq46
  have eq307 (X0 X1 X3 X4 : G) : (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = ((X3 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ (X4 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1)))))) := superpose eq273 eq304
  have eq311 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ X0)) = ((X2 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X1 ◇ X0)) := superpose eq280 eq91
  have eq312 (X0 X1 X2 : G) : (X1 ◇ (X1 ◇ X1)) = (((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq280 eq275
  have eq317 (X1 X3 X4 : G) : (X1 ◇ (X1 ◇ X1)) = ((X3 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X4 ◇ (X1 ◇ (X1 ◇ X1))))) := superpose eq280 eq307
  have eq325 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := superpose eq273 eq311
  have eq326 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X1 ◇ X0)) = X0 := superpose eq273 eq325
  have eq327 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq273 eq312
  have eq328 (X0 X1 X2 : G) : (X1 ◇ X1) = (X1 ◇ (X2 ◇ (X0 ◇ X1))) := superpose eq326 eq327
  have eq329 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X1 := superpose eq273 eq328
  have eq338 (X1 X3 X4 : G) : (X1 ◇ X1) = ((X3 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X4 ◇ (X1 ◇ X1)))) := superpose eq273 eq317
  have eq339 (X1 X3 X4 : G) : ((X3 ◇ X1) ◇ (X1 ◇ (X4 ◇ X1))) = X1 := superpose eq273 eq338
  have eq340 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq329 eq281
  have eq341 (X1 X3 : G) : ((X3 ◇ X1) ◇ X1) = X1 := superpose eq340 eq339
  have eq347 (X1 X3 : G) : (X3 ◇ X1) = X1 := superpose eq340 eq341
  have eq350 (X0 X1 : G) : X0 = X1 := superpose eq340 eq347
  have eq352 (X0 : G) : sK0 ≠ X0 := superpose eq350 eq8
  subsumption eq352 eq350


@[equational_result]
theorem Equation19830_implies_Equation2 (G : Type*) [Magma G] (h : Equation19830 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X4)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq21 (X0 X2 X3 X4 : G) : ((X3 ◇ X0) ◇ ((X2 ◇ X0) ◇ X4)) = X0 := superpose eq12 eq11
  have eq24 (X0 X1 X3 : G) : (X1 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := superpose eq12 eq11
  have eq31 (X0 X1 X2 X3 : G) : (X1 ◇ X3) = ((X2 ◇ (X1 ◇ X3)) ◇ (X0 ◇ X1)) := superpose eq11 eq12
  have eq48 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq12 eq24
  have eq71 (X1 X3 : G) : (X1 ◇ X3) = X1 := superpose eq48 eq31
  have eq93 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ (X2 ◇ X0)) = X0 := superpose eq71 eq21
  have eq104 (X0 X2 X3 : G) : ((X3 ◇ X0) ◇ X2) = X0 := superpose eq71 eq93
  have eq105 (X0 X2 X3 : G) : (X3 ◇ X2) = X0 := superpose eq71 eq104
  have eq106 (X0 X3 : G) : X0 = X3 := superpose eq105 eq105
  have eq111 (X0 : G) : sK0 ≠ X0 := superpose eq106 eq8
  subsumption eq111 eq106


@[equational_result]
theorem Equation19832_implies_Equation2 (G : Type*) [Magma G] (h : Equation19832 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X3) ◇ ((X3 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X1)) := superpose eq11 eq11
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X1)))) := superpose eq11 eq7
  have eq30 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq39 (X0 X1 X2 : G) : ((((X1 ◇ X0) ◇ X2) ◇ X2) ◇ X1) = X2 := superpose eq30 eq30
  have eq49 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq30 eq7
  have eq102 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq39 eq39
  have eq122 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq102 eq15
  have eq128 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ (X2 ◇ X0)) ◇ X0)) := superpose eq102 eq18
  have eq130 (X0 X1 : G) : (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := superpose eq102 eq11
  have eq132 (X0 X1 : G) : ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := superpose eq102 eq122
  have eq163 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0) := superpose eq130 eq39
  have eq165 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) := superpose eq132 eq163
  have eq166 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = X2 := superpose eq39 eq165
  have eq172 (X0 X1 : G) : (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := superpose eq166 eq128
  have eq243 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq49 eq172
  have eq244 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X0)) = X2 := superpose eq243 eq49
  have eq256 (X1 X2 : G) : ((X1 ◇ X2) ◇ X2) = X2 := superpose eq243 eq244
  have eq257 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq243 eq256
  have eq262 (X0 X1 : G) : X0 = X1 := superpose eq243 eq257
  have eq264 (X0 : G) : sK0 ≠ X0 := superpose eq262 eq8
  subsumption eq264 eq262


@[equational_result]
theorem Equation19834_implies_Equation2 (G : Type*) [Magma G] (h : Equation19834 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X1 ◇ X2)) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq12
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq12 eq12
  have eq22 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq16 eq15
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq92 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq92 eq39


@[equational_result]
theorem Equation19837_implies_Equation2 (G : Type*) [Magma G] (h : Equation19837 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq11 eq11
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq11 eq15
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq44 eq29


@[equational_result]
theorem Equation19838_implies_Equation2 (G : Type*) [Magma G] (h : Equation19838 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X4)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq12
  have eq28 (X0 X1 X2 X4 : G) : (X1 ◇ X2) = ((X0 ◇ X1) ◇ (X2 ◇ X4)) := superpose eq11 eq11
  have eq35 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq16 eq28
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq35 eq12
  have eq44 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq35 eq37
  have eq45 (X0 X3 : G) : X0 = X3 := superpose eq44 eq44
  have eq57 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq57 eq45


@[equational_result]
theorem Equation19840_implies_Equation2 (G : Type*) [Magma G] (h : Equation19840 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ X4) ◇ X4) ◇ (X0 ◇ X1)) = X4 := superpose eq7 eq7
  have eq14 (X0 X1 X2 X3 : G) : ((X0 ◇ X2) ◇ X1) = (X0 ◇ ((((X0 ◇ X2) ◇ X1) ◇ X3) ◇ (X1 ◇ X0))) := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X2) ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq27 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X2 ◇ (X2 ◇ X0))) := superpose eq10 eq11
  have eq48 (X0 X1 : G) : (X0 ◇ (X0 ◇ X1)) = X0 := superpose eq18 eq18
  have eq59 (X0 X1 X2 : G) : ((X0 ◇ X1) ◇ X2) = (X0 ◇ X2) := superpose eq48 eq27
  have eq64 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X2 ◇ X3)) ◇ X4) ◇ X4) ◇ (X0 ◇ X1)) = X4 := superpose eq59 eq12
  have eq66 (X1 X2 : G) : ((X1 ◇ X2) ◇ (X2 ◇ X1)) = X2 := superpose eq59 eq10
  have eq67 (X0 X1 X3 : G) : (X0 ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X3) ◇ (X1 ◇ X0))) := superpose eq59 eq14
  have eq84 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X0 ◇ X1)) = X4 := superpose eq59 eq64
  have eq85 (X0 X1 X4 : G) : ((X0 ◇ X4) ◇ (X0 ◇ X1)) = X4 := superpose eq59 eq84
  have eq86 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := superpose eq59 eq67
  have eq87 (X0 X1 : G) : (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq59 eq86
  have eq88 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq48 eq87
  have eq93 (X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X2 := superpose eq88 eq66
  have eq94 (X0 X4 : G) : ((X0 ◇ X4) ◇ X0) = X4 := superpose eq88 eq85
  have eq98 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq88 eq93
  have eq100 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq88 eq94
  have eq107 (X0 X1 : G) : X0 = X1 := superpose eq98 eq100
  have eq112 (X0 : G) : sK0 ≠ X0 := superpose eq107 eq8
  subsumption eq112 eq107


@[equational_result]
theorem Equation19841_implies_Equation2 (G : Type*) [Magma G] (h : Equation19841 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq13 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X2) ◇ (X3 ◇ X2)) = (X0 ◇ ((((X0 ◇ X2) ◇ (X3 ◇ X2)) ◇ X4) ◇ (X5 ◇ X4))) := superpose eq10 eq10
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq25 (X0 X2 X4 X5 : G) : (X0 ◇ ((X2 ◇ X4) ◇ (X5 ◇ X4))) = X2 := superpose eq18 eq13
  have eq32 (X0 X2 X4 : G) : (X0 ◇ X4) = X2 := superpose eq18 eq25
  have eq38 (X0 X3 : G) : X0 = X3 := superpose eq32 eq32
  have eq64 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq64 eq38


@[equational_result]
theorem Equation19842_implies_Equation2 (G : Type*) [Magma G] (h : Equation19842 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X2 ◇ X0) ◇ ((X0 ◇ (X4 ◇ X5)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq12 eq16
  have eq45 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq45 eq30


@[equational_result]
theorem Equation19843_implies_Equation2 (G : Type*) [Magma G] (h : Equation19843 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq12
  have eq34 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq16 eq16
  have eq83 (X0 X4 : G) : X0 = X4 := superpose eq12 eq34
  have eq175 (X0 : G) : sK0 ≠ X0 := superpose eq83 eq8
  subsumption eq175 eq83


@[equational_result]
theorem Equation19856_implies_Equation2 (G : Type*) [Magma G] (h : Equation19856 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X0) = (X0 ◇ X0) := superpose eq10 eq10
  have eq15 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((X0 ◇ X0) ◇ X3)) := superpose eq12 eq9
  have eq36 (X0 X1 X3 : G) : ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X3 := superpose eq15 eq10
  have eq49 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = X0 := superpose eq10 eq12
  have eq81 (X1 X3 : G) : (X1 ◇ X1) = X3 := superpose eq49 eq36
  have eq118 (X0 X2 : G) : X0 = X2 := superpose eq10 eq81
  have eq160 (X0 : G) : sK0 ≠ X0 := superpose eq118 eq8
  subsumption eq160 eq118


@[equational_result]
theorem Equation19859_implies_Equation2 (G : Type*) [Magma G] (h : Equation19859 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ ((X0 ◇ X0) ◇ X2)) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq11 eq11
  have eq18 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ (X1 ◇ X1)) ◇ X2) := superpose eq13 eq12
  have eq19 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2)) = X1 := superpose eq18 eq10
  have eq29 (X0 X3 : G) : X0 = X3 := superpose eq19 eq19
  have eq35 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq35 eq29


@[equational_result]
theorem Equation19861_implies_Equation2 (G : Type*) [Magma G] (h : Equation19861 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X3)) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X0)) = X3 := superpose eq7 eq10
  have eq22 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X2) ◇ (((X0 ◇ X1) ◇ X2) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))) := superpose eq10 eq11
  have eq28 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ X0)) = X2 := superpose eq10 eq11
  have eq45 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq16
  have eq74 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := superpose eq10 eq9
  have eq84 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X1 ◇ X0)))) = X3 := superpose eq9 eq7
  have eq86 (X0 X1 X2 X3 : G) : ((X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X3) ◇ (X1 ◇ (X1 ◇ X3)))) = X1 := superpose eq9 eq11
  have eq114 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) = (X2 ◇ (X1 ◇ X2)) := superpose eq45 eq45
  have eq119 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((((X1 ◇ X2) ◇ X2) ◇ (X1 ◇ X2)) ◇ X0)) = X3 := superpose eq10 eq45
  have eq136 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := superpose eq114 eq22
  have eq137 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := superpose eq114 eq74
  have eq145 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X2 := superpose eq136 eq28
  have eq161 (X0 X1 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := superpose eq137 eq84
  have eq162 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X3) ◇ (X1 ◇ (X1 ◇ X3)))) = X1 := superpose eq137 eq86
  have eq179 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X0)) = X3 := superpose eq136 eq119
  have eq194 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) ◇ ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1))) = X3 := superpose eq7 eq145
  have eq335 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((((X3 ◇ (X3 ◇ X4)) ◇ X3) ◇ X0) ◇ X1)) = X2 := superpose eq7 eq179
  have eq345 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq179
  have eq374 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X1) ◇ X3) ◇ X0) = X3 := superpose eq345 eq194
  have eq376 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq374 eq335
  have eq391 (X0 X1 X3 : G) : ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X3) = X1 := superpose eq376 eq162
  have eq486 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq391 eq391
  have eq504 (X0 X3 : G) : X0 = X3 := superpose eq161 eq486
  have eq584 (X0 : G) : sK0 ≠ X0 := superpose eq504 eq8
  subsumption eq584 eq504


@[equational_result]
theorem Equation19863_implies_Equation2 (G : Type*) [Magma G] (h : Equation19863 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ (((X1 ◇ X0) ◇ X0) ◇ X5)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq12
  have eq41 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq15 eq15
  have eq59 (X0 X1 X2 X5 : G) : (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X5)) = X2 := superpose eq41 eq10
  have eq74 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq41 eq59
  have eq81 (X0 X2 : G) : X0 = X2 := superpose eq12 eq74
  have eq90 (X0 : G) : sK0 ≠ X0 := superpose eq81 eq8
  subsumption eq90 eq81


@[equational_result]
theorem Equation19865_implies_Equation2 (G : Type*) [Magma G] (h : Equation19865 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ (X3 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1))) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X0)) ◇ X2) = ((X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2)) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ X0)) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq11 eq11
  have eq15 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X2)) = ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq11 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq11 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ X0)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq10
  have eq25 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X3))) ◇ X1) = (((X3 ◇ X0) ◇ ((X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X0)) ◇ X3))) ◇ X1)) ◇ (X0 ◇ (X3 ◇ X0))) := superpose eq7 eq10
  have eq62 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ X3)) ◇ X4) = (X3 ◇ (((X4 ◇ X3) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0)) ◇ (X4 ◇ X3))) := superpose eq10 eq9
  have eq67 (X0 X1 X2 X3 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X3 ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ X0)))) ◇ X0)) := superpose eq11 eq9
  have eq109 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = (((X3 ◇ X1) ◇ X3) ◇ (((X2 ◇ ((X3 ◇ X1) ◇ X3)) ◇ ((X3 ◇ X1) ◇ X3)) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X3)))) := superpose eq15 eq23
  have eq110 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) = ((X2 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ X2) := superpose eq23 eq23
  have eq115 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) = ((X0 ◇ X2) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq9 eq23
  have eq116 (X0 X1 X2 X3 : G) : (X2 ◇ (((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2))) = ((X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) := superpose eq23 eq23
  have eq120 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X3 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = (((X2 ◇ X1) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ ((X2 ◇ X1) ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq15 eq23
  have eq122 (X0 X1 X2 : G) : ((((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)) := superpose eq11 eq23
  have eq127 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X0) = ((X0 ◇ (X3 ◇ X2)) ◇ X0) := superpose eq23 eq23
  have eq131 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) = X0 := superpose eq23 eq7
  have eq137 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X2 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ X2)) = X1 := superpose eq23 eq7
  have eq142 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (((X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))))) := superpose eq23 eq11
  have eq147 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X2 ◇ (((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) ◇ (X4 ◇ ((X0 ◇ ((((X1 ◇ X2) ◇ X0) ◇ X0) ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))))) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2))) := superpose eq23 eq9
  have eq172 (X0 X1 X3 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X3 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)))) ◇ X0)) := superpose eq122 eq67
  have eq174 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) := superpose eq122 eq16
  have eq176 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ (X4 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2))) ◇ X1) := superpose eq7 eq127
  have eq180 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ X1) = ((X1 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X1) := superpose eq11 eq127
  have eq185 (X0 X1 X2 X4 : G) : ((X2 ◇ (X4 ◇ X1)) ◇ X2) = ((X2 ◇ (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)))) ◇ X2) := superpose eq23 eq127
  have eq186 (X0 X1 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X3 ◇ X1)) ◇ (X1 ◇ X0)) := superpose eq7 eq127
  have eq229 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ X2) ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := superpose eq127 eq11
  have eq230 (X0 X1 X2 X3 : G) : (((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((((X0 ◇ X1) ◇ (X2 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq127 eq23
  have eq250 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X4 ◇ X3))) = (X1 ◇ (((((X0 ◇ X1) ◇ (X4 ◇ X3)) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X4 ◇ X3)) ◇ X1))) := superpose eq127 eq23
  have eq287 (X0 X1 X3 : G) : ((X1 ◇ X0) ◇ X1) = (((X3 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X3 ◇ X0))) := superpose eq176 eq25
  have eq321 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) = ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2)))) := superpose eq186 eq115
  have eq347 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) = ((X2 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2)) ◇ (((((X0 ◇ X2) ◇ X2) ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X2)) := superpose eq23 eq13
  have eq353 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq13 eq10
  have eq360 (X0 X1 X2 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq13 eq7
  have eq370 (X0 X1 X2 X3 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = ((X2 ◇ (X3 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))) ◇ X2) := superpose eq13 eq127
  have eq375 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq370 eq360
  have eq378 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) := superpose eq186 eq375
  have eq383 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X3 ◇ X2) ◇ X3) ◇ ((((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ ((X3 ◇ X2) ◇ X3)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)))) := superpose eq10 eq131
  have eq425 (X0 X1 X2 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (((X3 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((((X0 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1) ◇ (X3 ◇ (((X0 ◇ (X2 ◇ X1)) ◇ X0) ◇ X1)))) := superpose eq12 eq287
  have eq470 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = ((X2 ◇ (X4 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ X2) := superpose eq287 eq127
  have eq485 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ (X0 ◇ (X4 ◇ X2))) ◇ X3) = ((X3 ◇ (X5 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)))) ◇ X3) := superpose eq127 eq180
  have eq489 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) := superpose eq287 eq180
  have eq653 (X0 X1 X3 X4 : G) : (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ ((X3 ◇ X4) ◇ X3)) ◇ (X1 ◇ X0)) := superpose eq7 eq489
  have eq662 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) = ((X2 ◇ ((X3 ◇ X4) ◇ X3)) ◇ X2) := superpose eq23 eq489
  have eq697 (X0 X1 X2 : G) : (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X2) ◇ (X1 ◇ X0)) := superpose eq7 eq489
  have eq817 (X2 X3 X4 : G) : ((X4 ◇ (X2 ◇ X3)) ◇ X4) = (X3 ◇ (X3 ◇ (X4 ◇ X3))) := superpose eq653 eq62
  have eq820 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = (((X3 ◇ X1) ◇ X3) ◇ (((X3 ◇ X1) ◇ X3) ◇ (X2 ◇ ((X3 ◇ X1) ◇ X3)))) := superpose eq653 eq109
  have eq823 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X3 ◇ ((X2 ◇ X1) ◇ X2))) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = (((X2 ◇ X1) ◇ X2) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq653 eq120
  have eq827 (X0 X1 X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ (((X3 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)))) := superpose eq653 eq383
  have eq829 (X0 : G) : ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq817 eq353
  have eq834 (X0 : G) : (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq817 eq829
  have eq841 (X0 X1 X2 : G) : (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) = ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X2) := superpose eq697 eq110
  have eq848 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X2)) = X1 := superpose eq697 eq137
  have eq851 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = (((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := superpose eq697 eq142
  have eq862 (X0 X1 X2 X4 : G) : ((X2 ◇ (X4 ◇ X1)) ◇ X2) = ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X2) := superpose eq697 eq185
  have eq867 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2) = ((X2 ◇ (((X0 ◇ (X1 ◇ X2)) ◇ X0) ◇ X2)) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) ◇ X2)) := superpose eq697 eq347
  have eq902 (X0 X1 X3 : G) : (((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq697 eq230
  have eq903 (X0 X1 X3 X4 : G) : (X1 ◇ (((((X0 ◇ X1) ◇ (X4 ◇ X3)) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ (X4 ◇ X3)) ◇ X1))) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X4 ◇ X3))) := superpose eq697 eq250
  have eq939 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)) := superpose eq697 eq122
  have eq948 (X0 X1 X2 X3 X4 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X2 ◇ (((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) ◇ (X4 ◇ ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))))) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2))) := superpose eq697 eq147
  have eq949 (X0 X1 X2 X3 : G) : (X2 ◇ (((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) ◇ X2) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2))) = ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) := superpose eq697 eq116
  have eq960 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = (X1 ◇ (((X2 ◇ X1) ◇ X1) ◇ (X2 ◇ X1))) := superpose eq180 eq841
  have eq961 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := superpose eq697 eq960
  have eq962 (X0 : G) : ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))) := superpose eq961 eq834
  have eq964 (X1 X2 : G) : ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = X1 := superpose eq180 eq848
  have eq970 (X1 X2 X4 : G) : ((X2 ◇ X1) ◇ X2) = ((X2 ◇ (X4 ◇ X1)) ◇ X2) := superpose eq180 eq862
  have eq994 (X0 X2 X3 : G) : (((X0 ◇ X2) ◇ X0) ◇ ((X3 ◇ X2) ◇ (X0 ◇ (X3 ◇ X2)))) = X0 := superpose eq970 eq229
  have eq1002 (X0 X2 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2)))) = (((X0 ◇ X2) ◇ X0) ◇ X2) := superpose eq970 eq321
  have eq1009 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (((X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ (X3 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)))) := superpose eq970 eq425
  have eq1015 (X0 X2 X3 X4 X5 : G) : ((X3 ◇ (X0 ◇ (X4 ◇ X2))) ◇ X3) = ((X3 ◇ (X5 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0)))) ◇ X3) := superpose eq970 eq485
  have eq1025 (X0 X2 X3 X4 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ X3)) ◇ X2) = (((X0 ◇ X2) ◇ X0) ◇ X2) := superpose eq970 eq662
  have eq1030 (X0 X2 X3 : G) : ((X3 ◇ X2) ◇ X3) = (((X0 ◇ X2) ◇ X0) ◇ (((X3 ◇ X2) ◇ X3) ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0)))) := superpose eq970 eq827
  have eq1073 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) ◇ X0)) := superpose eq970 eq172
  have eq1074 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := superpose eq970 eq174
  have eq1098 (X0 : G) : ((X0 ◇ X0) ◇ X0) = X0 := superpose eq994 eq962
  have eq1105 (X0 X2 X3 X4 : G) : ((X3 ◇ (X0 ◇ X2)) ◇ X3) = ((X3 ◇ (X0 ◇ (X4 ◇ X2))) ◇ X3) := superpose eq180 eq1015
  have eq1106 (X0 X2 X3 X4 : G) : ((X3 ◇ X2) ◇ X3) = ((X3 ◇ (X0 ◇ (X4 ◇ X2))) ◇ X3) := superpose eq970 eq1105
  have eq1109 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := superpose eq1030 eq378
  have eq1140 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) := superpose eq1106 eq1073
  have eq1141 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)) := superpose eq1098 eq1140
  have eq1142 (X0 X1 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1106 eq1141
  have eq1143 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1109 eq1142
  have eq1147 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq970 eq1074
  have eq1148 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1143 eq1147
  have eq1169 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X2) = ((X2 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) ◇ (((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X2) ◇ X0)) ◇ X2)) := superpose eq970 eq867
  have eq1170 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X2) = ((X2 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) := superpose eq1143 eq1169
  have eq1188 (X0 X1 : G) : (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq1106 eq902
  have eq1189 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := superpose eq697 eq1188
  have eq1191 (X0 X1 X3 X4 : G) : ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X4 ◇ X3))) = (X1 ◇ (X1 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ (X4 ◇ X3)) ◇ X1) ◇ X1)))) := superpose eq961 eq903
  have eq1214 (X0 X1 : G) : (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1106 eq939
  have eq1215 (X0 X1 : G) : ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1143 eq1214
  have eq1238 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X2 ◇ (((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2))) := superpose eq1106 eq948
  have eq1239 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X2 ◇ (((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) ◇ X0) ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2))) := superpose eq1106 eq1238
  have eq1240 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X2 ◇ (X2 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2))) := superpose eq697 eq1239
  have eq1241 (X0 X1 X2 X3 : G) : ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X2 ◇ (X2 ◇ (X2 ◇ ((((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2) ◇ X2)))) := superpose eq961 eq949
  have eq1350 (X0 X1 : G) : (X1 ◇ ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq1148 eq1148
  have eq1392 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := superpose eq1215 eq1350
  have eq1393 (X0 X1 : G) : (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = X1 := superpose eq964 eq1392
  have eq1394 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X2) = (X2 ◇ (((X0 ◇ X2) ◇ X0) ◇ X2)) := superpose eq1393 eq1170
  have eq1395 (X0 X2 : G) : (((X0 ◇ X2) ◇ X0) ◇ X2) = X2 := superpose eq1393 eq1394
  have eq1401 (X0 X2 : G) : ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2)))) = X2 := superpose eq1395 eq1002
  have eq1403 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (((X3 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X3 ◇ X1))) := superpose eq1395 eq1009
  have eq1404 (X2 X3 X4 : G) : ((X2 ◇ ((X3 ◇ X4) ◇ X3)) ◇ X2) = X2 := superpose eq1395 eq1025
  have eq1421 (X1 X2 X3 X4 : G) : ((X2 ◇ (X4 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ X2) = X2 := superpose eq1404 eq470
  have eq1432 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X1 := superpose eq1421 eq180
  have eq1440 (X0 X1 X3 : G) : (((X3 ◇ X0) ◇ X1) ◇ (X0 ◇ (X3 ◇ X0))) = X1 := superpose eq1432 eq287
  have eq1459 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = (X3 ◇ (X3 ◇ (X2 ◇ X3))) := superpose eq1432 eq820
  have eq1461 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X3 ◇ X2)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = (X2 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1432 eq823
  have eq1595 (X2 X3 : G) : (X3 ◇ (X3 ◇ (X2 ◇ X3))) = X2 := superpose eq1432 eq1459
  have eq1599 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X0)) = ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X1)) := superpose eq1595 eq851
  have eq1608 (X0 X1 X2 X3 : G) : (X2 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) := superpose eq1595 eq1241
  have eq1609 (X0 X1 X3 X4 : G) : (X1 ◇ (((X0 ◇ X1) ◇ (X4 ◇ X3)) ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X4 ◇ X3))) := superpose eq1595 eq1191
  have eq1612 (X0 X1 X2 X3 : G) : (X2 ◇ (X2 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2))) = ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) := superpose eq1595 eq1240
  have eq1620 (X0 X1 X2 X3 : G) : (X2 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2)) = ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) := superpose eq1595 eq1608
  have eq1622 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X1))) := superpose eq1609 eq1189
  have eq1629 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) := superpose eq1595 eq1612
  have eq1630 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X3 ◇ X0)) = (X2 ◇ (((X1 ◇ X2) ◇ (X3 ◇ X0)) ◇ X2)) := superpose eq1629 eq1620
  have eq1633 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := superpose eq1630 eq1622
  have eq1641 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := superpose eq1432 eq1461
  have eq1642 (X0 X1 X3 : G) : ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = (((X3 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X3 ◇ X1))) := superpose eq1641 eq1403
  have eq1644 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := superpose eq1440 eq1642
  have eq1647 (X0 X2 : G) : ((X0 ◇ X2) ◇ (X2 ◇ (X0 ◇ X2))) = X2 := superpose eq1644 eq1401
  have eq1650 (X0 X1 : G) : (X1 ◇ (X0 ◇ X1)) = X1 := superpose eq1647 eq1644
  have eq1652 (X0 X1 : G) : (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := superpose eq1650 eq1633
  have eq1676 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq1650 eq1652
  have eq1680 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ X1)) := superpose eq1676 eq1599
  have eq1686 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ X1) := superpose eq1676 eq1680
  have eq1687 (X0 X1 X2 : G) : (X2 ◇ X0) = ((X2 ◇ X0) ◇ X1) := superpose eq1676 eq1686
  have eq1688 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq1676 eq1687
  have eq1699 (X0 X1 : G) : X0 = X1 := superpose eq1688 eq1676
  have eq1701 (X0 : G) : sK0 ≠ X0 := superpose eq1699 eq8
  subsumption eq1701 eq1699


@[equational_result]
theorem Equation19867_implies_Equation2 (G : Type*) [Magma G] (h : Equation19867 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X4)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq27 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) = X3 := superpose eq7 eq11
  have eq32 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ (X2 ◇ X3)) ◇ X0) := superpose eq11 eq12
  have eq42 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X0) = X3 := superpose eq32 eq27
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq42 eq42
  have eq96 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq96 eq51


@[equational_result]
theorem Equation19869_implies_Equation2 (G : Type*) [Magma G] (h : Equation19869 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3) ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) = (X3 ◇ (((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3) ◇ (X4 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3))) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3))) := superpose eq7 eq9
  have eq15 (X0 X1 X2 X3 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ X1))) = (X1 ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) := superpose eq7 eq9
  have eq22 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := superpose eq9 eq9
  have eq23 (X0 X1 X2 X3 : G) : ((X1 ◇ X3) ◇ (X0 ◇ (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)))) = X3 := superpose eq9 eq7
  have eq30 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X2) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) = X2 := superpose eq7 eq10
  have eq40 (X0 X1 X2 X3 X4 X5 : G) : ((((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X0) ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) = (X4 ◇ (((((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X4) ◇ (X5 ◇ (((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X4))) ◇ (((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X3) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X4))) := superpose eq10 eq9
  have eq66 (X0 X1 X2 X3 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (((X0 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := superpose eq22 eq7
  have eq109 (X0 X1 X2 X3 X4 : G) : (X2 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) = (X0 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X4) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq23 eq10
  have eq118 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq7 eq30
  have eq133 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X1) = (((X1 ◇ (X3 ◇ X1)) ◇ X1) ◇ (((X1 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X1)))) := superpose eq30 eq9
  have eq134 (X0 X1 X2 X3 : G) : (X0 ◇ (((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X0) ◇ (X3 ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X0))) ◇ (((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X0))) = (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) := superpose eq30 eq7
  have eq143 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X0)))) = X0 := superpose eq118 eq66
  have eq145 (X0 X1 X2 : G) : (X1 ◇ ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) = (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) := superpose eq118 eq15
  have eq147 (X0 X1 X2 X3 : G) : (X2 ◇ ((((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := superpose eq145 eq109
  have eq151 (X0 X1 X2 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) = (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) := superpose eq134 eq11
  have eq158 (X0 X1 X2 X4 X5 : G) : (((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) = (X4 ◇ ((((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X4) ◇ (X5 ◇ ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X4))) ◇ ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X4))) := superpose eq151 eq40
  have eq169 (X0 X1 X2 : G) : (((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X0) ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1))) = (X1 ◇ (X1 ◇ ((X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) ◇ X1))) := superpose eq147 eq158
  have eq173 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X1) = (((X1 ◇ (X3 ◇ X1)) ◇ X1) ◇ (X1 ◇ (X1 ◇ ((X1 ◇ ((X1 ◇ (X3 ◇ X1)) ◇ X1)) ◇ X1)))) := superpose eq169 eq133
  have eq179 (X1 X2 : G) : ((X1 ◇ (X2 ◇ X1)) ◇ X1) = X1 := superpose eq143 eq173
  have eq180 (X0 X1 : G) : ((X1 ◇ X0) ◇ X1) = X0 := superpose eq179 eq7
  have eq181 (X0 X1 X3 : G) : (X0 ◇ (((X1 ◇ X0) ◇ (X3 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) = X1 := superpose eq179 eq9
  have eq224 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq179 eq181
  have eq225 (X1 X2 : G) : (X2 ◇ X1) = X1 := superpose eq224 eq179
  have eq226 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq225 eq224
  have eq227 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq225 eq180
  have eq237 (X0 X1 : G) : X0 = X1 := superpose eq227 eq226
  have eq242 (X0 : G) : sK0 ≠ X0 := superpose eq237 eq8
  subsumption eq242 eq237


@[equational_result]
theorem Equation19871_implies_Equation2 (G : Type*) [Magma G] (h : Equation19871 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq12
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq12 eq12
  have eq22 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq16 eq15
  have eq38 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq91 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq91 eq38


@[equational_result]
theorem Equation19875_implies_Equation2 (G : Type*) [Magma G] (h : Equation19875 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X4)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq11 eq11
  have eq20 (X0 X2 X4 : G) : (X0 ◇ (X0 ◇ X4)) = X2 := superpose eq15 eq10
  have eq26 (X0 X2 : G) : X0 = X2 := superpose eq11 eq20
  have eq34 (X0 : G) : sK0 ≠ X0 := superpose eq26 eq8
  subsumption eq34 eq26


@[equational_result]
theorem Equation19877_implies_Equation2 (G : Type*) [Magma G] (h : Equation19877 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ (X4 ◇ X5)) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X1 ◇ X0))) = X2 := superpose eq7 eq7
  have eq19 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq7 eq11
  have eq20 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := superpose eq10 eq11
  have eq23 (X0 X1 X2 X3 : G) : ((X0 ◇ X3) ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) = X3 := superpose eq10 eq11
  have eq40 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq20 eq20
  have eq41 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = ((X0 ◇ X1) ◇ X0) := superpose eq20 eq20
  have eq52 (X0 X1 X2 X3 X4 : G) : (X2 ◇ (X0 ◇ X2)) = (((X0 ◇ X1) ◇ X0) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X2)) := superpose eq20 eq7
  have eq88 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X0)) = (((X1 ◇ (X4 ◇ X5)) ◇ X1) ◇ ((X0 ◇ (X6 ◇ X7)) ◇ X0)) := superpose eq7 eq9
  have eq93 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ X2) = ((X2 ◇ (X0 ◇ X2)) ◇ ((((X0 ◇ X1) ◇ X0) ◇ (X5 ◇ X6)) ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq20 eq9
  have eq121 (X0 X1 X2 X3 : G) : (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X2 ◇ X3)) ◇ (X1 ◇ X0)) := superpose eq52 eq88
  have eq137 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ X2) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := superpose eq121 eq93
  have eq157 (X0 X1 X4 : G) : (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ X4) ◇ (X1 ◇ X0)) := superpose eq7 eq41
  have eq163 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = (((X0 ◇ X1) ◇ X0) ◇ X2) := superpose eq20 eq41
  have eq180 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq41 eq11
  have eq228 (X0 X1 X2 X3 X4 : G) : (((((X0 ◇ X1) ◇ (X2 ◇ X3)) ◇ (X0 ◇ X1)) ◇ X4) ◇ X0) = X4 := superpose eq7 eq23
  have eq247 (X0 X1 X4 : G) : (((X1 ◇ (X0 ◇ X1)) ◇ X4) ◇ X0) = X4 := superpose eq157 eq228
  have eq264 (X0 X1 X2 : G) : (((X0 ◇ X1) ◇ X0) ◇ X2) = X0 := superpose eq41 eq247
  have eq283 (X0 X1 X3 : G) : ((X0 ◇ X3) ◇ X1) = X3 := superpose eq264 eq23
  have eq312 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = ((X2 ◇ (X0 ◇ X2)) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X1)) := superpose eq283 eq40
  have eq313 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X4)) ◇ X2) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) := superpose eq283 eq137
  have eq315 (X1 X2 X3 : G) : (X1 ◇ X2) = ((X2 ◇ X3) ◇ X2) := superpose eq283 eq163
  have eq316 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ (X0 ◇ X2))) = X0 := superpose eq283 eq180
  have eq346 (X0 X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq283 eq312
  have eq347 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X1) = X1 := superpose eq316 eq19
  have eq353 (X0 X1 X2 : G) : ((X2 ◇ (X0 ◇ X2)) ◇ (X0 ◇ X1)) = X2 := superpose eq347 eq313
  have eq354 (X2 X3 : G) : ((X2 ◇ X3) ◇ X2) = X2 := superpose eq353 eq346
  have eq356 (X1 X2 : G) : (X1 ◇ X2) = X2 := superpose eq354 eq315
  have eq358 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X0 := superpose eq356 eq316
  have eq364 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq356 eq358
  have eq365 (X0 X3 : G) : X0 = X3 := superpose eq364 eq364
  have eq370 (X0 : G) : sK0 ≠ X0 := superpose eq365 eq8
  subsumption eq370 eq365


@[equational_result]
theorem Equation19878_implies_Equation2 (G : Type*) [Magma G] (h : Equation19878 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ (X5 ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X3)))) = X2 := superpose eq7 eq10
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq29 (X0 X1 X2 X3 X4 X5 : G) : (X0 ◇ (X0 ◇ (X5 ◇ ((X1 ◇ (X3 ◇ X4)) ◇ X3)))) = X2 := superpose eq19 eq15
  have eq36 (X0 X2 X3 X4 X5 : G) : (X0 ◇ (X0 ◇ (X5 ◇ (X3 ◇ X4)))) = X2 := superpose eq19 eq29
  have eq74 (X0 X5 : G) : X0 = X5 := superpose eq19 eq36
  have eq91 (X0 : G) : sK0 ≠ X0 := superpose eq74 eq8
  subsumption eq91 eq74


@[equational_result]
theorem Equation19879_implies_Equation2 (G : Type*) [Magma G] (h : Equation19879 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((X1 ◇ X0) ◇ ((X3 ◇ (X4 ◇ X5)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X4 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X4)) = X2 := superpose eq7 eq7
  have eq14 (X0 X2 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ ((X2 ◇ X3) ◇ X5)) = X4 := superpose eq11 eq11
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq14 eq10
  have eq31 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq23 eq23
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq23 eq31
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq55 eq32


@[equational_result]
theorem Equation19880_implies_Equation2 (G : Type*) [Magma G] (h : Equation19880 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X6 : G) : (((X1 ◇ X0) ◇ X2) ◇ (X0 ◇ X6)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq12
  have eq22 (X0 X2 X6 : G) : (X0 ◇ (X0 ◇ X6)) = X2 := superpose eq16 eq11
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq12 eq22
  have eq37 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq37 eq28


@[equational_result]
theorem Equation19899_implies_Equation2 (G : Type*) [Magma G] (h : Equation19899 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ ((X3 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq21 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq7 eq9
  have eq22 (X0 X1 X2 X3 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ X1) = ((X3 ◇ (X1 ◇ X2)) ◇ X1) := superpose eq9 eq9
  have eq23 (X0 X1 X2 : G) : ((X2 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))) = X0 := superpose eq9 eq7
  have eq101 (X0 X1 : G) : (((X1 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq7 eq23
  have eq123 (X0 X1 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := superpose eq101 eq9
  have eq130 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) = ((X0 ◇ X0) ◇ ((X3 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq101 eq9
  have eq137 (X0 X1 X2 : G) : (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0))) := superpose eq123 eq21
  have eq140 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := superpose eq7 eq130
  have eq141 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq123 eq140
  have eq156 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X2) := superpose eq137 eq9
  have eq157 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X2) = ((X0 ◇ X0) ◇ X2) := superpose eq137 eq22
  have eq159 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X2 := superpose eq137 eq10
  have eq170 (X0 X1 X2 : G) : ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X2) = X0 := superpose eq141 eq156
  have eq173 (X0 X2 : G) : ((X0 ◇ X0) ◇ X2) = X0 := superpose eq170 eq157
  have eq178 (X0 X2 : G) : (((X0 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq141 eq159
  have eq179 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq173 eq178
  have eq284 (X0 X2 : G) : X0 = X2 := superpose eq179 eq179
  have eq292 (X0 : G) : sK0 ≠ X0 := superpose eq284 eq8
  subsumption eq292 eq284


@[equational_result]
theorem Equation19900_implies_Equation2 (G : Type*) [Magma G] (h : Equation19900 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((X3 ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X1 := superpose eq7 eq7
  have eq22 (X0 X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X1) = X0 := superpose eq7 eq9
  have eq44 (X0 X1 X2 : G) : (((X1 ◇ (((X2 ◇ X0) ◇ (X2 ◇ X0)) ◇ (X2 ◇ X0))) ◇ X1) ◇ X0) = X1 := superpose eq7 eq10
  have eq56 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq22 eq44
  have eq59 (X0 X2 : G) : X0 = X2 := superpose eq56 eq56
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq119 eq59


@[equational_result]
theorem Equation19901_implies_Equation2 (G : Type*) [Magma G] (h : Equation19901 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ (X0 ◇ X4)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq31 (X0 X3 X4 : G) : (X0 ◇ X0) = (X3 ◇ X4) := superpose eq10 eq11
  have eq51 (X0 X2 X3 : G) : (X2 ◇ X3) = X0 := superpose eq11 eq31
  have eq67 (X0 X2 : G) : X0 = X2 := superpose eq11 eq51
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq67 eq8
  subsumption eq106 eq67


@[equational_result]
theorem Equation19903_implies_Equation2 (G : Type*) [Magma G] (h : Equation19903 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ X1) = (X0 ◇ ((X3 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ X2) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ (X2 ◇ X0)) = (((X3 ◇ (X2 ◇ X2)) ◇ X2) ◇ ((X4 ◇ (X0 ◇ X0)) ◇ X0)) := superpose eq7 eq9
  have eq20 (X0 X1 X2 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := superpose eq9 eq9
  have eq21 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ (X2 ◇ X0)))) = X3 := superpose eq9 eq7
  have eq29 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) := superpose eq9 eq10
  have eq36 (X0 X1 X2 X3 : G) : (X0 ◇ ((X1 ◇ (((((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ X0) ◇ ((((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ X0))) ◇ ((((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ X0))) = ((((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) := superpose eq9 eq10
  have eq37 (X0 X1 X2 X3 : G) : ((X2 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X3 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)))) := superpose eq10 eq9
  have eq41 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ (X2 ◇ (X3 ◇ X3)))) ◇ (X2 ◇ (X3 ◇ X3))) = (X3 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) := superpose eq10 eq9
  have eq43 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X3) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X2))) = X3 := superpose eq10 eq7
  have eq46 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) = (X3 ◇ ((X4 ◇ (((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X3) ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X3))) ◇ ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ X3))) := superpose eq10 eq9
  have eq48 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ X3) = (X0 ◇ ((X1 ◇ (((((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ X0) ◇ ((((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ X0))) ◇ ((((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ X0))) := superpose eq10 eq36
  have eq50 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) := superpose eq48 eq46
  have eq51 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = ((X2 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) := superpose eq50 eq37
  have eq81 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X3 ◇ (X1 ◇ X1))) = (X1 ◇ ((X4 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) := superpose eq20 eq9
  have eq104 (X0 X1 X2 X3 : G) : (X1 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) = ((X2 ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X3 ◇ (X1 ◇ X1))) := superpose eq51 eq81
  have eq126 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ X3) ◇ (((X4 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X2)) ◇ ((X5 ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)))) = X3 := superpose eq9 eq21
  have eq134 (X0 X1 X2 X3 : G) : ((X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) ◇ (X3 ◇ X1))) ◇ (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) ◇ (X3 ◇ X1)))) = ((X0 ◇ ((X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) ◇ (X3 ◇ X1))) ◇ (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) ◇ (X3 ◇ X1))))) ◇ (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) ◇ (X3 ◇ X1)))) := superpose eq20 eq21
  have eq136 (X0 X1 X2 X3 X4 : G) : (X0 ◇ ((X1 ◇ (((X2 ◇ ((X3 ◇ ((X4 ◇ X2) ◇ (X4 ◇ X2))) ◇ (X4 ◇ X2))) ◇ X0) ◇ ((X2 ◇ ((X3 ◇ ((X4 ◇ X2) ◇ (X4 ◇ X2))) ◇ (X4 ◇ X2))) ◇ X0))) ◇ ((X2 ◇ ((X3 ◇ ((X4 ◇ X2) ◇ (X4 ◇ X2))) ◇ (X4 ◇ X2))) ◇ X0))) = ((X2 ◇ ((X3 ◇ ((X4 ◇ X2) ◇ (X4 ◇ X2))) ◇ (X4 ◇ X2))) ◇ (X2 ◇ ((X3 ◇ ((X4 ◇ X2) ◇ (X4 ◇ X2))) ◇ (X4 ◇ X2)))) := superpose eq9 eq21
  have eq154 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X3) ◇ (((X4 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) ◇ (X1 ◇ X2)) ◇ (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)))) = X3 := superpose eq51 eq126
  have eq160 (X0 X1 X2 X3 : G) : (X2 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = (X0 ◇ (X3 ◇ (((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0)) ◇ X0))) := superpose eq43 eq43
  have eq182 (X0 X1 X2 X3 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq7 eq43
  have eq220 (X0 X1 X2 X3 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ X3) = (X0 ◇ ((X1 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) := superpose eq182 eq48
  have eq227 (X0 X2 X3 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ X3) = (X0 ◇ (((X2 ◇ (X3 ◇ X3)) ◇ X3) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) := superpose eq51 eq220
  have eq228 (X1 X2 X3 X4 : G) : ((X2 ◇ (X3 ◇ X3)) ◇ X3) = ((X4 ◇ ((X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)))) ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) := superpose eq227 eq29
  have eq229 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = X3 := superpose eq227 eq154
  have eq234 (X1 X2 X3 : G) : ((X2 ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) ◇ (X3 ◇ X1)) = ((X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) ◇ (X3 ◇ X1))) ◇ (X1 ◇ ((X2 ◇ ((X3 ◇ X1) ◇ (X3 ◇ X1))) ◇ (X3 ◇ X1)))) := superpose eq228 eq134
  have eq237 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ ((X4 ◇ X2) ◇ (X4 ◇ X2))) ◇ (X4 ◇ X2)) = (X0 ◇ ((X1 ◇ (((X2 ◇ ((X3 ◇ ((X4 ◇ X2) ◇ (X4 ◇ X2))) ◇ (X4 ◇ X2))) ◇ X0) ◇ ((X2 ◇ ((X3 ◇ ((X4 ◇ X2) ◇ (X4 ◇ X2))) ◇ (X4 ◇ X2))) ◇ X0))) ◇ ((X2 ◇ ((X3 ◇ ((X4 ◇ X2) ◇ (X4 ◇ X2))) ◇ (X4 ◇ X2))) ◇ X0))) := superpose eq234 eq136
  have eq254 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ ((X3 ◇ (X1 ◇ X1)) ◇ (X3 ◇ (X1 ◇ X1)))) ◇ (X3 ◇ (X1 ◇ X1))) := superpose eq229 eq104
  have eq257 (X0 X1 X2 : G) : ((X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) ◇ (X2 ◇ X0)) = X2 := superpose eq229 eq15
  have eq264 (X0 X2 X3 : G) : (X3 ◇ X3) = (X3 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3))) := superpose eq254 eq41
  have eq271 (X0 X1 X2 : G) : (X0 ◇ X0) = (X2 ◇ ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := superpose eq264 eq160
  have eq276 (X0 X2 : G) : (X0 ◇ X0) = (X2 ◇ X0) := superpose eq257 eq271
  have eq284 (X1 X3 : G) : ((X1 ◇ X3) ◇ (X1 ◇ X3)) = X3 := superpose eq257 eq234
  have eq285 (X0 X1 X2 X4 : G) : (X0 ◇ ((X1 ◇ (((X2 ◇ X4) ◇ X0) ◇ ((X2 ◇ X4) ◇ X0))) ◇ ((X2 ◇ X4) ◇ X0))) = X4 := superpose eq257 eq237
  have eq297 (X0 X1 : G) : ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := superpose eq276 eq7
  have eq320 (X0 X2 X4 : G) : (X0 ◇ (((X2 ◇ X4) ◇ X0) ◇ ((X2 ◇ X4) ◇ X0))) = X4 := superpose eq276 eq285
  have eq321 (X0 X4 : G) : (X0 ◇ X0) = X4 := superpose eq284 eq320
  have eq335 (X0 X1 : G) : X0 = X1 := superpose eq297 eq321
  have eq362 (X0 : G) : sK0 ≠ X0 := superpose eq335 eq8
  subsumption eq362 eq335


@[equational_result]
theorem Equation19905_implies_Equation2 (G : Type*) [Magma G] (h : Equation19905 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ (X0 ◇ X4)) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X1)) ◇ X3) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq7 eq11
  have eq13 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := superpose eq11 eq11
  have eq19 (X1 X2 X3 : G) : (X1 ◇ X1) = ((X2 ◇ (X1 ◇ X1)) ◇ X3) := superpose eq13 eq12
  have eq20 (X0 X2 X3 X4 : G) : ((X2 ◇ X2) ◇ (X0 ◇ X4)) = X3 := superpose eq19 eq10
  have eq33 (X0 X1 : G) : X0 = X1 := superpose eq11 eq20
  have eq42 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq42 eq33


@[equational_result]
theorem Equation19909_implies_Equation2 (G : Type*) [Magma G] (h : Equation19909 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X1)) ◇ X3) ◇ (X0 ◇ X4)) = X3 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ ((X1 ◇ X0) ◇ X4)) := superpose eq7 eq12
  have eq14 (X0 X1 X2 X3 : G) : (X1 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := superpose eq12 eq12
  have eq18 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X3)) = X2 := superpose eq12 eq7
  have eq27 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ (X4 ◇ X5)) := superpose eq7 eq11
  have eq39 (X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ X2)) ◇ X3) = X1 := superpose eq18 eq27
  have eq40 (X0 X1 X4 : G) : (X0 ◇ ((X1 ◇ X0) ◇ X4)) = X1 := superpose eq39 eq13
  have eq46 (X1 X2 : G) : (X1 ◇ X2) = X1 := superpose eq40 eq14
  have eq47 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq46 eq40
  have eq52 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq46 eq47
  have eq54 (X0 X1 : G) : X0 = X1 := superpose eq46 eq52
  have eq56 (X0 : G) : sK0 ≠ X0 := superpose eq54 eq8
  subsumption eq56 eq54


@[equational_result]
theorem Equation19911_implies_Equation2 (G : Type*) [Magma G] (h : Equation19911 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X4 := superpose eq7 eq7
  have eq31 (X0 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ X0)) = X4 := superpose eq7 eq11
  have eq49 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X2) ◇ X4) ◇ X0) = X4 := superpose eq7 eq31
  have eq52 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq31 eq31
  have eq65 (X0 X2 X4 : G) : (X2 ◇ X0) = X4 := superpose eq52 eq49
  have eq144 (X0 X4 : G) : X0 = X4 := superpose eq7 eq65
  have eq256 (X0 : G) : sK0 ≠ X0 := superpose eq144 eq8
  subsumption eq256 eq144


@[equational_result]
theorem Equation19912_implies_Equation2 (G : Type*) [Magma G] (h : Equation19912 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X0) ◇ X3)) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq10 eq10
  have eq50 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq18 eq18
  have eq66 (X0 X2 X3 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X3)) = X2 := superpose eq50 eq10
  have eq90 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq50 eq66
  have eq105 (X0 X2 : G) : X0 = X2 := superpose eq90 eq90
  have eq107 (X0 : G) : sK0 ≠ X0 := superpose eq105 eq8
  subsumption eq107 eq105


@[equational_result]
theorem Equation19913_implies_Equation2 (G : Type*) [Magma G] (h : Equation19913 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X0) ◇ ((X4 ◇ (X1 ◇ X5)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ (X0 ◇ X3)) = X4 := superpose eq7 eq7
  have eq15 (X0 X3 X4 X5 : G) : ((X0 ◇ X4) ◇ (X5 ◇ X3)) = X4 := superpose eq7 eq11
  have eq25 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq15 eq10
  have eq28 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq25 eq25
  have eq40 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq28 eq25
  have eq55 (X0 X2 : G) : X0 = X2 := superpose eq40 eq40
  have eq71 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq71 eq55


@[equational_result]
theorem Equation19914_implies_Equation2 (G : Type*) [Magma G] (h : Equation19914 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X7 : G) : (((X1 ◇ X0) ◇ X2) ◇ ((X3 ◇ X0) ◇ X7)) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ X2) ◇ X0) = X2 := superpose eq7 eq12
  have eq42 (X0 X2 X3 : G) : ((X0 ◇ X3) ◇ X2) = X3 := superpose eq15 eq15
  have eq58 (X0 X2 X3 X7 : G) : (X0 ◇ ((X3 ◇ X0) ◇ X7)) = X2 := superpose eq42 eq10
  have eq69 (X0 X2 : G) : (X0 ◇ X0) = X2 := superpose eq42 eq58
  have eq78 (X0 X2 : G) : X0 = X2 := superpose eq12 eq69
  have eq87 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq87 eq78


@[equational_result]
theorem Equation19917_implies_Equation2 (G : Type*) [Magma G] (h : Equation19917 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X2) = (X0 ◇ ((X3 ◇ (X3 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2))) ◇ X3)) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X2) = ((X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) ◇ (((X3 ◇ X0) ◇ X0) ◇ (X3 ◇ X0))) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X1)) := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X1) = ((X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) ◇ X0) := superpose eq7 eq10
  have eq32 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := superpose eq25 eq14
  have eq81 (X0 X1 X3 : G) : (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X3 ◇ (X3 ◇ X1)) ◇ X3)) = X1 := superpose eq25 eq7
  have eq92 (X0 X1 X2 : G) : ((X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) ◇ X2) = X1 := superpose eq81 eq32
  have eq213 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (((X2 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X3))) ◇ X0) ◇ (X2 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X0)) ◇ X3)))))) ◇ X1) = X2 := superpose eq92 eq92
  have eq227 (X0 X1 X3 : G) : (X0 ◇ ((X3 ◇ (X3 ◇ X1)) ◇ X3)) = X1 := superpose eq92 eq7
  have eq241 (X1 X2 : G) : ((X2 ◇ X1) ◇ X2) = X1 := superpose eq227 eq92
  have eq243 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ (((X2 ◇ X0) ◇ X0) ◇ (X2 ◇ X0)))) ◇ X1) = X2 := superpose eq227 eq213
  have eq244 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ (X2 ◇ X0)) = X0 := superpose eq241 eq7
  have eq248 (X0 X1 X3 : G) : (X0 ◇ (X3 ◇ X1)) = X1 := superpose eq241 eq227
  have eq261 (X0 X1 X2 : G) : ((((X2 ◇ X0) ◇ X0) ◇ (X2 ◇ X0)) ◇ X1) = X2 := superpose eq248 eq243
  have eq262 (X0 X1 X2 : G) : (X0 ◇ X1) = X2 := superpose eq244 eq261
  have eq263 (X0 X3 : G) : X0 = X3 := superpose eq262 eq262
  have eq274 (X0 : G) : sK0 ≠ X0 := superpose eq263 eq8
  subsumption eq274 eq263


@[equational_result]
theorem Equation19918_implies_Equation2 (G : Type*) [Magma G] (h : Equation19918 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 X5 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X3) = (X0 ◇ ((X4 ◇ (X4 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3))) ◇ X5)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq19 (X0 X2 X3 X4 : G) : (X2 ◇ X0) = (X0 ◇ ((X3 ◇ (X3 ◇ (X2 ◇ X0))) ◇ X4)) := superpose eq11 eq7
  have eq20 (X0 X1 X2 X3 X4 X5 X6 : G) : (((X1 ◇ X0) ◇ X0) ◇ X4) = (((X2 ◇ (X2 ◇ X0)) ◇ X3) ◇ ((X5 ◇ (X5 ◇ (((X1 ◇ X0) ◇ X0) ◇ X4))) ◇ X6)) := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 X4 X5 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = ((X2 ◇ X0) ◇ ((X4 ◇ (X4 ◇ (((X1 ◇ X0) ◇ X0) ◇ X3))) ◇ X5)) := superpose eq11 eq9
  have eq28 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = (X2 ◇ (((X3 ◇ X0) ◇ X0) ◇ X4)) := superpose eq11 eq9
  have eq34 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) = X0 := superpose eq11 eq9
  have eq35 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ (X4 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) ◇ X5) = ((X3 ◇ ((X4 ◇ (X4 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) ◇ X5)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := superpose eq9 eq11
  have eq38 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) ◇ X4) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X5 ◇ (X5 ◇ ((X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) ◇ X4))) ◇ X6)) := superpose eq9 eq7
  have eq40 (X0 X1 X2 X3 X4 : G) : ((X4 ◇ X2) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) = X2 := superpose eq9 eq7
  have eq41 (X0 X2 : G) : (X2 ◇ X0) = (X0 ◇ X0) := superpose eq34 eq19
  have eq45 (X0 X2 X3 : G) : ((X2 ◇ (X2 ◇ X0)) ◇ X3) = (X0 ◇ X3) := superpose eq34 eq9
  have eq46 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ X0) ◇ X3) = ((X2 ◇ X0) ◇ X3) := superpose eq34 eq21
  have eq47 (X0 X1 X2 X3 X4 : G) : (((X1 ◇ X0) ◇ X0) ◇ X4) = (((X2 ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) := superpose eq34 eq20
  have eq49 (X0 X1 X2 X4 : G) : ((X1 ◇ (X1 ◇ X2)) ◇ X0) = (X2 ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq41 eq28
  have eq60 (X0 X2 X4 : G) : (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X0) ◇ X4)) := superpose eq45 eq49
  have eq63 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = ((X0 ◇ X0) ◇ X3) := superpose eq41 eq46
  have eq64 (X0 X1 X3 X4 : G) : (((X1 ◇ X0) ◇ X0) ◇ X4) = ((X0 ◇ X3) ◇ X4) := superpose eq45 eq47
  have eq65 (X0 X3 X4 : G) : ((X0 ◇ X0) ◇ X4) = ((X0 ◇ X3) ◇ X4) := superpose eq41 eq64
  have eq68 (X0 X2 X3 X4 X5 : G) : ((X4 ◇ (X4 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X5) = ((X3 ◇ ((X4 ◇ (X4 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X5)) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq65 eq35
  have eq69 (X0 X2 X3 X4 X5 : G) : ((X4 ◇ X4) ◇ X5) = ((X3 ◇ ((X4 ◇ X4) ◇ X5)) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq65 eq68
  have eq70 (X0 X2 X3 X4 X5 : G) : ((X4 ◇ X4) ◇ X5) = ((X3 ◇ X4) ◇ ((X0 ◇ X0) ◇ X2)) := superpose eq60 eq69
  have eq76 (X0 X1 X2 X3 X4 X5 X6 : G) : ((X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) ◇ X4) = (((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X5 ◇ X5) ◇ X6)) := superpose eq65 eq38
  have eq77 (X0 X2 X3 X4 X5 X6 : G) : ((X3 ◇ (X3 ◇ ((X0 ◇ X0) ◇ X2))) ◇ X4) = (((X0 ◇ X0) ◇ X2) ◇ ((X5 ◇ X5) ◇ X6)) := superpose eq65 eq76
  have eq78 (X0 X2 X5 X6 : G) : (((X0 ◇ X0) ◇ X2) ◇ ((X5 ◇ X5) ◇ X6)) = X2 := superpose eq34 eq77
  have eq79 (X0 X2 X3 X4 : G) : ((X4 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) = X2 := superpose eq65 eq40
  have eq80 (X4 X5 : G) : ((X4 ◇ X4) ◇ X5) = X4 := superpose eq79 eq70
  have eq84 (X0 X2 X3 : G) : ((X2 ◇ X0) ◇ X3) = X0 := superpose eq80 eq63
  have eq87 (X0 X2 X5 X6 : G) : (X0 ◇ ((X5 ◇ X5) ◇ X6)) = X2 := superpose eq80 eq78
  have eq94 (X0 X2 X5 : G) : (X0 ◇ X5) = X2 := superpose eq84 eq87
  have eq95 (X0 X3 : G) : X0 = X3 := superpose eq11 eq94
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq95 eq8
  subsumption eq119 eq95


@[equational_result]
theorem Equation19922_implies_Equation2 (G : Type*) [Magma G] (h : Equation19922 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X1 ◇ X2)) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq12
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq12 eq12
  have eq22 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq16 eq15
  have eq37 (X0 X4 : G) : X0 = X4 := superpose eq7 eq22
  have eq139 (X0 : G) : sK0 ≠ X0 := superpose eq37 eq8
  subsumption eq139 eq37


@[equational_result]
theorem Equation19925_implies_Equation2 (G : Type*) [Magma G] (h : Equation19925 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ ((((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq32 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq32 eq8
  subsumption eq51 eq32


@[equational_result]
theorem Equation19926_implies_Equation2 (G : Type*) [Magma G] (h : Equation19926 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq12
  have eq27 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq30 (X0 X3 : G) : X0 = X3 := superpose eq12 eq27
  have eq74 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq74 eq30


@[equational_result]
theorem Equation19928_implies_Equation2 (G : Type*) [Magma G] (h : Equation19928 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ ((X0 ◇ X1) ◇ X2)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq11
  have eq49 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq15 eq15
  have eq61 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq49 eq10
  have eq67 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq61 eq49
  have eq75 (X0 X3 : G) : X0 = X3 := superpose eq15 eq67
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq119 eq75


@[equational_result]
theorem Equation19929_implies_Equation2 (G : Type*) [Magma G] (h : Equation19929 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X0) ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq50 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq19 eq19
  have eq87 (X0 X3 : G) : X0 = X3 := superpose eq19 eq50
  have eq171 (X0 : G) : sK0 ≠ X0 := superpose eq87 eq8
  subsumption eq171 eq87


@[equational_result]
theorem Equation19930_implies_Equation2 (G : Type*) [Magma G] (h : Equation19930 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X0) ◇ X0) ◇ ((X4 ◇ (X4 ◇ X5)) ◇ X5))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq13
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq13 eq16
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq54 eq35


@[equational_result]
theorem Equation19931_implies_Equation2 (G : Type*) [Magma G] (h : Equation19931 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq12
  have eq26 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq29 (X0 X4 : G) : X0 = X4 := superpose eq12 eq26
  have eq73 (X0 : G) : sK0 ≠ X0 := superpose eq29 eq8
  subsumption eq73 eq29


@[equational_result]
theorem Equation19933_implies_Equation2 (G : Type*) [Magma G] (h : Equation19933 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X0)) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq11 eq11
  have eq21 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq16 eq15
  have eq47 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq47 eq8
  subsumption eq137 eq47


@[equational_result]
theorem Equation19934_implies_Equation2 (G : Type*) [Magma G] (h : Equation19934 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X2 ◇ X1) ◇ (X0 ◇ X1)) = X1 := superpose eq7 eq7
  have eq27 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq49 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq27 eq27
  have eq72 (X0 X3 : G) : X0 = X3 := superpose eq12 eq49
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq72 eq8
  subsumption eq126 eq72


@[equational_result]
theorem Equation19935_implies_Equation2 (G : Type*) [Magma G] (h : Equation19935 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X4 ◇ (X2 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq18 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq34 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq18 eq18
  have eq39 (X0 X4 : G) : X0 = X4 := superpose eq11 eq34
  have eq94 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq94 eq39


@[equational_result]
theorem Equation19936_implies_Equation2 (G : Type*) [Magma G] (h : Equation19936 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X6)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq25 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq11 eq25
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq72 eq28


@[equational_result]
theorem Equation19938_implies_Equation2 (G : Type*) [Magma G] (h : Equation19938 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq11 eq11
  have eq21 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq16 eq15
  have eq63 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq134 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq134 eq63


@[equational_result]
theorem Equation19939_implies_Equation2 (G : Type*) [Magma G] (h : Equation19939 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 X4 X5 : G) : ((X2 ◇ (X3 ◇ X1)) ◇ X2) = (X0 ◇ ((X4 ◇ (X5 ◇ (X1 ◇ X0))) ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X0))) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq25 (X0 X1 X2 X3 X5 : G) : ((X2 ◇ (X3 ◇ X1)) ◇ X2) = (X0 ◇ (X5 ◇ (X1 ◇ X0))) := superpose eq16 eq9
  have eq34 (X0 X1 X4 X5 : G) : (X0 ◇ X1) = (X4 ◇ (X5 ◇ (X1 ◇ X4))) := superpose eq11 eq25
  have eq39 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X1) = ((X4 ◇ X3) ◇ X0) := superpose eq11 eq25
  have eq54 (X1 X2 X3 : G) : ((X1 ◇ (X2 ◇ X3)) ◇ X1) = X3 := superpose eq16 eq39
  have eq55 (X0 X1 X5 : G) : (X0 ◇ (X5 ◇ (X1 ◇ X0))) = X1 := superpose eq54 eq25
  have eq56 (X0 X1 : G) : (X0 ◇ X1) = X1 := superpose eq55 eq34
  have eq65 (X0 X1 : G) : (X0 ◇ (X1 ◇ X0)) = X1 := superpose eq56 eq55
  have eq74 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq56 eq65
  have eq81 (X0 X2 : G) : X0 = X2 := superpose eq74 eq74
  have eq83 (X0 : G) : sK0 ≠ X0 := superpose eq81 eq8
  subsumption eq83 eq81


@[equational_result]
theorem Equation19940_implies_Equation2 (G : Type*) [Magma G] (h : Equation19940 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X4 ◇ (X1 ◇ X3)))) = X2 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq36 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq19 eq19
  have eq41 (X0 X5 : G) : X0 = X5 := superpose eq11 eq36
  have eq77 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq77 eq41


@[equational_result]
theorem Equation19941_implies_Equation2 (G : Type*) [Magma G] (h : Equation19941 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X6)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq25 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq11 eq25
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq72 eq28


@[equational_result]
theorem Equation19943_implies_Equation2 (G : Type*) [Magma G] (h : Equation19943 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X2) ◇ ((((X3 ◇ (X4 ◇ X3)) ◇ X5) ◇ X0) ◇ X1)) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X3 X4 : G) : ((((X2 ◇ (X3 ◇ X2)) ◇ X1) ◇ X4) ◇ (X0 ◇ X1)) = X4 := superpose eq7 eq7
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ (((X3 ◇ X4) ◇ X0) ◇ X1)) = X2 := superpose eq11 eq7
  have eq35 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq11 eq10
  have eq52 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq35 eq21
  have eq57 (X0 X2 X3 : G) : (X2 ◇ X0) = X3 := superpose eq52 eq35
  have eq63 (X0 X3 : G) : X0 = X3 := superpose eq57 eq57
  have eq75 (X0 : G) : sK0 ≠ X0 := superpose eq63 eq8
  subsumption eq75 eq63


@[equational_result]
theorem Equation19944_implies_Equation2 (G : Type*) [Magma G] (h : Equation19944 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((((X3 ◇ (X4 ◇ X3)) ◇ X3) ◇ X0) ◇ ((X3 ◇ (X4 ◇ X3)) ◇ X3))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq13
  have eq35 (X0 X3 : G) : X0 = X3 := superpose eq13 eq16
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq35 eq8
  subsumption eq54 eq35


@[equational_result]
theorem Equation19945_implies_Equation2 (G : Type*) [Magma G] (h : Equation19945 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X4) ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X2)) = X4 := superpose eq7 eq7
  have eq37 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq12
  have eq78 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq37 eq37
  have eq97 (X0 X3 : G) : X0 = X3 := superpose eq37 eq78
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq97 eq8
  subsumption eq153 eq97


@[equational_result]
theorem Equation19946_implies_Equation2 (G : Type*) [Magma G] (h : Equation19946 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X6)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq25 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq11 eq25
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq72 eq28


@[equational_result]
theorem Equation19948_implies_Equation2 (G : Type*) [Magma G] (h : Equation19948 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 : G) : ((((X1 ◇ (X2 ◇ X2)) ◇ X3) ◇ X4) ◇ X0) = X4 := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq11 eq11
  have eq21 (X0 X3 X4 : G) : (X3 ◇ X0) = X4 := superpose eq16 eq15
  have eq44 (X0 X4 : G) : X0 = X4 := superpose eq7 eq21
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq44 eq8
  subsumption eq153 eq44


@[equational_result]
theorem Equation19949_implies_Equation2 (G : Type*) [Magma G] (h : Equation19949 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X0)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq25 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq14 eq14
  have eq28 (X0 X3 : G) : X0 = X3 := superpose eq11 eq25
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq72 eq28


@[equational_result]
theorem Equation19950_implies_Equation2 (G : Type*) [Magma G] (h : Equation19950 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ ((X4 ◇ (X0 ◇ X0)) ◇ X0))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq15 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq12 eq12
  have eq33 (X0 X3 : G) : X0 = X3 := superpose eq12 eq15
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq52 eq33


@[equational_result]
theorem Equation19951_implies_Equation2 (G : Type*) [Magma G] (h : Equation19951 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X6)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq25 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq11 eq25
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq72 eq28


@[equational_result]
theorem Equation19953_implies_Equation2 (G : Type*) [Magma G] (h : Equation19953 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X1)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 X4 X5 : G) : ((((X1 ◇ (X2 ◇ X3)) ◇ X4) ◇ X5) ◇ X0) = X5 := superpose eq7 eq11
  have eq16 (X0 X1 X2 X3 : G) : (((X1 ◇ X2) ◇ X3) ◇ X0) = X3 := superpose eq11 eq11
  have eq21 (X0 X4 X5 : G) : (X4 ◇ X0) = X5 := superpose eq16 eq15
  have eq38 (X0 X5 : G) : X0 = X5 := superpose eq7 eq21
  have eq143 (X0 : G) : sK0 ≠ X0 := superpose eq38 eq8
  subsumption eq143 eq38


@[equational_result]
theorem Equation19954_implies_Equation2 (G : Type*) [Magma G] (h : Equation19954 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ X3) ◇ (X0 ◇ X1)) = X3 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq12
  have eq34 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq73 (X0 X4 : G) : X0 = X4 := superpose eq12 eq34
  have eq174 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq174 eq73


@[equational_result]
theorem Equation19955_implies_Equation2 (G : Type*) [Magma G] (h : Equation19955 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ (X4 ◇ X0))) = X2 := superpose eq7 eq7
  have eq11 (X0 X1 X2 X4 X5 X6 : G) : ((X1 ◇ X2) ◇ (X0 ◇ (X4 ◇ (X5 ◇ X6)))) = X2 := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq38 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq19 eq19
  have eq73 (X0 X6 : G) : X0 = X6 := superpose eq11 eq38
  have eq155 (X0 : G) : sK0 ≠ X0 := superpose eq73 eq8
  subsumption eq155 eq73


@[equational_result]
theorem Equation19956_implies_Equation2 (G : Type*) [Magma G] (h : Equation19956 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 X5 X6 X7 : G) : ((X1 ◇ X2) ◇ ((X3 ◇ X0) ◇ ((X5 ◇ (X6 ◇ X7)) ◇ X7))) = X2 := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq10
  have eq16 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq13 eq13
  have eq36 (X0 X3 : G) : X0 = X3 := superpose eq13 eq16
  have eq55 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq55 eq36


@[equational_result]
theorem Equation19957_implies_Equation2 (G : Type*) [Magma G] (h : Equation19957 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 X5 : G) : ((X1 ◇ X0) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ X5)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 X8 : G) : ((X1 ◇ X2) ◇ (X0 ◇ X8)) = X2 := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : ((X1 ◇ X2) ◇ X0) = X2 := superpose eq7 eq11
  have eq25 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq15 eq15
  have eq28 (X0 X4 : G) : X0 = X4 := superpose eq11 eq25
  have eq72 (X0 : G) : sK0 ≠ X0 := superpose eq28 eq8
  subsumption eq72 eq28


@[equational_result]
theorem Equation19960_implies_Equation2 (G : Type*) [Magma G] (h : Equation19960 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = X1 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq7 eq14
  have eq43 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq43 eq21


@[equational_result]
theorem Equation19963_implies_Equation2 (G : Type*) [Magma G] (h : Equation19963 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = ((((X0 ◇ (X0 ◇ X1)) ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) ◇ (((X1 ◇ X1) ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 : G) : (X1 ◇ X1) = (((((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2) ◇ (((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) ◇ X2)) ◇ X0) := superpose eq7 eq9
  have eq20 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq15
  have eq33 (X0 X2 : G) : X0 = X2 := superpose eq20 eq20
  have eq98 (X0 : G) : sK0 ≠ X0 := superpose eq33 eq8
  subsumption eq98 eq33


@[equational_result]
theorem Equation19965_implies_Equation2 (G : Type*) [Magma G] (h : Equation19965 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq17 (X0 X1 X2 : G) : (X1 ◇ X1) = ((((X0 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ (X1 ◇ X1))) ◇ X0) := superpose eq7 eq10
  have eq18 (X0 X1 X2 : G) : (X1 ◇ X1) = (((((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) ◇ (((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X1))) ◇ (X0 ◇ X0)) := superpose eq10 eq10
  have eq24 (X0 X1 X2 X5 : G) : (X1 ◇ ((X2 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X5)) ◇ (X1 ◇ (X1 ◇ X5))))) = X2 := superpose eq9 eq9
  have eq25 (X0 X1 X2 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X1 ◇ X2))))) := superpose eq10 eq9
  have eq34 (X0 X1 X2 X3 X4 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ (((X2 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (((X2 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4))))) ◇ X0) = X2 := superpose eq9 eq7
  have eq37 (X0 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := superpose eq24 eq25
  have eq39 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := superpose eq7 eq37
  have eq42 (X0 X1 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := superpose eq10 eq37
  have eq57 (X0 X1 X2 X3 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X2 ◇ X3)))) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X2 ◇ (X2 ◇ X3))))) ◇ X0) = X2 := superpose eq39 eq34
  have eq59 (X0 X1 X2 : G) : ((((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ X2))) ◇ X0) = X2 := superpose eq39 eq57
  have eq60 (X1 : G) : (X1 ◇ X1) = X1 := superpose eq59 eq17
  have eq65 (X0 X1 X2 : G) : (X1 ◇ X1) = ((((X0 ◇ X0) ◇ X2) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := superpose eq60 eq18
  have eq79 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ X2) ◇ (X1 ◇ X1)) ◇ X0) := superpose eq60 eq65
  have eq80 (X0 X1 X2 : G) : (((X0 ◇ X2) ◇ X1) ◇ X0) = X1 := superpose eq60 eq79
  have eq94 (X0 X1 : G) : (X0 ◇ X1) = X0 := superpose eq60 eq42
  have eq97 (X0 X1 X2 : G) : ((X0 ◇ X2) ◇ X0) = X1 := superpose eq94 eq80
  have eq107 (X0 X1 : G) : (X0 ◇ X0) = X1 := superpose eq94 eq97
  have eq114 (X0 X2 : G) : X0 = X2 := superpose eq107 eq107
  have eq122 (X0 : G) : sK0 ≠ X0 := superpose eq114 eq8
  subsumption eq122 eq114


@[equational_result]
theorem Equation19967_implies_Equation2 (G : Type*) [Magma G] (h : Equation19967 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = X2 := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq36 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq95 (X0 : G) : sK0 ≠ X0 := superpose eq36 eq8
  subsumption eq95 eq36


@[equational_result]
theorem Equation19970_implies_Equation2 (G : Type*) [Magma G] (h : Equation19970 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq14 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) := superpose eq10 eq10
  have eq73 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ X0) := superpose eq7 eq14
  have eq96 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq73
  have eq204 (X0 X2 : G) : X0 = X2 := superpose eq96 eq96
  have eq352 (X0 : G) : sK0 ≠ X0 := superpose eq204 eq8
  subsumption eq352 eq204


@[equational_result]
theorem Equation19973_implies_Equation2 (G : Type*) [Magma G] (h : Equation19973 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq12 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq30 (X0 X2 : G) : X0 = X2 := superpose eq12 eq12
  have eq52 (X0 : G) : sK0 ≠ X0 := superpose eq30 eq8
  subsumption eq52 eq30


@[equational_result]
theorem Equation19975_implies_Equation2 (G : Type*) [Magma G] (h : Equation19975 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X1 := superpose eq9 eq9
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq7 eq9
  have eq18 (X0 : G) : (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := superpose eq9 eq10
  have eq31 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq11 eq18
  have eq32 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := superpose eq31 eq12
  have eq39 (X0 X1 X2 : G) : (X2 ◇ X2) = (X1 ◇ (X0 ◇ X1)) := superpose eq31 eq32
  have eq66 (X0 X1 X2 : G) : (X1 ◇ (X2 ◇ X1)) = X0 := superpose eq31 eq39
  have eq78 (X0 X3 : G) : X0 = X3 := superpose eq66 eq66
  have eq106 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq106 eq78


@[equational_result]
theorem Equation19976_implies_Equation2 (G : Type*) [Magma G] (h : Equation19976 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq13 (X0 X1 X2 : G) : ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) := superpose eq7 eq10
  have eq17 (X0 X1 : G) : ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := superpose eq10 eq7
  have eq21 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X2)) ◇ (X0 ◇ X2)) := superpose eq13 eq10
  have eq32 (X0 : G) : (X0 ◇ X0) = ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := superpose eq21 eq21
  have eq34 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3)) ◇ ((X2 ◇ X2) ◇ ((X0 ◇ X0) ◇ X3))) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X0)) := superpose eq21 eq21
  have eq36 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X3)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X0)) := superpose eq13 eq34
  have eq40 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq17
  have eq51 (X0 X1 : G) : ((X0 ◇ X0) ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) = X0 := superpose eq17 eq7
  have eq56 (X0 : G) : (X0 ◇ X0) = X0 := superpose eq51 eq32
  have eq61 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ X0) ◇ X3)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) ◇ (X0 ◇ X0)) := superpose eq56 eq36
  have eq63 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := superpose eq56 eq40
  have eq92 (X0 X1 X2 X3 : G) : (X1 ◇ X1) = (((((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3)) ◇ ((X1 ◇ X1) ◇ (X2 ◇ X3))) ◇ X0) := superpose eq56 eq61
  have eq93 (X0 X1 X2 X3 : G) : (((((X2 ◇ X2) ◇ (X2 ◇ X2)) ◇ (X0 ◇ X3)) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) = X1 := superpose eq56 eq92
  have eq94 (X0 X1 X2 X3 : G) : ((((X2 ◇ X2) ◇ (X0 ◇ X3)) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) = X1 := superpose eq56 eq93
  have eq95 (X0 X1 X2 X3 : G) : (((X2 ◇ (X0 ◇ X3)) ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) = X1 := superpose eq56 eq94
  have eq99 (X0 X1 : G) : (X1 ◇ X1) = (X1 ◇ X0) := superpose eq56 eq63
  have eq100 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq56 eq99
  have eq102 (X0 X1 X2 X3 : G) : ((X2 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0) = X1 := superpose eq100 eq95
  have eq109 (X0 X1 X2 : G) : (X2 ◇ X0) = X1 := superpose eq100 eq102
  have eq110 (X0 X1 : G) : X0 = X1 := superpose eq56 eq109
  have eq118 (X0 : G) : sK0 ≠ X0 := superpose eq110 eq8
  subsumption eq118 eq110


@[equational_result]
theorem Equation19977_implies_Equation2 (G : Type*) [Magma G] (h : Equation19977 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X1 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq49 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq120 (X0 : G) : sK0 ≠ X0 := superpose eq49 eq8
  subsumption eq120 eq49


@[equational_result]
theorem Equation19979_implies_Equation2 (G : Type*) [Magma G] (h : Equation19979 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 : G) : ((X0 ◇ (X2 ◇ X0)) ◇ X3) = ((X1 ◇ X1) ◇ ((((X0 ◇ (X2 ◇ X0)) ◇ X3) ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq22 (X0 X1 X5 : G) : ((X5 ◇ X5) ◇ ((X0 ◇ X1) ◇ X5)) = X0 := superpose eq9 eq10
  have eq32 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X2 := superpose eq9 eq22
  have eq78 (X0 X3 : G) : X0 = X3 := superpose eq7 eq32
  have eq168 (X0 : G) : sK0 ≠ X0 := superpose eq78 eq8
  subsumption eq168 eq78


@[equational_result]
theorem Equation19981_implies_Equation2 (G : Type*) [Magma G] (h : Equation19981 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X4)) = X2 := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X0) = X2 := superpose eq9 eq9
  have eq51 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq131 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq131 eq51


@[equational_result]
theorem Equation19983_implies_Equation2 (G : Type*) [Magma G] (h : Equation19983 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq14 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq39 (X0 X2 : G) : X0 = X2 := superpose eq14 eq14
  have eq85 (X0 : G) : sK0 ≠ X0 := superpose eq39 eq8
  subsumption eq85 eq39


@[equational_result]
theorem Equation19985_implies_Equation2 (G : Type*) [Magma G] (h : Equation19985 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X1) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq16 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq11
  have eq59 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq59 eq8
  subsumption eq154 eq59


@[equational_result]
theorem Equation19987_implies_Equation2 (G : Type*) [Magma G] (h : Equation19987 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X2 ◇ X2))) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = ((((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) ◇ X0) := superpose eq7 eq7
  have eq43 (X0 X1 X2 : G) : (((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X2))) = X0 := superpose eq7 eq11
  have eq69 (X0 X2 : G) : (X2 ◇ X2) = (X0 ◇ X0) := superpose eq43 eq12
  have eq70 (X0 X2 : G) : (X2 ◇ X2) = X0 := superpose eq7 eq69
  have eq157 (X0 X2 : G) : X0 = X2 := superpose eq7 eq70
  have eq292 (X0 : G) : sK0 ≠ X0 := superpose eq157 eq8
  subsumption eq292 eq157


@[equational_result]
theorem Equation19988_implies_Equation2 (G : Type*) [Magma G] (h : Equation19988 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (((X0 ◇ (X2 ◇ X2)) ◇ X2) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X2)) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq18 (X0 X1 X2 X3 X4 : G) : ((X2 ◇ X2) ◇ ((X3 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X1 ◇ (X4 ◇ X4)) ◇ X4))) = X3 := superpose eq9 eq7
  have eq19 (X0 X1 X3 X4 : G) : (((X0 ◇ X0) ◇ X1) ◇ ((X3 ◇ (X4 ◇ X4)) ◇ X4)) = X3 := superpose eq9 eq7
  have eq225 (X0 X3 X4 : G) : (X0 ◇ ((X3 ◇ (X4 ◇ X4)) ◇ X4)) = X3 := superpose eq7 eq19
  have eq288 (X1 X2 X3 : G) : ((X2 ◇ X2) ◇ X1) = X3 := superpose eq225 eq18
  have eq308 (X0 X3 : G) : X0 = X3 := superpose eq7 eq288
  have eq428 (X0 : G) : sK0 ≠ X0 := superpose eq308 eq8
  subsumption eq428 eq308


@[equational_result]
theorem Equation19989_implies_Equation2 (G : Type*) [Magma G] (h : Equation19989 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq12
  have eq53 (X0 X2 : G) : X0 = X2 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation19991_implies_Equation2 (G : Type*) [Magma G] (h : Equation19991 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq35 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq11
  have eq57 (X0 X3 : G) : X0 = X3 := superpose eq7 eq35
  have eq137 (X0 : G) : sK0 ≠ X0 := superpose eq57 eq8
  subsumption eq137 eq57


@[equational_result]
theorem Equation19992_implies_Equation2 (G : Type*) [Magma G] (h : Equation19992 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ (X3 ◇ X3))) = X2 := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X3 ◇ X4)))) := superpose eq7 eq7
  have eq36 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq9 eq10
  have eq51 (X0 X1 : G) : X0 = X1 := superpose eq9 eq36
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq153 eq51


@[equational_result]
theorem Equation19993_implies_Equation2 (G : Type*) [Magma G] (h : Equation19993 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ (X0 ◇ X4)) := superpose eq7 eq7
  have eq19 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq93 (X0 X2 : G) : X0 = X2 := superpose eq19 eq19
  have eq145 (X0 : G) : sK0 ≠ X0 := superpose eq93 eq8
  subsumption eq145 eq93


@[equational_result]
theorem Equation19994_implies_Equation2 (G : Type*) [Magma G] (h : Equation19994 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 X3 : G) : (X2 ◇ X3) = ((X1 ◇ X1) ◇ X0) := superpose eq7 eq7
  have eq19 (X0 X1 X2 : G) : (X1 ◇ X2) = X0 := superpose eq7 eq12
  have eq53 (X0 X5 : G) : X0 = X5 := superpose eq7 eq19
  have eq119 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq119 eq53


@[equational_result]
theorem Equation19997_implies_Equation2 (G : Type*) [Magma G] (h : Equation19997 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X0)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq10 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) = X1 := superpose eq7 eq7
  have eq11 (X0 X1 : G) : (X1 ◇ (X0 ◇ X0)) = X1 := superpose eq10 eq9
  have eq13 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X2)) = X0 := superpose eq11 eq7
  have eq21 (X0 X3 : G) : X0 = X3 := superpose eq13 eq13
  have eq29 (X0 : G) : sK0 ≠ X0 := superpose eq21 eq8
  subsumption eq29 eq21


@[equational_result]
theorem Equation20000_implies_Equation2 (G : Type*) [Magma G] (h : Equation20000 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X2)) := superpose eq7 eq7
  have eq15 (X0 X1 : G) : (X1 ◇ (((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1)) = X0 := superpose eq7 eq10
  have eq66 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq15 eq7
  have eq75 (X0 X3 : G) : X0 = X3 := superpose eq7 eq66
  have eq188 (X0 : G) : sK0 ≠ X0 := superpose eq75 eq8
  subsumption eq188 eq75


@[equational_result]
theorem Equation20002_implies_Equation2 (G : Type*) [Magma G] (h : Equation20002 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 : G) : (X2 ◇ X2) = ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq53 (X0 X2 : G) : X0 = X2 := superpose eq16 eq16
  have eq154 (X0 : G) : sK0 ≠ X0 := superpose eq53 eq8
  subsumption eq154 eq53


@[equational_result]
theorem Equation20004_implies_Equation2 (G : Type*) [Magma G] (h : Equation20004 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X4 : G) : (X1 ◇ (X0 ◇ X2)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X4)) := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = X1 := superpose eq7 eq7
  have eq12 (X0 X1 X2 : G) : (X1 ◇ (X0 ◇ X2)) = X1 := superpose eq11 eq10
  have eq14 (X0 X1 X3 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X3)) = X0 := superpose eq12 eq7
  have eq16 (X0 X1 : G) : (X1 ◇ X0) = X1 := superpose eq12 eq12
  have eq17 (X0 X1 : G) : ((X1 ◇ X1) ◇ X1) = X0 := superpose eq16 eq14
  have eq21 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq16 eq17
  have eq22 (X0 X2 : G) : X0 = X2 := superpose eq21 eq21
  have eq24 (X0 : G) : sK0 ≠ X0 := superpose eq22 eq8
  subsumption eq24 eq22


@[equational_result]
theorem Equation20007_implies_Equation2 (G : Type*) [Magma G] (h : Equation20007 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X1 ◇ (X1 ◇ X0)) ◇ X2) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (((X1 ◇ X1) ◇ X0) ◇ X3)) := superpose eq7 eq7
  have eq23 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) ◇ X2) = X0 := superpose eq7 eq9
  have eq33 (X0 X1 X2 X3 : G) : (((X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) ◇ ((X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))) ◇ (X0 ◇ X2))) ◇ X3) = X2 := superpose eq23 eq23
  have eq50 (X0 X2 X3 : G) : (X0 ◇ X3) = X2 := superpose eq23 eq33
  have eq51 (X0 X3 : G) : X0 = X3 := superpose eq7 eq50
  have eq148 (X0 : G) : sK0 ≠ X0 := superpose eq51 eq8
  subsumption eq148 eq51


@[equational_result]
theorem Equation20009_implies_Equation2 (G : Type*) [Magma G] (h : Equation20009 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X2 : G) : X0 = X2 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation20010_implies_Equation2 (G : Type*) [Magma G] (h : Equation20010 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation20012_implies_Equation2 (G : Type*) [Magma G] (h : Equation20012 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20013_implies_Equation2 (G : Type*) [Magma G] (h : Equation20013 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20014_implies_Equation2 (G : Type*) [Magma G] (h : Equation20014 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20016_implies_Equation2 (G : Type*) [Magma G] (h : Equation20016 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 : G) : (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = X1 := superpose eq7 eq7
  have eq13 (X0 X1 : G) : X0 = X1 := superpose eq7 eq10
  have eq44 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq44 eq13


@[equational_result]
theorem Equation20018_implies_Equation2 (G : Type*) [Magma G] (h : Equation20018 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ X0) = X2 := superpose eq7 eq7
  have eq15 (X0 X2 : G) : X0 = X2 := superpose eq7 eq11
  have eq51 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq51 eq15


@[equational_result]
theorem Equation20020_implies_Equation2 (G : Type*) [Magma G] (h : Equation20020 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20021_implies_Equation2 (G : Type*) [Magma G] (h : Equation20021 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20022_implies_Equation2 (G : Type*) [Magma G] (h : Equation20022 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20024_implies_Equation2 (G : Type*) [Magma G] (h : Equation20024 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation20025_implies_Equation2 (G : Type*) [Magma G] (h : Equation20025 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


@[equational_result]
theorem Equation20026_implies_Equation2 (G : Type*) [Magma G] (h : Equation20026 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20028_implies_Equation2 (G : Type*) [Magma G] (h : Equation20028 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20029_implies_Equation2 (G : Type*) [Magma G] (h : Equation20029 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20030_implies_Equation2 (G : Type*) [Magma G] (h : Equation20030 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20031_implies_Equation2 (G : Type*) [Magma G] (h : Equation20031 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20033_implies_Equation2 (G : Type*) [Magma G] (h : Equation20033 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X0 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))))) = X3 := superpose eq7 eq7
  have eq11 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 X2 : G) : (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := superpose eq7 eq11
  have eq38 (X0 X3 : G) : (X0 ◇ X0) = X3 := superpose eq25 eq9
  have eq41 (X0 X2 : G) : X0 = X2 := superpose eq7 eq38
  have eq66 (X0 : G) : sK0 ≠ X0 := superpose eq41 eq8
  subsumption eq66 eq41


@[equational_result]
theorem Equation20035_implies_Equation2 (G : Type*) [Magma G] (h : Equation20035 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X4 : G) : X0 = X4 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20037_implies_Equation2 (G : Type*) [Magma G] (h : Equation20037 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 : G) : (X2 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := superpose eq7 eq7
  have eq15 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = ((((X3 ◇ (X0 ◇ X2)) ◇ X2) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X0) := superpose eq7 eq10
  have eq28 (X0 X1 X2 X3 : G) : (X1 ◇ X0) = (((X2 ◇ X2) ◇ ((X3 ◇ (X0 ◇ X2)) ◇ X2)) ◇ X0) := superpose eq10 eq15
  have eq29 (X0 X1 : G) : (X0 ◇ X0) = (X1 ◇ X0) := superpose eq7 eq28
  have eq31 (X0 X1 : G) : ((X1 ◇ X1) ◇ (X1 ◇ X1)) = X0 := superpose eq29 eq7
  have eq45 (X0 X2 : G) : X0 = X2 := superpose eq31 eq31
  have eq54 (X0 : G) : sK0 ≠ X0 := superpose eq45 eq8
  subsumption eq54 eq45


@[equational_result]
theorem Equation20039_implies_Equation2 (G : Type*) [Magma G] (h : Equation20039 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq65 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq65 eq14


@[equational_result]
theorem Equation20043_implies_Equation2 (G : Type*) [Magma G] (h : Equation20043 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ (X3 ◇ X2)) ◇ X4)) = X3 := superpose eq7 eq7
  have eq16 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq9 eq9
  have eq55 (X0 X4 : G) : X0 = X4 := superpose eq7 eq16
  have eq163 (X0 : G) : sK0 ≠ X0 := superpose eq55 eq8
  subsumption eq163 eq55


@[equational_result]
theorem Equation20045_implies_Equation2 (G : Type*) [Magma G] (h : Equation20045 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq10 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X1)) := superpose eq7 eq7
  have eq25 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq10
  have eq89 (X0 X3 : G) : X0 = X3 := superpose eq7 eq25
  have eq194 (X0 : G) : sK0 ≠ X0 := superpose eq89 eq8
  subsumption eq194 eq89


@[equational_result]
theorem Equation20046_implies_Equation2 (G : Type*) [Magma G] (h : Equation20046 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X1 ◇ X1) ◇ ((X2 ◇ X0) ◇ X2)) := superpose eq7 eq7
  have eq48 (X0 X1 : G) : (X1 ◇ X1) = X0 := superpose eq7 eq9
  have eq68 (X0 X2 : G) : X0 = X2 := superpose eq48 eq48
  have eq173 (X0 : G) : sK0 ≠ X0 := superpose eq68 eq8
  subsumption eq173 eq68


@[equational_result]
theorem Equation20047_implies_Equation2 (G : Type*) [Magma G] (h : Equation20047 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq60 eq14


@[equational_result]
theorem Equation20048_implies_Equation2 (G : Type*) [Magma G] (h : Equation20048 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq12
  have eq49 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq49 eq16


@[equational_result]
theorem Equation20050_implies_Equation2 (G : Type*) [Magma G] (h : Equation20050 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ (X1 ◇ X0)) ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 : G) : (((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := superpose eq7 eq7
  have eq12 (X0 X1 X2 X3 : G) : ((X2 ◇ (X0 ◇ X3)) ◇ (X2 ◇ (X0 ◇ X3))) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X3 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X1 ◇ X0))) := superpose eq10 eq10
  have eq13 (X0 X1 X2 : G) : (X2 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := superpose eq7 eq10
  have eq37 (X0 X1 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ X2)) = (((X3 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))) ◇ (X3 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))))) ◇ (X0 ◇ (X3 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))))) := superpose eq9 eq10
  have eq44 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1))) := superpose eq9 eq10
  have eq56 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = ((((X0 ◇ (X1 ◇ X2)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2) := superpose eq7 eq44
  have eq57 (X0 X1 X2 X3 : G) : (X3 ◇ X2) = (((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X1)) ◇ X2) := superpose eq13 eq56
  have eq58 (X2 X3 : G) : (X2 ◇ X2) = (X3 ◇ X2) := superpose eq7 eq57
  have eq60 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X2 ◇ X0) ◇ (X1 ◇ X1))) := superpose eq58 eq9
  have eq78 (X0 X2 X3 X4 : G) : (X4 ◇ (X0 ◇ X2)) = (((X3 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))) := superpose eq60 eq37
  have eq83 (X0 X2 X4 : G) : (X4 ◇ (X0 ◇ X2)) = X0 := superpose eq10 eq78
  have eq88 (X0 X1 X2 X3 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X3 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X1 ◇ X0))) = X2 := superpose eq83 eq12
  have eq93 (X0 X1 X2 : G) : (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X2 := superpose eq83 eq88
  have eq94 (X1 X2 : G) : (X1 ◇ X1) = X2 := superpose eq83 eq93
  have eq114 (X0 X2 : G) : X0 = X2 := superpose eq94 eq94
  have eq126 (X0 : G) : sK0 ≠ X0 := superpose eq114 eq8
  subsumption eq126 eq114


@[equational_result]
theorem Equation20052_implies_Equation2 (G : Type*) [Magma G] (h : Equation20052 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq11 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ X0) = X2 := superpose eq7 eq7
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq11
  have eq60 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq60 eq14


@[equational_result]
theorem Equation20054_implies_Equation2 (G : Type*) [Magma G] (h : Equation20054 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation20055_implies_Equation2 (G : Type*) [Magma G] (h : Equation20055 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq12 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq14 (X0 : G) : sK0 ≠ X0 := superpose eq12 eq8
  subsumption eq14 eq12


@[equational_result]
theorem Equation20056_implies_Equation2 (G : Type*) [Magma G] (h : Equation20056 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20058_implies_Equation2 (G : Type*) [Magma G] (h : Equation20058 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20059_implies_Equation2 (G : Type*) [Magma G] (h : Equation20059 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20060_implies_Equation2 (G : Type*) [Magma G] (h : Equation20060 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20062_implies_Equation2 (G : Type*) [Magma G] (h : Equation20062 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20063_implies_Equation2 (G : Type*) [Magma G] (h : Equation20063 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20064_implies_Equation2 (G : Type*) [Magma G] (h : Equation20064 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20065_implies_Equation2 (G : Type*) [Magma G] (h : Equation20065 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X1 ◇ X3)) ◇ X4)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq16 (X0 X5 : G) : X0 = X5 := superpose eq7 eq7
  have eq18 (X0 : G) : sK0 ≠ X0 := superpose eq16 eq8
  subsumption eq18 eq16


@[equational_result]
theorem Equation20068_implies_Equation2 (G : Type*) [Magma G] (h : Equation20068 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X1 X2 X3 : G) : ((X3 ◇ (X3 ◇ X0)) ◇ X3) = ((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ X0) ◇ (X2 ◇ X2))) := superpose eq7 eq7
  have eq10 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ (((X4 ◇ X4) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) ◇ (X4 ◇ X4))) = (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) := superpose eq7 eq9
  have eq11 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X4) ◇ (((X5 ◇ X5) ◇ (((X3 ◇ X3) ◇ X1) ◇ (X3 ◇ X3))) ◇ (X5 ◇ X5))) = (((X2 ◇ X2) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq9 eq9
  have eq14 (X0 X1 X2 X4 X5 : G) : ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1))) = ((X4 ◇ X4) ◇ (((X5 ◇ X5) ◇ X2) ◇ (X5 ◇ X5))) := superpose eq9 eq9
  have eq15 (X0 X1 X2 X3 X4 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2))) ◇ X1) = ((X3 ◇ X3) ◇ (X0 ◇ (X4 ◇ X4))) := superpose eq7 eq9
  have eq19 (X0 X1 X2 : G) : ((X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0))) ◇ X1) = X0 := superpose eq7 eq9
  have eq21 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ (((X4 ◇ (X4 ◇ X2)) ◇ ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1)))) ◇ (X4 ◇ (X4 ◇ X2)))) = X4 := superpose eq9 eq7
  have eq23 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq9 eq7
  have eq25 (X0 X1 X3 X4 : G) : (((X1 ◇ X1) ◇ X0) ◇ (X1 ◇ X1)) = ((X3 ◇ X3) ◇ (X0 ◇ (X4 ◇ X4))) := superpose eq7 eq10
  have eq26 (X1 X2 X3 X4 X5 : G) : ((X4 ◇ X4) ◇ (((X5 ◇ X5) ◇ (((X3 ◇ X3) ◇ X1) ◇ (X3 ◇ X3))) ◇ (X5 ◇ X5))) = (X1 ◇ (X2 ◇ X2)) := superpose eq7 eq11
  have eq31 (X0 X1 X2 : G) : (X1 ◇ X1) = (((X2 ◇ X2) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq9 eq19
  have eq34 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ X0) ◇ (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := superpose eq9 eq19
  have eq35 (X0 X1 X2 X3 : G) : ((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ ((X2 ◇ X2) ◇ X3)) ◇ (X1 ◇ X1))) = X3 := superpose eq9 eq19
  have eq40 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ (((X2 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X0))) ◇ X0) ◇ (X2 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X0))))) = X2 := superpose eq19 eq7
  have eq41 (X1 X2 : G) : (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X2 ◇ X2)) := superpose eq7 eq31
  have eq43 (X0 X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ (X1 ◇ X1))) := superpose eq41 eq23
  have eq46 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := superpose eq41 eq34
  have eq47 (X0 X1 : G) : (X1 ◇ X1) = (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ (X1 ◇ X1)) := superpose eq41 eq46
  have eq48 (X1 X2 : G) : (X1 ◇ X1) = ((X2 ◇ X2) ◇ (X1 ◇ X1)) := superpose eq47 eq43
  have eq336 (X0 X1 : G) : (X1 ◇ X1) = (X0 ◇ X0) := superpose eq48 eq41
  have eq384 (X0 X1 X2 X3 X4 X5 : G) : ((X4 ◇ X4) ◇ ((X1 ◇ (X3 ◇ X3)) ◇ (X5 ◇ X5))) = ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) := superpose eq25 eq25
  have eq619 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X2)) = X2 := superpose eq336 eq7
  have eq2006 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : ((((X6 ◇ X6) ◇ X2) ◇ (X6 ◇ X6)) ◇ (X7 ◇ X7)) = ((X3 ◇ X3) ◇ (((X4 ◇ X4) ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1))) ◇ (X5 ◇ X5))) ◇ (X4 ◇ X4))) := superpose eq14 eq26
  have eq2160 (X0 X1 X2 X3 X4 : G) : (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ (((X2 ◇ X2) ◇ ((X3 ◇ X3) ◇ X4)) ◇ (X2 ◇ X2))) ◇ (X1 ◇ X1))) ◇ ((X3 ◇ X3) ◇ X4)) = X4 := superpose eq26 eq19
  have eq2365 (X0 X1 X3 X4 : G) : (((X0 ◇ X0) ◇ (X4 ◇ (X1 ◇ X1))) ◇ ((X3 ◇ X3) ◇ X4)) = X4 := superpose eq35 eq2160
  have eq3870 (X0 X1 X2 X3 X4 X5 X6 X7 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ ((((X3 ◇ X3) ◇ (X0 ◇ (X1 ◇ X1))) ◇ ((X6 ◇ X6) ◇ (((X7 ◇ X7) ◇ (((X4 ◇ X4) ◇ (((X5 ◇ X5) ◇ X0) ◇ (X5 ◇ X5))) ◇ (X4 ◇ X4))) ◇ (X7 ◇ X7)))) ◇ ((X3 ◇ X3) ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq26 eq21
  have eq6971 (X0 X1 X2 : G) : ((((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2))) ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := superpose eq2365 eq19
  have eq27006 (X0 X1 X2 : G) : (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2)))) = X0 := superpose eq619 eq40
  have eq27026 (X0 X1 : G) : (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := superpose eq41 eq27006
  have eq27219 (X0 X1 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4))) = ((X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) := superpose eq27026 eq15
  have eq27500 (X0 X2 X3 X4 : G) : ((X3 ◇ X3) ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X4 ◇ X4))) = X0 := superpose eq19 eq27219
  have eq27501 (X0 X1 X2 : G) : ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ (X2 ◇ X2)) = X1 := superpose eq27500 eq384
  have eq27522 (X0 X1 X2 X3 X4 X5 : G) : ((X3 ◇ X3) ◇ (((X4 ◇ X4) ◇ (((X0 ◇ X0) ◇ (((X1 ◇ X1) ◇ X2) ◇ (X1 ◇ X1))) ◇ (X5 ◇ X5))) ◇ (X4 ◇ X4))) = X2 := superpose eq27501 eq2006
  have eq27538 (X0 X1 X2 X3 : G) : (X3 ◇ X3) = ((X2 ◇ X2) ◇ ((((X3 ◇ X3) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ ((X3 ◇ X3) ◇ (X0 ◇ (X1 ◇ X1))))) := superpose eq27522 eq3870
  have eq27541 (X0 X2 X3 : G) : ((X2 ◇ X2) ◇ X0) = (X3 ◇ X3) := superpose eq6971 eq27538
  have eq29053 (X0 X3 : G) : (X3 ◇ X3) = X0 := superpose eq7 eq27541
  have eq30511 (X0 X2 : G) : X0 = X2 := superpose eq29053 eq29053
  have eq30531 (X0 : G) : sK0 ≠ X0 := superpose eq30511 eq8
  subsumption eq30531 eq30511


@[equational_result]
theorem Equation20069_implies_Equation2 (G : Type*) [Magma G] (h : Equation20069 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq9 (X0 X2 X3 X4 : G) : (X0 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = X3 := superpose eq7 eq7
  have eq14 (X0 X1 X3 : G) : (X1 ◇ X0) = X3 := superpose eq9 eq9
  have eq61 (X0 X4 : G) : X0 = X4 := superpose eq7 eq14
  have eq153 (X0 : G) : sK0 ≠ X0 := superpose eq61 eq8
  subsumption eq153 eq61


@[equational_result]
theorem Equation20071_implies_Equation2 (G : Type*) [Magma G] (h : Equation20071 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20072_implies_Equation2 (G : Type*) [Magma G] (h : Equation20072 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20073_implies_Equation2 (G : Type*) [Magma G] (h : Equation20073 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 X3 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X3)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq14 (X0 X4 : G) : X0 = X4 := superpose eq7 eq7
  have eq16 (X0 : G) : sK0 ≠ X0 := superpose eq14 eq8
  subsumption eq16 eq14


@[equational_result]
theorem Equation20075_implies_Equation2 (G : Type*) [Magma G] (h : Equation20075 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X1)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq15 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq17 (X0 : G) : sK0 ≠ X0 := superpose eq15 eq8
  subsumption eq17 eq15


@[equational_result]
theorem Equation20076_implies_Equation2 (G : Type*) [Magma G] (h : Equation20076 G) : Equation2 G := by
  by_contra nh
  simp only [not_forall] at nh
  obtain ⟨sK0, sK1, nh⟩ := nh
  have eq7 (X0 X1 X2 : G) : ((X1 ◇ X1) ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X2)) = X0 := mod_symm (h ..)
  have eq8 : sK0 ≠ sK1 := mod_symm nh
  have eq13 (X0 X3 : G) : X0 = X3 := superpose eq7 eq7
  have eq15 (X0 : G) : sK0 ≠ X0 := superpose eq13 eq8
  subsumption eq15 eq13


